module Machine where

import Prelude hiding (read)

import Control.Monad (when)
import Control.Monad.ST (ST, runST)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans (lift)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef)
import Data.Vector (Vector)
import Data.Vector.Mutable (MVector)
import Data.Word (Word32)

import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as MVector

import Closure (Exp(..), toInt, toList)

data Prim
  = PAddr !Int
  | PVar !Int
  | PNat32 !Word32
  deriving (Eq, Show)

data PrimOp
  = PAddNat32 Prim Prim
  deriving (Eq, Show)

data Node
  = NodeAppF Prim Prim
  | NodeAppT Prim Prim
  | NodeSubst Prim Prim
  | NodeLam Prim Prim
  | NodeUnit
  | NodeClosure (Vector Prim)
  | NodePrimOp PrimOp
  deriving (Eq, Show)

data Code = CPrim Prim | CNode Node
  deriving (Eq, Show)

data Cell
  = Node Node
  | Prim Prim
  | Blackhole
  | Empty
  deriving (Eq, Show)

data Action
  = Eval
  | Apply Prim
  | Update Int
  | Spread Prim
  | Extend Prim
  deriving (Eq, Show)

data State s
  = State
  { heapPointer :: STRef s Int
  , heap :: MVector s Cell
  , kont :: STRef s [Action]
  , code :: STRef s Code
  }

data Trace
  = Trace
  { traceHP :: Int
  , traceHeap :: Vector Cell
  , traceKont :: [Action]
  , traceCode :: Code
  } deriving (Eq, Show)

traceState :: State s -> ST s Trace
traceState st = do
  h <- readSTRef $ heapPointer st
  hp <- Vector.freeze $ heap st
  ks <- readSTRef $ kont st
  cde <- readSTRef $ code st
  pure $
    Trace
    { traceHP = h
    , traceHeap = hp
    , traceKont = ks
    , traceCode = cde
    }

data RuntimeError
  = HeapExhausted
  | OutOfBounds
  | InvalidNode
  | Loop
  | InvalidState Trace
  deriving (Eq, Show)

alloc :: State s -> Cell -> ExceptT RuntimeError (ST s) Int
alloc st n = do
  addr <- lift $ readSTRef (heapPointer st)
  when (addr == MVector.length (heap st)) $ throwError HeapExhausted
  lift $ writeSTRef (heapPointer st) (addr+1)
  addr <$ MVector.write (heap st) addr n

checkBounds :: State s -> Int -> ExceptT RuntimeError (ST s) ()
checkBounds st addr = do
  hp <- lift $ readSTRef (heapPointer st)
  when (addr >= hp) $ throwError OutOfBounds

update :: State s -> Int -> Cell -> ExceptT RuntimeError (ST s) ()
update st addr c = checkBounds st addr *> MVector.write (heap st) addr c

read :: State s -> Int -> ExceptT RuntimeError (ST s) Cell
read st addr = checkBounds st addr *> MVector.read (heap st) addr

loadVar :: Exp a -> ExceptT RuntimeError (ST s) Prim
loadVar e =
  case toInt e of
    Nothing -> throwError InvalidNode
    Just n -> pure $ PVar n

loadCtx :: State s -> Exp a -> ExceptT RuntimeError (ST s) Prim
loadCtx st e =
  case toList e of
    Nothing -> throwError InvalidNode
    Just as -> do
      as' <- traverse (load st) as
      PAddr <$> alloc st (Node $ NodeClosure $ Vector.fromList as')

load :: State s -> Exp a -> ExceptT RuntimeError (ST s) Prim
load st e =
  case e of
    VZ{} -> loadVar e
    VS{} -> loadVar e
    Nat32 _ n -> pure $ PNat32 n
    AppF _ a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeAppF a' b')
    AppT _ a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeAppT a' b')
    Subst _ a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeSubst a' b')
    Lam _ a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeLam a' b')
    Nil{} -> loadCtx st e
    Cons{} -> loadCtx st e
    Unit _ -> PAddr <$> alloc st (Node NodeUnit)
    AddNat32 _ a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodePrimOp $ PAddNat32 a' b')

initialState :: Int -> ST s (State s)
initialState sz = do
  hp <- newSTRef 0
  h <- MVector.replicate sz Empty
  ks <- newSTRef []
  cde <- newSTRef undefined
  pure $
    State
    { heapPointer = hp
    , heap = h
    , kont = ks
    , code = cde
    }

run :: Int -> Exp a -> Either RuntimeError [Trace]
run sz e =
  runST $ do
    st <- initialState sz
    runExceptT $ eval st e

eval :: State s -> Exp a -> ExceptT RuntimeError (ST s) [Trace]
eval st e = do
  start <- load st e
  lift $ writeSTRef (code st) (CPrim start)
  lift $ modifySTRef (kont st) (Eval :)
  go
  where
    halt tr = pure [tr]

    continue tr = (tr :) <$> go

    invalidState :: Trace -> ExceptT RuntimeError (ST s) a
    invalidState tr = throwError $ InvalidState tr

    go = do
      tr <- lift $ traceState st
      insts <- lift $ readSTRef (kont st)
      case insts of
        [] -> halt tr
        Update a : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim p -> update st a $ Prim p
            CNode n -> update st a $ Node n
          lift $ writeSTRef (kont st) rest
          continue tr
        Apply arg : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim{} -> invalidState tr
            CNode n ->
              case n of
                NodePrimOp{} -> invalidState tr
                NodeAppF{} -> do
                  addr' <- PAddr <$> alloc st (Node n)
                  lift $ writeSTRef (code st) (CNode $ NodeAppF addr' arg)
                  lift $ writeSTRef (kont st) rest
                NodeSubst{} ->
                  lift $ modifySTRef (kont st) (Eval :)
                NodeAppT{} ->
                  lift $ modifySTRef (kont st) (Eval :)
                NodeLam a b -> do
                  lift $ writeSTRef (code st) (CPrim a)
                  lift $ writeSTRef (kont st) (Eval : Extend arg : Apply b : Eval : rest)
                NodeUnit -> invalidState tr
                NodeClosure{} -> invalidState tr
          continue tr
        Extend addr : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim{} -> invalidState tr
            CNode n ->
              case n of
                NodeClosure cl -> do
                  lift $ writeSTRef (code st) (CNode $ NodeClosure $ Vector.cons addr cl)
                  lift $ writeSTRef (kont st) rest
                  continue tr
                _ -> invalidState tr
        Spread arg : rest -> do
          cur <- lift $ readSTRef (code st)
          case arg of
            PAddr addr ->
              case cur of
                CPrim p ->
                  case p of
                    PNat32{} -> invalidState tr
                    PVar v -> do
                      c <- read st addr
                      case c of
                        Node (NodeClosure cl) -> lift $ writeSTRef (code st) (CPrim $ cl Vector.! v)
                        _ -> invalidState tr
                    PAddr{} -> lift $ modifySTRef (kont st) (Eval :)
                CNode n ->
                  case n of
                    NodePrimOp p -> do
                      c <- read st addr
                      case c of
                        Node (NodeClosure cl) ->
                          case p of
                            PAddNat32 a b -> do
                              a' <-
                                case a of
                                  PNat32{} -> pure a
                                  PAddr{} -> invalidState tr
                                  PVar v -> pure $ cl Vector.! v
                              b' <-
                                case b of
                                  PNat32{} -> pure b
                                  PAddr{} -> invalidState tr
                                  PVar v -> pure $ cl Vector.! v
                              lift $ writeSTRef (code st) (CNode $ NodePrimOp $ PAddNat32 a' b')
                              lift $ writeSTRef (kont st) rest
                        _ -> invalidState tr
                    NodeUnit -> invalidState tr
                    NodeAppF a b -> do
                      a' <- PAddr <$> alloc st (Node $ NodeAppT (PAddr addr) a)
                      b' <- PAddr <$> alloc st (Node $ NodeAppT (PAddr addr) b)
                      lift $ writeSTRef (code st) (CNode $ NodeAppT a' b')
                      lift $ writeSTRef (kont st) rest
                    NodeSubst{} -> lift $ modifySTRef (kont st) (Eval :)
                    NodeAppT{} -> lift $ modifySTRef (kont st) (Eval :)
                    NodeLam a b -> do
                      a' <- PAddr <$> alloc st (Node $ NodeAppT (PAddr addr) a)
                      lift $ writeSTRef (code st) (CNode $ NodeLam a' b)
                      lift $ writeSTRef (kont st) rest
                    NodeClosure cl -> do
                      cl' <- traverse (\c -> PAddr <$> alloc st (Node $ NodeAppT (PAddr addr) c)) cl
                      lift $ writeSTRef (code st) (CNode $ NodeClosure cl')
                      lift $ writeSTRef (kont st) rest
            _ -> invalidState tr
          continue tr
        Eval : rest -> do
          cur <- lift $ readSTRef (code st)
          let
            evalNode n =
              case n of
                NodePrimOp p ->
                  case p of
                    PAddNat32 a b ->
                      case (a, b) of
                        (PNat32 v1, PNat32 v2) ->
                          lift $ writeSTRef (code st) (CPrim $ PNat32 (v1+v2))
                        _ -> pure ()
                NodeAppF{} -> pure ()
                NodeUnit -> pure ()
                NodeLam{} -> pure ()
                NodeClosure{} -> pure ()
                NodeSubst a b -> do
                  lift $ writeSTRef (code st) (CPrim b)
                  lift $ writeSTRef (kont st) (Spread a : rest)
                NodeAppT a b -> do
                  lift $ writeSTRef (code st) (CPrim a)
                  lift $ modifySTRef (kont st) ((:) Eval . (:) (Apply b))

          case cur of
            CPrim p ->
              case p of
                PVar{} -> do
                  lift $ writeSTRef (kont st) rest
                  continue tr
                PNat32{} -> do
                  lift $ writeSTRef (kont st) rest
                  continue tr
                PAddr addr -> do
                  c <- read st addr
                  case c of
                    Prim p' -> do
                      lift $ writeSTRef (code st) (CPrim p')
                      lift $ writeSTRef (kont st) rest
                      continue tr
                    Blackhole -> throwError Loop
                    Empty -> throwError OutOfBounds
                    Node n -> do
                      lift $ writeSTRef (kont st) (Update addr : rest)
                      lift $ writeSTRef (code st) (CNode n)
                      evalNode n
                      continue tr
            CNode n -> do
              lift $ writeSTRef (kont st) rest
              evalNode n
              continue tr