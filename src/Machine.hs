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
  | PNat !Word32
  deriving (Eq, Show)

data Node
  = NodeAppF Prim Prim
  | NodeAppT Prim Prim
  | NodeLam Prim Prim
  | NodeUnit
  | NodeNat Word32
  | NodeNatS
  | NodeClosure (Vector Prim)
  deriving (Eq, Show)

data Code = CPrim Prim | CNode Node
  deriving (Eq, Show)

data Cell
  = Node Node
  | Blackhole
  | Empty
  deriving (Eq, Show)

data PrimOp
  = PSuc
  deriving (Eq, Show)

data Action
  = Eval
  | Apply Prim
  | Update Int
  | Spread Int
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

loadVar :: Exp -> ExceptT RuntimeError (ST s) Prim
loadVar e =
  case toInt e of
    Nothing -> throwError InvalidNode
    Just n -> pure $ PVar n

loadCtx :: State s -> Exp -> ExceptT RuntimeError (ST s) Prim
loadCtx st e =
  case toList e of
    Nothing -> throwError InvalidNode
    Just as -> do
      as' <- traverse (load st) as
      PAddr <$> alloc st (Node $ NodeClosure $ Vector.fromList as')

load :: State s -> Exp -> ExceptT RuntimeError (ST s) Prim
load st e =
  case e of
    VZ{} -> loadVar e
    VS{} -> loadVar e
    NatZ -> pure $ PNat 0
    NatS -> PAddr <$> alloc st (Node NodeNatS)
    Nat n -> pure $ PNat n
    AppF a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeAppF a' b')
    AppT a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeAppT a' b')
    Lam a b -> do
      a' <- load st a
      b' <- load st b
      PAddr <$> alloc st (Node $ NodeLam a' b')
    Nil{} -> loadCtx st e
    Cons{} -> loadCtx st e
    Unit -> PAddr <$> alloc st (Node NodeUnit)
    Ann a _ -> load st a

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

run :: Int -> Exp -> Either RuntimeError [Trace]
run sz e =
  runST $ do
    st <- initialState sz
    runExceptT $ eval st e

eval :: State s -> Exp -> ExceptT RuntimeError (ST s) [Trace]
eval st e = do
  start <- load st e
  lift $ writeSTRef (code st) (CPrim start)
  lift $ modifySTRef (kont st) (Eval :)
  go
  where
    halt = do
      tr <- lift $ traceState st
      pure [tr]

    continue = do
      tr <- lift $ traceState st
      (tr :) <$> go

    invalidState = do
      tr <- lift $ traceState st
      throwError $ InvalidState tr

    go = do
      insts <- lift $ readSTRef (kont st)
      case insts of
        [] -> halt
        Update a : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim{} -> invalidState
            CNode n -> update st a $ Node n
          lift $ writeSTRef (kont st) rest
          continue
        Apply arg : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim{} -> invalidState
            CNode n ->
              case n of
                NodeAppF{} -> do
                  addr' <- PAddr <$> alloc st (Node n)
                  lift $ writeSTRef (code st) (CNode $ NodeAppF addr' arg)
                  lift $ writeSTRef (kont st) rest
                NodeAppT{} -> lift $ modifySTRef (kont st) (Eval :)
                NodeLam a b -> do
                  lift $ writeSTRef (code st) (CPrim a)
                  lift $ writeSTRef (kont st) (Extend arg : Apply b : rest)
                NodeUnit -> invalidState
                NodeNat{} -> invalidState
                NodeNatS ->
                  case arg of
                    PNat num -> do
                      lift $ writeSTRef (code st) (CPrim $ PNat (num+1))
                      lift $ writeSTRef (kont st) rest
                    _ -> invalidState
                NodeClosure cl -> do
                  addr' <- alloc st (Node n)
                  lift $ writeSTRef (kont st) (Spread addr' : rest)
                  lift $ writeSTRef (code st) (CPrim arg)
          continue
        Extend addr : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim{} -> invalidState
            CNode n ->
              case n of
                NodeClosure cl -> do
                  addr' <- PAddr <$> alloc st (Node $ NodeClosure $ Vector.cons addr cl)
                  lift $ writeSTRef (kont st) rest
                  lift $ writeSTRef (code st) (CPrim addr')
                  continue
                _ -> invalidState
        Spread addr : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim p ->
              case p of
                PNat{} -> invalidState
                PVar v -> do
                  c <- read st addr
                  case c of
                    Node (NodeClosure cl) -> lift $ writeSTRef (code st) (CPrim $ cl Vector.! v)
                    _ -> invalidState
                PAddr{} -> lift $ modifySTRef (kont st) (Eval :)
            CNode n ->
              case n of
                NodeUnit -> invalidState
                NodeNatS -> invalidState
                NodeNat{} -> invalidState
                NodeAppF a b -> _
                NodeAppT{} -> _
                NodeLam a b -> _
                NodeClosure cl -> _
          continue
        Eval : rest -> do
          cur <- lift $ readSTRef (code st)
          case cur of
            CPrim p ->
              case p of
                PVar{} -> do
                  lift $ writeSTRef (kont st) rest
                  continue
                PNat{} -> do
                  lift $ writeSTRef (kont st) rest
                  continue
                PAddr addr -> do
                  c <- read st addr
                  case c of
                    Blackhole -> throwError Loop
                    Empty -> throwError OutOfBounds
                    Node n -> do
                      lift $ writeSTRef (code st) (CNode n)
                      lift $ writeSTRef (kont st) (Update addr : rest)
                      continue
            CNode n -> do
              case n of
                NodeNat{} -> lift $ writeSTRef (kont st) rest
                NodeNatS -> lift $ writeSTRef (kont st) rest
                NodeAppF{} -> lift $ writeSTRef (kont st) rest
                NodeUnit -> lift $ writeSTRef (kont st) rest
                NodeLam{} -> lift $ writeSTRef (kont st) rest
                NodeClosure{} -> lift $ writeSTRef (kont st) rest
                NodeAppT a b -> do
                  lift $ writeSTRef (code st) (CPrim a)
                  lift $ writeSTRef (kont st) (Eval : Apply b : rest)
              continue