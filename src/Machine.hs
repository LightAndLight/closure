module Machine where

import Prelude hiding (read)

import Control.Monad (when)
import Control.Monad.ST (ST, runST)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans (lift)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef)
import Data.Vector (Vector)
import Data.Vector.Mutable (MVector)

import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as MVector

import Closure (Exp(..), toInt, toList)

data Prim
  = Addr Int
  | Var Int
  deriving (Eq, Show)

data Node
  = NodeAppF Prim Prim
  | NodeAppT Prim Prim
  | NodeLam Prim Prim
  | NodeUnit
  | NodeClosure (Vector Prim)
  deriving (Eq, Show)

data Cell
  = Node Node
  | Blackhole
  | Empty
  deriving (Eq, Show)

data Action
  = Apply Prim
  | Update Int
  | Spread Int
  | Extend Prim
  deriving (Eq, Show)

data State s
  = State
  { heapPointer :: STRef s Int
  , heap :: MVector s Cell
  , stack :: STRef s [Action]
  , current :: STRef s Prim
  }

data Trace
  = Trace
  { traceHP :: Int
  , traceHeap :: Vector Cell
  , traceStack :: [Action]
  , traceCurrent :: Prim
  } deriving (Eq, Show)

traceState :: State s -> ST s Trace
traceState st = do
  h <- readSTRef $ heapPointer st
  hp <- Vector.freeze $ heap st
  stk <- readSTRef $ stack st
  cur <- readSTRef $ current st
  pure $
    Trace
    { traceHP = h
    , traceHeap = hp
    , traceStack = stk
    , traceCurrent = cur
    }

data RuntimeError
  = HeapExhausted
  | OutOfBounds
  | InvalidNode
  | Loop
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
    Just n -> pure $ Var n

loadCtx :: State s -> Exp -> ExceptT RuntimeError (ST s) Prim
loadCtx st e =
  case toList e of
    Nothing -> throwError InvalidNode
    Just as -> do
      as' <- traverse (load st) as
      Addr <$> alloc st (Node $ NodeClosure $ Vector.fromList as')

load :: State s -> Exp -> ExceptT RuntimeError (ST s) Prim
load st e =
  case e of
    Z{} -> loadVar e
    S{} -> loadVar e
    AppF a b -> do
      a' <- load st a
      b' <- load st b
      Addr <$> alloc st (Node $ NodeAppF a' b')
    AppT a b -> do
      a' <- load st a
      b' <- load st b
      Addr <$> alloc st (Node $ NodeAppT a' b')
    Lam a b -> do
      a' <- load st a
      b' <- load st b
      Addr <$> alloc st (Node $ NodeLam a' b')
    Nil{} -> loadCtx st e
    Cons{} -> loadCtx st e
    Unit -> Addr <$> alloc st (Node NodeUnit)
    Ann a _ -> load st a

initialState :: Int -> ST s (State s)
initialState sz = do
  hp <- newSTRef 0
  h <- MVector.replicate sz Empty
  stk <- newSTRef []
  cur <- newSTRef undefined
  pure $
    State
    { heapPointer = hp
    , heap = h
    , stack = stk
    , current = cur
    }

run :: Int -> Exp -> Either RuntimeError [Trace]
run sz e =
  runST $ do
    st <- initialState sz
    runExceptT $ eval st e

eval :: State s -> Exp -> ExceptT RuntimeError (ST s) [Trace]
eval st e = do
  start <- load st e
  lift $ writeSTRef (current st) start
  go
  where
    go = do
      tr <- lift $ traceState st
      cur <- lift $ readSTRef (current st)
      case cur of
        Var{} -> pure []
        Addr addr -> do
          c <- read st addr
          insts <- lift $ readSTRef (stack st)
          case insts of
            Update a : rest -> do
              update st a c

              lift $ writeSTRef (stack st) rest
              (tr :) <$> go
            _ ->
              case c of
                Blackhole -> throwError Loop
                Empty -> throwError InvalidNode
                Node n ->
                  case n of
                    NodeAppF a b -> do
                      insts <- lift $ readSTRef (stack st)
                      case insts of
                        Spread clAddr : rest -> do
                          x <- alloc st . Node $ NodeAppT (Addr clAddr) a
                          y <- alloc st . Node $ NodeAppT (Addr clAddr) b
                          update st addr . Node $ NodeAppT (Addr x) (Addr y)

                          lift $ writeSTRef (stack st) rest
                          (tr :) <$> go
                        _ -> pure [tr]
                    NodeUnit -> pure [tr]
                    NodeLam a b -> do
                      insts <- lift $ readSTRef (stack st)
                      case insts of
                        Apply c : rest ->
                          case a of
                            Var{} -> throwError InvalidNode
                            Addr a' -> do
                              lift $ writeSTRef (current st) (Addr a')

                              lift $ writeSTRef (stack st) (Extend c : Apply b : rest)
                              (tr :) <$> go
                        Spread clAddr : rest -> do
                          addr' <- alloc st (Node $ NodeAppT (Addr clAddr) a)
                          update st addr . Node $ NodeLam (Addr addr') b

                          lift $ writeSTRef (stack st) rest
                          (tr :) <$> go
                        _ -> pure [tr]
                    NodeClosure cl -> do
                      insts <- lift $ readSTRef (stack st)
                      case insts of
                        Apply c : rest -> do
                          lift $ case c of
                            Var n -> do
                              writeSTRef (current st) (cl Vector.! n)
                              writeSTRef (stack st) rest
                            Addr a -> do
                              writeSTRef (current st) (Addr a)
                              writeSTRef (stack st) (Spread addr : rest)
                          (tr :) <$> go
                        Spread clAddr : rest -> do
                          cl' <-
                            traverse
                            (\p -> Addr <$> alloc st (Node $ NodeAppT (Addr clAddr) p))
                            cl
                          update st addr . Node $ NodeClosure cl'

                          lift $ writeSTRef (stack st) rest
                          (tr :) <$> go
                        Extend p : rest -> do
                          addr' <- alloc st . Node $ NodeClosure (Vector.cons p cl)
                          lift $ writeSTRef (current st) (Addr addr')

                          lift $ writeSTRef (stack st) rest
                          (tr :) <$> go
                        _ -> pure [tr]
                    NodeAppT a b -> do
                      lift $ modifySTRef (stack st) ((Apply b :) . (Update addr :))

                      lift $ writeSTRef (current st) a
                      (tr :) <$> go