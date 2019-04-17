module Machine where

import Prelude hiding (read)

import Control.Monad (when)
import Control.Monad.ST (ST)
import Control.Monad.Except (ExceptT, throwError)
import Control.Monad.Trans (lift)
import Data.STRef (STRef, readSTRef, writeSTRef, modifySTRef)
import Data.Vector (Vector)
import Data.Vector.Mutable (MVector)

import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as MVector

import Closure

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
  deriving (Eq, Show)

data Action
  = Apply Prim
  | Update Int
  deriving (Eq, Show)

data State s
  = State
  { heapPointer :: STRef s Int
  , heap :: MVector s Cell
  , env :: STRef s (Vector Prim)
  , stack :: STRef s [Action]
  , current :: STRef s Prim
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

eval :: State s -> Exp -> ExceptT RuntimeError (ST s) ()
eval st e = do
  start <- load st e
  lift $ writeSTRef (current st) start
  go
  where
    go = do
      cur <- lift $ readSTRef (current st)
      case cur of
        Var{} -> pure ()
        Addr addr -> do
          c <- read st addr
          case c of
            Blackhole -> throwError Loop
            Node n ->
              case n of
                NodeAppF{} -> pure ()
                NodeUnit -> pure ()
                NodeLam a b -> do
                  insts <- lift $ readSTRef (stack st)
                  case insts of
                    Apply c : rest -> do
                      case a of
                        Var{} -> throwError InvalidNode
                        Addr a' -> do
                          a'' <- read st a'
                          case a'' of
                            Blackhole -> throwError Loop
                            Node (NodeClosure cl) -> do
                              addr' <- alloc st (Node $ NodeClosure $ Vector.cons c cl)
                              lift $ writeSTRef (stack st) rest
                              update st addr (Node $ NodeAppT (Addr addr') b)
                            _ -> throwError InvalidNode
                    _ -> pure ()
                NodeClosure cl -> do
                  insts <- lift $ readSTRef (stack st)
                  case insts of
                    Apply c : rest ->
                      case c of
                        Var n -> lift $ writeSTRef (current st) (cl Vector.! n)
                        Addr a -> _
                    _ -> pure ()
                NodeAppT a b ->
                  lift $ do
                    modifySTRef (stack st) ((Apply b :) . (Update addr :))
                    writeSTRef (current st) a