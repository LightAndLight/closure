{-# language FlexibleContexts #-}
{-# language TupleSections #-}
module LL
  ( Ty(..), ANF.LocalName(..), FunName(..)
  , AExpL(..), CExpL(..), Decl(..), Prog(..)
  , lambdaLift
  )
where

import Control.Monad.Writer (MonadWriter, runWriterT, tell)
import Control.Monad.State (MonadState, evalState, get, put)
import Data.Word (Word32)

import Closure (Ty(..))
import qualified ANF

data AExpL a b
  = A_Var (Either a b)
  | A_Ix !Int
  | A_AppF (AExpL a b) (AExpL a b)
  | A_Fun a (AExpL a b)
  | A_Nat32 !Word32
  | A_Unit
  | A_Nil
  | A_AddNat32 (AExpL a b) (AExpL a b)
  deriving (Eq, Show)

data CExpL a b
  = C_AppT (AExpL a b) (AExpL a b)
  | C_Cons (AExpL a b) (AExpL a b)
  | C_ConsMany [AExpL a b]
  | C_Subst (AExpL a b) (AExpL a b)
  deriving (Eq, Show)

data Decl a b
  -- |
  -- At this stage, a lifted lambda takes two arguments: a closure
  -- and a formal parameter
  = D_Fun Ty a Ty [(Ty, b, CExpL a b)] (AExpL a b)
  | D_Val Ty b (CExpL a b)
  deriving (Eq, Show)

newtype FunName = FunName String
  deriving (Eq, Show)

data Prog a b = Prog [Decl a b] (AExpL a b)
  deriving (Eq, Show)

freshFunName :: MonadState Int m => m FunName
freshFunName = do
  n <- get
  FunName ('f' : show n) <$ put (n+1)

toValDecl :: (Ty, b, CExpL a b) -> Decl a b
toValDecl (a, b, c) = D_Val a b c

liftAExp ::
  ( MonadWriter [Decl FunName b] m
  , MonadState Int m
  ) =>
  ANF.AExp b ->
  m (AExpL FunName b)
liftAExp tm =
  case tm of
    ANF.A_Var a -> pure $ A_Var (Right a)
    ANF.A_Ix a -> pure $ A_Ix a
    ANF.A_AppF a b -> A_AppF <$> liftAExp a <*> liftAExp b
    ANF.A_Lam a b inTy retTy -> do
      a' <- liftAExp a
      (b', bdecls) <- liftExp b
      n <- freshFunName
      tell [D_Fun retTy n inTy bdecls b']
      pure $ A_Fun n a'
    ANF.A_Nat32 a -> pure $ A_Nat32 a
    ANF.A_Unit -> pure A_Unit
    ANF.A_Nil -> pure A_Nil
    ANF.A_AddNat32 a b -> A_AddNat32 <$> liftAExp a <*> liftAExp b

liftCExp ::
  ( MonadWriter [Decl FunName b] m
  , MonadState Int m
  ) =>
  ANF.CExp b ->
  m (CExpL FunName b)
liftCExp tm =
  case tm of
    ANF.C_AppT a b -> C_AppT <$> liftAExp a <*> liftAExp b
    ANF.C_Cons a b -> C_Cons <$> liftAExp a <*> liftAExp b
    ANF.C_ConsMany a -> C_ConsMany <$> traverse liftAExp a
    ANF.C_Subst a b -> C_Subst <$> liftAExp a <*> liftAExp b

liftExp ::
  ( MonadState Int m
  , MonadWriter [Decl FunName b] m
  )=>
  ANF.Exp b ->
  m (AExpL FunName b, [(Ty, b, CExpL FunName b)])
liftExp e =
  case e of
    ANF.E_Let a ty b c -> do
      b' <- liftCExp b
      (c', cdecls) <- liftExp c
      pure (c', (ty, a, b') : cdecls)
    ANF.E_AExp a -> (, []) <$> liftAExp a

lambdaLift :: ANF.Exp b -> Prog FunName b
lambdaLift e = Prog (decls <> fmap toValDecl adecls) a
  where
    ((a, adecls), decls) = evalState (runWriterT $ liftExp e) 0