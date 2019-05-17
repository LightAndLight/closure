{-# language FlexibleContexts #-}
module ANF where

import Control.Monad.State (MonadState, evalStateT, get, put)
import Control.Monad.Writer (MonadWriter, runWriter, runWriterT, tell)
import Data.Monoid (Endo(..))
import Data.Word (Word32)

import qualified Closure

data AExp a
  = A_Var a
  | A_Ix !Int
  | A_AppF (AExp a) (AExp a)
  | A_Lam (AExp a) (Exp a) Closure.Ty Closure.Ty
  | A_Nat32 !Word32
  | A_Unit
  | A_Nil
  | A_AddNat32 (AExp a) (AExp a)
  deriving (Eq, Show)

data CExp a
  = C_AppT (AExp a) (AExp a)
  | C_Cons (AExp a) (AExp a)
  | C_ConsMany [AExp a]
  | C_Subst (AExp a) (AExp a)
  deriving (Eq, Show)

data Exp a
  = E_Let a Closure.Ty (CExp a) (Exp a)
  | E_AExp (AExp a)
  deriving (Eq, Show)

newtype LocalName = LocalName String
  deriving (Eq, Show)

freshLocalName :: MonadState Int m => m LocalName
freshLocalName = do
  n <- get
  LocalName ('x' : show n) <$ put (n+1)

aexp ::
  ( MonadWriter (Endo (Exp LocalName)) m
  , MonadState Int m
  ) =>
  Closure.Exp Closure.Ty ->
  m (AExp LocalName, Closure.Ty)
aexp tm =
  case tm of
    Closure.VZ t ->
      case Closure.toInt tm of
        Nothing -> error "malformed index"
        Just a -> pure (A_Ix a, t)
    Closure.VS t _ ->
      case Closure.toInt tm of
        Nothing -> error "malformed index"
        Just a -> pure (A_Ix a, t)
    Closure.AppF t a b -> do
      (a', _) <- aexp a
      (b', _) <- aexp b
      pure (A_AppF a' b', t)
    Closure.AppT t a b -> do
      (va, _) <- aexp a
      (vb, _) <- aexp b
      var <- freshLocalName
      tell . Endo $ E_Let var t (C_AppT va vb)
      pure (A_Var var, t)
    Closure.Subst t a b -> do
      (va, _) <- aexp a
      (vb, _) <- aexp b
      var <- freshLocalName
      tell . Endo $ E_Let var t (C_Subst va vb)
      pure (A_Var var, t)
    Closure.Lam t a b ->
      case t of
        Closure.TyArr inTy outTy -> do
          (a', _) <- aexp a
          (b', _) <- exp_ b
          pure (A_Lam a' b' inTy outTy, t)
        _ -> error "incorrect type for lam"
    Closure.Nil t -> pure (A_Nil, t)
    Closure.Cons t a b ->
      case Closure.toList tm of
        Nothing -> do
          (va, _) <- aexp a
          (vb, _) <- aexp b
          var <- freshLocalName
          tell . Endo $ E_Let var t (C_Cons va vb)
          pure (A_Var var, t)
        Just ls -> do
          ls' <- traverse (fmap fst . aexp) ls
          var <- freshLocalName
          tell . Endo $ E_Let var t (C_ConsMany ls')
          pure (A_Var var, t)
    Closure.Unit t -> pure (A_Unit, t)
    Closure.Nat32 t a -> pure (A_Nat32 a, t)
    Closure.AddNat32 t a b -> do
      (a', _) <- aexp a
      (b', _) <- aexp b
      pure (A_AddNat32 a' b', t)

exp_ ::
  MonadState Int m =>
  Closure.Exp Closure.Ty ->
  m (Exp LocalName, Closure.Ty)
exp_ tm = do
  ((v, t), rest) <- runWriterT $ aexp tm
  pure (appEndo rest $ E_AExp v, t)

anf :: Closure.Exp Closure.Ty -> Exp LocalName
anf tm = appEndo rest $ E_AExp v
  where
    ((v, _), rest) = runWriter $ evalStateT (aexp tm) 0