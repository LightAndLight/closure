{-# language FlexibleContexts #-}
module ANF where

import Control.Monad.State (MonadState, evalStateT, get, put)
import Control.Monad.Writer (MonadWriter, runWriter, tell)
import Data.Monoid (Endo(..))
import Data.Word (Word32)

import qualified Closure

data AExp a
  = A_Var a
  | A_Ix !Int
  | A_AppF (AExp a) (AExp a)
  | A_Lam (AExp a) (AExp a)
  | A_Nat32 !Word32
  | A_Unit
  | A_Nil
  | A_Cons (AExp a) (AExp a)
  | A_AddNat32 (AExp a) (AExp a)
  deriving (Eq, Show)

data CExp a
  = C_AppT (AExp a) (AExp a)
  | C_Subst (AExp a) (AExp a)
  deriving (Eq, Show)

data Exp a
  = E_Let String (CExp a) (Exp a)
  | E_AExp (AExp a)
  deriving (Eq, Show)

fresh :: MonadState Int m => m Int
fresh = do
  n <- get
  n <$ put (n+1)

aexp ::
  ( MonadWriter (Endo (Exp String)) m
  , MonadState Int m
  ) =>
  Closure.Exp ->
  m (AExp String)
aexp tm =
  case tm of
    Closure.VZ{} ->
      case Closure.toInt tm of
        Nothing -> error "malformed index"
        Just a -> pure $ A_Ix a
    Closure.VS{} ->
      case Closure.toInt tm of
        Nothing -> error "malformed index"
        Just a -> pure $ A_Ix a
    Closure.AppF a b -> A_AppF <$> aexp a <*>  aexp b
    Closure.AppT a b -> do
      va <- aexp a
      vb <- aexp b
      var <- ('v' :) . show <$> fresh
      tell . Endo $ E_Let var (C_AppT va vb)
      pure $ A_Var var
    Closure.Subst a b -> do
      va <- aexp a
      vb <- aexp b
      var <- ('v' :) . show <$> fresh
      tell . Endo $ E_Let var (C_Subst va vb)
      pure $ A_Var var
    Closure.Lam a b -> A_Lam <$> aexp a <*> aexp b
    Closure.Nil -> pure A_Nil
    Closure.Cons a b -> A_Cons <$> aexp a <*> aexp b
    Closure.Unit -> pure A_Unit
    Closure.Ann a _ -> aexp a
    Closure.Nat32 a -> pure $ A_Nat32 a
    Closure.AddNat32 a b -> A_AddNat32 <$> aexp a <*> aexp b

anf :: Closure.Exp -> Exp String
anf tm = appEndo rest $ E_AExp v
  where
    (v, rest) = runWriter $ evalStateT (aexp tm) 0
