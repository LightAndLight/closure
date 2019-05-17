{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LLVM where

import Control.Monad (void)
import Control.Monad.Reader (MonadReader, asks, local)
import Data.Foldable (traverse_)

import LLVM.AST (Operand)
import LLVM.IRBuilder (MonadModuleBuilder, MonadIRBuilder)

import qualified LLVM.AST.Constant as LLVM
import qualified LLVM.AST.Name as LLVM
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.IRBuilder as LLVM

import LL

data Env
  = Env
  { names :: [(Either FunName LocalName, Operand)]
  , args :: Maybe (Operand, Operand)
  }

aexpLLVM ::
  ( MonadIRBuilder m
  , MonadReader Env m
  ) =>
  AExpL FunName LocalName ->
  m Operand
aexpLLVM tm =
  case tm of
    A_Var a -> do
      mv <- asks $ lookup a . names
      case mv of
        Nothing -> error "missing variable"
        Just v -> pure v
    A_Ix a -> do
      mv <- asks args
      case mv of
        Nothing -> error "not in function"
        Just (env, arg) ->
          case a of
            0 -> pure arg
            n -> LLVM.extractValue env [fromIntegral $ n-1]
    A_AppF a b -> error "appF unsupported"
    A_Fun a b -> do
      b' <- aexpLLVM b
      clos <-
        LLVM.struct
          Nothing
          False
          [ LLVM.Undef $ LLVM.ptr LLVM.void
          , LLVM.Undef $
            LLVM.FunctionType
              LLVM.void
              [LLVM.ptr LLVM.void, LLVM.void]
              False
          ]
      mv <- asks $ lookup (Left a) . names
      case mv of
        Nothing -> error "function name not found"
        Just v -> do
          LLVM.insertValue clos b' [0]
          LLVM.insertValue clos v [1]
    A_Nat32 a -> LLVM.int32 $ fromIntegral a
    A_Unit -> LLVM.array []
    A_Nil -> LLVM.array []
    A_AddNat32 a b -> do
      a' <- aexpLLVM a
      b' <- aexpLLVM b
      LLVM.add a' b'

tyLLVM :: Ty -> LLVM.Type
tyLLVM t =
  case t of
    TyArr a b ->
      LLVM.StructureType
        False
        [ LLVM.ptr LLVM.void
        , LLVM.FunctionType
            (tyLLVM b)
            [LLVM.ptr LLVM.void, tyLLVM a]
            False
        ]
    TyUnit -> LLVM.void
    TyNat32 -> LLVM.i32
    TySub{} -> LLVM.ptr LLVM.void

valDeclLLVM ::
  ( MonadModuleBuilder m
  , MonadReader Env m
  ) =>
  (Ty, LocalName, CExpL FunName LocalName) ->
  m Operand
valDeclLLVM (ty, n, body) = _

valDeclsLLVM ::
  ( MonadModuleBuilder m
  , MonadReader Env m
  ) =>
  [(Ty, LocalName, CExpL FunName LocalName)] ->
  m a ->
  m a
valDeclsLLVM [] m = m
valDeclsLLVM (d@(_, n, _) : ds) m = do
  vname <- valDeclLLVM d
  local (\e -> e { names = (Right n, vname) : names e}) $
    valDeclsLLVM ds m

declsLLVM ::
  ( MonadModuleBuilder m
  , MonadReader Env m
  ) =>
  [Decl FunName LocalName] ->
  m a ->
  m a
declsLLVM [] m = m
declsLLVM (d : ds) m =
  case d of
    D_Fun retTy (FunName n) inTy body ret -> do
      fname <-
        LLVM.function
          (LLVM.mkName n)
          [ (LLVM.ptr LLVM.void, LLVM.ParameterName "env")
          , (tyLLVM inTy, LLVM.ParameterName "x")
          ]
          (tyLLVM retTy) $ \[env, arg] ->
            local (\e -> e { args = Just (env, arg) }) $
            valDeclsLLVM body $ LLVM.ret =<< aexpLLVM ret
      local (\e -> e { names = (Left $ FunName n, fname) : names e}) $
        declsLLVM ds m
    D_Val ty n body -> do
      vname <- valDeclLLVM (ty, n, body)
      local (\e -> e { names = (Right n, vname) : names e}) $
        declsLLVM ds m

progLLVM ::
  ( MonadModuleBuilder m
  , MonadReader Env m
  ) =>
  Prog FunName LocalName ->
  m ()
progLLVM (Prog ds val) =
  declsLLVM ds $
  void . LLVM.function "main" [] LLVM.i32 $ \_ -> do
    LLVM.ret =<< aexpLLVM val
