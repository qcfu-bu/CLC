open Bindlib
open Names
open Terms
open Context

exception NonPureContextExn of t VarMap.t * int

exception UnexpectedTypeExn of t * t

exception UnexpectedContextExn of t VarMap.t * t VarMap.t

exception LinearFixExn of t * ty

exception InferMetaExn of Meta.t

exception InferLambdaExn of t

exception InferFixExn of t

exception InferAppExn of t

exception InferMatchNonInductiveExn of t

exception InferMatchLinearMotiveExn of t * ty

exception InferMatchMotiveFailedExn of t * ty

exception InferPscopeUnevenLength of pscope * int

exception InferTscopeUnevenLength of tscope * int

exception CheckMetaExn of Meta.t

exception CheckMatchNonInductiveExn of t

exception CheckMotive of mot

exception CoverageExn of pbinder list

exception CoverageArityPscopeExn of pscope * t list

exception CoverageArityTscopeExn of tscope * t var list

exception CoverageStripExn of p

exception ParamTscopeExn of ty

exception ParamTscopeParamExn of t var list * t list

exception CheckTscopeExn of ty * sort * sort
