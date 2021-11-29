open Bindlib
open Names
open Terms
open Context
open Format

exception UnificationFailure of t * t

exception OccursCheckFailure of Meta.t * t

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

let _ =
  Printexc.register_printer (function
    | UnificationFailure (t1, t2) ->
      Some (asprintf "UnificationFailure (%a, %a)" Terms.pp t1 Terms.pp t2)
    | OccursCheckFailure (x, t) ->
      Some (asprintf "OccursCheckFailure (%a, %a)" Meta.pp x Terms.pp t)
    | NonPureContextExn (ctx, i) ->
      Some (asprintf "NonPureContextExn (%a, %d)" pp' ctx i)
    | UnexpectedTypeExn (ty1, ty2) ->
      Some (asprintf "UnexpectedTypeExn (%a, %a)" Terms.pp ty1 Terms.pp ty2)
    | UnexpectedContextExn (ctx1, ctx2) ->
      Some (asprintf "UnexpectedContextExn (%a, %a)" pp' ctx1 pp' ctx2)
    | LinearFixExn (t, ty) ->
      Some (asprintf "LinearFixExn (%a, %a)" Terms.pp t Terms.pp ty)
    | InferMetaExn x -> Some (asprintf "InferMetaExn (%a)" Meta.pp x)
    | InferLambdaExn t -> Some (asprintf "InferLambdaExn (%a)" Terms.pp t)
    | InferFixExn t -> Some (asprintf "InferFixExn (%a)" Terms.pp t)
    | InferAppExn t -> Some (asprintf "InferAppExn (%a)" Terms.pp t)
    | InferMatchNonInductiveExn t ->
      Some (asprintf "InferMatchNonInductiveExn (%a)" Terms.pp t)
    | InferMatchLinearMotiveExn (t, ty) ->
      Some
        (asprintf "InferMatchLinearMotiveExn (%a, %a)" Terms.pp t Terms.pp ty)
    | InferMatchMotiveFailedExn (t, ty) ->
      Some
        (asprintf "InferMatchMotiveFailedExn (%a, %a)" Terms.pp t Terms.pp ty)
    | InferPscopeUnevenLength (ps, i) ->
      Some (asprintf "InferPscopeUnevenLength (%a, %d)" Terms.pp_pscope ps i)
    | InferTscopeUnevenLength (ts, i) ->
      Some (asprintf "InferTscopeUnevenLength (%a, %d)" Terms.pp_tscope ts i)
    | CheckMetaExn x -> Some (asprintf "CheckMetaExn (%a)" Meta.pp x)
    | CheckMatchNonInductiveExn t ->
      Some (asprintf "CheckMatchNonInductiveExn (%a)" Terms.pp t)
    | CheckMotive mot -> Some (asprintf "CheckMotive (%a)" Terms.pp_mt mot)
    | CoverageExn pbs -> Some (asprintf "CoverageExn (%a)" Terms.pp_cls pbs)
    | CoverageArityPscopeExn (ps, ts) ->
      Some
        (asprintf "CoverageArityPscopeExn (%a, %a)" Terms.pp_pscope ps
           Terms.pp_ts ts)
    | CoverageArityTscopeExn (ts, xs) ->
      Some
        (asprintf "CoverageArityTscopeExn (%a, %a)" Terms.pp_tscope ts
           Terms.pp_vs xs)
    | CoverageStripExn p -> Some (asprintf "CoverageStripExn (%a)" Terms.pp_p p)
    | ParamTscopeExn ty -> Some (asprintf "ParamTscopeExn (%a)" Terms.pp ty)
    | ParamTscopeParamExn (xs, ts) ->
      Some
        (asprintf "ParamTscopeParamExn (%a, %a)" Terms.pp_vs xs Terms.pp_ts ts)
    | CheckTscopeExn (ty, s1, s2) ->
      Some
        (asprintf "CheckTscopeExn (%a, %a, %a)" Terms.pp ty Terms.pp_s s1
           Terms.pp_s s2)
    | _ -> None)
