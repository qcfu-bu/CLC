open Format
open Bindlib
open Cclc
open Core
open Raw
open Name
open Prelude
open Eval

let prelude = RTop.core Prelude.raw

let _ = printf "%a@.@." Top.pp prelude

let _ = EvalTop.eval prelude