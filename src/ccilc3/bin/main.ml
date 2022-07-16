open Fmt
open Lang
open Names
open Parser0
open Equality1
open Prelude

let _ = pr "%a" D.pp Prelude.unit_d

(* let parse s =
     let ch = open_in s in
     try
       match parse_channel ch with
       | Success dcls ->
         let _ = pr "%a@." Syntax0.pp_dcls dcls in
         let _ = pr "----------------------------------------------@." in
         let _, _, dcls = Trans01.trans_dcls SMap.empty SMap.empty dcls in
         let _ = pr "%a@." Syntax1.pp_dcls dcls in
         let _ = pr "----------------------------------------------@." in
         let _ = pr "%a@." Pprint1.pp_dcls dcls in
         let _ = pr "----------------------------------------------@." in
         let dcls = eval rd_all VMap.empty dcls in
         let _ = pr "%a@." Pprint1.pp_dcls dcls in
         ()
       | Failed (s, _) -> epr "%s\n" s
     with
     | Failure s -> epr "Failure: %s" s

   let _ = parse "lib/prelude.clc" *)
