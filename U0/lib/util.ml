open Terms
open Format

let pp_p fmt (t1, t2) =
  fprintf fmt "<%a ?= %a>" pp t1 pp t2

let pp_ps fmt ps =
  let pp_aux fmt ps =
    List.iter (fun p -> fprintf fmt "@[%a;@]@;" pp_p p) ps
  in
  fprintf fmt "@[{%a}@]@." pp_aux ps