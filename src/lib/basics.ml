open Pparser
let basic = 
  let ch = open_in "./prelude/basics.v" in
  parse ch

let v_ctx, id_ctx = snd basic

let _tt = SMap.find "tt" id_ctx
let _O = SMap.find "O" id_ctx
let _S = SMap.find "S" id_ctx
let _add = SMap.find "add" v_ctx
let _sigma = SMap.find "sigma" id_ctx
let _pair = SMap.find "pair" id_ctx
let _tensor = SMap.find "tensor" id_ctx
let _ftensor = SMap.find "ftensor" id_ctx
let _tpair = SMap.find "tpair" id_ctx
let _fpair = SMap.find "fpair" id_ctx
let _PtsTo = SMap.find "PtsTo" v_ctx
let _New = SMap.find "New" v_ctx
let _Free = SMap.find "Free" v_ctx
let _Get = SMap.find "Get" v_ctx
let _Set = SMap.find "Set" v_ctx
