type ctx 

val empty : ctx
val add : Terms.tvar -> Terms.term * Rig.rig -> ctx -> ctx
val remove : Terms.tvar -> ctx -> ctx
val iter : (Terms.tvar -> Terms.term * Rig.rig -> unit) -> ctx -> unit
val find : Terms.tvar -> ctx -> Terms.term * Rig.rig
val same : ctx -> ctx -> bool
val scale : Rig.rig -> ctx -> ctx
val sum : ctx -> ctx -> ctx
val pp : Format.formatter -> ctx -> unit