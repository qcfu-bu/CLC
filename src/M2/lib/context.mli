type ctx 

val empty : ctx
val add : Terms.tvar -> Terms.term -> Ring.ring -> ctx -> ctx
val remove : Terms.tvar -> ctx -> ctx
val iter : (Terms.tvar -> Terms.term * Ring.ring -> unit) -> ctx -> unit
val find : Terms.tvar -> ctx -> Terms.term * Ring.ring
val contract : Terms.tvar -> ctx -> ctx
val equal : ctx -> ctx -> bool
val scale : Ring.ring -> ctx -> ctx
val sum : ctx -> ctx -> ctx
val sub : ctx -> ctx -> ctx
val is_positive : ctx -> bool
val is_zero : ctx -> bool
