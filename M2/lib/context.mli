type ctx 

val empty : ctx
val add : Terms.tvar -> Terms.term -> int -> ctx -> ctx
val remove : Terms.tvar -> ctx -> ctx
val find : Terms.tvar -> ctx -> Terms.term * int
val contract : Terms.tvar -> ctx -> ctx
val equal : ctx -> ctx -> bool
val scale : int -> ctx -> ctx
val sum : ctx -> ctx -> ctx
val sub : ctx -> ctx -> ctx
val is_positive : ctx -> bool
val is_zero : ctx -> bool
