type ring

val ( + ) : ring -> ring -> ring
val ( - ) : ring -> ring -> ring
val ( * ) : ring -> ring -> ring
val ( = ) : ring -> ring -> bool
val ( <= ) : ring -> ring -> bool

val z : ring
val o : ring
val w : ring

val pp : Format.formatter -> ring -> unit