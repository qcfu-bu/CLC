val d : bool ref 
val check : Context.ctx -> Terms.term -> Ring.ring -> Terms.term -> Context.ctx
val infer : Context.ctx -> Ring.ring -> Terms.term -> Context.ctx * Terms.term
