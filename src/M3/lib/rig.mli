
type rig

val _Zero : rig
val _One : rig
val _W : rig

val ( + ) : rig -> rig -> rig
val ( * ) : rig -> rig -> rig
val ( = ) : rig -> rig -> bool
val ( <= ) : rig -> rig -> bool

val pp : Format.formatter -> rig -> unit