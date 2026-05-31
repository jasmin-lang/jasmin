exception AnnotationError of Location.t * (Format.formatter -> unit)

val error : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val on_attribute :
  ?on_empty:(Location.t -> Annotations.symbol -> unit -> 'a) ->
  ?on_int:(Location.t -> Annotations.symbol -> Z.t -> 'a) ->
  ?on_id:(Location.t -> Annotations.symbol -> Annotations.symbol -> 'a) ->
  ?on_string:(Location.t -> Annotations.symbol -> string -> 'a) ->
  ?on_ws:(Location.t -> Annotations.symbol -> Wsize.wsize -> 'a) ->
  ?on_struct:(Location.t -> Annotations.symbol -> Annotations.annotations -> 'a) ->
  (Location.t -> Annotations.symbol -> 'a) ->
  Annotations.annotation ->
  'a

val pp_dfl_attribute :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

val error_attribute :
  Location.t ->
  string ->
  (Format.formatter -> 'a -> unit) ->
  'a ->
  (Format.formatter -> 'b -> unit) ->
  'b option ->
  'c

val on_empty : ('a -> 'b -> 'c) -> 'c option -> 'a -> 'b -> unit -> 'c

val filter_string_list :
  Annotations.symbol option ->
  (Annotations.symbol * 'a) list ->
  Annotations.annotation ->
  'a

val bool :
  bool ->
  Annotations.annotation ->
  bool

val none :
  Annotations.annotation ->
  unit

val int :
  Z.t option ->
  Annotations.annotation ->
  Z.t

val pos_int :
  Z.t option ->
  Annotations.annotation ->
  Z.t

val ws_strings : (string * Wsize.wsize) list
val ws_of_string : string -> Wsize.wsize

val wsize :
  Wsize.wsize option ->
  Annotations.annotation ->
  Wsize.wsize

val filter_attribute :
  ?case_sensitive:bool ->
  Annotations.symbol ->
  (Annotations.annotation -> 'a) ->
  Annotations.annotations ->
  (Annotations.pident * 'a) list

val process_annot :
  ?case_sensitive:bool ->
  (string * (Annotations.annotation -> 'a)) list ->
  Annotations.annotations ->
  (Annotations.pident * 'a) list

val ensure_uniq :
  ?case_sensitive:bool ->
  (string * (Annotations.annotation -> 'a)) list ->
  Annotations.annotations ->
  'a option

val ensure_uniq1 :
  ?case_sensitive:bool ->
  string ->
  (Annotations.annotation -> 'a) ->
  Annotations.annotations ->
  'a option

val consume :
  string -> Annotations.annotations -> Annotations.annotations
