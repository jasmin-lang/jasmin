exception AnnotationError of Location.t * (Format.formatter -> unit)

val error : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val on_attribute :
  ?on_empty:(Location.t -> 'a -> unit -> 'b) ->
  ?on_int:(Location.t -> 'a -> Z.t -> 'b) ->
  ?on_id:(Location.t -> 'a -> Annotations.symbol -> 'b) ->
  ?on_string:(Location.t -> 'a -> string -> 'b) ->
  ?on_ws:(Location.t -> 'a -> Annotations.wsize -> 'b) ->
  ?on_struct:(Location.t -> 'a -> Annotations.annotations -> 'b) ->
  (Location.t -> 'a -> 'b) ->
  'a Location.located * Annotations.simple_attribute Location.located option ->
  'b

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
  string Location.located * Annotations.simple_attribute Location.located option ->
  'a

val bool :
  bool ->
  string Location.located * Annotations.simple_attribute Location.located option ->
  bool

val none :
  string Location.located * Annotations.simple_attribute Location.located option ->
  unit

val int :
  Z.t option ->
  string Location.located * Annotations.simple_attribute Location.located option ->
  Z.t

val pos_int :
  Z.t option ->
  string Location.located * Annotations.simple_attribute Location.located option ->
  Z.t

val ws_strings : (string * Annotations.wsize) list
val ws_of_string : string -> Annotations.wsize

val wsize :
  Annotations.wsize option ->
  string Location.located * Annotations.simple_attribute Location.located option ->
  Annotations.wsize

val filter_attribute :
  ?case_sensitive:bool ->
  Annotations.symbol ->
  (Annotations.annotation -> 'a) ->
  Annotations.annotations ->
  (Annotations.symbol Location.located * 'a) list

val process_annot :
  ?case_sensitive:bool ->
  (string * (Annotations.annotation -> 'a)) list ->
  Annotations.annotations ->
  (Annotations.symbol Location.located * 'a) list

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
  Utils.String.t -> Annotations.annotation list -> Annotations.annotations
