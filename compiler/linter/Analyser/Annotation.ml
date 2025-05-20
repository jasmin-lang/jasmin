type 'domain annotation =
| Empty
| Annotation of 'domain

let pp pp_domain fmt (loc, annot) =
    match annot with
    | Empty -> Format.fprintf fmt "Empty"
    | Annotation domain -> pp_domain fmt (loc, domain)

let merge d1 d2 merge =
    match (d1, d2) with
    | Empty, a
     |a, Empty ->
        a
    | Annotation d1, Annotation d2 -> Annotation (merge d1 d2)

let included a b included =
    match (a, b) with
    | Empty, _ -> true
    | _, Empty -> false
    | Annotation a, Annotation b -> included a b

let bind b f =
    match b with
    | Empty -> Empty
    | Annotation a -> f a

let unwrap annotation =
    match annotation with
    | Empty -> invalid_arg "Annotation.unwrap"
    | Annotation a -> a

let map annotation map_function =
    match annotation with
    | Empty -> Empty
    | Annotation a -> Annotation (map_function a)
