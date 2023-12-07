open Interval
open Semantics

let string_of_lbl l = if l = exit_lbl then "EXIT" else string_of_int l
let string_of_value v = match v with Value n -> string_of_int n | Addr a -> a

let string_of_mem mem =
  let init = "[" in
  let f k v (acc, first) =
    let semicolon = if first then "" else " ; " in
    (acc ^ semicolon ^ k ^ " |-> " ^ string_of_value v, false)
  in
  let ret, _ = LocMap.fold f mem (init, true) in
  ret ^ "]"

let string_of_memset ms =
  let init = "{" in
  let f v (acc, first) =
    let comma = if first then "\n " else ",\n " in
    (acc ^ comma ^ string_of_mem v, false)
  in
  let ret, first = MemSet.fold f ms (init, true) in
  if first then ret ^ "}" else ret ^ "\n}"

let string_of_col col =
  let init = "" in
  let f k v acc = acc ^ string_of_lbl k ^ ":\n" ^ string_of_memset v ^ "\n" in
  LblMap.fold f col init

let string_of_aint i = string_of_itv i

let string_of_aloc (a : LocSet.t) =
  let init = "{" in
  let f v (acc, first) =
    let comma = if first then "" else ", " in
    (acc ^ comma ^ v, false)
  in
  let ret, _ = LocSet.fold f a (init, true) in
  ret ^ "}"

let string_of_aval (n, a) =
  "(" ^ string_of_aint n ^ ", " ^ string_of_aloc a ^ ")"

let string_of_amem amem =
  let init = "[" in
  let f k v (acc, first) =
    let semicolon = if first then "" else " ; " in
    (acc ^ semicolon ^ k ^ " |-> " ^ string_of_aval v, false)
  in
  let ret, _ = LocMap.fold f amem (init, true) in
  ret ^ "]"

let string_of_asem (asem : abstract_semantics) =
  let init = "" in
  let f k v acc = acc ^ string_of_lbl k ^ ":\n" ^ string_of_amem v ^ "\n" in
  LblMap.fold f asem init
