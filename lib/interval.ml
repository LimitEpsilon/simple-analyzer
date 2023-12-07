type bound =
  | Fin of int
  | Inf
  (* ∞ *)
  | NegInf (* -∞ *)

(* 
 * always Itv (l, r) satisfies: 
 * (1) l <= r
 * (2) if l = -∞ then r != -∞
 * (3) if r = ∞ then l != ∞ 
 *)
type itv = Bot | Itv of bound * bound

let top_itv = Itv (NegInf, Inf)

let max_bound b1 b2 =
  match (b1, b2) with
  | NegInf, _ -> b2
  | _, NegInf -> b1
  | Inf, _ -> Inf
  | _, Inf -> Inf
  | Fin n1, Fin n2 -> Fin (max n1 n2)

let min_bound b1 b2 =
  match (b1, b2) with
  | NegInf, _ -> NegInf
  | _, NegInf -> NegInf
  | Inf, _ -> b2
  | _, Inf -> b1
  | Fin n1, Fin n2 -> Fin (min n1 n2)

(* b1 <= b2 *)
let leq_bound b1 b2 = min_bound b1 b2 = b1

let plus_bound b1 b2 =
  match (b1, b2) with
  | NegInf, Inf | Inf, NegInf -> failwith "plus_bound not defined"
  | NegInf, _ | _, NegInf -> NegInf
  | Inf, _ | _, Inf -> Inf
  | Fin n1, Fin n2 -> Fin (n1 + n2)

let mult_bound b1 b2 =
  match (b1, b2) with
  | NegInf, Inf | Inf, NegInf -> NegInf
  | NegInf, NegInf | Inf, Inf -> Inf
  | Fin n1, Fin n2 -> Fin (n1 * n2)
  | NegInf, Fin n | Fin n, NegInf ->
    if n > 0 then NegInf else if n = 0 then Fin 0 else Inf
  | Inf, Fin n | Fin n, Inf ->
    if n > 0 then Inf else if n = 0 then Fin 0 else NegInf

let neg_bound b =
  match b with NegInf -> Inf | Inf -> NegInf | Fin n -> Fin (-n)

let meet_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | Itv (l, r), Itv (l', r') ->
    let meet =
      match (max_bound l l', min_bound r r') with
      | NegInf, r -> Itv (NegInf, r)
      | l, Inf -> Itv (l, Inf)
      | Fin l, Fin r -> if l <= r then Itv (Fin l, Fin r) else Bot
      | _ -> Bot
    in
    meet

let join_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ -> i2
  | _, Bot -> i1
  | Itv (l, r), Itv (l', r') -> Itv (min_bound l l', max_bound r r')

let widen_itv i1 i2 =
  let i = join_itv i1 i2 in
  match (i1, i) with
  | Bot, _ | _, Bot -> i
  | Itv (l, r), Itv (l', r') ->
    let left = if leq_bound l l' then l else NegInf in
    let right = if leq_bound r' r then r else Inf in
    Itv (left, right)

let plus_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ | _, Bot -> Bot
  | Itv (l, r), Itv (l', r') -> Itv (plus_bound l l', plus_bound r r')

let mult_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ | _, Bot -> Bot
  | Itv (l, r), Itv (l', r') ->
    let l =
      [mult_bound l l'; mult_bound l r'; mult_bound r l'; mult_bound r r']
    in
    let maximum = List.fold_left max_bound NegInf l in
    let minimum = List.fold_left min_bound Inf l in
    Itv (minimum, maximum)

let neg_itv i =
  match i with Bot -> Bot | Itv (l, r) -> Itv (neg_bound r, neg_bound l)

let itv_true = Itv (Fin 1, Fin 1)
let itv_false = Itv (Fin 0, Fin 0)
let itv_bool_top = Itv (Fin 0, Fin 1)

(* i1 < i2 *)
let less_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ | _, Bot -> Bot
  | Itv (l, r), Itv (l', r') -> (
    match (leq_bound l' r, leq_bound r' l) with
    | true, true -> itv_false
    | true, false -> itv_bool_top
    | false, _ -> itv_true)

(* does the interval contain 0? *)
let maybe_f_itv i =
  match i with
  | Bot -> false
  | Itv (l, r) -> leq_bound l (Fin 0) && leq_bound (Fin 0) r

(* does the interval contain a non-zero value? *)
let maybe_t_itv i =
  match i with
  | Bot -> false
  | Itv (l, r) -> ( match (l, r) with Fin 0, Fin 0 -> false | _ -> true)

let not_itv i =
  match (maybe_f_itv i, maybe_t_itv i) with
  | false, false -> Bot (* bottom *)
  | false, true -> itv_false
  | true, false -> itv_true
  | true, true -> itv_bool_top

let and_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ | _, Bot -> Bot
  | _ -> (
    let t1 = maybe_t_itv i1 in
    let t2 = maybe_t_itv i2 in
    let f1 = maybe_f_itv i1 in
    let f2 = maybe_f_itv i2 in
    match (t1 && t2, f1 || f2) with
    | true, true -> itv_bool_top
    | true, false -> itv_true
    | _ -> itv_false)

let or_itv i1 i2 =
  match (i1, i2) with
  | Bot, _ | _, Bot -> Bot
  | _ -> (
    let t1 = maybe_t_itv i1 in
    let t2 = maybe_t_itv i2 in
    let f1 = maybe_f_itv i1 in
    let f2 = maybe_f_itv i2 in
    match (t1 || t2, f1 && f2) with
    | true, true -> itv_bool_top
    | true, false -> itv_true
    | _ -> itv_false)

let string_of_bound b =
  match b with Inf -> "∞" | NegInf -> "-∞" | Fin n -> string_of_int n

let string_of_itv i =
  match i with
  | Bot -> "⟂"
  | Itv (l, r) -> "[" ^ string_of_bound l ^ ", " ^ string_of_bound r ^ "]"
