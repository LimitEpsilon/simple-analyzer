open Syntax
open Interval

exception Not_LIA

type term =
  | TmConst of int (* z *)
  | TmVar of int * id (* z * x *)
  | TmAdd of term * term (* t + t *)

type formula =
  | FmPos of term (* t ≥ 0 *)
  | FmAnd of formula * formula (* f ∧ f *)
  | FmNot of formula (* ¬ f *)

let tm_add t1 t2 = TmAdd (t1, t2)

let rec tm_mult t1 t2 =
  match (t1, t2) with
  | TmConst c1, TmConst c2 -> TmConst (c1 * c2)
  | TmConst c1, TmVar (c2, x) | TmVar (c2, x), TmConst c1 -> TmVar (c1 * c2, x)
  | t, TmAdd (t1, t2) | TmAdd (t1, t2), t -> TmAdd (tm_mult t t1, tm_mult t t2)
  | TmVar _, TmVar _ -> raise Not_LIA

let rec tm_minus t =
  match t with
  | TmConst c -> TmConst (-c)
  | TmVar (c, x) -> TmVar (-c, x)
  | TmAdd (t1, t2) -> TmAdd (tm_minus t1, tm_minus t2)

let rec term_of_exp (e : exp) : term =
  match e with
  | NUM n -> TmConst n
  | VAR x -> TmVar (1, x)
  | ADD (e1, e2) -> bop_exp tm_add e1 e2
  | MULT (e1, e2) -> bop_exp tm_mult e1 e2
  | MINUS e -> tm_minus (term_of_exp e)
  | _ -> raise Not_LIA

and bop_exp bop e1 e2 = bop (term_of_exp e1) (term_of_exp e2)

let rec formula_of_exp (e : exp) : formula =
  match e with
  | NOT e -> FmNot (formula_of_exp e)
  | ANDALSO (e1, e2) ->
    let f1 = formula_of_exp e1 in
    let f2 = formula_of_exp e2 in
    FmAnd (f1, f2)
  | ORELSE (e1, e2) ->
    let f1 = formula_of_exp e1 in
    let f2 = formula_of_exp e2 in
    FmNot (FmAnd (FmNot f1, FmNot f2))
  | LESS (e1, e2) ->
    let t = term_of_exp (ADD (e1, MINUS e2)) in
    FmNot (FmPos t)
  | _ -> raise Not_LIA

(* (a1x1 + ... + anxn) + c *)
type reduced_term = (id * int) list * int

let merge_reduced_tm (l1, c1) (l2, c2) : reduced_term =
  let rec merge_list l1 l2 =
    match (l1, l2) with
    | [], _ -> l2
    | _, [] -> l1
    | (x1, c1) :: tl1, (x2, c2) :: tl2 ->
      let comp = compare x1 x2 in
      if comp < 0 then (x1, c1) :: merge_list tl1 l2
      else if comp > 0 then (x2, c2) :: merge_list l1 tl2
      else (x1, c1 + c2) :: merge_list tl1 tl2
  in
  (merge_list l1 l2, c1 + c2)

let rec reduce_tm t : reduced_term =
  let v, c =
    match t with
    | TmConst c -> ([], c)
    | TmVar (c, x) -> ([(x, c)], 0)
    | TmAdd (t1, t2) ->
      (* always sorted *)
      merge_reduced_tm (reduce_tm t1) (reduce_tm t2)
  in
  (List.filter (fun (_, c) -> c <> 0) v, c)

type conjunction =
  | CTrue
  | CPos of reduced_term * conjunction (* t >= 0 *)
  | CNeg of reduced_term * conjunction (* t < 0 *)

let rec conj_not = function
  | CTrue -> []
  | CPos (t, c) -> CNeg (t, CTrue) :: conj_not c
  | CNeg (t, c) -> CPos (t, CTrue) :: conj_not c

let rec conj_and c1 c2 =
  match c1 with
  | CTrue -> c2
  | CPos (t, c1) -> CPos (t, conj_and c1 c2)
  | CNeg (t, c1) -> CNeg (t, conj_and c1 c2)

let conj_mult cl1 cl2 =
  let mult_one l c = List.map (conj_and c) l in
  List.flatten (List.map (mult_one cl1) cl2)

(* disjuction of conjunctions *)
let rec reduce_formula f =
  match f with
  | FmPos t -> [CPos (reduce_tm t, CTrue)]
  | FmNot f -> (
    let l = reduce_formula f in
    let ll = List.map conj_not l in
    match ll with [] -> [] | hd :: tl -> List.fold_left conj_mult hd tl)
  | FmAnd (f1, f2) -> conj_mult (reduce_formula f1) (reduce_formula f2)

let rec simpl_formula f =
  match f with
  | FmNot (FmNot f) -> simpl_formula f
  | FmAnd (f1, f2) -> FmAnd (simpl_formula f1, simpl_formula f2)
  | _ -> f

type filter = (id * itv) list

let rec join_filter l1 l2 =
  match (l1, l2) with
  | [], _ -> []
  | _, [] -> []
  | (x1, i1) :: tl1, (x2, i2) :: tl2 ->
    let comp = compare x1 x2 in
    if comp < 0 then join_filter tl1 l2
    else if comp > 0 then join_filter l1 tl2
    else (x1, join_itv i1 i2) :: join_filter tl1 tl2

let rec meet_filter l1 l2 =
  match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | (x1, i1) :: tl1, (x2, i2) :: tl2 ->
    let comp = compare x1 x2 in
    if comp < 0 then (x1, i1) :: meet_filter tl1 l2
    else if comp > 0 then (x2, i2) :: meet_filter l1 tl2
    else (x1, meet_itv i1 i2) :: meet_filter tl1 tl2

let filter_of_pos ((l, c) : reduced_term) =
  match l with
  | [] -> []
  | [(x, a)] ->
    (* ax + c ≥ 0 *)
    if a > 0 then [(x, Itv (Fin (-c / a), Inf))]
    else [(x, Itv (NegInf, Fin (c / -a)))]
  | _ -> List.map (fun (x, _) -> (x, top_itv)) l

let filter_of_neg ((l, c) : reduced_term) =
  match l with
  | [] -> []
  | [(x, a)] ->
    (* ax + c < 0 *)
    if a > 0 then [(x, Itv (NegInf, Fin (-c / a)))]
    else [(x, Itv (Fin (c / -a), Inf))]
  | _ -> List.map (fun (x, _) -> (x, top_itv)) l

let filter_of_conj c =
  let rec f c acc =
    match c with
    | CTrue -> acc
    | CPos (t, c) -> f c (meet_filter (filter_of_pos t) acc)
    | CNeg (t, c) -> f c (meet_filter (filter_of_neg t) acc)
  in
  f c []

let filter_of_formula f =
  let cl = reduce_formula (simpl_formula f) in
  match cl with
  | [] -> []
  | hd :: tl ->
    List.fold_left
      (fun acc c -> join_filter acc (filter_of_conj c))
      (filter_of_conj hd) tl

let filter_tbl : (exp, filter * filter) Hashtbl.t = Hashtbl.create 10

let make_filter e =
  match Hashtbl.find filter_tbl e with
  | exception Not_found ->
    let f =
      match formula_of_exp e with
      | exception Not_LIA -> ([], [])
      | f -> (filter_of_formula f, filter_of_formula (FmNot f))
    in
    Hashtbl.add filter_tbl e f;
    f
  | f -> f
