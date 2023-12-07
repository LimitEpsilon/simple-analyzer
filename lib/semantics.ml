open Syntax
open Interval

type loc = id
type lbl = int
type value = Value of int | Addr of loc

module LocSet = Set.Make (struct
  type t = loc

  let compare = compare
end)

module LocMap = Map.Make (struct
  type t = loc

  let compare = compare
end)

module LblMap = Map.Make (struct
  type t = lbl

  let compare = compare
end)

module LblSet = Set.Make (struct
  type t = lbl

  let compare = compare
end)

type memory = value LocMap.t

module MemSet = Set.Make (struct
  type t = memory

  let compare = LocMap.compare (compare : value -> value -> int)
end)

type collecting_semantics = MemSet.t LblMap.t
type abs_int = itv

let top_int = top_itv
let join_int i1 i2 = join_itv i1 i2
let widen_int i1 i2 = widen_itv i1 i2
let plus_int i1 i2 = plus_itv i1 i2
let mult_int i1 i2 = mult_itv i1 i2
let neg_int i = neg_itv i
let less_int i1 i2 = less_itv i1 i2
let not_int i = not_itv i
let and_int i1 i2 = and_itv i1 i2
let or_int i1 i2 = or_itv i1 i2
let maybe_t_int i = maybe_t_itv i
let maybe_f_int i = maybe_f_itv i

type abs_val = abs_int * LocSet.t

let join_loc l1 l2 = LocSet.union l1 l2
let join (n1, a1) (n2, a2) = (join_int n1 n2, join_loc a1 a2)
let widen (n1, a1) (n2, a2) = (widen_int n1 n2, join_loc a1 a2)
let plus (n1, _) (n2, _) = (plus_int n1 n2, LocSet.empty)
let mult (n1, _) (n2, _) = (mult_int n1 n2, LocSet.empty)
let neg (n, _) = (neg_int n, LocSet.empty)
let less (n1, _) (n2, _) = (less_int n1 n2, LocSet.empty)
let lnot (n, _) = (not_int n, LocSet.empty)
let andalso (n1, _) (n2, _) = (and_int n1 n2, LocSet.empty)
let orelse (n1, _) (n2, _) = (or_int n1 n2, LocSet.empty)
let maybe_t (n, _) = maybe_t_int n
let maybe_f (n, _) = maybe_f_int n
let eqb_aint i1 i2 = i1 = i2
let eqb_aval (n1, a1) (n2, a2) = eqb_aint n1 n2 && LocSet.equal a1 a2

type abs_mem = abs_val LocMap.t
type abstract_semantics = abs_mem LblMap.t

let locmap_find_opt x m =
  match LocMap.find x m with exception Not_found -> None | v -> Some v

let rec interp_exp e (m : memory) =
  match e with
  | NUM n -> Some (Value n)
  | VAR x -> locmap_find_opt x m
  | DEREF x -> (
    match locmap_find_opt x m with
    | Some (Addr a) -> locmap_find_opt a m
    | _ -> None)
  | AT x -> Some (Addr x)
  | ADD (e1, e2) -> (
    match (interp_exp e1 m, interp_exp e2 m) with
    | Some (Value n1), Some (Value n2) -> Some (Value (n1 + n2))
    | _, _ -> None)
  | MULT (e1, e2) -> (
    match (interp_exp e1 m, interp_exp e2 m) with
    | Some (Value n1), Some (Value n2) -> Some (Value (n1 * n2))
    | _, _ -> None)
  | MINUS e -> (
    match interp_exp e m with Some (Value n) -> Some (Value (-n)) | _ -> None)
  | TRUE -> Some (Value 1)
  | FALSE -> Some (Value 0)
  | READ -> Some (Value (read_int ()))
  | NOT e -> (
    match interp_exp e m with
    | Some (Value n) -> if n = 0 then Some (Value 1) else Some (Value 0)
    | _ -> None)
  | ANDALSO (e1, e2) -> (
    match (interp_exp e1 m, interp_exp e2 m) with
    | Some (Value n1), Some (Value n2) ->
      if n1 * n2 = 0 then Some (Value 0) else Some (Value 1)
    | _, _ -> None)
  | ORELSE (e1, e2) -> (
    match (interp_exp e1 m, interp_exp e2 m) with
    | Some (Value n1), Some (Value n2) ->
      if n1 = 0 && n2 = 0 then Some (Value 0) else Some (Value 1)
    | _, _ -> None)
  | LESS (e1, e2) -> (
    match (interp_exp e1 m, interp_exp e2 m) with
    | Some (Value n1), Some (Value n2) ->
      if n1 < n2 then Some (Value 1) else Some (Value 0)
    | _, _ -> None)

let rec ainterp_exp e (m : abs_mem) : abs_val =
  match e with
  | NUM n -> (Itv (Fin n, Fin n), LocSet.empty)
  | VAR x -> (
    match locmap_find_opt x m with None -> (Bot, LocSet.empty) | Some v -> v)
  | DEREF x -> (
    match locmap_find_opt x m with
    | None -> (Bot, LocSet.empty)
    | Some (_, addrs) ->
      LocSet.fold
        (fun x acc ->
          let v =
            match locmap_find_opt x m with
            | None -> (Bot, LocSet.empty)
            | Some v -> v
          in
          join v acc)
        addrs (Bot, LocSet.empty))
  | AT x -> (Bot, LocSet.singleton x)
  | ADD (e1, e2) -> plus (ainterp_exp e1 m) (ainterp_exp e2 m)
  | MULT (e1, e2) -> mult (ainterp_exp e1 m) (ainterp_exp e2 m)
  | MINUS e -> neg (ainterp_exp e m)
  | TRUE -> (itv_true, LocSet.empty)
  | FALSE -> (itv_false, LocSet.empty)
  | READ -> (top_int, LocSet.empty)
  | NOT e -> lnot (ainterp_exp e m)
  | ANDALSO (e1, e2) -> andalso (ainterp_exp e1 m) (ainterp_exp e2 m)
  | ORELSE (e1, e2) -> orelse (ainterp_exp e1 m) (ainterp_exp e2 m)
  | LESS (e1, e2) -> less (ainterp_exp e1 m) (ainterp_exp e2 m)

(* execution *)
type cfg = {next : lbl -> lbl; nextTrue : lbl -> lbl; nextFalse : lbl -> lbl}

let exit_lbl = -1
let lbl_to_cmd : (lbl, cmd) Hashtbl.t = Hashtbl.create 10
let bind (f : lbl -> lbl) lbl c l = if l = lbl then c else f l
let label_of (LBL (l, _)) = l

let rec make_cfg (c : program) (l_exit : int) (cfg : cfg) : cfg =
  match c with
  | LBL (l, c) -> (
    Hashtbl.add lbl_to_cmd l c;
    match c with
    | SEQ (c1, c2) ->
      let next = bind cfg.next l (label_of c1) in
      let cfg = make_cfg c1 (label_of c2) {cfg with next} in
      make_cfg c2 l_exit cfg
    | IF (_, c1, c2) ->
      let nextTrue = bind cfg.nextTrue l (label_of c1) in
      let nextFalse = bind cfg.nextFalse l (label_of c2) in
      let cfg = make_cfg c1 l_exit {cfg with nextTrue; nextFalse} in
      make_cfg c2 l_exit cfg
    | WHILE (_, c) ->
      let nextTrue = bind cfg.nextTrue l (label_of c) in
      let nextFalse = bind cfg.nextFalse l l_exit in
      make_cfg c l {cfg with nextTrue; nextFalse}
    | GOTO _ -> cfg
    | ASSIGN _ ->
      let next = bind cfg.next l l_exit in
      {cfg with next}
    | PTRASSIGN _ ->
      let next = bind cfg.next l l_exit in
      {cfg with next})

let rec intp_aux l m cfg =
  match Hashtbl.find lbl_to_cmd l with
  | exception Not_found -> m
  | c -> (
    match c with
    | IF (e, _, _) | WHILE (e, _) -> (
      match interp_exp e m with
      | Some (Value n) ->
        if n = 0 then intp_aux (cfg.nextFalse l) m cfg
        else intp_aux (cfg.nextTrue l) m cfg
      | _ -> m)
    | SEQ (_, _) -> intp_aux (cfg.next l) m cfg
    | GOTO e -> (
      match interp_exp e m with Some (Value l) -> intp_aux l m cfg | _ -> m)
    | ASSIGN (x, e) -> (
      match interp_exp e m with
      | Some v -> intp_aux (cfg.next l) (LocMap.add x v m) cfg
      | _ -> m)
    | PTRASSIGN (x, e) -> (
      match (locmap_find_opt x m, interp_exp e m) with
      | Some (Addr a), Some v -> intp_aux (cfg.next l) (LocMap.add a v m) cfg
      | _ -> m))

let intp pgm =
  let init _ = exit_lbl in
  let init_cfg = {next = init; nextTrue = init; nextFalse = init} in
  Hashtbl.clear lbl_to_cmd;
  let cfg = make_cfg pgm exit_lbl init_cfg in
  let init_mem = LocMap.empty in
  intp_aux (label_of pgm) init_mem cfg

let rec cintp_aux l m acc cfg =
  let acc =
    let single_map = LblMap.add l (MemSet.singleton m) LblMap.empty in
    LblMap.merge
      (fun _ v1 v2 ->
        match (v1, v2) with
        | None, None -> None
        | Some v, None -> Some v
        | None, Some v -> Some v
        | Some v1, Some v2 -> Some (MemSet.union v1 v2))
      acc single_map
  in
  match Hashtbl.find lbl_to_cmd l with
  | exception Not_found -> acc
  | c -> (
    match c with
    | IF (e, _, _) | WHILE (e, _) -> (
      match interp_exp e m with
      | Some (Value n) ->
        if n = 0 then cintp_aux (cfg.nextFalse l) m acc cfg
        else cintp_aux (cfg.nextTrue l) m acc cfg
      | _ -> acc)
    | SEQ (_, _) -> cintp_aux (cfg.next l) m acc cfg
    | GOTO e -> (
      match interp_exp e m with
      | Some (Value l) -> cintp_aux l m acc cfg
      | _ -> acc)
    | ASSIGN (x, e) -> (
      match interp_exp e m with
      | Some v -> cintp_aux (cfg.next l) (LocMap.add x v m) acc cfg
      | _ -> acc)
    | PTRASSIGN (x, e) -> (
      match (locmap_find_opt x m, interp_exp e m) with
      | Some (Addr a), Some v ->
        cintp_aux (cfg.next l) (LocMap.add a v m) acc cfg
      | _ -> acc))

(* collecting semantics *)
let cintp pgm : collecting_semantics =
  let init _ = exit_lbl in
  let init_cfg = {next = init; nextTrue = init; nextFalse = init} in
  Hashtbl.clear lbl_to_cmd;
  let cfg = make_cfg pgm exit_lbl init_cfg in
  let init_mem = LocMap.empty in
  cintp_aux (label_of pgm) init_mem LblMap.empty cfg

let merge_mem merge (m1 : abs_mem) (m2 : abs_mem) : abs_mem =
  let m _ v1 v2 =
    match (v1, v2) with
    | None, None -> None
    | Some v1, None -> Some v1
    | None, Some v2 -> Some v2
    | Some v1, Some v2 -> Some (merge v1 v2)
  in
  LocMap.merge m m1 m2

let join_mem (m1 : abs_mem) (m2 : abs_mem) : abs_mem = merge_mem join m1 m2
let widen_mem (m1 : abs_mem) (m2 : abs_mem) : abs_mem = merge_mem widen m1 m2

let meet_with_filter (m : abs_mem) (filter : Lia.filter) : abs_mem =
  let f acc (x, cstr) =
    match locmap_find_opt x acc with
    | None -> LocMap.empty
    | Some (i, _) -> (
      match meet_itv i cstr with
      | Bot -> LocMap.empty
      | i -> LocMap.add x (i, LocSet.empty) acc)
  in
  List.fold_left f m filter

let filter_true (e : exp) (m : abs_mem) =
  let true_filter, _ = Lia.make_filter e in
  meet_with_filter m true_filter

let filter_false (e : exp) (m : abs_mem) =
  let _, false_filter = Lia.make_filter e in
  meet_with_filter m false_filter

let goto_targets = ref LblSet.empty
let update_goto_targets t = goto_targets := LblSet.add t !goto_targets

let ainterp_cmd (l, m) (sem : abstract_semantics) cfg :
    abstract_semantics * (int * abs_mem) list =
  let m_orig, new_entry =
    match LblMap.find l sem with
    | exception Not_found -> (LocMap.empty, true)
    | m_orig -> (m_orig, false)
  in
  let widen =
    match Hashtbl.find lbl_to_cmd l with
    | exception Not_found -> false
    | WHILE _ -> true
    | _ -> LblSet.mem l !goto_targets
  in
  let m = if widen then widen_mem m_orig m else join_mem m_orig m in
  let sem = LblMap.add l m sem in
  let not_changed = LocMap.equal eqb_aval m_orig m && not new_entry in
  if not_changed then (sem, [])
  else
    let worklist =
      match Hashtbl.find lbl_to_cmd l with
      | exception Not_found -> []
      | IF (e, _, _) | WHILE (e, _) ->
        let condition = ainterp_exp e m in
        let if_true =
          if maybe_t condition then filter_true e m else LocMap.empty
        in
        let if_false =
          if maybe_f condition then filter_false e m else LocMap.empty
        in
        [(cfg.nextTrue l, if_true); (cfg.nextFalse l, if_false)]
      | SEQ (_, _) -> [(cfg.next l, m)]
      | GOTO e ->
        let i, _ = ainterp_exp e m in
        let test_target t =
          let test_itv =
            match i with
            | Itv (NegInf, Inf) -> true
            | Itv (NegInf, Fin r) -> t <= r
            | Itv (Fin l, Inf) -> l <= t
            | Itv (Fin l, Fin r) -> l <= t && t <= r
            | _ -> false
          in
          test_itv
        in
        let targets =
          Hashtbl.fold
            (fun t _ acc ->
              if test_target t then
                let () = update_goto_targets t in
                t :: acc
              else acc)
            lbl_to_cmd []
        in
        let may_exit =
          match i with
          | Itv (Fin l, Fin r) ->
            (* assume that labels are contiguous *)
            not (Hashtbl.mem lbl_to_cmd l && Hashtbl.mem lbl_to_cmd r)
          | _ -> true
        in
        let targets = if may_exit then exit_lbl :: targets else targets in
        List.map (fun l -> (l, m)) targets
      | ASSIGN (x, e) ->
        let v = ainterp_exp e m in
        (* strong update *)
        let m = LocMap.add x v m in
        [(cfg.next l, m)]
      | PTRASSIGN (x, e) ->
        let m =
          match locmap_find_opt x m with
          | None -> LocMap.empty
          | Some (_, addrs) ->
            let v = ainterp_exp e m in
            LocSet.fold
              (fun a acc -> join_mem (LocMap.add a v m) acc)
              addrs LocMap.empty
        in
        [(cfg.next l, m)]
    in
    (sem, worklist)

(* analysis *)
let analysis pgm : abstract_semantics =
  let init _ = exit_lbl in
  let init_cfg = {next = init; nextTrue = init; nextFalse = init} in
  Hashtbl.clear lbl_to_cmd;
  goto_targets := LblSet.empty;
  let cfg = make_cfg pgm exit_lbl init_cfg in
  let rec loop sem worklist =
    match worklist with
    | [] -> sem
    | hd :: tl ->
      let sem, worklist = ainterp_cmd hd sem cfg in
      loop sem (List.rev_append worklist tl)
  in
  loop LblMap.empty [(label_of pgm, LocMap.empty)]
