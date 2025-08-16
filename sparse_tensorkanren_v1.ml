

(* SEMIRING TYPES *)

module type Semiring = sig
  type t

  val zero: elt
  val one: elt

  val add: elt -> elt -> elt
  val mul: elt -> elt -> elt
end

module AddMulSemiring : Semiring
  with type t = float
= struct
    type t = float

    let zero = 0.0
    let one = 1.0

    let add = ( +. )
    let mul = ( *. )
end

module MaxAddSemiring : Semiring
  with type t = float
= struct
  type t = float

  let zero = Float.neg_infinity
  let one = 0.0

  let add = Float.max
  let mul = ( +. )
end

module MaxMinSemiring : Semiring
  with type t = float
= struct
  type t = float

  let zero = Float.neg_infinity
  let one = Float.infinity

  let add = Float.max
  let mul = Float.min
end

module BoolSemiring : Semiring
  with type t = bool
= struct
  type t = bool

  let zero = false
  let one = true

  let add = (||)
  let mul = (&&)
end

(* TENSORKANREN *)

module TK = struct

  (* TYPES *)
  
  (* variable types *)
  type adt =
  | Unit
  | Sum of adt * adt
  | Prod of adt * adt

  (* value types, used for output *)
  type adv =
  | Sole
  | Left of adv
  | Right of adv
  | Pair of adv * adv

  (* variable is a DeBruijn index with a type *)
  type var = int * adt

  (* expression *)
  type 'elt tk =
  | Succeed
  | Fail
  | Conj of 'elt tk * 'elt tk
  | Disj of 'elt tk * 'elt tk
  | Fresh of adt * 'elt tk
  | Rel of string * (var list)
  | Eqo of var * var
  | Neqo of var * var
  | Soleo of var
  | Lefto of var * var (* a + b, a *)
  | Righto of var * var (* a + b, b *)
  | Pairo of var * var * var (* a * b, a, b *)
  | Factor of 'elt

  (* relation *)
  type 'elt rel = {
    name: string;
    args: adt list;
    body: 'elt tk;
  }

  (* program *)
  type 'elt tk_prgm = 'elt rel list

  (* MACROS *)

  (* bool type and values *)
  let bool_adt = Sum (Unit, Unit)
  let true_adv = Left Sole
  let false_adv = Right Sole

  (* relations on bool types *)
  let trueo (v, vt) =
    Fresh (Unit,
      Conj (
        Lefto ((v + 1, vt), (0, Unit)),
        Soleo (0, Unit)))

  let falseo (v, vt) =
    Fresh (Unit,
      Conj (
        Righto ((v + 1, vt), (0, Unit)),
        Soleo (0, Unit)))

  (* conjunction of a list *)
  let rec conj (tks : 'elt tk list) : 'elt tk =
    match tks with
    | [] -> Succeed
    | a :: d -> Conj (a, (conj d))

  (* disjunction of a list *)
  let rec disj (tks : 'elt tk list) : 'elt tk =
    match tks with
    | [] -> Fail
    | a :: d -> Disj (a, (disj d))

  (* check that a variable has a set value *)
  let rec var_has_val (vr : var) (vl : adv) =
    let vv, vt = vr in
    match vt, vl with
    | Unit, Sole -> Soleo vr
    | Sum (lt, _rt), Left lv ->
        Fresh (lt, Conj (Lefto ((vv + 1, vt), (0, lt)), var_has_val (0, lt) lv))
    | Sum (_lt, rt), Right rv ->
        Fresh (rt, Conj (Righto ((vv + 1, vt), (0, rt)), var_has_val (0, rt) rv))
    | Prod (lt, rt), Pair (lv, rv) ->
        Fresh (lt,
          Fresh (rt,
            Conj (
              Pairo ((vv + 2, vt), (1, lt), (0, rt)),
              Conj (
                var_has_val (1, lt) lv,
                var_has_val (0, rt) rv))))
    | _ -> invalid_arg "Variable type does not match value type!"

  (* check that a variable avoids a set value *)
  (* boils down to swapping left and right at highest points possible *)
  (* only works for types that contain a sum type *)
  let rec var_avoids_val (vr : var) (vl : adv) =
    let vv, vt = vr in
    match vt, vl with
    | Unit, Sole -> Fail
    | Sum (lt, rt), Left lv ->
        Disj (
          Fresh (lt, (* either value is avoided deeper in type *)
            Conj (
              Lefto ((vv + 1, vt), (0, lt)),
              var_avoids_val (0, lt) lv)),
          Fresh (rt, (* or value is avoided here *)
            Righto ((vv + 1, vt), (0, rt))))
    | Sum (lt, rt), Right rv ->
        Disj (
          Fresh (lt, (* either value is avoided here *)
            Lefto ((vv + 1, vt), (0, lt))),
          Fresh (rt,
            Conj (
              Righto ((vv + 1, vt), (0, rt)),
              var_avoids_val (0, rt) rv)))
    | Prod (lt, rt), Pair (lv, rv) ->
        Fresh (lt,
          Fresh (rt,
            Conj (
              Pairo ((vv + 2, vt), (1, lt), (0, rt)),
              Disj ( (* as long as value is avoided at least once deeper, we're good *)
                var_avoids_val (1, lt) lv,
                var_avoids_val (0, rt) rv))))

  (* sum type corresponding to nats with s as the max value *)
  let rec nat_adt s =
    match s with
    | 1 -> Unit
    | m -> Sum (Unit, nat_adt (m - 1))

  (* construct value of nat n corresponding to nat_adt s *)
  let rec nat_adv s n =
    if n = 0 then
      if s = 1 then
        Sole (* built up enough successors already *)
      else
        Left Sole
    else
      Right (nat_adv (s - 1) (n - 1))

  (* prod of bools corresponding to nats with s as near-max value *)
  (* min value for s is 2 *)
  let rec bin_adt s =
    match s with
    | 1 -> bool_adt (* handle non-power-of-2 args *)
    | 2 -> bool_adt
    | m -> Prod (bool_adt, bin_adt (m / 2))

  (* construct value of nat n corresponding to bin_adt s *)
  (* big endian, so cleanly maps to unary *)
  let rec bin_adv_help s n acc =
    if s = 1 then
      acc
    else
      if (n mod 2 = 0) then
        bin_adv_help (s / 2) (n / 2) (Pair (true_adv, acc))
      else
        bin_adv_help (s / 2) (n / 2) (Pair (false_adv, acc))

  let rec bin_adv s n =
    let rightbit = if (n mod 2) = 0 then true_adv else false_adv in
    bin_adv_help (s / 2) (n / 2) rightbit

  (* HELPER FUNCTIONS *)

  (* size of an adt *)
  let rec adt_size (t : adt) : int =
    match t with
    | Unit -> 1
    | Sum (x, y) -> (adt_size x) + (adt_size y)
    | Prod (x, y) -> (adt_size x) * (adt_size y)

  (* size of a list of adts *)
  let env_size env =
    List.fold_left
      (fun acc x -> acc + (adt_size x))
      0
      env

  (* TODO: re-add compiling adts to bitstrings *)

end

(* SPARSE TENSORKANREN *)

module SparseTK(SR: Semiring) = struct

  (* TYPES *)

  type t = SR.t

  open TK

  type tk = t tk
  type rel = t rel
  type tk_prgm = t tk_prgm

  type arr = ((adv list) * t) list (* list of nonzero entries in sparse tensor *)

  type comp_rel = {
    name: string;
    args: adt list;
    body: arr
  }

  (* HELPERS *)

  let rec arr_mul a1 a2 =
    List.filter_map
      (fun (x1, w1) ->
        match List.find_opt (fun (x2, w2) -> x2 = x1) a2 with
        | None -> None
        | Some (x2, w2) -> Some (x1, SR.mul w1 w2))
      a1

  let rec consolidate_entries array =
    match array with
    | [] -> []
    | (a, aw) :: d ->
        let same, diff = List.partition (fun (x, xw) -> x = a) (consolidate_entries d) in
        let samesum = List.fold_left (fun acc (x, xw) -> SR.add acc xw) SR.zero same in
        (a, samesum + aw) :: diff

  let rec cartesian_prod l =
    match l with
    | [] -> []
    | a :: [] -> List.map (fun x -> [x]) a
    | a :: d ->
      List.map
        (fun x ->
          (List.map
            (fun y ->
              y :: x)
            a))
        (cartesian_prod d)
      |> List.flatten

  let rec gen_all_adt_advs (typ : adt) =
    match typ with
    | Unit -> [Sole]
    | Sum (lt, rt) ->
        let lvs = gen_all_adt_advs lt in
        let rvs = gen_all_adt_advs rt in
        (List.map (fun x -> Left x) lvs) @ (List.map (fun x -> Right x) rvs)
    | Prod (at, bt) ->
        List.map
        (fun (x :: y :: []) -> Pair (x, y))
        (cartesian_prod [(gen_all_adt_advs at); (gen_all_adt_advs bt)])



  (* EVALUATION *)

  (* GO FROM HERE *)
  let rec eval_tk (exp : tk) (env : adt list) (rels : comp_rel list) : arr =
    match exp with
    | Succeed ->
        List.map 
          (fun vs -> (SR.one, v))
          (List.map gen_all_adt_advs env)
    | Fail -> []
    | Conj (e1, e2) ->
        arr_mul (eval_tk e1 env rels) (eval_tk e2 env rels)
    | Disj  (e1, e2) ->
        consolidate_entries ((eval_tk e1 env rels) ++ (eval_tk e2 env rels))
    | Fresh (vt, body) ->
        let body_res = eval_tk body (vt :: env) rels in
        consolidate_entries (List.map (fun (x, w) -> (List.tl x, w)) body_res)
    | Rel (name, args) -> ...
    | Eqo (a, b) -> ...
    | Neqo (a, b) -> ...
    | Soleo (n, t) ->
        List.map 
          (fun vs -> (SR.one, v))
          (List.map gen_all_adt_advs env)
    | Lefto ((abn, abt), (an, at)) -> ...
    | Righto (ab, b) -> ...
    | Pairo (ab, a, b) -> ...
    | Factor w -> ...
    



end
