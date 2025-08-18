#require "nx"
#require "msat"
#require "msat.sat"
#require "msat.tseitin"

#install_printer Nx.pp

module Sat = Msat_sat
module E = Sat.Int_lit
module F = Msat_tseitin.Make(E)

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
  (* create freshes with given type *)
  let rec create_freshes (ts : adt list) (body : 'elt tk) : 'elt tk =
    match ts with
    | [] -> body
    | at :: dts ->
        create_freshes dts (Fresh (at, body))


  (* COMPILING ADTS TO BITSTRINGS *)

  let rec compile_adt (t : adt) : adt =
    match t with
    | Unit -> Unit
    | Sum (Unit, Unit) -> Sum (Unit, Unit) (* bools still allowed *)
    | Sum (x, y) ->
        let xc = compile_adt x in
        let yc = compile_adt y in
        let c = if (adt_size xc) > (adt_size yc) then xc else yc in (* find bigger type *)
        Prod (bool_adt, c) (* put a tag in front of it *)
    | Prod (x, y) -> Prod (compile_adt x, compile_adt y)

  let compile_var (v, vt) = (v, compile_adt vt)

  (* variable (of compiled type) and original type, ensures only inhabits valid values *)
  let rec enforce_var_type (v : var) (ot : adt) =
    let vv, vt = v in
    match vt, ot with
    | Unit, Unit -> Succeed
    | Sum (Unit, Unit), Sum (Unit, Unit) -> Succeed
    | Sum (Unit, Unit), Unit -> trueo v
    | Prod (Sum (Unit, Unit), wt), Sum (at, bt) ->
        Fresh (bool_adt,
          Fresh (wt,
            Conj (
              Pairo ((vv + 2, vt), (1, bool_adt), (0, wt)),
              Disj (
                Conj (
                  trueo (1, bool_adt),
                  enforce_var_type (0, wt) at),
                Conj (
                  falseo (1, bool_adt),
                  enforce_var_type (0, wt) bt)))))
    | Prod (xt, yt), Unit ->
        Fresh (xt,
          Fresh (yt,
            Conj (
              Pairo ((vv + 2, vt), (1, xt), (0, yt)),
              Conj (
                enforce_var_type (1, xt) Unit,
                enforce_var_type (0, yt) Unit))))
    | Prod (xt, yt), Prod (at, bt) ->
        Fresh (xt,
          Fresh (yt,
            Conj (
              Pairo ((vv + 2, vt), (1, xt), (0, yt)),
              Conj (
                enforce_var_type (1, xt) at,
                enforce_var_type (0, yt) bt))))
    | _ -> invalid_arg "Var has improperly compiled type!"

  let rec count_adt_bools (t : adt) : int =
    match t with
    | Unit -> 0
    | Sum (Unit, Unit) -> 1
    | Prod (at, bt) -> (count_adt_bools at) + (count_adt_bools bt)
    | _ -> invalid_arg "passed type must be compiled"

  (* unifies an adt with bool vars with debruijn indices in given inclusive range *)
  let rec unify_adt_bools (x : var) (first_bv : int) (num_bv : int) : 'elt tk =
    let xv, xt = x in
    match xt with
    | Unit -> Succeed
    | Sum (Unit, Unit) ->
        if num_bv = 0 then
          trueo x (* force to a single value *)
        else
          Eqo (x, (first_bv, bool_adt))
    | Prod (xt, yt) ->
        let xt_num_bools = count_adt_bools xt in
        Fresh (xt,
          Fresh (yt,
            Conj (
              Pairo ((xv + 2, xt), (1, xt), (0, yt)),
              Conj (
                unify_adt_bools
                  (1, xt) (first_bv + 2) xt_num_bools,
                unify_adt_bools
                  (0, yt) (first_bv + 2 + xt_num_bools) (num_bv - xt_num_bools)))))
    | _ -> invalid_arg "passed type must be compiled"

  (* assumes both source and target are (potentially different) compiled versions *)
  (* generates code so that they both hold the same value *)
  let rec coerced_unify (a : var) (b : var) =
    let av, at = a in
      let bv, bt = b in
    if (adt_size at) > (adt_size bt) then
      coerced_unify b a (* first variable should be smaller *)
    else
      let num_bools = count_adt_bools at in
      create_freshes
        (List.init num_bools (fun _ -> bool_adt))
        (Conj (
          unify_adt_bools (av + num_bools, at) 0 num_bools,
          unify_adt_bools (bv + num_bools, bt) 0 num_bools))

  let rec compile_tk (e : 'elt tk) : 'elt tk =
    match e with
    | Succeed -> Succeed
    | Fail -> Fail
    | Conj (a, b) -> Conj (compile_tk a, compile_tk b)
    | Disj (a, b) -> Disj (compile_tk a, compile_tk b)
    | Fresh (t, exp) ->
        Fresh (compile_adt t,
          Conj (
            enforce_var_type (0, compile_adt t) t,
            compile_tk exp))
    | Rel (name, args) ->
        Rel (name,
          List.map (fun (v, vt) -> (v, compile_adt vt)) args)
    | Eqo (a, b) -> Eqo (compile_var a, compile_var b)
    | Neqo (a, b) -> Neqo (compile_var a, compile_var b)
    | Soleo (v, vt) -> Soleo (v, compile_adt vt)
    | Lefto ((ab, Sum (Unit, Unit)), (a, Unit)) -> (* a + b, a *)
        Lefto ((ab, Sum (Unit, Unit)), (a, Unit))
    | Lefto ((ab, abt), (a, at)) -> (* a + b, a *)
        let abtc = compile_adt abt in
        let Prod (_, vt) = abtc in (* get the compiled child type *)
        Fresh (vt,
          Fresh (bool_adt,
            Conj (
              Conj (
                coerced_unify (1, vt) (a + 2, compile_adt at),
                Pairo ((ab + 2, abtc), (0, bool_adt), (1, vt))),
            trueo (0, bool_adt))))
    | Righto ((ab, Sum (Unit, Unit)), (b, Unit)) -> (* a + b, b *)
        Righto ((ab, Sum (Unit, Unit)), (b, Unit))
    | Righto ((ab, abt), (b, bt)) -> (* a + b, b *)
        let abtc = compile_adt abt in
        let Prod (_, vt) = abtc in (* get the compiled child type *)
        Fresh (vt, 
          Fresh (bool_adt,
            Conj (
              Conj (
                coerced_unify (1, vt) (b + 2, compile_adt bt),
                Pairo ((ab + 2, abtc), (0, bool_adt), (1, vt))),
              falseo (0, bool_adt))))
    | Pairo ((ab, abt), (a, at), (b, bt)) -> (* a * b, a, b *)
        let abtc = compile_adt abt in
        let Prod (atc, btc) = abtc in
        Pairo ((ab, abtc), (a, atc), (b, btc))
    | Factor x -> Factor x

  let enforce_arg_types (cts : adt list) (ots : adt list) : 'elt tk =
    let enforce_exps =
      List.map2
        enforce_var_type
        (List.mapi (fun i t -> (i, t)) cts)
        ots
    in
      conj enforce_exps

  let compile_rel (r : 'elt rel) : 'elt rel =
    let cargs = List.map compile_adt r.args in
    { name = r.name;
      args = cargs;
      body =
        Conj (
          enforce_arg_types cargs r.args,
          compile_tk r.body) }

  let compile_tk_prgm (p : 'elt tk_prgm) : 'elt tk_prgm =
    List.map compile_rel p

end

(* tensor whose elements form semiring *)
module type TensorSemiring = sig
  type elt
  type arr
  
  val zero : elt
  val one : elt

  val init : int array -> (int array -> elt) -> arr (* should return [|0|] in shape [||] case *)
  val shape : arr -> int array
  val reshape : arr -> int array -> arr
  val concat_horizontal : arr -> arr -> arr

  (* axis, array. should reduce rank by one *)
  val sum : int -> arr -> arr
  val add : arr -> arr -> arr
  val mul : arr -> arr -> arr
  val smul : elt -> arr -> arr

  val print : arr -> unit
end

(* TensorSemiring with standard + and * *)
module AddMulTensorSemiring : TensorSemiring
  with type elt = float
  with type arr = Nx.float64_t
= struct

  type elt = float
  type arr = Nx.float64_t

  let zero = 0.0
  let one = 1.0

  let init = Nx.init Float64
  let shape = Nx.shape
  let reshape = Fun.flip Nx.reshape
  let concat_horizontal a b = Nx.concatenate ~axis:0 [a; b]

  let sum axis x = Nx.sum ~axes:[|axis|] ~keepdims:false x
  let add = Nx.add
  let mul = Nx.mul
  let smul = Nx.rmul_s

  let print x = Nx.print_data x

end

(* TensorSemiring with max and add (max tropical semiring) *)
module MaxAddTensorSemiring : TensorSemiring
  with type elt = float
  with type arr = Nx.float64_t
= struct

  type elt = float
  type arr = Nx.float64_t

  let zero = Float.neg_infinity
  let one = 0.0
  
  let init = Nx.init Float64
  let shape = Nx.shape
  let reshape = Fun.flip Nx.reshape
  let concat_horizontal a b = Nx.concatenate ~axis:0 [a; b]

  let sum axis x = Nx.max ~axes:[|axis|] ~keepdims:false x
  let add = Nx.maximum
  let mul = Nx.add
  let smul = Nx.radd_s

  let print x = Nx.print_data x

end

(* TensorSemiring with max and min (max min/fuzzy semiring) *)
module MaxMinTensorSemiring : TensorSemiring
  with type elt = float
  with type arr = Nx.float64_t
= struct
  type elt = float
  type arr = Nx.float64_t

  let zero = Float.neg_infinity
  let one = Float.infinity

  let init = Nx.init Float64
  let shape = Nx.shape
  let reshape = Fun.flip Nx.reshape
  let concat_horizontal a b = Nx.concatenate ~axis:0 [a; b]

  let sum axis x = Nx.max ~axes:[|axis|] ~keepdims:false x
  let add = Nx.maximum
  let mul = Nx.minimum
  let smul = Nx.rminimum_s

  let print x = Nx.print_data x
end

module TensorTK(TS : TensorSemiring) = struct
  
  (* TYPES *)

  type adt = TK.adt
  type adv = TK.adv
  type var = TK.var
  type tk = TS.elt TK.tk
  type rel = TS.elt TK.rel
  type tk_prgm = TS.elt TK.tk_prgm

  type comp_rel = {
    name: string;
    args: adt list;
    body: TS.arr
  }

  type comp_tk_prgm = comp_rel list

  (* HELPER FUNCTIONS *)

  (* zeros and ones *)
  let zeros shp = TS.init shp (Fun.const TS.zero)
  let ones shp = TS.init shp (Fun.const TS.one)

  (* corresponding tensor shape of a list of adts *)
  let shape_of_env env =  Array.of_list @@ List.map TK.adt_size env

  (* like kronecker product, but tensor-shaped *)
  let tensor_prod (a : TS.arr) (b : TS.arr) : TS.arr =
    let a_shape = TS.shape a in
    let b_shape = TS.shape b in
    let a_rank = Array.length a_shape in
    let b_rank = Array.length b_shape in
    let a_good_rank =
      TS.reshape
        a
        (Array.append a_shape (Array.init b_rank (Fun.const 1)))
    in
    let b_good_rank =
      TS.reshape
      b
      (Array.append (Array.init a_rank (Fun.const 1)) b_shape)
    in
    TS.mul a_good_rank b_good_rank

  (* kronecker product of vectors *)
  let vec_kron_prod a b = TS.reshape (tensor_prod a b) [|-1|]

  (* kronecker sum of vectors *)
  let vec_kron_sum a b = TS.concat_horizontal a b

  (* zero vector of length s with 1 at position n *)
  let rec unit_basis s n =
    match s, n with
    | 0, _ -> zeros [|0|]
    | ss, 0 -> vec_kron_sum (ones [|1|]) (unit_basis (s - 1) (n - 1))
    | ss, sn -> vec_kron_sum (zeros [|1|]) (unit_basis (s - 1) (n - 1))

  (* vectors corresponding to true_adv and false_adv *)
  let true_vec = unit_basis 2 0
  let false_vec = unit_basis 2 1

  (* EVALUATION *)

  (* evaluate a tk expression by turn into a tensor *)
  let rec eval_tk (exp : tk) (env : adt list) (rels : comp_rel list) : TS.arr =
    match exp with
    | Succeed ->
        (* all-one tensor w/ env shape *)
        ones (shape_of_env env)
    | Fail ->
        (* all-zero tensor w/ env shape *)
        zeros (shape_of_env env);
    | Conj (e1, e2) ->
        (* element-wise multiplication *)
        TS.mul (eval_tk e1 env rels) (eval_tk e2 env rels)
    | Disj (e1, e2) ->
        (* element-wise addition *)
        TS.add (eval_tk e1 env rels) (eval_tk e2 env rels)
    | Fresh (vt, body) -> 
        (* evaluate body with new variable in environment *)
        let body_res = eval_tk body (vt :: env) rels in
        (* sum over the variable (designed to be axis 0) *)
        TS.sum 0 body_res
    | Rel (name, args) ->
        (* get the result of the relation, then unify it with the corresponding variables *)
        let rel = List.find (fun r -> r.name = name) rels in
        let nargs = List.length rel.args in
        let args_and_env = rel.args @ env in
        let unify_arg_tensors = 
          List.mapi
            (fun i a ->
              let (ai, at) = a in
              TS.init (shape_of_env args_and_env) (* unify *)
                (fun idx ->
                  if idx.(i) = idx.(ai + nargs) then (* arg index w/ corrected var index *)
                    TS.one
                  else
                    TS.zero))
            args (* (int * adt) list *)
        in
        let unified_args_env = (* conj the unifications for each arg and rel result *)
          List.fold_left
            TS.mul
              (tensor_prod rel.body (ones (shape_of_env env)))
              unify_arg_tensors
        in
        List.fold_left (* sum over the rel args *)
          (fun res_tensor _ -> TS.sum 0 res_tensor)
          unified_args_env
          args
    | Eqo (a, b) ->
        (* unify a and b *)
        let (av, _) = a in
        let (bv, _) = b in
        TS.init (shape_of_env env)
          (fun idx ->
            if idx.(av) = idx.(bv) then
              TS.one
            else
              TS.zero)
    | Neqo (a, b) ->
        (* deunify a and b *)
        let (av, _) = a in
        let (bv, _) = b in
        TS.init (shape_of_env env)
          (fun idx ->
            if idx.(av) = idx.(bv) then
              TS.zero
            else
              TS.one)
    | Soleo (n, t) ->
        (* same as succeed, b/c guaranteed by "typechecking"*)
        ones (shape_of_env env)
    | Lefto (ab, a) ->
        (* check that left side matches *)
        let (abv, _) = ab in
        let (av, _) = a in
        TS.init (shape_of_env env)
          (fun idx ->
            if idx.(abv) = idx.(av) then
              TS.one
            else
              TS.zero)
    | Righto (ab, b) ->
        (* check that right side matches *)
        let (abv, Sum (at, _bt)) = ab in
        let (bv, _) = b in
        let sa = TK.adt_size at in
        TS.init (shape_of_env env)
          (fun idx ->
            if idx.(abv) = (sa + idx.(bv)) then
              TS.one
            else
              TS.zero)
    | Pairo (ab, a, b) ->
        (* check that a and b match with ab *)
        let (abv, _) = ab in
        let (av, at) = a in
        let (bv, bt) = b in
        let sb = TK.adt_size bt in
        TS.init (shape_of_env env)
          (fun idx ->
            if idx.(abv) = ((idx.(av) * sb) + idx.(bv)) then
              TS.one
            else
              TS.zero)
    | Factor w ->
        TS.(smul w (ones (shape_of_env env)))

  let eval_rel (r : rel) (rels : comp_rel list) : comp_rel =
    { name = r.name;
      args = r.args;
      body = eval_tk r.body r.args rels }

  let rec eval_tk_prgm_help (prgm : rel list) (prev_comp : comp_rel list) =
    let comp = List.map (fun r -> eval_rel r prev_comp) prgm in
    (* print_endline "----------------------------"; *)
    (* List.iter (fun r -> print_endline r.name; TS.print r.body; print_endline "") comp; *)
    if comp = prev_comp then
      comp
    else
      eval_tk_prgm_help prgm comp

  let eval_tk_prgm (prgm : rel list) : comp_rel list =
    let init_comp_rels =
      List.map
        (fun (r : rel) ->
          { name = r.name;
            args = r.args;
            body = zeros (shape_of_env r.args)})
        prgm
    in
    eval_tk_prgm_help prgm init_comp_rels

  let eval_tk_prgm_maino (prgm : rel list) : comp_rel =
    List.find (fun r -> r.name = "maino") (eval_tk_prgm prgm)

end

(* EXAMPLES/TESTS *)

module MaxAddTKEx = struct

  open TK
  module TTK = TensorTK(MaxAddTensorSemiring)
  open TTK

  let ex_basic : tk_prgm = [ (* expected: Left Sole *)
    { name = "maino";
      args = [Sum (Unit, Unit)];
      body =
        Fresh (Unit,
               conj [
                 Lefto ((1, Sum (Unit, Unit)), (0, Unit));
                 Soleo (0, Unit)])}]

  let trueo : rel = {
    name = "trueo";
    args = [bool_adt];
    body =
      Fresh (Unit,
             conj [
               Lefto ((1, Sum (Unit, Unit)), (0, Unit));
               Soleo (0, Unit)])}

  let falseo : rel = {
    name = "falseo";
    args = [bool_adt];
    body =
      Fresh (Unit,
             conj [
               Righto ((1, Sum (Unit, Unit)), (0, Unit));
               Soleo (0, Unit)])}

  let ex_trueo : tk_prgm = [ (* expected: true_adv *)
    trueo;
    { name = "maino";
      args = [bool_adt];
      body = Rel ("trueo", [(0, bool_adt)])}]

  let ex_true_or_false : tk_prgm = [ (* expected: true_adv and false_adv *)
    trueo; falseo;
    { name = "maino";
      args = [bool_adt];
      body = disj [
        Rel ("trueo", [(0, bool_adt)]);
        Rel ("falseo", [(0, bool_adt)])]}]

  let ex_true_and_false : tk_prgm = [ (* expected: no solution *)
    trueo; falseo;
    {
      name = "maino";
      args = [bool_adt];
      body = conj [
        Rel ("trueo", [(0, bool_adt)]);
        Rel ("falseo", [(0, bool_adt)])]}]

  let noto : rel = { (* expects trueo and falseo to also be rels *)
    name = "noto";
    args = [bool_adt; bool_adt];
    body = disj [
        conj [
          Rel ("falseo", [(0, bool_adt)]);
          Rel ("trueo", [(1, bool_adt)])];
        conj [
          Rel ("trueo", [(0, bool_adt)]);
          Rel ("falseo", [(1, bool_adt)])]]}

  let sameo : rel = { (* expects trueo and falseo to also be rels *)
    name = "sameo";
    args = [bool_adt; bool_adt];
    body = disj [
        conj [
          Rel ("trueo", [(0, bool_adt)]);
          Rel ("trueo", [(1, bool_adt)])];
        conj [
          Rel ("falseo", [(0, bool_adt)]);
          Rel ("falseo", [(1, bool_adt)])]]}

  let ex_noto : tk_prgm = [ (* expected: true_adv *)
    trueo; falseo; noto;
    { name = "maino";
      args = [bool_adt];
      body =
        Fresh (bool_adt,
               conj [
                 Rel ("falseo", [(0, bool_adt)]);
                 Rel ("noto", [(0, bool_adt); (1, bool_adt)])])}]

  let ex_noto_rev : tk_prgm = [ (* expected: true_adv *)
    trueo; falseo; noto;
    { name = "maino";
      args = [bool_adt];
      body =
        Fresh (bool_adt,
               conj [
                 Rel ("falseo", [(0, bool_adt)]);
                 Rel ("noto", [(1, bool_adt); (0, bool_adt)])])}]

  let xoro : rel = { (* expects trueo, falseo, noto, sameo to be rels *)
    name = "xoro";
    args = [bool_adt; bool_adt; bool_adt];
    body = disj [
      conj [
        Rel ("noto", [(0, bool_adt); (1, bool_adt)]);
        Rel ("trueo", [(2, bool_adt)])];
      conj [
        Rel ("sameo", [(0, bool_adt); (1, bool_adt)]);
        Rel ("falseo", [(2, bool_adt)])]]}

  let ex_xoro : tk_prgm = [ (* expected: true_adv *)
    trueo; falseo; noto; sameo; xoro;
    { name = "maino";
      args = [bool_adt];
      body = 
        Fresh (bool_adt,
          Fresh (bool_adt,
            conj [
              Rel ("falseo", [(1, bool_adt)]);
              Rel ("trueo", [(0, bool_adt)]);
              Rel ("xoro", [(1, bool_adt); (0, bool_adt); (2, bool_adt)])]))}]

  let ex_xoro_rev : tk_prgm = [ (* expected: true_adv *)
    trueo; falseo; noto; sameo; xoro;
    { name = "maino";
      args = [bool_adt];
      body = 
        Fresh (bool_adt,
          Fresh (bool_adt,
            conj [
              Rel ("falseo", [(1, bool_adt)]);
              Rel ("trueo", [(0, bool_adt)]);
              Rel ("xoro", [(2, bool_adt); (0, bool_adt); (1, bool_adt)])]))}]

  let ex_noto_pair : tk_prgm = [ (* expected: Pair (true_adv, false_adv) and Pair (false_adv, true_adv) *)
    trueo; falseo; noto;
    { name = "maino";
      args = [Prod (bool_adt, bool_adt)];
      body = 
        Fresh (bool_adt,
          Fresh (bool_adt,
            conj [
              Pairo (
                (2, Prod (bool_adt, bool_adt)),
                (1, bool_adt),
                (0, bool_adt));
              Rel ("noto", [(1, bool_adt); (0, bool_adt)])]))}]

  let ex_pair : tk_prgm = [
    { name = "maino";
      args = [Prod (bool_adt, bool_adt)];
      body = Fresh (bool_adt,
        Pairo (
          (1, Prod (bool_adt, bool_adt)),
          (0, bool_adt),
          (0, bool_adt)))}]

  let succeedo : rel = {
    name = "succeedo";
    args = [];
    body = Succeed }

  let failo : rel = {
    name = "failo";
    args = [];
    body = Fail }

  let ex_succeedo : tk_prgm = [
    succeedo;
    { name = "maino";
      args = [Prod (bool_adt, bool_adt)];
      body = Rel ("succeedo", [])}]

  let ex_no_vars_succeed : tk_prgm = [ (* expected: 1 *)
    succeedo;
    { name = "maino";
      args = [];
      body = Rel ("succeedo", [])}]

  let ex_no_vars_fail : tk_prgm = [ (* expected: 0 *)
    failo;
    { name = "maino";
      args = [];
      body = Rel ("failo", [])}]

  let ex_multi_vars : tk_prgm = [ (* expected: 2 x 2 identity matrix *)
    trueo; falseo; sameo;
    { name = "maino";
      args = [bool_adt; bool_adt];
      body = Rel ("sameo", [(0, bool_adt); (1, bool_adt)])}]

  let ex_contra_recursion : tk_prgm = [ (* not sure what this should return, depends on how init rels *)
    trueo; falseo; noto; sameo; xoro;
    { name = "maino";
      args = [bool_adt];
      body = Fresh (bool_adt,
        Conj (
          Rel ("maino", [(0, bool_adt)]),
          Rel ("noto", [(0, bool_adt); (1, bool_adt)])))}]

  let ex_var_has_val_zero : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_has_val (0, nat_adt 3) (nat_adv 3 0) }]

  let ex_var_has_val_one : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_has_val (0, nat_adt 3) (nat_adv 3 1) }]

  let ex_var_has_val_two : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_has_val (0, nat_adt 3) (nat_adv 3 2) }]

  let ex_small_transitive_closure : tk_prgm = [ 
    { name = "grapho";
      args = [nat_adt 3; nat_adt 3];
      body =
        Disj (
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 0),
            var_has_val (1, nat_adt 3) (nat_adv 3 1)),
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 1),
            var_has_val (1, nat_adt 3) (nat_adv 3 2))) };
    { name = "connecto";
      args = [nat_adt 3; nat_adt 3];
      body = 
        Disj (
          Rel ("grapho", [(0, nat_adt 3); (1, nat_adt 3)]),
          Fresh (nat_adt 3,
            Conj (
              Rel ("connecto", [(1, nat_adt 3); (0, nat_adt 3)]),
              Rel ("connecto", [(0, nat_adt 3); (2, nat_adt 3)]))))};
    { name = "maino";
      args = [nat_adt 3; nat_adt 3];
      body = Rel ("connecto", [(0, nat_adt 3); (1, nat_adt 3)])}]

  let ex_potential_infinite_loop : tk_prgm = [
    { name = "maino";
      args = [];
      body = Disj (Succeed, Rel ("maino", [])) }]

  let ex_small_transitive_closure_loop : tk_prgm = [ 
    { name = "grapho";
      args = [nat_adt 3; nat_adt 3];
      body =
        disj [
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 0),
            var_has_val (1, nat_adt 3) (nat_adv 3 1));
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 1),
            var_has_val (1, nat_adt 3) (nat_adv 3 2));
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 2),
            var_has_val (1, nat_adt 3) (nat_adv 3 0))]};
    { name = "connecto";
      args = [nat_adt 3; nat_adt 3];
      body = 
        Disj (
          Rel ("grapho", [(0, nat_adt 3); (1, nat_adt 3)]),
          Fresh (nat_adt 3,
            Conj (
              Rel ("connecto", [(1, nat_adt 3); (0, nat_adt 3)]),
              Rel ("connecto", [(0, nat_adt 3); (2, nat_adt 3)]))))};
    { name = "maino";
      args = [nat_adt 3; nat_adt 3];
      body = Rel ("connecto", [(0, nat_adt 3); (1, nat_adt 3)])}]

  let ex_coin_flip : tk_prgm = [
    { name = "maino";
      args = [bool_adt];
      body =
        Disj (
          Conj (
            Factor 0.5,
            var_has_val (0, bool_adt) true_adv),
          Conj (
            Factor 0.5,
            var_has_val (0, bool_adt) false_adv)) }]

  let ex_var_avoids_val_zero : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_avoids_val (0, nat_adt 3) (nat_adv 3 0) }]

  let ex_var_avoids_val_one : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_avoids_val (0, nat_adt 3) (nat_adv 3 1) }]

  let ex_var_avoids_val_two : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_avoids_val (0, nat_adt 3) (nat_adv 3 2) }]

  let ex_var_has_val_zero_comp : tk_prgm = TK.compile_tk_prgm ex_var_has_val_zero
  let ex_var_has_val_one_comp : tk_prgm = TK.compile_tk_prgm ex_var_has_val_one
  let ex_var_has_val_two_comp : tk_prgm = TK.compile_tk_prgm ex_var_has_val_two

  let ex_small_transitive_closure_comp : tk_prgm =
    TK.compile_tk_prgm ex_small_transitive_closure
  let ex_small_transitive_closure_loop_comp : tk_prgm =
    TK.compile_tk_prgm ex_small_transitive_closure_loop

  let ex_neqo : tk_prgm = [
    { name = "maino";
      args = [bool_adt; bool_adt];
      body = Neqo ((0, bool_adt), (1, bool_adt))}]

  let ex_neqo_big : tk_prgm = TK.compile_tk_prgm [
    { name = "maino";
      args = [nat_adt 4; nat_adt 4];
      body = Neqo ((0, nat_adt 4), (1, nat_adt 4))}]

  let ex_coerced_unify : tk_prgm = [
    falseo;
    { name = "maino";
      args = [bool_adt];
      body = 
        Fresh (Prod (Prod (bool_adt, bool_adt), bool_adt),
          Fresh (Prod (bool_adt, bool_adt),
            Fresh (Prod (bool_adt, Prod (bool_adt, bool_adt)),
              Fresh (Prod (bool_adt, bool_adt),
                Fresh (bool_adt,
                  Fresh (bool_adt,
                    Fresh (bool_adt,
                      conj [
                        Pairo ((4, Prod (Prod (bool_adt, bool_adt), bool_adt)),
                          (2, bool_adt), (3, Prod (bool_adt, bool_adt)));
                        Pairo ((3, Prod (bool_adt, bool_adt)),
                          (1, bool_adt), (0, bool_adt));
                        Rel ("falseo", [(0, bool_adt)]);
                        coerced_unify
                          (4, Prod (Prod (bool_adt, bool_adt), bool_adt))
                          (6, Prod (bool_adt, Prod (bool_adt, bool_adt)));
                        Pairo ((6, Prod (bool_adt, Prod (bool_adt, bool_adt))),
                          (5, Prod (bool_adt, bool_adt)), (7, bool_adt))])))))))}]

  (* run tests *)

  let test_examples () =
    let etpm = eval_tk_prgm_maino in
    let one = MaxAddTensorSemiring.one in
    let zero = MaxAddTensorSemiring.zero in
    let init = MaxAddTensorSemiring.init in

    let of_array a =
      Nx.of_bigarray @@ Bigarray.genarray_of_array1 @@
      (Bigarray.Array1.of_array Float64 C_layout a) in
    let of_arrays a =
      Nx.of_bigarray @@ Bigarray.genarray_of_array2 @@
      (Bigarray.Array2.of_array Float64 C_layout a) in
    
    print_endline "ex_basic";
    assert ((etpm ex_basic).body = (of_array [|one; zero|]));

    print_endline "ex_trueo";
    assert ((etpm ex_trueo).body = (of_array [|one; zero|]));

    print_endline "ex_true_or_false";
    assert ((etpm ex_true_or_false).body = (of_array [|one; one|]));

    print_endline "ex_true_and_false";
    assert ((etpm ex_true_and_false).body = (of_array [|zero; zero|]));

    print_endline "ex_noto";
    assert ((etpm ex_noto).body = (of_array [|one; zero|]));

    print_endline "ex_noto_rev";
    assert ((etpm ex_noto_rev).body = (of_array [|one; zero|]));

    print_endline "ex_xoro";
    assert ((etpm ex_xoro).body = (of_array [|one; zero|]));

    print_endline "ex_xoro_rev";
    assert ((etpm ex_xoro_rev).body = (of_array [|one; zero|]));

    print_endline "ex_noto_pair";
    assert ((etpm ex_noto_pair).body = (of_array [|zero; one; one; zero|]));

    print_endline "ex_pair";
    assert ((etpm ex_pair).body = (of_array [|one; zero; zero; one|]));

    print_endline "ex_succeedo";
    assert ((etpm ex_succeedo).body = (of_array [|one; one; one; one|]));

    print_endline "ex_no_vars_succeed";
    assert ((etpm ex_no_vars_succeed).body = (init [||] (Fun.const one)));

    print_endline "ex_no_vars_fail";
    assert ((etpm ex_no_vars_fail).body = (init [||] (Fun.const zero)));

    print_endline "ex_multi_vars";
    assert ((etpm ex_multi_vars).body = (of_arrays [|[|one; zero|]; [|zero; one|]|]));

    print_endline "ex_contra_recursion";
    assert ((etpm ex_contra_recursion).body = (of_array [|zero; zero|]));

    print_endline "ex_var_has_val_zero";
    assert ((etpm ex_var_has_val_zero).body = (of_array [|one; zero; zero|]));
    
    print_endline "ex_var_has_val_one";
    assert ((etpm ex_var_has_val_one).body = (of_array [|zero; one; zero|]));

    print_endline "ex_var_has_val_two";
    assert ((etpm ex_var_has_val_two).body = (of_array [|zero; zero; one|]));

    print_endline "ex_small_transitive_closure";
    assert (
      (etpm ex_small_transitive_closure).body =
      (of_arrays [|
        [|zero; one; one|];
        [|zero; zero; one|];
        [|zero; zero; zero|]|]));

    print_endline "ex_potential_infinite_loop";
    assert ((etpm ex_potential_infinite_loop).body = (init [||] (Fun.const one)));

    print_endline "ex_small_transitive_closure_loop";
    assert (
      (etpm ex_small_transitive_closure_loop).body =
      (of_arrays [|
        [|one; one; one|];
        [|one; one; one|];
        [|one; one; one|]|]));
        
    print_endline "ex_coin_flip";
    assert ((etpm ex_coin_flip).body = (of_array [|0.5; 0.5|]));

    print_endline "ex_var_avoid_val_zero";
    assert ((etpm ex_var_avoids_val_zero).body = (of_array [|zero; one; one|]));

    print_endline "ex_var_avoid_val_one";
    assert ((etpm ex_var_avoids_val_one).body = (of_array [|one; zero; one|]));

    print_endline "ex_var_avoid_val_two";
    assert ((etpm ex_var_avoids_val_two).body = (of_array [|one; one; zero|]));

    print_endline "ex_var_has_val_zero_comp";
    assert (
      (etpm ex_var_has_val_zero_comp).body =
        (of_array [|one; zero; zero; zero|]));

    print_endline "ex_var_has_val_one_comp";
    assert (
      (etpm ex_var_has_val_one_comp).body =
        (of_array [|zero; zero; one; zero|]));

    print_endline "ex_var_has_val_two_comp";
    assert (
      (etpm ex_var_has_val_two_comp).body =
        (of_array [|zero; zero; zero; one|]));

    print_endline "ex_small_transitive_closure_comp";
    assert (
      (etpm ex_small_transitive_closure_comp).body =
        (of_arrays [|
          [|zero; zero; one; one|];
          [|zero; zero; zero; zero|];
          [|zero; zero; zero; one|];
          [|zero; zero; zero; zero|]|]));

    print_endline "ex_small_transitive_closure_loop_comp";
    assert (
      (etpm ex_small_transitive_closure_loop_comp).body =
        (of_arrays [|
          [|one; zero; one; one|];
          [|zero; zero; zero; zero|];
          [|one; zero; one; one|];
          [|one; zero; one; one|]|]));

    print_endline "ex_neqo";
    assert (
      (etpm ex_neqo).body =
        (of_arrays [|
          [|zero; one|];
          [|one; zero|]|]));

    print_endline "ex_neqo_big";
    assert (
      (etpm ex_neqo_big).body =
        (of_arrays [|
          [|zero; zero; zero; zero; one; zero; one; one|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|one; zero; zero; zero; zero; zero; one; one|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|one; zero; zero; zero; one; zero; zero; one|];
          [|one; zero; zero; zero; one; zero; one; zero|]|]));

    print_endline "ex_coerced_unify";
    assert ((etpm ex_coerced_unify).body = (of_array [|zero; one|]));

    ()

end

module AddMulTKEx = struct

  open TK
  module TTK = TensorTK(AddMulTensorSemiring)
  open TTK

  let failo : rel = {
    name = "failo";
    args = [];
    body = Fail }

  let ex_coin_flip : tk_prgm = [
    { name = "maino";
      args = [bool_adt];
      body =
        Disj (
          Conj (
            Factor 0.5,
            var_has_val (0, bool_adt) true_adv),
          Conj (
            Factor 0.5,
            var_has_val (0, bool_adt) false_adv)) }]

  let ex_infinite_coin_flip : tk_prgm = [
    { name = "maino";
      args = [];
      body = Disj (
        Factor 0.5,
        Conj (
          Factor 0.5,
          Rel ("maino", []))) }]

  let test_examples () =
    let etpm = eval_tk_prgm_maino in
    let one = AddMulTensorSemiring.one in
    let zero = AddMulTensorSemiring.zero in
    let init = AddMulTensorSemiring.init in

    let of_array a =
      Nx.of_bigarray @@ Bigarray.genarray_of_array1 @@
      (Bigarray.Array1.of_array Float64 C_layout a) in

    print_endline "ex_coin_flip";
    assert ((etpm ex_coin_flip).body = (of_array [|0.5; 0.5|]));

    print_endline "ex_infinite_coin_flip";
    assert ((etpm ex_infinite_coin_flip).body = (init [||] (Fun.const one)));

    ()

end

(* COMPILING TO SAT *)

module SatTK = struct

  open TK

  let rec bind_vars (avs : var list) (bvs : var list) : 'elt tk =
    match avs, bvs with
    | [], [] -> Succeed
    | (av :: avds), (bv :: bvds) ->
        Conj (
          Eqo (av, bv),
          bind_vars avds bvds)

  let rec unroll_recursions (exp : 'elt tk) (rels : bool tk_prgm) (gas : int) : 'elt tk =
    match exp with
    | Succeed -> Succeed
    | Fail -> Fail
    | Conj (e1, e2) -> Conj (unroll_recursions e1 rels gas, unroll_recursions e2 rels gas)
    | Disj (e1, e2) -> Disj (unroll_recursions e1 rels gas, unroll_recursions e2 rels gas)
    | Fresh (t, body) -> Fresh (t, unroll_recursions body rels gas)
    | Rel (name, args) ->
        if gas = 0 then Fail else
          let nargs = List.length args in
          let new_vars = List.mapi (fun idx (vv, vt) -> (idx, vt)) args in
          let old_vars = List.map (fun (vv, vt) -> (vv + nargs, vt)) args in
          let arg_ts = List.map snd args in
          let bound_var_exp = bind_vars new_vars old_vars in
          let body = (List.find (fun r -> r.name = name) rels).body in
          create_freshes
            arg_ts
            (Conj
              (bound_var_exp,
              unroll_recursions body rels (gas - 1)))
    | Eqo (a, b) -> Eqo (a, b)
    | Neqo (a, b) -> Neqo (a, b)
    | Soleo a -> Soleo a
    | Lefto (ab, a) -> Lefto (ab, a)
    | Righto (ab, b) -> Righto (ab, b)
    | Pairo (ab, a, b) -> Pairo (ab, a, b)
    | Factor x -> Factor x

  type 'i range = int * int (* inclusive, exclusive *)

  type satvar =
  | SatUnit
  | SatVar of E.t
  | SatPair of satvar * satvar

  let rec string_of_satvar sv =
    match sv with
    | SatUnit -> "SatUnit"
    | SatVar _ -> "SatVar"
    | SatPair (a, b) ->
        "SatPair (" ^ (string_of_satvar a) ^ ", " ^ (string_of_satvar b) ^ ")"

  let rec satvar_of_adt typ =
    match typ with
    | Unit -> SatUnit
    | Sum (Unit, Unit) -> SatVar (E.fresh ())
    | Prod (a, b) -> SatPair (satvar_of_adt a, satvar_of_adt b)
    | Sum (_, _) -> invalid_arg "doesn't handle non-bool sums"

  (* vars unified with unit should be true *)
  (* otherwise unify via recursion and equality *)
  let rec unify_satvars sv1 sv2 =
    match sv1, sv2 with
    | SatUnit, SatUnit -> F.f_true
    | SatVar v1, SatVar v2 -> F.make_equiv (F.make_atom v1) (F.make_atom v2)
    | SatPair (sv1a, sv1d), SatPair (sv2a, sv2d) ->
        F.make_and [unify_satvars sv1a sv2a; unify_satvars sv1d sv2d]

  (* env has satdts at index corresponding to variable number *)
  let rec sat_of_tk (exp : bool tk) (env : satvar list) : F.t =
    match exp with
    | Succeed -> F.f_true
    | Fail -> F.f_false
    | Conj (e1, e2) -> F.make_and [sat_of_tk e1 env; sat_of_tk e2 env]
    | Disj (e1, e2) -> F.make_or [sat_of_tk e1 env; sat_of_tk e2 env]
    | Fresh (t, body) -> sat_of_tk body ((satvar_of_adt t) :: env)
    | Rel (name, args) -> invalid_arg "sat_of_tk doesn't handle recursions!"
    | Eqo ((av, at), (bv, bt)) ->
        unify_satvars (List.nth env av) (List.nth env bv)
    | Neqo ((av, at), (bv, bt)) ->
        F.make_not (unify_satvars (List.nth env av) (List.nth env bv))
    | Soleo a -> F.f_true
    | Lefto ((abv, Sum (Unit, Unit)), (_av, Unit)) ->
        (* should be true if ab is true *)
        let SatVar atom = List.nth env abv in
        F.make_atom atom
    | Righto ((abv, Sum (Unit, Unit)), (_bv, Unit)) ->
        (* should be true if ab is false *)
        let SatVar atom = List.nth env abv in
        F.make_not (F.make_atom atom)
    | Pairo ((abv, _), (av, _), (bv, _)) ->
        let SatPair (absva, absvd) = List.nth env abv in
        let asv = List.nth env av in
        let bsv = List.nth env bv in
        F.make_and [unify_satvars absva asv; unify_satvars absvd bsv]
    | Factor x -> if x then F.f_true else F.f_false

  let rec reify_satvar evalr v =
    match v with
    | SatUnit -> Sole
    | SatVar sv -> if (evalr sv) then Left Sole else Right Sole
    | SatPair (a, d) -> Pair (reify_satvar evalr a, reify_satvar evalr d)

  let sat_eval_tk_prgm (p : bool tk_prgm) (name : string) (gas : int) =
    let comp_p = TK.compile_tk_prgm p in
    let rel_to_convert = List.find (fun r -> r.name = name) comp_p in
    let rel_unrolled = unroll_recursions rel_to_convert.body comp_p gas in
    let sat_args = List.map satvar_of_adt rel_to_convert.args in
    let rel_tseitin = sat_of_tk rel_unrolled sat_args in
    let prgm_cnf = F.make_cnf rel_tseitin in
    let solver = Sat.create () in
    Sat.assume solver prgm_cnf ();
    match Sat.solve solver with
    | Unsat _ -> None
    | Sat r -> Some (List.map (reify_satvar r.eval) sat_args)

  let sat_eval_tk_prgm_maino p gas = sat_eval_tk_prgm p "maino" gas

end

module SatTKEx = struct

  open TK
  open SatTK

  type tk_prgm = bool TK.tk_prgm
  type rel = bool TK.rel

  let ex_basic : tk_prgm = [ (* expected: Left Sole *)
    { name = "maino";
      args = [Sum (Unit, Unit)];
      body =
        Fresh (Unit,
               conj [
                 Lefto ((1, Sum (Unit, Unit)), (0, Unit));
                 Soleo (0, Unit)])}]

  let trueo : rel = {
    name = "trueo";
    args = [bool_adt];
    body =
      Fresh (Unit,
             conj [
               Lefto ((1, Sum (Unit, Unit)), (0, Unit));
               Soleo (0, Unit)])}

  let falseo : rel = {
    name = "falseo";
    args = [bool_adt];
    body =
      Fresh (Unit,
             conj [
               Righto ((1, Sum (Unit, Unit)), (0, Unit));
               Soleo (0, Unit)])}

  let ex_trueo : tk_prgm = [ (* expected: true_adv *)
    trueo;
    { name = "maino";
      args = [bool_adt];
      body = Rel ("trueo", [(0, bool_adt)])}]

  let ex_true_or_false : tk_prgm = [ (* expected: true_adv and false_adv *)
    trueo; falseo;
    { name = "maino";
      args = [bool_adt];
      body = disj [
        Rel ("trueo", [(0, bool_adt)]);
        Rel ("falseo", [(0, bool_adt)])]}]

  let ex_true_and_false : tk_prgm = [ (* expected: no solution *)
    trueo; falseo;
    {
      name = "maino";
      args = [bool_adt];
      body = conj [
        Rel ("trueo", [(0, bool_adt)]);
        Rel ("falseo", [(0, bool_adt)])]}]

  let noto : rel = { (* expects trueo and falseo to also be rels *)
    name = "noto";
    args = [bool_adt; bool_adt];
    body = disj [
        conj [
          Rel ("falseo", [(0, bool_adt)]);
          Rel ("trueo", [(1, bool_adt)])];
        conj [
          Rel ("trueo", [(0, bool_adt)]);
          Rel ("falseo", [(1, bool_adt)])]]}

  let sameo : rel = { (* expects trueo and falseo to also be rels *)
    name = "sameo";
    args = [bool_adt; bool_adt];
    body = disj [
        conj [
          Rel ("trueo", [(0, bool_adt)]);
          Rel ("trueo", [(1, bool_adt)])];
        conj [
          Rel ("falseo", [(0, bool_adt)]);
          Rel ("falseo", [(1, bool_adt)])]]}

  let ex_pair : tk_prgm = [
    { name = "maino";
      args = [Prod (bool_adt, bool_adt)];
      body = Fresh (bool_adt,
        Pairo (
          (1, Prod (bool_adt, bool_adt)),
          (0, bool_adt),
          (0, bool_adt)))}]

  let ex_no_vars_succeed : tk_prgm = [ (* expected: 1 *)
    { name = "maino";
      args = [];
      body = Succeed}]

  let ex_contra_recursion : tk_prgm = [ (* not sure what this should return, depends on how init rels *)
    trueo; falseo; noto;
    { name = "maino";
      args = [bool_adt];
      body = Fresh (bool_adt,
        Conj (
          Rel ("maino", [(0, bool_adt)]),
          Rel ("noto", [(0, bool_adt); (1, bool_adt)])))}]

  let ex_var_has_val_zero : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_has_val (0, nat_adt 3) (nat_adv 3 0) }]

  let ex_var_has_val_one : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_has_val (0, nat_adt 3) (nat_adv 3 1) }]

  let ex_var_has_val_two : tk_prgm = [
    { name = "maino";
      args = [nat_adt 3];
      body = var_has_val (0, nat_adt 3) (nat_adv 3 2) }]

  let ex_small_transitive_closure : tk_prgm = [ 
    { name = "grapho";
      args = [nat_adt 3; nat_adt 3];
      body =
        Disj (
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 0),
            var_has_val (1, nat_adt 3) (nat_adv 3 1)),
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 1),
            var_has_val (1, nat_adt 3) (nat_adv 3 2))) };
    { name = "connecto";
      args = [nat_adt 3; nat_adt 3];
      body = 
        Disj (
          Rel ("grapho", [(0, nat_adt 3); (1, nat_adt 3)]),
          Fresh (nat_adt 3,
            Conj (
              Rel ("connecto", [(1, nat_adt 3); (0, nat_adt 3)]),
              Rel ("connecto", [(0, nat_adt 3); (2, nat_adt 3)]))))};
    { name = "maino";
      args = [nat_adt 3; nat_adt 3];
      body = Rel ("connecto", [(0, nat_adt 3); (1, nat_adt 3)])}]

  let ex_small_transitive_closure_loop : tk_prgm = [ 
    { name = "grapho";
      args = [nat_adt 3; nat_adt 3];
      body =
        disj [
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 0),
            var_has_val (1, nat_adt 3) (nat_adv 3 1));
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 1),
            var_has_val (1, nat_adt 3) (nat_adv 3 2));
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 2),
            var_has_val (1, nat_adt 3) (nat_adv 3 0))]};
    { name = "connecto";
      args = [nat_adt 3; nat_adt 3];
      body = 
        Disj (
          Rel ("grapho", [(0, nat_adt 3); (1, nat_adt 3)]),
          Fresh (nat_adt 3,
            Conj (
              Rel ("connecto", [(1, nat_adt 3); (0, nat_adt 3)]),
              Rel ("connecto", [(0, nat_adt 3); (2, nat_adt 3)]))))};
    { name = "maino";
      args = [nat_adt 3; nat_adt 3];
      body = Rel ("connecto", [(0, nat_adt 3); (1, nat_adt 3)])}]

  let ex_small_transitive_closure_loop_fail : tk_prgm = [ 
    { name = "grapho";
      args = [nat_adt 3; nat_adt 3];
      body =
        disj [
          (* 0 and 1 have a loop, 1 is connected to 2 *)
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 0),
            var_has_val (1, nat_adt 3) (nat_adv 3 1));
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 1),
            var_has_val (1, nat_adt 3) (nat_adv 3 0));
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 1),
            var_has_val (1, nat_adt 3) (nat_adv 3 2))]};
    { name = "connecto";
      args = [nat_adt 3; nat_adt 3];
      body = 
        Disj (
          Rel ("grapho", [(0, nat_adt 3); (1, nat_adt 3)]),
          Fresh (nat_adt 3,
            Conj (
              Rel ("connecto", [(1, nat_adt 3); (0, nat_adt 3)]),
              Rel ("connecto", [(0, nat_adt 3); (2, nat_adt 3)]))))};
    { name = "maino";
      args = [nat_adt 3; nat_adt 3];
      body =
        (* test if 2 is connected to 0, should fail *)
        Conj (
          Rel ("connecto", [(0, nat_adt 3); (1, nat_adt 3)]),
          Conj (
            var_has_val (0, nat_adt 3) (nat_adv 3 2),
            var_has_val (1, nat_adt 3) (nat_adv 3 0)))}]

  let ex_sudoku : tk_prgm = [
    { name = "valid_4x4";
      args = [nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4];
      body =
        conj [
          Neqo ((0, nat_adt 4), (1, nat_adt 4));
          Neqo ((0, nat_adt 4), (2, nat_adt 4));
          Neqo ((0, nat_adt 4), (3, nat_adt 4));
          Neqo ((1, nat_adt 4), (2, nat_adt 4));
          Neqo ((1, nat_adt 4), (3, nat_adt 4));
          Neqo ((2, nat_adt 4), (3, nat_adt 4))
        ]};
    { name = "sudoku_4x4";
      args = [
        nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; 
        nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4
      ];
      body =
        conj [
          Rel ("valid_4x4", [(0, nat_adt 4); (1, nat_adt 4); (2, nat_adt 4); (3, nat_adt 4)]);
          Rel ("valid_4x4", [(0, nat_adt 4); (1, nat_adt 4); (4, nat_adt 4); (5, nat_adt 4)]);
          Rel ("valid_4x4", [(0, nat_adt 4); (4, nat_adt 4); (8, nat_adt 4); (12, nat_adt 4)]);
          Rel ("valid_4x4", [(8, nat_adt 4); (9, nat_adt 4); (12, nat_adt 4); (13, nat_adt 4)]);
          Rel ("valid_4x4", [(8, nat_adt 4); (9, nat_adt 4); (10, nat_adt 4); (11, nat_adt 4)]);
          Rel ("valid_4x4", [(10, nat_adt 4); (11, nat_adt 4); (14, nat_adt 4); (15, nat_adt 4)]);
          Rel ("valid_4x4", [(12, nat_adt 4); (13, nat_adt 4); (14, nat_adt 4); (15, nat_adt 4)]);
          Rel ("valid_4x4", [(1, nat_adt 4); (5, nat_adt 4); (9, nat_adt 4); (13, nat_adt 4)]);
          Rel ("valid_4x4", [(4, nat_adt 4); (5, nat_adt 4); (6, nat_adt 4); (7, nat_adt 4)]);
          Rel ("valid_4x4", [(2, nat_adt 4); (3, nat_adt 4); (6, nat_adt 4); (7, nat_adt 4)]);
          Rel ("valid_4x4", [(3, nat_adt 4); (7, nat_adt 4); (11, nat_adt 4); (15, nat_adt 4)]);
          Rel ("valid_4x4", [(2, nat_adt 4); (6, nat_adt 4); (10, nat_adt 4); (14, nat_adt 4)])]};
    { name = "maino";
      args = [
        nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; 
        nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4; nat_adt 4
      ];
      body =
        conj [
          var_has_val (0, nat_adt 4) (nat_adv 4 3);
          var_has_val (2, nat_adt 4) (nat_adv 4 0);
          var_has_val (13, nat_adt 4) (nat_adv 4 0);
          var_has_val (15, nat_adt 4) (nat_adv 4 2);
          Rel ("sudoku_4x4",
            [(0, nat_adt 4); (1, nat_adt 4); (2, nat_adt 4); (3, nat_adt 4); 
              (4, nat_adt 4); (5, nat_adt 4); (6, nat_adt 4); (7, nat_adt 4); 
              (8, nat_adt 4); (9, nat_adt 4); (10, nat_adt 4); (11, nat_adt 4); 
              (12, nat_adt 4); (13, nat_adt 4); (14, nat_adt 4); (15, nat_adt 4)])]}]
   (* (sudoku_4x4 3 b 0 d e f g h i j k l m 0 o 2))) *)

  let test_examples () =
    let etpm = sat_eval_tk_prgm_maino in

    print_endline "ex_basic";
    assert ((etpm ex_basic 5) = Some [Left Sole]);

    print_endline "ex_trueo";
    assert ((etpm ex_trueo 5) = Some [Left Sole]);

    print_endline "ex_true_or_false";
    assert ((etpm ex_true_or_false 5) = Some [Right Sole]);

    print_endline "ex_true_and_false";
    assert ((etpm ex_true_and_false 5) = None);

    print_endline "ex_pair";
    assert ((etpm ex_pair 5) = Some [Pair (Left Sole, Left Sole)]);

    print_endline "ex_no_vars_succeed";
    assert ((etpm ex_no_vars_succeed 5) = Some []);

    print_endline "ex_contra_recursion";
    assert ((etpm ex_contra_recursion 5) = None);

    print_endline "ex_var_has_val_zero";
    assert (
      (etpm ex_var_has_val_zero 5)
      =
      Some [Pair (Left Sole, Left Sole)]);

    print_endline "ex_var_has_val_one";
    assert (
      (etpm ex_var_has_val_one 5)
      =
      Some [Pair (Right Sole, Left Sole)]);

    print_endline "ex_var_has_val_two";
    assert (
      (etpm ex_var_has_val_two 5)
      =
      Some [Pair (Right Sole, Right Sole)]);

    print_endline "ex_small_transitive_closure";
    assert (
      (etpm ex_small_transitive_closure 5)
      =
      Some [Pair (Left Sole, Left Sole); Pair (Right Sole, Right Sole)]);

    print_endline "ex_small_transitive_closure_loop";
    assert (
      (etpm ex_small_transitive_closure_loop 5)
      =
      Some [Pair (Right Sole, Right Sole); Pair (Right Sole, Left Sole)]);

    print_endline "ex_small_transitive_closure_loop_fail";
    assert ((etpm ex_small_transitive_closure_loop_fail 5) = None);

    print_endline "ex_sudoku";
    assert (
      (etpm ex_sudoku 5)
      =
      Some
       [Pair (Right Sole, Pair (Right Sole, Right Sole));
        Pair (Right Sole, Pair (Right Sole, Left Sole));
        Pair (Left Sole, Pair (Left Sole, Left Sole));
        Pair (Right Sole, Pair (Left Sole, Left Sole));
        Pair (Left Sole, Pair (Left Sole, Left Sole));
        Pair (Right Sole, Pair (Left Sole, Left Sole));
        Pair (Right Sole, Pair (Right Sole, Left Sole));
        Pair (Right Sole, Pair (Right Sole, Right Sole));
        Pair (Right Sole, Pair (Right Sole, Left Sole));
        Pair (Right Sole, Pair (Right Sole, Right Sole));
        Pair (Right Sole, Pair (Left Sole, Left Sole));
        Pair (Left Sole, Pair (Left Sole, Left Sole));
        Pair (Right Sole, Pair (Left Sole, Left Sole));
        Pair (Left Sole, Pair (Left Sole, Left Sole));
        Pair (Right Sole, Pair (Right Sole, Right Sole));
        Pair (Right Sole, Pair (Right Sole, Left Sole))]);

    ()

end
