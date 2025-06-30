#require "owl-top"
open Owl

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
    | Prod (x, y) -> Prod (x, y)

  let compile_var (v, vt) : var = (v, compile_adt vt)

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
    | Rel (name, args) -> Rel (name, List.map compile_var args)
    | Eqo (a, b) -> Eqo (compile_var a, compile_var b)
    | Neqo (a, b) -> Neqo (compile_var a, compile_var b)
    | Soleo (v, vt) -> Soleo (v, compile_adt vt)
    | Lefto ((ab, Sum (Unit, Unit)), (a, Unit)) -> (* a + b, a *)
        Lefto ((ab, Sum (Unit, Unit)), (a, Unit))
    | Lefto ((ab, abt), (a, at)) -> (* a + b, a *)
        let abtc = compile_adt abt in
        let Prod (_, vt) = abtc in (* get the compiled child type *)
        Fresh (bool_adt,
          Conj (
            Pairo ((ab + 1, abtc), (0, bool_adt), (a + 1, vt)),
            trueo (0, bool_adt)))
    | Righto ((ab, Sum (Unit, Unit)), (b, Unit)) -> (* a + b, b *)
        Righto ((ab, Sum (Unit, Unit)), (b, Unit))
    | Righto ((ab, abt), (b, bt)) -> (* a + b, b *)
        let abtc = compile_adt abt in
        let Prod (_, vt) = abtc in (* get the compiled child type *)
        Fresh (bool_adt,
          Conj (
            Pairo ((ab + 1, abtc), (0, bool_adt), (b + 1, vt)),
            falseo (0, bool_adt)))
    | Pairo (ab, a, b) -> (* a * b, a, b *)
        Pairo (compile_var ab, compile_var a, compile_var b)
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

  val sum : ?axis:int -> ?keep_dims:bool -> arr -> arr
  val add : arr -> arr -> arr
  val mul : arr -> arr -> arr
  val smul : elt -> arr -> arr

  val print : arr -> unit
end

let init_nd_or_scalar shp f =
  if shp = [||] then
    Arr.create [||] (f [|0|])
  else
    Arr.init_nd shp f

(* TensorSemiring with standard + and * *)
module AddMulTensorSemiring : TensorSemiring
  with type elt = float
  with type arr = Arr.arr
= struct

  type elt = float
  type arr = Arr.arr

  let zero = 0.0
  let one = 1.0

  let init = init_nd_or_scalar
  let shape = Arr.shape
  let reshape = Arr.reshape
  let concat_horizontal = Arr.concat_horizontal

  let sum = Arr.sum
  let add = Arr.add
  let mul = Arr.mul
  let smul = Arr.scalar_mul

  let print x = Arr.print x

end

(* TensorSemiring with max and add (max tropical semiring) *)
module MaxAddTensorSemiring : TensorSemiring
  with type elt = float
  with type arr = Arr.arr
= struct

  type elt = float
  type arr = Arr.arr

  let zero = Float.neg_infinity
  let one = 0.0
  
  let init = init_nd_or_scalar
  let shape = Arr.shape
  let reshape = Arr.reshape
  let concat_horizontal = Arr.concat_horizontal

  let sum = Arr.max
  let add = Arr.max2
  let mul = Arr.add
  let smul = Arr.scalar_add

  let print x = Arr.print x

end

(* TensorSemiring with max and min (max min/fuzzy semiring) *)
module MaxMinTensorSemiring : TensorSemiring
  with type elt = float
  with type arr = Arr.arr
= struct
  type elt = float
  type arr = Arr.arr

  let zero = Float.neg_infinity
  let one = Float.infinity

  let init = init_nd_or_scalar
  let shape = Arr.shape
  let reshape = Arr.reshape
  let concat_horizontal = Arr.concat_horizontal

  let sum = Arr.max
  let add = Arr.max2
  let mul = Arr.min2
  let smul e a = Arr.(min2 (create (shape a) e) a)

  let print x = Arr.print x
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
        TS.sum ~keep_dims:false ~axis:0 body_res
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
          (fun res_tensor _ -> TS.sum ~keep_dims:false ~axis:0 res_tensor)
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

  (* run tests *)

  let test_examples () =
    let etpm = eval_tk_prgm_maino in
    let one = MaxAddTensorSemiring.one in
    let zero = MaxAddTensorSemiring.zero in
    let init = MaxAddTensorSemiring.init in
    
    print_endline "ex_basic";
    assert ((etpm ex_basic).body = (Arr.of_array [|one; zero|] [|2|]));

    print_endline "ex_trueo";
    assert ((etpm ex_trueo).body = (Arr.of_array [|one; zero|] [|2|]));

    print_endline "ex_true_or_false";
    assert ((etpm ex_true_or_false).body = (Arr.of_array [|one; one|] [|2|]));

    print_endline "ex_true_and_false";
    assert ((etpm ex_true_and_false).body = (Arr.of_array [|zero; zero|] [|2|]));

    print_endline "ex_noto";
    assert ((etpm ex_noto).body = (Arr.of_array [|one; zero|] [|2|]));

    print_endline "ex_noto_rev";
    assert ((etpm ex_noto_rev).body = (Arr.of_array [|one; zero|] [|2|]));

    print_endline "ex_xoro";
    assert ((etpm ex_xoro).body = (Arr.of_array [|one; zero|] [|2|]));

    print_endline "ex_xoro_rev";
    assert ((etpm ex_xoro_rev).body = (Arr.of_array [|one; zero|] [|2|]));

    print_endline "ex_noto_pair";
    assert ((etpm ex_noto_pair).body = (Arr.of_array [|zero; one; one; zero|] [|4|]));

    print_endline "ex_pair";
    assert ((etpm ex_pair).body = (Arr.of_array [|one; zero; zero; one|] [|4|]));

    print_endline "ex_succeedo";
    assert ((etpm ex_succeedo).body = (Arr.of_array [|one; one; one; one|] [|4|]));

    print_endline "ex_no_vars_succeed";
    assert ((etpm ex_no_vars_succeed).body = (init [||] (Fun.const one)));

    print_endline "ex_no_vars_fail";
    assert ((etpm ex_no_vars_fail).body = (init [||] (Fun.const zero)));

    print_endline "ex_multi_vars";
    assert ((etpm ex_multi_vars).body = (Arr.of_arrays [|[|one; zero|]; [|zero; one|]|]));

    print_endline "ex_contra_recursion";
    assert ((etpm ex_contra_recursion).body = (Arr.of_array [|zero; zero|] [|2|]));

    print_endline "ex_var_has_val_zero";
    assert ((etpm ex_var_has_val_zero).body = (Arr.of_array [|one; zero; zero|] [|3|]));
    
    print_endline "ex_var_has_val_one";
    assert ((etpm ex_var_has_val_one).body = (Arr.of_array [|zero; one; zero|] [|3|]));

    print_endline "ex_var_has_val_two";
    assert ((etpm ex_var_has_val_two).body = (Arr.of_array [|zero; zero; one|] [|3|]));

    print_endline "ex_small_transitive_closure";
    assert (
      (etpm ex_small_transitive_closure).body =
      (Arr.of_arrays [|
        [|zero; one; one|];
        [|zero; zero; one|];
        [|zero; zero; zero|]|]));

    print_endline "ex_potential_infinite_loop";
    assert ((etpm ex_potential_infinite_loop).body = (init [||] (Fun.const one)));

    print_endline "ex_small_transitive_closure_loop";
    assert (
      (etpm ex_small_transitive_closure_loop).body =
      (Arr.of_arrays [|
        [|one; one; one|];
        [|one; one; one|];
        [|one; one; one|]|]));
        
    print_endline "ex_coin_flip";
    assert ((etpm ex_coin_flip).body = (Arr.of_array [|0.5; 0.5|] [|2|]));

    print_endline "ex_var_avoid_val_zero";
    assert ((etpm ex_var_avoids_val_zero).body = (Arr.of_array [|zero; one; one|] [|3|]));

    print_endline "ex_var_avoid_val_one";
    assert ((etpm ex_var_avoids_val_one).body = (Arr.of_array [|one; zero; one|] [|3|]));

    print_endline "ex_var_avoid_val_two";
    assert ((etpm ex_var_avoids_val_two).body = (Arr.of_array [|one; one; zero|] [|3|]));

    print_endline "ex_var_has_val_zero_comp";
    assert (
      (etpm ex_var_has_val_zero_comp).body =
        (Arr.of_array [|one; zero; zero; zero|] [|4|]));

    print_endline "ex_var_has_val_one_comp";
    assert (
      (etpm ex_var_has_val_one_comp).body =
        (Arr.of_array [|zero; zero; one; zero|] [|4|]));

    print_endline "ex_var_has_val_two_comp";
    assert (
      (etpm ex_var_has_val_two_comp).body =
        (Arr.of_array [|zero; zero; zero; one|] [|4|]));

    print_endline "ex_small_transitive_closure_comp";
    assert (
      (etpm ex_small_transitive_closure_comp).body =
        (Arr.of_arrays [|
          [|zero; zero; one; one|];
          [|zero; zero; zero; zero|];
          [|zero; zero; zero; one|];
          [|zero; zero; zero; zero|]|]));

    print_endline "ex_small_transitive_closure_loop_comp";
    assert (
      (etpm ex_small_transitive_closure_loop_comp).body =
        (Arr.of_arrays [|
          [|one; zero; one; one|];
          [|zero; zero; zero; zero|];
          [|one; zero; one; one|];
          [|one; zero; one; one|]|]));

    print_endline "ex_neqo";
    assert (
      (etpm ex_neqo).body =
        (Arr.of_arrays [|
          [|zero; one|];
          [|one; zero|]|]));

    print_endline "ex_neqo_big";
    assert (
      (etpm ex_neqo_big).body =
        (Arr.of_arrays [|
          [|zero; zero; zero; zero; one; zero; one; one|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|one; zero; zero; zero; zero; zero; one; one|];
          [|zero; zero; zero; zero; zero; zero; zero; zero|];
          [|one; zero; zero; zero; one; zero; zero; one|];
          [|one; zero; zero; zero; one; zero; one; zero|]|]));

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

    print_endline "ex_coin_flip";
    assert ((etpm ex_coin_flip).body = (Arr.of_array [|0.5; 0.5|] [|2|]));

    print_endline "ex_infinite_coin_flip";
    assert ((etpm ex_infinite_coin_flip).body = (init [||] (Fun.const one)));

    ()

end
