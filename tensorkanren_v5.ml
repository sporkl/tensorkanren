
#require "owl-top"

open Owl

(* CORE TYPES *)

type adt =
  | Unit
  | Sum of adt * adt
  | Prod of adt * adt

type adv = (* used as output values, but not in the language itself *)
  | Sole
  | Left of adv
  | Right of adv
  | Pair of adv * adv

type var = int * adt

type tk =
  | Succeed
  | Fail
  | Conj of tk * tk
  | Disj of tk * tk
  | Fresh of adt * tk
  | Rel of string * (var list)
  | Soleo of var
  | Lefto of var * var (* a + b, a *)
  | Righto of var * var (* a + b, b *)
  | Pairo of var * var * var (* a * b, a, b *)

type rel = {
  name: string;
  args: adt list;
  body: tk;
}

type tk_prgm = rel list
(* programs are just lists of relations *)
(* if only want one output, just extract it from the list after eval*)

(* CONVENIENCE HELPERS *)

let rec conj (tks : tk list) : tk =
  match tks with
  | [] -> Succeed
  | a :: d -> Conj (a, (conj d))

let rec disj (tks : tk list) : tk =
  match tks with
  | [] -> Fail
  | a :: d -> Disj (a, (disj d))

(* TODO: helper for equality by destructing the adt? *)

(* EXAMPLE ADVs *)

let bool_adt = Sum (Unit, Unit)
let true_adv = Left Sole
let false_adv = Right Sole

let ex_adv_adt = [
  true_adv, bool_adt;
  false_adv, bool_adt;
  (Pair (true_adv, true_adv)), (Prod (bool_adt, bool_adt));
  (Pair (false_adv, true_adv)), (Prod (bool_adt, bool_adt));
  (Pair (true_adv, false_adv)), (Prod (bool_adt, bool_adt));
  (Pair (false_adv, false_adv)), (Prod (bool_adt, bool_adt));
  (Left true_adv), (Sum (bool_adt, bool_adt));
  (Left false_adv), (Sum (bool_adt, bool_adt));
  (Right true_adv), (Sum (bool_adt, bool_adt));
  (Right false_adv), (Sum (bool_adt, bool_adt));
  (Left Sole), (Sum (Unit, Unit));
  (Right Sole), (Sum (Unit, Unit));
  (Pair (Sole, Sole)), (Prod (Unit, Unit))]

(* EXAMPLE PROGRAMS *)

let ex_basic = [ (* expected: Left Sole *)
  { name = "maino";
    args = [Sum (Unit, Unit)];
    body =
      Fresh (Unit,
             conj [
               Lefto ((1, Sum (Unit, Unit)), (0, Unit));
               Soleo (0, Unit)])}]

let trueo = {
  name = "trueo";
  args = [bool_adt];
  body =
    Fresh (Unit,
           conj [
             Lefto ((1, Sum (Unit, Unit)), (0, Unit));
             Soleo (0, Unit)])}

let falseo = {
  name = "falseo";
  args = [bool_adt];
  body =
    Fresh (Unit,
           conj [
             Righto ((1, Sum (Unit, Unit)), (0, Unit));
             Soleo (0, Unit)])}

let ex_trueo = [ (* expected: true_adv *)
  trueo;
  { name = "maino";
    args = [bool_adt];
    body = Rel ("trueo", [(0, bool_adt)])}]

let ex_true_or_false = [ (* expected: true_adv and false_adv *)
  trueo; falseo;
  { name = "maino";
    args = [bool_adt];
    body = disj [
      Rel ("trueo", [(0, bool_adt)]);
      Rel ("falseo", [(0, bool_adt)])]}]

let ex_true_and_false = [ (* expected: no solution *)
  trueo; falseo;
  {
    name = "maino";
    args = [bool_adt];
    body = conj [
      Rel ("trueo", [(0, bool_adt)]);
      Rel ("falseo", [(0, bool_adt)])]}]

let noto = { (* expects trueo and falseo to also be rels *)
  name = "noto";
  args = [bool_adt; bool_adt];
  body = disj [
      conj [
        Rel ("falseo", [(0, bool_adt)]);
        Rel ("trueo", [(1, bool_adt)])];
      conj [
        Rel ("trueo", [(0, bool_adt)]);
        Rel ("falseo", [(1, bool_adt)])]]}

let sameo = { (* expects trueo and falseo to also be rels *)
  name = "sameo";
  args = [bool_adt; bool_adt];
  body = disj [
      conj [
        Rel ("trueo", [(0, bool_adt)]);
        Rel ("trueo", [(1, bool_adt)])];
      conj [
        Rel ("falseo", [(0, bool_adt)]);
        Rel ("falseo", [(1, bool_adt)])]]}

let ex_noto = [ (* expected: true_adv *)
  trueo; falseo; noto;
  { name = "maino";
    args = [bool_adt];
    body =
      Fresh (bool_adt,
             conj [
               Rel ("falseo", [(0, bool_adt)]);
               Rel ("noto", [(0, bool_adt); (1, bool_adt)])])}]

let ex_noto_rev = [ (* expected: true_adv *)
  trueo; falseo; noto;
  { name = "maino";
    args = [bool_adt];
    body =
      Fresh (bool_adt,
             conj [
               Rel ("falseo", [(0, bool_adt)]);
               Rel ("noto", [(1, bool_adt); (0, bool_adt)])])}]

let xoro = { (* expects trueo, falseo, noto, sameo to be rels *)
  name = "xoro";
  args = [bool_adt; bool_adt; bool_adt];
  body = disj [
    conj [
      Rel ("noto", [(0, bool_adt); (1, bool_adt)]);
      Rel ("trueo", [(2, bool_adt)])];
    conj [
      Rel ("sameo", [(0, bool_adt); (1, bool_adt)]);
      Rel ("falseo", [(2, bool_adt)])]]}

let ex_xoro = [ (* expected: true_adv *)
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

let ex_xoro_rev = [ (* expected: true_adv *)
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

let ex_noto_pair = [ (* expected: Pair (true_adv, false_adv) and Pair (false_adv, true_adv) *)
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

let ex_pair = [
  { name = "maino";
    args = [Prod (bool_adt, bool_adt)];
    body = Fresh (bool_adt,
      Pairo (
        (1, Prod (bool_adt, bool_adt)),
        (0, bool_adt),
        (0, bool_adt)))}]

let succeedo = {
  name = "succeedo";
  args = [];
  body = Succeed }

let failo = {
  name = "failo";
  args = [];
  body = Fail }

let ex_succeedo = [
  succeedo;
  { name = "maino";
    args = [Prod (bool_adt, bool_adt)];
    body = Rel ("succeedo", [])}]

let ex_no_vars_succeed = [ (* expected: 1 *)
  succeedo;
  { name = "maino";
    args = [];
    body = Rel ("succeedo", [])}]

let ex_no_vars_fail = [ (* expected: 0 *)
  failo;
  { name = "maino";
    args = [];
    body = Rel ("failo", [])}]

let ex_multi_vars = [ (* expected: 2 x 2 identity matrix *)
  trueo; falseo; sameo;
  { name = "maino";
    args = [bool_adt; bool_adt];
    body = Rel ("sameo", [(0, bool_adt); (1, bool_adt)])}]

let ex_contra_recursion = [ (* not sure what this should return, depends on how init rels *)
  trueo; falseo; noto; sameo; xoro;
  { name = "maino";
    args = [bool_adt];
    body = Fresh (bool_adt,
      Conj (
        Rel ("maino", [(0, bool_adt)]),
        Rel ("noto", [(0, bool_adt); (1, bool_adt)])))}]

(* sum type corresponding to nats with n as the max value *)
let rec nat_adt n =
  match n with
  | 0 -> Unit
  | m -> Sum (Unit, nat_adt (m - 1))

(* construct value of nat n corresponding to nat_adt s *)
let rec nat_adv n s =
  if n = 0 then
    if s = 0 then
      Sole (* built up enough successors already *)
    else
      Left Sole
  else
    Right (nat_adv (n - 1) (s - 1))

(* generate code enforcing value of nat_adt var *)
(* todo: rewrite to calculate "s" from type? *)
let rec nat_var_has_value (v : var) (n : int) (s : int) =
  let (x, t) = v in
  if n = 0 then
    if s = 0 then
      Soleo v
    else
      Fresh (
        Unit,
        Lefto ((x + 1, t), (0, Unit)))
  else
    Fresh (
      nat_adt (s - 1),
      Conj (
        Righto ((x + 1, t), (0, nat_adt (s - 1))),
        nat_var_has_value (0, nat_adt (s - 1)) (n - 1) (s - 1)))

let ex_var_has_value_zero = [
  { name = "maino";
    args = [nat_adt 2];
    body = nat_var_has_value (0, nat_adt 2) 0 2 }]

let ex_var_has_value_one = [
  { name = "maino";
    args = [nat_adt 2];
    body = nat_var_has_value (0, nat_adt 2) 1 2 }]

let ex_var_has_value_two = [
  { name = "maino";
    args = [nat_adt 2];
    body = nat_var_has_value (0, nat_adt 2) 2 2 }]

let ex_small_transitive_closure = [ 
  { name = "grapho";
    args = [nat_adt 2; nat_adt 2];
    body =
      Disj (
        Conj (
          nat_var_has_value (0, nat_adt 2) 0 2,
          nat_var_has_value (1, nat_adt 2) 1 2),
        Conj (
          nat_var_has_value (0, nat_adt 2) 1 2,
          nat_var_has_value (1, nat_adt 2) 2 2)) };
  { name = "connecto";
    args = [nat_adt 2; nat_adt 2];
    body = 
      Disj (
        Rel ("grapho", [(0, nat_adt 2); (1, nat_adt 2)]),
        Fresh (nat_adt 2,
          Conj (
            Rel ("connecto", [(1, nat_adt 2); (0, nat_adt 2)]),
            Rel ("connecto", [(0, nat_adt 2); (2, nat_adt 2)]))))};
  { name = "maino";
    args = [nat_adt 2; nat_adt 2];
    body = Rel ("connecto", [(0, nat_adt 2); (1, nat_adt 2)])}]

let ex_potential_infinite_loop = [
  { name = "maino";
    args = [];
    body = Disj (Succeed, Rel ("maino", [])) }]

let ex_small_transitive_closure_loop = [ 
  { name = "grapho";
    args = [nat_adt 2; nat_adt 2];
    body =
      disj [
        Conj (
          nat_var_has_value (0, nat_adt 2) 0 2,
          nat_var_has_value (1, nat_adt 2) 1 2);
        Conj (
          nat_var_has_value (0, nat_adt 2) 1 2,
          nat_var_has_value (1, nat_adt 2) 2 2);
        Conj (
          nat_var_has_value (0, nat_adt 2) 2 2,
          nat_var_has_value (1, nat_adt 2) 0 2)]};
  { name = "connecto";
    args = [nat_adt 2; nat_adt 2];
    body = 
      Disj (
        Rel ("grapho", [(0, nat_adt 2); (1, nat_adt 2)]),
        Fresh (nat_adt 2,
          Conj (
            Rel ("connecto", [(1, nat_adt 2); (0, nat_adt 2)]),
            Rel ("connecto", [(0, nat_adt 2); (2, nat_adt 2)]))))};
  { name = "maino";
    args = [nat_adt 2; nat_adt 2];
    body = Rel ("connecto", [(0, nat_adt 2); (1, nat_adt 2)])}]

(* COMPILING ADTs *)

(* want to compile to a vector representation, so that multiple can be compiled as a tensor *)

(* Unit -> 1 (or [1]) *)
(* Sum (Unit, Unit) -> [1 0] | [0 1]; corresponds to Kronecker sum? [1] (+) [1] = [1 1] *)
(* Pair (Sole, Sole) -> [1]; corresponds to Kronecker product? [1] (x) [1] = [1] *)
(* not worrying about optimization for now *)

(* every ADT can be represented as a one-hot vector *)

(* like kronecker product, but tensor-shaped *)
let tensor_prod (a : Arr.arr) (b : Arr.arr) : Arr.arr =
  let ab_good_rank =
    Arr.expand b ((Arr.num_dims a) + (Arr.num_dims b))
  in
  let ab_good_shape =
    Arr.repeat
      ab_good_rank
      Array.(append (Arr.shape a) (init (Arr.num_dims b) (fun _ -> 1)))
  in
  let a_good_rank =
    Arr.expand ~hi:true a ((Arr.num_dims a) + (Arr.num_dims b))
  in
  Arr.mul a_good_rank ab_good_shape

let vec_kron_prod a b = Arr.flatten @@ tensor_prod a b

let vec_kron_sum = Arr.concat_horizontal

let rec adt_size (t : adt) : int =
  match t with
  | Unit -> 1
  | Sum (x, y) -> (adt_size x) + (adt_size y)
  | Prod (x, y) -> (adt_size x) * (adt_size y)

let rec compile_adv (v : adv) (t : adt) : Arr.arr =
  match v, t with
  | Sole, Unit -> Arr.ones [|1|]
  | Left x, Sum (xt, yt) -> vec_kron_sum (compile_adv x xt) (Arr.zeros [|adt_size yt|])
  | Right y, Sum (xt, yt) -> vec_kron_sum (Arr.zeros [|adt_size xt|]) (compile_adv y yt)
  | Pair (x, y), Prod (xt, yt) -> vec_kron_prod (compile_adv x xt) (compile_adv y yt)
  | _ -> invalid_arg "Type does not match value!"

let ex_compile_adv =
  List.map
    (fun (v, t) -> compile_adv v t)
    ex_adv_adt

let true_vec = compile_adv true_adv bool_adt
let false_vec = compile_adv false_adv bool_adt

let find_vec_index f vec =
  let exception Return of int in
  try
    Arr.iteri
      (fun i n -> if n = f then raise (Return i) else ())
      vec;
    None
  with
  | Return i -> Some i

let vec_size v = (Arr.shape v).(0)
    
(* assumes input is a valid one-hot vector *)
let rec decompile_adv (vec : Mat.mat) (t : adt) : adv =
  if (adt_size t) <> (vec_size vec) then
    invalid_arg "Type does not match vector!"
  else
    match t with
    | Unit ->
        if vec = (Arr.ones [|1|]) then
          Sole
        else
          invalid_arg "Type does not match vector!"
    | Sum (xt, yt) ->
        if (vec_size vec) = (adt_size t) then
          let x = Arr.get_slice [[0; (adt_size xt) - 1]] vec in
          let y = Arr.get_slice [[(adt_size xt); (adt_size xt) + (adt_size yt) - 1]] vec in
          if (Arr.exists (fun f -> f = 1.0) x) then
            Left (decompile_adv x xt)
          else if (Arr.exists (fun f -> f = 1.0) y) then
            Right (decompile_adv y yt)
          else
            invalid_arg "Invalid input vector!"
        else
          invalid_arg "Type does not match vector!"
    | Prod (xt, yt) ->
        match find_vec_index 1.0 vec with
        | None -> invalid_arg "Invalid input vector!"
        | Some n ->
            let y_index = n mod (adt_size yt) in
            let x_index = (n - y_index) / (adt_size yt) in
            Pair (
              decompile_adv (Arr.unit_basis (adt_size xt) x_index) xt,
              decompile_adv (Arr.unit_basis (adt_size yt) y_index) yt)

let compile_adv_isomorphic (v : adv) (t : adt) : adv =
  decompile_adv (compile_adv v t) t

let ex_compile_adv_isomorphic =
  List.map
    (fun (v, t) -> compile_adv_isomorphic v t)
    ex_adv_adt

(* COMPILING TO TENSOR OPS *)

type comp_rel = {
  name: string;
  args: adt list;
  body: Mat.mat;
}

let var_size v =
  let (_, t) = v in adt_size t

let env_size env = 
  let var_sizes = List.map adt_size env in
  List.fold_left (+) 0 var_sizes

let shape_of_env env = Array.of_list @@ List.map adt_size env

let var_possible_states (v : var) : Mat.mat list =
  let s = var_size v in
  List.init s (Arr.unit_basis s)

let gen_single_unify
  (target_state : Arr.arr) (ab : var) (a : var) (env : adt list) (wrap : Arr.arr -> Arr.arr)
  : Arr.arr = 
  List.fold_right
    (fun v env_tensor ->
      let v_tensor =
        if v = ab then
          wrap target_state
        else if v = a then
          target_state
        else
          Arr.ones [|var_size v|]
      in
      tensor_prod v_tensor env_tensor)
    (List.mapi (fun i a -> (i, a)) env) (* bundle with index to treat as var *)
    (Arr.ones [||])

(* wrap should take a vector with same type as a, and convert it to fit ab *)
let gen_unify (ab : var) (a : var) (env : adt list) (wrap : Arr.arr -> Arr.arr) : Arr.arr =
  List.fold_left (* sum over possible equalities *)
    (fun peq_sum peq ->
      let peq_env_tensor = gen_single_unify peq ab a env wrap in
      Arr.max2 peq_env_tensor peq_sum)
    (Arr.zeros (shape_of_env env))
    (var_possible_states a)

(* environment assumed tensor where each dimension corresponds to a variable *)
(* operations should return a tensor representation of the given environment *)
(* new vars get added to front of environment *)

let rec eval_tk (exp : tk) (env : adt list) (rels : comp_rel list) : Arr.arr =
  match exp with
  | Succeed ->
      (* all-one tensor w/ env shape *)
      Arr.ones (shape_of_env env)
  | Fail ->
      (* all-zero tensor w/ env shape *)
      Arr.zeros (shape_of_env env);
  | Conj (e1, e2) ->
      (* element-wise multiplication *)
      Arr.mul (eval_tk e1 env rels) (eval_tk e2 env rels)
  | Disj (e1, e2) ->
      (* element-wise addition *)
      Arr.max2 (eval_tk e1 env rels) (eval_tk e2 env rels)
  | Fresh (vt, body) -> 
      (* evaluate body with new variable in environment *)
      let body_res = eval_tk body (vt :: env) rels in
      (* sum over the variable (designed to be axis 0) *)
      Arr.max ~keep_dims:false ~axis:0 body_res
  | Rel (name, args) ->
      let rel = List.find (fun r -> r.name = name) rels in
      let nargs = List.length rel.args in
      let args_and_env = rel.args @ env in
      let unify_arg_tensors = 
        List.mapi
          (fun i a ->
            let (ai, at) = a in
            gen_unify (* unify *)
              (i, at) (* rel variable at index *)
              (ai + nargs, at) (* with argument variable w/ corrected index *)
              args_and_env
              Fun.id)
          args (* (int * adt) list *)
      in
      let unified_args_env = (* conj the unifications for each arg and rel result *)
        List.fold_left
          Arr.mul
          (tensor_prod rel.body (Arr.ones (shape_of_env env)))
          unify_arg_tensors
      in
      List.fold_left (* sum over the rel args *)
        (fun res_tensor _ -> Arr.max ~keep_dims:false ~axis:0 res_tensor)
        unified_args_env
        args
  | Soleo (n, t) ->
      (* same as succeed, b/c guaranteed by "typechecking"*)
      Arr.ones (shape_of_env env)
  | Lefto (ab, a) ->
      (* check that left side matches *)
      let (_, Sum (_at, bt)) = ab in
      gen_unify ab a env
        (fun va -> vec_kron_sum va (Arr.zeros [|adt_size bt|]))
  | Righto (ab, b) ->
      (* check that right side matches *)
      let (_, Sum (at, _bt)) = ab in
      gen_unify ab b env
        (fun vb -> vec_kron_sum (Arr.zeros [|adt_size at|]) vb)
  | Pairo (ab, a, b) ->
      (* check that a and b match *)
      let (_, Prod (at, bt)) = ab in
      let a_check =
        gen_unify ab a env (fun va -> vec_kron_prod va (Arr.ones [|adt_size bt|]))
      in
      let b_check =
        gen_unify ab b env (fun vb -> vec_kron_prod (Arr.ones [|adt_size at|]) vb)
      in
      Arr.mul a_check b_check

let eval_rel (r : rel) (rels : comp_rel list) : Arr.arr =
  eval_tk r.body r.args rels

let compile_rel (r : rel) (rels : comp_rel list) : comp_rel =
  { name = r.name;
    args = r.args;
    body = eval_rel r rels }

let rec eval_tk_prgm_help (prgm : rel list) (prev_comp : comp_rel list) =
  let comp = List.map (fun r -> compile_rel r prev_comp) prgm in
  print_endline "----------------------------";
  List.iter (fun r -> print_endline r.name; Arr.print r.body) comp;
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
          body = Arr.zeros (shape_of_env r.args)})
      prgm
  in
  eval_tk_prgm_help prgm init_comp_rels

let eval_tk_prgm_maino (prgm : rel list) : comp_rel =
  List.find (fun r -> r.name = "maino") (eval_tk_prgm prgm)



