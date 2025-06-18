
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

type var = string * adt

type tk =
  | Succeed
  | Fail
  | Conj of tk * tk
  | Disj of tk * tk
  | Fresh of var * tk
  | Rel of string * (var list)
  | Soleo of var
  | Lefto of var * var (* a + b, a *)
  | Righto of var * var (* a + b, b *)
  | Pairo of var * var * var (* a * b, a, b *)

type rel = {
  name: string;
  args: var list;
  body: tk;
}

type tk_prgm = {
  rels: rel list;
  main: rel
}

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

let ex_basic = { (* expected: Left Sole *)
  rels = [];
  main = {
    name = "maino";
    args = [("x", Sum (Unit, Unit))];
    body =
      Fresh (("u", Unit),
             conj [
               Lefto (("x", Sum (Unit, Unit)), ("u", Unit));
               Soleo ("u", Unit)])}}

let trueo = {
  name = "trueo";
  args = [("x", bool_adt)];
  body =
    Fresh (("u", Unit),
           conj [
             Lefto (("x", Sum (Unit, Unit)), ("u", Unit));
             Soleo ("u", Unit)])}

let falseo = {
  name = "falseo";
  args = [("x", bool_adt)];
  body =
    Fresh (("u", Unit),
           conj [
             Lefto (("x", Sum (Unit, Unit)), ("u", Unit));
             Soleo ("u", Unit)])}

let ex_trueo = { (* expected: true_adv *)
  rels = [trueo];
  main = {
    name = "maino";
    args = [("x", bool_adt)];
    body = Rel ("trueo", [("x", bool_adt)])}}

let ex_true_or_false = { (* expected: true_adv and false_adv *)
  rels = [trueo; falseo];
  main = {
    name = "maino";
    args = [("x", bool_adt)];
    body = disj [
      Rel ("trueo", [("x", bool_adt)]);
      Rel ("falseo", [("x", bool_adt)])]}}

let ex_true_and_false = { (* expected: no solution *)
  rels = [trueo; falseo];
  main = {
    name = "maino";
    args = [("x", bool_adt)];
    body = disj [
      Rel ("trueo", [("x", bool_adt)]);
      Rel ("falseo", [("x", bool_adt)])]}}

let noto = { (* expects trueo and falseo to also be rels *)
  name = "noto";
  args = [("x", bool_adt); ("o", bool_adt)];
  body = disj [
      conj [
        Rel ("falseo", [("x", bool_adt)]);
        Rel ("trueo", [("o", bool_adt)])];
      conj [
        Rel ("trueo", [("x", bool_adt)]);
        Rel ("falseo", [("o", bool_adt)])]]}

let sameo = { (* expects trueo and falseo to also be rels *)
  name = "sameo";
  args = [("x", bool_adt); ("o", bool_adt)];
  body = disj [
      conj [
        Rel ("trueo", [("x", bool_adt)]);
        Rel ("trueo", [("o", bool_adt)])];
      conj [
        Rel ("falseo", [("x", bool_adt)]);
        Rel ("falseo", [("o", bool_adt)])]]}

let ex_noto = { (* expected: true_adv *)
  rels = [trueo; falseo; noto];
  main = {
    name = "maino";
    args = [("o", bool_adt)];
    body =
      Fresh (("x", bool_adt),
             conj [
               Rel ("falseo", [("x", bool_adt)]);
               Rel ("noto", [("x", bool_adt); ("o", bool_adt)])])}}

let ex_noto_rev = { (* expected: true_adv *)
  rels = [trueo; falseo; noto];
  main = {
    name = "maino";
    args = [("o", bool_adt)];
    body =
      Fresh (("x", bool_adt),
             conj [
               Rel ("falseo", [("x", bool_adt)]);
               Rel ("noto", [("o", bool_adt); ("x", bool_adt)])])}}

let xoro = { (* expects trueo, falseo, noto, sameo to be rels *)
  name = "xoro";
  args = [("x", bool_adt); ("y", bool_adt); ("o", bool_adt)];
  body = disj [
    conj [
      Rel ("noto", [("x", bool_adt); ("y", bool_adt)]);
      Rel ("trueo", [("o", bool_adt)])];
    disj [
      Rel ("sameo", [("x", bool_adt); ("y", bool_adt)]);
      Rel ("falseo", [("o", bool_adt)])]]}

let ex_xoro = { (* expected: true_adv *)
  rels = [trueo; falseo; noto; sameo; xoro];
  main = {
    name = "maino";
    args = [("o", bool_adt)];
    body = 
      Fresh (("x", bool_adt),
        Fresh (("y", bool_adt),
          conj [
            Rel ("falseo", [("x", bool_adt)]);
            Rel ("trueo", [("y", bool_adt)]);
            Rel ("xoro", [("x", bool_adt); ("y", bool_adt); ("o", bool_adt)])]))}}

let ex_xoro_rev = { (* expected: true_adv *)
  rels = [trueo; falseo; noto; sameo; xoro];
  main = {
    name = "maino";
    args = [("o", bool_adt)];
    body = 
      Fresh (("x", bool_adt),
        Fresh (("y", bool_adt),
          conj [
            Rel ("falseo", [("x", bool_adt)]);
            Rel ("trueo", [("y", bool_adt)]);
            Rel ("xoro", [("o", bool_adt); ("y", bool_adt); ("x", bool_adt)])]))}}

let ex_noto_pair = { (* expected: Pair (true_adv, false_adv) and Pair (false_adv, true_adv) *)
  rels = [trueo; falseo; noto];
  main = {
    name = "maino";
    args = [("x", Prod (bool_adt, bool_adt))];
    body = 
      Fresh (("a", bool_adt),
        Fresh (("b", bool_adt),
          conj [
            Pairo (
              ("x", Prod (bool_adt, bool_adt)),
              ("a", bool_adt),
              ("b", bool_adt));
            Rel ("noto", [("a", bool_adt); ("b", bool_adt)])]))}}

let ex_pairo = {
  rels = [];
  main = {
    name = "maino";
    args = [("aa", Prod (bool_adt, bool_adt))];
    body = Fresh (("a", bool_adt),
      Pairo (
        ("aa", Prod (bool_adt, bool_adt)),
        ("a", bool_adt),
        ("a", bool_adt)))}}

let succeedo = {
  name = "succeedo";
  args = [];
  body = Succeed}

let ex_succeedo = {
  rels = [succeedo];
  main = {
    name = "maino";
    args = [("x", Prod (bool_adt, bool_adt))];
    body = Rel ("succeedo", [])}}

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
  args: var list;
  body: Mat.mat;
}

let var_size v =
  let (_, t) = v in adt_size t

let env_size env = 
  let var_sizes = List.map var_size env in
  List.fold_left (+) 0 var_sizes

let shape_of_env env = Array.of_list @@ List.map var_size env

let var_possible_states (v : var) : Mat.mat list =
  let s = var_size v in
  List.init s (Arr.unit_basis s)

let gen_single_eq_check
  (target_state : Arr.arr) (ab : var) (a : var) (env : var list) (wrap : Arr.arr -> Arr.arr)
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
    env
    (Arr.ones [||])

(* wrap should take a vector with same type as a, and convert it to fit ab *)
let gen_eq_check (ab : var) (a : var) (env : var list) (wrap : Arr.arr -> Arr.arr) : Arr.arr =
  List.fold_left (* sum over possible equalities *)
    (fun peq_sum peq ->
      let peq_env_tensor = gen_single_eq_check peq ab a env wrap in
      Arr.add peq_env_tensor peq_sum)
    (Arr.zeros (shape_of_env env))
    (var_possible_states a)

(* environment assumed tensor where each dimension corresponds to a variable *)
(* operations should return a tensor representation of the given environment *)
(* new vars get added to front of environment *)

let rec eval_tk (exp : tk) (env : var list) (rels : comp_rel list) : Arr.arr =
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
      Arr.add (eval_tk e1 env rels) (eval_tk e2 env rels)
  | Fresh (v, body) -> 
      (* evaluate body with new variable in environment *)
      let body_res = eval_tk body (v :: env) rels in
      (* sum over the variable (designed to be axis 0) *)
      Arr.sum ~axis:0 body_res
  | Rel (name, args) ->
      (* TODO: rewrite this. needs to handle same var passed multiples times *)
      let env_tensor_with_holes = (* all-1 tensor, with 1/n tensors at positions of args *)
        List.fold_right
          (fun v acc_env_tensor ->
            if List.mem v args then
              tensor_prod
                Arr.((ones [|var_size v|]) /$ (Float.of_int @@ var_size v))
                acc_env_tensor
            else
              tensor_prod (Arr.ones [|var_size v|]) acc_env_tensor)
          env
          (Arr.ones [||])
      in
      (* add rel result to front *)
      let rel_pairs = List.map (fun r -> (r.name, r.body)) rels in
      let rel_prod_env =
        tensor_prod (List.assoc name rel_pairs) env_tensor_with_holes in
      let args_len = List.length args in
      let swapped_holes_env = (* swap rel result with correct vars *)
        List.fold_left
          (fun acc_env v ->
            let test_eq_v x = (x = v) in
            let arg_idx =
              Option.get (List.find_index test_eq_v args)
            in
            let env_idx =
              Option.get (List.find_index test_eq_v env)
            in
            Arr.swap arg_idx (args_len + env_idx) acc_env)
          rel_prod_env
          args
      in
      Arr.sum_reduce (* get rid of now-unneeded extra vars in front *)
        ~axis:(Array.init args_len Fun.id)
        swapped_holes_env
  | Soleo (n, t) ->
      (* same as succeed, b/c guaranteed by "typechecking"*)
      Arr.ones (shape_of_env env)
  | Lefto (ab, a) ->
      (* check that left side matches *)
      let (_, Sum (_at, bt)) = ab in
      gen_eq_check ab a env
        (fun va -> vec_kron_sum va (Arr.zeros [|adt_size bt|]))
  | Righto (ab, b) ->
      (* check that right side matches *)
      let (_, Sum (at, _bt)) = ab in
      gen_eq_check ab b env
        (fun vb -> vec_kron_sum (Arr.zeros [|adt_size at|]) vb)
  | Pairo (ab, a, b) ->
      (* check that a and b match *)
      let (_, Prod (at, bt)) = ab in
      let a_check =
        gen_eq_check ab a env (fun va -> vec_kron_prod va (Arr.ones [|adt_size bt|]))
      in
      let b_check =
        gen_eq_check ab b env (fun vb -> vec_kron_prod (Arr.ones [|adt_size at|]) vb)
      in
      Arr.mul a_check b_check

let eval_rel (r : rel) (rels : comp_rel list) : Arr.arr =
  eval_tk r.body r.args rels

let compile_rel (r : rel) (rels : comp_rel list) : comp_rel =
  { name = r.name;
    args = r.args;
    body = eval_rel r rels }

let eval_tk_prgm (t : tk_prgm) : Arr.arr =
  let comp_rels = 
    List.fold_left
      (fun (acc_comp_rels : comp_rel list) (r : rel) ->
        (compile_rel r acc_comp_rels) :: acc_comp_rels)
      []
      t.rels
  in
  eval_rel t.main comp_rels
