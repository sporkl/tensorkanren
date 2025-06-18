
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

let bool_adt = Sum (Unit, Unit)
let true_adv = Left Sole
let false_adv = Right Sole

let trueo = {
  name = "lefto";
  args = [("x", bool_adt)];
  body =
    Fresh (("u", Unit),
           conj [
             Lefto (("x", Sum (Unit, Unit)), ("u", Unit));
             Soleo ("u", Unit)])}

let falseo = {
  name = "lefto";
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

(* COMPILING ADTs *)

(* want to compile to a vector representation, so that multiple can be compiled as a tensor *)

(* Unit -> 1 (or [1]) *)
(* Sum (Unit, Unit) -> [1 0] | [0 1]; corresponds to Kronecker sum? [1] (+) [1] = [1 1] *)
(* Pair (Sole, Sole) -> [1]; corresponds to Kronecker product? [1] (x) [1] = [1] *)
(* not worrying about optimization for now *)

(* is it possible that every ADT compiles to a vector with a single 1 somewhere? with # entries = ADT size? *)
(* in which case attempting to optimize might not do anything *)

let kron_prod = Mat.kron

let kron_sum = Mat.concat_horizontal

let init_zeros = Mat.vector_zeros

let init_one_hot hi len =
  let a = Mat.vector_zeros len in
  Mat.set a 0 hi 1.0; a

let rec adt_size (t : adt) : int =
  match t with
  | Unit -> 1
  | Sum (x, y) -> (adt_size x) + (adt_size y)
  | Prod (x, y) -> (adt_size x) * (adt_size y)

let rec compile_adv (v : adv) (t : adt) : Mat.mat =
  match v, t with
  | Sole, Unit -> Mat.vector_ones 1
  | Left x, Sum (xt, yt) -> kron_sum (compile_adv x xt) (init_zeros @@ adt_size yt)
  | Right y, Sum (xt, yt) -> kron_sum (init_zeros @@ adt_size xt) (compile_adv y yt)
  | Pair (x, y), Prod (xt, yt) -> kron_prod (compile_adv x xt) (compile_adv y yt)
  | _ -> invalid_arg "Type does not match value!"

let ex_compile_adv = [
  compile_adv true_adv bool_adt;
  compile_adv false_adv bool_adt;
  compile_adv (Pair (true_adv, true_adv)) (Prod (bool_adt, bool_adt));
  compile_adv (Pair (false_adv, true_adv)) (Prod (bool_adt, bool_adt));
  compile_adv (Pair (true_adv, false_adv)) (Prod (bool_adt, bool_adt));
  compile_adv (Pair (false_adv, false_adv)) (Prod (bool_adt, bool_adt));
  compile_adv (Left true_adv) (Sum (bool_adt, bool_adt));
  compile_adv (Left false_adv) (Sum (bool_adt, bool_adt));
  compile_adv (Right true_adv) (Sum (bool_adt, bool_adt));
  compile_adv (Right false_adv) (Sum (bool_adt, bool_adt));
  compile_adv (Left Sole) (Sum (Unit, Unit));
  compile_adv (Right Sole) (Sum (Unit, Unit));
  compile_adv (Pair (Sole, Sole)) (Prod (Unit, Unit))]

let find_vec_index f vec =
  let res_col = ref None in
  Mat.iteri_2d
    (fun _ c v -> if v = f then res_col := (Some c) else ())
    vec;
  !res_col

(* assumes input is a valid one-hot vector *)
let rec decompile_adv (vec : Mat.mat) (t : adt) : adv =
  if (adt_size t) <> (Mat.col_num vec) then
    invalid_arg "Type does not match vector!"
  else
    match t with
    | Unit ->
        if vec = (Mat.vector_ones 1) then
          Sole
        else
          invalid_arg "Type does not match vector!"
    | Sum (xt, yt) ->
        if (Mat.col_num vec) = (adt_size t) then
          let x = Mat.get_slice [[]; [0; (adt_size xt) - 1]] vec in
          let y = Mat.get_slice [[]; [(adt_size xt); (adt_size xt) + (adt_size yt) - 1]] vec in
          if (Mat.exists (fun f -> f = 1.0) x) then
            Left (decompile_adv x xt)
          else if (Mat.exists (fun f -> f = 1.0) y) then
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
              decompile_adv (init_one_hot x_index (adt_size xt)) xt,
              decompile_adv (init_one_hot y_index (adt_size yt)) yt)

let compile_adv_isomorphic (v : adv) (t : adt) : adv =
  decompile_adv (compile_adv v t) t

(* COMPILING TO MATRIX OPS *)

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

(* starting statevector is equal superposition *)
(* statevector is the values of variables in the environment *)


let rec compile_tk (exp : tk) (env : var list) (rels : comp_rel list) : Mat.mat =
  match exp with
  | Succeed ->
      (* all states succeed *)
      (* results in "equal superposition" vector averaged over sum of prev vector. good? *)
      (* or should define Succeed and Fail in terms of existing ops? *)
      let s = env_size env in
      Mat.((ones s s) /$ (float_of_int s)) (* TODO: should be identity *)
  | Fail ->
      (* all states fail *)
      (* rewrites to all-zero vector *)
      let s = env_size env in Mat.(zeros s s)
  | Conj (e1, e2) ->
      (* element-wise multiplication *)
      (* TODO: I think this might not work properly *)
      Mat.mul (compile_tk e1 env rels) (compile tk e2 env rels)
  | Disj (e1, e2) ->
      (* element-wise addition *)
      (* TODO: I think this also might not work properly *)
      Mat.add (compile_tk e1 env rels) (compile_tk e2 env rels)
  | Fresh (v, e) -> 
      (* matrix that prepends fresh variable to tensor product *)
      let v_size = var_size v in
      let rest_size = env_size env in
      let prep_mat = Mat.(kron (ones 1 v_size) (eye rest_size)) in
      let body_mat = compile_tk e (v :: env) rels in
      let sum_mat = Mat.ones rest_size (v_size * rest_size) in (* TODO: THIS IS WRONG, FIX *)
      Mat.(sum_mat *@ body_mat *@ prep_mat)
  | Rel (name, args) -> ... (* swap into rel-compatible matrix, then apply that with id, then unswap *)
  | Soleo (n, t) -> Mat.eye (env_size env) (* always succeeds b/c "typechecking" *)
  | Lefto (ab, a) -> ...
  | Righto (ab, b) -> ...
  | Pairo (ab, a, b) -> ...

  (* TODO: express with tensor operations instead of trying to do as one big matrix operation? *)
  (* in the conj and disj cases, want to add/multiply the vectors together, not the matrices *)
  (* but not sure if that's expressable as a single matrix. possible with diagonalization? *)
  (* unsure how to express lefto, righto, pairo *)

  (* are all matrixes diagonal in current form? *)
  (* write down examples explicitly. noto is good *)

  ([1 0] (x) [0 1]) + ([0 1] (x) [1 0]) = [0 1 0 0] + [0 0 1 0] = [0 1 1 0]

  (* test: a = [1 1], (a, a) = [1 0 0 1] or [1 1 1 1] . former preferable *)
  (* [aa] (fresh (a : bool) (pairo aa a a)) *)

  

  [0 1] [1]
  [1 0] [0]

(* [ 0 1 1 0 ] *)

(* type tk = *)
(*   | Succeed *)
(*   | Fail *)
(*   | Conj of tk * tk *)
(*   | Disj of tk * tk *)
(*   | Fresh of var * tk *)
(*   | Rel of string * (var list) *)
(*   | Soleo of var *)
(*   | Lefto of var * var (1* a + b, a *1) *)
(*   | Righto of var * var (1* a + b, b *1) *)
(*   | Pairo of var * var * var (1* a * b, a, b *1) *)
  

