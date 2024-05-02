(** {1 Export queries to Z3} *)

open Z3

type sat =
  | SAT
  | UNSAT
  | TIMEOUT

module Cache = Hashtbl.Make(Form.Form)

type t = {
  context : context;
  cache   : sat Cache.t;
  solver  : Solver.solver;
}

let create () =
  let context = mk_context [] in
  let cache   = Cache.create 1024 in
  let solver  = Solver.mk_solver_s context "NIA" in
  { context; cache; solver }

let rec mk_term (context : context) (e : Term.t) =
  match e.node with
  | Var v -> mk_var context v
  | Cst c -> mk_const context c
  | Bop (op, e1, e2) -> mk_arith_op context op [mk_term context e1; mk_term context e2]

and mk_arith_op (context : context) (op : Term.Bop.t) =
  match op with
  | ADD -> Arithmetic.mk_add context
  | SUB -> Arithmetic.mk_sub context
  | MUL -> Arithmetic.mk_mul context

and mk_var (context : context) (v : Term.Var.t) =
  Format.kasprintf (Symbol.mk_string context) "%a" Term.Var.pp v
  |> Arithmetic.Integer.mk_const context

and mk_const (context : context) (c : int) =
  Arithmetic.Integer.mk_numeral_i context c

let mk_forall context var body =
  Z3.Quantifier.mk_forall_const context [mk_var context var] body None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

let mk_exists context var body =
  Z3.Quantifier.mk_exists_const context [mk_var context var] body None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

let rec mk_form (context : context) (f : Form.t) =
  match f.node with
  | Cst true -> Boolean.mk_true context
  | Cst false -> Boolean.mk_false context
  | Bop (op, f1, f2) -> mk_bool_op context op [mk_form context f1; mk_form context f2]
  | Not f -> Boolean.mk_not context (mk_form context f)
  | Cmp (cmp, e1, e2) -> mk_cmp context cmp (mk_term context e1) (mk_term context e2)
  | Quant (FORALL, x, f) -> mk_forall context x (mk_form context f)
  | Quant (EXISTS, x, f) -> mk_exists context x (mk_form context f)

and mk_bool_op context (op : Form.Bop.t) =
  match op with
  | Form.Bop.OR -> Boolean.mk_or context
  | Form.Bop.AND -> Boolean.mk_and context
  | Form.Bop.IMP -> function [x; y] -> Boolean.mk_implies context x y | _ -> invalid_arg "mk_bool_op"

and mk_cmp (context : context) (cmp : Form.Cmp.t) =
  match cmp with
  | Form.Cmp.LE -> Arithmetic.mk_le context
  | Form.Cmp.LT -> Arithmetic.mk_lt context
  | Form.Cmp.EQ -> Boolean.mk_eq context

let really_check_sat solver (f : Form.t) =
  Solver.reset solver.solver;
  Solver.add solver.solver [mk_form solver.context f];
  match Solver.check solver.solver [] with
  | SATISFIABLE -> SAT
  | UNSATISFIABLE -> UNSAT
  | UNKNOWN -> TIMEOUT

let check_sat solver (f : Form.t) =
  match Cache.find_opt solver.cache f.node with
  | Some res -> res
  | None ->
    let res = really_check_sat solver f in
    Cache.add solver.cache f.node res;
    res

(** returns [true] only if [f] is sat,
    no guarantees when it returns [false] *)
let is_sat solver f =
  match check_sat solver f with
  | SAT -> true
  | _ -> false

(** returns [true] only if [f] is unsat,
  no guarantees when it returns [false] *)
let is_unsat solver f =
  match check_sat solver f with
  | UNSAT -> true
  | _ -> false