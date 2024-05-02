(** {1 Formula Construction API} *)

(** Binary operators *)
module Bop = struct
  type t =
    | AND
    | OR
    | IMP
end

(** Comparisons *)
module Cmp = struct
  type t =
    | LT
    | LE
    | EQ
end

module Quant = struct
  type t = FORALL | EXISTS
end

type t = form_node Hashcons.hash_consed
and form_node =
  | Cst of bool
  | Bop of Bop.t * t * t
  | Not of t
  | Cmp of Cmp.t * Term.t * Term.t
  | Quant of Quant.t * Term.Var.t * t

(** Auxilary functions to instantiate [Hashcons] *)
module Form = struct
  type t = form_node
  let equal t1 t2 =
    match t1, t2 with
    | Cst c1, Cst c2 ->
      c1 = c2
    | Bop (op1, lhs1, rhs1), Bop (op2, lhs2, rhs2) ->
      op1 = op2 && lhs1 == lhs2 && rhs1 == rhs2
    | Cmp (cmp1, lhs1, rhs1), Cmp (cmp2, lhs2, rhs2) ->
      cmp1 = cmp2 && lhs1 == lhs2 && rhs1 == rhs2
    | Not t1, Not t2 ->
      t1 == t2
    | _ -> false
  
  let hash (x : t) =
    match x with
    | Cst i ->
      Hashtbl.hash i
    | Bop (op, e1, e2) ->
      Hashtbl.hash (op, e1.hkey, e2.hkey)
    | Not e ->
      Hashtbl.hash e.hkey
    | Cmp (cmp, e1, e2) ->
      Hashtbl.hash (cmp, e1.hkey, e2.hkey)
    | Quant (q, x, e) ->
      Hashtbl.hash (q, x, e.hkey)
end

module HForm = Hashcons.Make(Form)
let world = HForm.create 1024

(** {2 Smart constructors} *)

let forall x e : t =
  HForm.hashcons world (Quant (Quant.FORALL, x, e))

let exists x e : t =
  HForm.hashcons world (Quant (EXISTS, x, e))

let mk_const (b : bool) : t =
  HForm.hashcons world (Cst b)

let mk_and (e1 : t) (e2 : t) : t =
  match e1.node, e2.node with
  | Cst true, _ -> e2
  | _, Cst true -> e1
  | Cst false, _ -> e1
  | _, Cst false -> e2
  | _, _ -> HForm.hashcons world (Bop (AND, e1, e2))

let mk_imp (e1 : t) (e2 : t) : t =
  match e1.node, e2.node with
  | Cst false, _ -> mk_const true
  | _, _ -> HForm.hashcons world (Bop (IMP, e1, e2))

let mk_or (e1 : t) (e2 : t) : t =
  match e1.node, e2.node with
  | Cst true, _ -> e1
  | _, Cst true -> e2
  | Cst false, _ -> e2
  | _, Cst false -> e1
  | _, _ -> HForm.hashcons world (Bop (OR, e1, e2))

let mk_eq (e1 : Term.t) (e2 : Term.t) : t =
  if e1 == e2 then mk_const true
  else HForm.hashcons world (Cmp (EQ, e1, e2))

let mk_le (e1 : Term.t) (e2 : Term.t) : t =
  match e1.node, e2.node with
  | Cst c1, Cst c2 -> mk_const (c1 <= c2)
  | _, _ ->
    if e1 == e2 then mk_const true
    else HForm.hashcons world (Cmp (LE, e1, e2))

let mk_lt (e1 : Term.t) (e2 : Term.t) : t =
  match e1.node, e2.node with
  | Cst c1, Cst c2 -> mk_const (c1 < c2)
  | _, _ -> HForm.hashcons world (Cmp (LT, e1, e2))

let mk_gt e1 e2 : t = mk_lt e2 e1

let mk_ge e1 e2 : t = mk_le e2 e1

let mk_op (op : Bop.t) (e1 : t) (e2 : t) : t =
  match op with
  | OR -> mk_or e1 e2
  | AND -> mk_and e1 e2
  | IMP -> mk_imp e1 e2

let mk_cmp (cmp : Cmp.t) (e1 : Term.t) (e2 : Term.t) : t =
  match cmp with
  | EQ -> mk_eq e1 e2
  | LE -> mk_le e1 e2
  | LT -> mk_lt e1 e2

let rec mk_not (e : t) : t =
  match e.node with
  | Cst c -> mk_const (not c)
  | Cmp (LT, x, y) -> mk_ge x y
  | Cmp (LE, x, y) -> mk_gt x y
  | Bop (AND, x, y) -> mk_or (mk_not x) (mk_not y)
  | Bop (OR, x, y) -> mk_and (mk_not x) (mk_not y)
  | Not x -> x
  | _ -> HForm.hashcons world (Not e)

let mk_neq (e1 : Term.t) (e2 : Term.t) : t =
  mk_not (mk_eq e1 e2)

let mk_quant q x e : t =
  HForm.hashcons world (Quant (q, x, e))

let rec mk_forall (xs : Term.Var.t list) (e : t) : t =
  match xs with
  | [] -> e
  | x::xs -> mk_quant Quant.FORALL x (mk_forall xs e)

let rec mk_exists (xs : Term.Var.t list) (e : t) : t =
  match xs with
  | [] -> e
  | x::xs -> mk_quant Quant.EXISTS x (mk_exists xs e)

let free_vars (e : t) =
  let rec go fv (e : t) =
    match e.node with
    | Cst _ -> fv
    | Bop (_, e1, e2) -> go (go fv e1) e2
    | Not e -> go fv e
    | Cmp (_, e1, e2) ->
      let open Term.Vars in
      union fv (union (Term.free_vars e1) (Term.free_vars e2))
    | Quant (_, x, e) -> Term.Vars.remove x (go fv e)
  in go Term.Vars.empty e