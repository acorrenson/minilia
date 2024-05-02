(** {1 Term Construction API} *)

(** Binary operators *)
module Bop = struct
  type t =
    | ADD
    | SUB
    | MUL

  let pp fmt = function
    | ADD -> Format.fprintf fmt "+"
    | SUB -> Format.fprintf fmt "-"
    | MUL -> Format.fprintf fmt "*"
end

(** Variables *)
module Var : sig 
  type t
  val pp : Format.formatter -> t -> unit
  val make : string -> t
  val fresh : ?name:string -> unit -> t
end = struct
  let _counter = ref 0

  type t = {
    id: int;
    name: string;
  }

  let pp fmt { id; name } =
    if id = 0 then
      Format.fprintf fmt "%s" name
    else
      Format.fprintf fmt "%s_%d" name id

  let make (name : string) : t =
    { id = 0; name }

  let fresh ?(name = "fresh") () : t =
    incr _counter;
    { id = !_counter; name }
end


type t = term_node Hashcons.hash_consed
and term_node =
  | Var of Var.t
  | Cst of int
  | Bop of Bop.t * t * t

let rec pp (fmt : Format.formatter) (e : t) =
  match e.node with
  | Var v -> Format.fprintf fmt "%a" Var.pp v
  | Cst i -> Format.fprintf fmt "%d" i
  | Bop (op, e1, e2) ->
    Format.fprintf fmt "(%a %a %a)" pp e1 Bop.pp op pp e2

(** Auxilary functions to instanciate [Hashcons] *)
module Term = struct
  type t = term_node
  let equal t1 t2 =
    match t1, t2 with
    | Var v1, Var v2 ->
      v1 = v2
    | Cst c1, Cst c2 ->
      c1 = c2
    | Bop (op1, lhs1, rhs1), Bop (op2, lhs2, rhs2) ->
      op1 = op2 && lhs1 == lhs2 && rhs1 == rhs2
    | _ -> false
  
  let hash (x : t) =
    match x with
    | Cst i -> i
    | Var v -> Hashtbl.hash v
    | Bop (op, e1, e2) ->
      Hashtbl.hash (op, e1.hkey, e2.hkey)
end

module Vars = Set.Make(struct
  type t = Var.t
  let compare = compare
end)

let free_vars (e : t) =
  let rec go fv (e : t) =
    match e.node with
    | Var v -> Vars.add v fv
    | Bop (_, e1, e2) -> go (go fv e1) e2
    | Cst _ -> fv
  in go Vars.empty e


module HTerm = Hashcons.Make(Term)
let world = HTerm.create 1024

let mk_var v : t =
  HTerm.hashcons world (Var v)

let mk_const c : t =
  HTerm.hashcons world (Cst c)

let rec mk_add (e1 : t) (e2 : t) : t =
  match e1.node, e2.node with
  | Cst c1, Cst c2 -> mk_const (c1 + c2)
  | Cst _, _ -> mk_add e2 e1
  | Bop (ADD, e1_lhs, e1_rhs), _ ->
    mk_add e1_lhs (mk_add e1_rhs e2)
  | _, _ -> HTerm.hashcons world (Bop (ADD, e1, e2))

let mk_sub (e1 : t) (e2 : t) : t =
  match e1.node, e2.node with
  | Cst c1, Cst c2 -> mk_const (c1 - c2)
  | _, _ -> HTerm.hashcons world (Bop (SUB, e1, e2))

let rec mk_mul (e1 : t) (e2 : t) : t =
  match e1.node, e2.node with
  | Cst c1, Cst c2 -> mk_const (c1 * c2)
  | Cst _, _ -> mk_mul e2 e1
  | Bop (ADD, e1_lhs, e1_rhs), _ ->
    mk_mul e1_lhs (mk_mul e1_rhs e2)
  | _, _ -> HTerm.hashcons world (Bop (MUL, e1, e2))

let mk_bop (op : Bop.t) (e1 : t) (e2 : t) : t =
  match op with
  | ADD -> mk_add e1 e2
  | MUL -> mk_mul e1 e2
  | SUB -> mk_sub e1 e2