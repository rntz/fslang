exception Unimplemented

type ordering = EQ | LT | GT

type var = string
module Cx = Map.Make(String)

(* pointed set types *)
type tp
  = Map of set * tp             (* finitely supported map *)
  | Hom of tp * tp              (* point-preserving function *)
  | Maybe of set                (* adds a point *)
  | Cross of tp list            (* cross/direct product *)
  (* how do I represent smash/tensor at runtime?
   * I can't decide equality with the point in general. agh! *)
  | Smash of tp list            (* smash/tensor product *)
  | Int                         (* the point is zero *)

(* sets *)
and set
  = U of tp                     (* underlying set of a pointed type *)
  | Fun of set * set           (* arbitrary function *)
  | Empty                       (* empty type *)
  (* | Tuple of set list *)
  (* TODO: sum types *)

(* set with one value *)
let unit: set = U (Maybe Empty)
(* type with two values; identity of smash/tensor product *)
let bool: tp = Maybe unit

let subset: set -> set -> bool = (=)
let subtype: tp -> tp -> bool = (=)

(* all terms, whether set or pointed;
 * also represents patterns *)
type term
  = Var of var
  | Asc of tp * term
  | AscSet of set * term
  | Nil                         (* the point *)
  | Let of pat * term * term    (* Cross, Smash, Maybe *)
  | Just of term                (* Maybe *)
  (* Fun, Map, Hom *)
  | Lam of var * term | App of term * term
  (* | App of term * pat *)
  | Tuple of term list          (* Cross, Smash *)
  | Proj of int * term          (* Cross *)

and pat = PVar of var
        | PTuple of pat list
        | PJust of pat
        | PEquals of term

(* Explicitly typed language, post-elaboration. *)
module type TYPED = sig
  type pat
  type t

  val pvar: var -> pat
  val ptuple: pat list -> pat
  val pjust: pat -> pat
  val pequals: t -> pat

  val var: tp -> var -> t
  val var_set: set -> var -> t

  val lam: tp -> tp -> var -> t -> t
  val lam_set: set -> set -> var -> t -> t
  val lam_map: set -> tp -> var -> t -> t

  val app: tp -> tp -> t -> t -> t
  val app_set: set -> set -> t -> t -> t
  (* should the second arg here be a pattern? *)
  val app_map: set -> tp -> t -> pat -> t

  val int: int -> t
  val nil: tp -> t
  val just: set -> t -> t
  (* let p = (t1: a) in (t2: b) *)
  val let_pat: tp -> tp -> pat -> t -> t -> t
end


module Eval: TYPED = struct
  type value
    = VTuple of value list
    | VFun of (value -> value)
    | VMap of (value * value) list (* input/output rows *)
    | VNil
    | VJust of value
    | VInt of int

  exception InvalidComparison of value * value

  module Value = struct
    type t = value
    let compare = Stdlib.compare (* generic comparison *)
  end
  module Table = Map.Make(Value)
  type table = value Table.t

  type env = value Cx.t

  (* this is finite support lang
   * expressions are finitely supported
   * evaluating an expression produces a table of rows
   *
   * row = (env, value)
   * env = the values of f.s. variables
   * value = the value of the expression
   *
   * IDEA: maybe I should pass in a VARIABLE ORDER
   * and then rows come out LEXICALLY SORTED wrt that order
   * this will make joins easier to implement.
   * will also make projecting away things easier, I think.
   *)
  type row = env * value
  type t = env -> row list

  module Rows = struct
    (* Give me the variable order & I'll give you the rows. *)
    type rows = var list -> row list

    let merge (order: var list) (tables: (tp * row list) list): row list =
      raise Unimplemented

    let single (v: value) (_order: var list): row list = [(Cx.empty, v)]

    (* lexically compares two environments, interpreting "absence" as "match anything".
     * EQ does not mean they are equal, merely equal on the keys in their intersection.
     *)
    let rec lexical (order: var list) (r: env) (s: env): int =
      match order with
      | [] -> 0
      | v::vs ->
         match Cx.find_opt v r, Cx.find_opt v s with
         | Some x, Some y ->
            let t = Value.compare x y in
            if t != 0 then t else lexical vs r s
         | _ -> lexical vs r s

    (* (\* waitaminute -
     *  * this should only ever be applied when all vars are present
     *  * in every row from both halves!
     *  * Can I simplify `lexical` for this case?
     *  *\)
     * let outer_join2 (rtp: tp) (stp: tp) (r: rows) (s: rows) (order: var list): row list =
     *   let rec loop r s =
     *     match r, s with
     *     | [], [] -> []
     *     | (r::rs), [] -> raise Unimplemented
     *     | [], (s::ss) -> raise Unimplemented
     *     | ((renv, rval)::rs), ((senv, sval)::ss) ->
     *        match lexical order renv senv with
     *        | EQ -> raise Unimplemented
     *        | GT -> raise Unimplemented
     *        | LT -> raise Unimplemented
     *   in loop (r order) (s order) *)

    open List
    open Either

    let span (p: 'a -> bool) (xs: 'a list): 'a list * 'a list =
      let rec loop acc list = match list with
        | [] -> acc, []
        | x::xs -> if p x then loop (x::acc) xs else acc, list
      in loop [] xs

    (* let outerjoin (tables: (tp * rows) list) (order: var list): row list =
     *   let n = length tables in
     *   let (tps, lists) = split tables in
     *   (\* add explicit indices to the lists *\)
     *   let lists = mapi (fun i rs -> i, rs order) lists in
     *   (\* keep only non-empty lists, split into head and tail *\)
     *   let lists = filter_map (function i, [] -> None
     *                                  | i, (xenv,xval)::xs -> Some (i,xenv,xval,xs))
     *                 lists in
     *   (\* sort the lists so the one with the lexically smallest key is in front;
     *    * we will maintain this as a loop invariant *\)
     *   let lists = fast_sort (fun (_,x,_,_) (_,y,_,_) -> lexical order x y) lists in
     *   let rec loop = function
     *     | [] -> []
     *     | (i, xenv, xval, xs) :: rest as lists ->
     *        (\* Join with all rows with a key matching xenv.
     *         * Since they're in lexically sorted order, we can just take from the head until
     *         * they're not "equal" to xenv.
     *         *\)
     *        let match_xenv (_, yenv, _, _) = 0 == lexical order xenv yenv in
     *        let matches, rest = span match_xenv lists in
     *        (\* TODO *\)
     *        (\* combine the matches and the values *\)
     *        raise Unimplemented
     *   in loop lists *)

    let outerjoin (tables: (tp * rows) list) (order: var list): row list =
      let n = length tables in
      let tables = List.map (fun (tp,rows) -> tp, rows order) tables in
      let rec loop lists =
        match List.filter_map (function tp, [] -> None
                                      | tp, (xenv,_)::_ -> Some xenv)
                lists with
        | [] -> []
        | env::envs ->
           (* fold to find minimum key. but, is there even a well-defined minimum?
            * more to the point, will (lexical order) find it?
            * if the envs might have different var-sets, don't we need to accumulate them? *)
           raise Unimplemented
      in match lists with [] -> [] | _ -> loop lists

    (* let union (tables: (tp * rows) list) (order: var list): row list =
     *   let tables = List.map (fun (tp, rows) -> tp, rows order) tables in
     *   let rec loop (tables: (tp * row list) list) =
     *     let heads = List.filter_map
     * 
     *     if List.for_all (fun (tp, x) -> List.is_empty x) tables then []
     *     else
     *       (\* grab the minimum key.
     *        * pick all matching keys.
     *        * fill out remaining vars with nil. *\)
     *       let keys = List.map (fun (tp,x) -> List.hd x) tables
     *   in loop tables *)

    (* let inner_join (r: rows) (s: rows) (order: var list): row list =
     *   let r, s = r order, s order in
     *   match r, s with *)
  end

  type pat = Var of var | Just of pat | Tuple of pat list | Equals of t
  let pvar x = Var x
  let ptuple xs = Tuple xs
  let pjust x = Just x
  let pequals x = Equals x

  let var _tp x env = [(Cx.empty, Cx.find x env)]
  (* is this correct? should the set language also be returning a table? *)
  let var_set _set x env = [(Cx.empty, Cx.find x env)]

  let lam a b x body = raise Unimplemented
  let lam_set a b x body = raise Unimplemented

  (* lam_map = grouping away the variable x. *)
  let lam_map (a: set) (b: tp) (x: var) (body: t) (env: env): row list =
    let results = body env in
    raise Unimplemented

  let app a b fnc arg = raise Unimplemented
  let app_set a b fnc arg = raise Unimplemented
  let app_map a b fnc pat = raise Unimplemented

  let int x = raise Unimplemented
  let nil tp = raise Unimplemented
  let just set x = raise Unimplemented
  let let_pat a b p t u = raise Unimplemented
end


(* (\* typing contexts for pointed terms *\)
 * type how = Set of set           (\* may be used freely *\)
 *          | Lin of tp            (\* must be used in point-preserving way *\)
 *          | Sup of set           (\* must be finitely supported *\)
 * type cx = how Cx.t
 * 
 * exception Unimplemented
 * exception Ill of string          (\* ill typed *\) *)


(* (\* Produces the result type and an updated context.
 *  * The updated context is identical except that some vars which were
 *  * mapped to (Set s) may now be mapped to (Sup s).
 *  *\)
 * let rec check (cx: cx) (expect: tp option) (tm: term): cx * tp =
 *   let synth (got: tp): tp = match expect with
 *     | None -> got
 *     | Some want -> if subtype got want then got
 *                    (\* TODO better error message *\)
 *                    else raise (Ill "want/got mismatch") in
 *   match expect, tm with
 *   | _, Var v ->
 *      (match Cx.find_opt v cx with
 *       | None -> raise (Ill ("unbound variable: " ^ v))
 *       | Some (Lin tp) -> (cx, synth tp)
 *       | _ -> raise Unimplemented)
 * 
 *   (\* Asc *\)
 *   | None, Asc (tp, tm) -> check cx (Some tp) tm
 *   | Some want, Asc (tp, tm) ->
 *      if subtype tp want then check cx (Some tp) tm
 *      else raise (Ill "type ascription is not subtype of expected type")
 * 
 *   (\* Lam *\)
 *   | None, Lam _ -> raise (Ill "cannot infer type for lambda")
 *   | _, _ -> raise Unimplemented *)

