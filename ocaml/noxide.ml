type var = int [@@deriving show]
type ty_var = int [@@deriving show]
type rgn_var = int [@@deriving show]
type loan_id = int [@@deriving show]

type muta = Shared | Unique [@@deriving show]
type place =
  | Var of var
  | Deref of place
  | FieldProj of place * string
  | IndexProj of place * int
  [@@deriving show]
type rgn_atom =
  | RgnVar of rgn_var
  | Loan of loan_id * place
  [@@deriving show]
type rgn = rgn_atom list [@@deriving show]
type loans = (loan_id * place) list [@@deriving show]

type kind = Star | Rgn [@@deriving show]
type base_ty = Bool | U32 | Unit [@@deriving show]
type ty =
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of rgn * muta * ty
  | Fun of rgn_var list * ty_var list * ty list * ty
  | Array of ty * int
  | Tup of ty list
  [@@deriving show]

type global_env = () (* TODO: actual global environment definition *)
type tyvar_env = rgn_var list * ty_var list
type var_env = (var * ty) list [@@deriving show]

let var_env_lookup (gamma : var_env) (x : var) : ty = List.assoc x gamma
let var_env_include (gamma : var_env) (x : var) (typ : ty) = List.cons (x, typ) gamma
let var_env_exclude (gamma : var_env) (x : var) = List.remove_assoc x gamma

let is_empty (lst : 'a list) : bool = List.length lst = 0

(* checks that mu_prime is at least mu *)
let is_at_least (mu : muta) (mu_prime : muta) : bool =
  match (mu, mu_prime) with
  | (Shared, _) -> true
  | (Unique, Unique) -> true
  | (Unique, Shared) -> false

(* extract all the specific loans from a given region *)
let rgn_to_loans (rgn : rgn) : loans =
  let work (atom : rgn_atom) (loans : loans) : loans =
    match atom with
    | RgnVar _ -> loans
    | Loan (id, pi) -> List.cons (id, pi) loans
  in List.fold_right work rgn []

(* compute all the at-least-mu loans in a given gamma *)
let all_loans (mu : muta) (gamma : var_env) : loans =
  let rec work (typ : ty) (loans : loans) : loans =
    match typ with
    | BaseTy _ -> loans
    | TyVar _ -> loans
    | Ref (rgn, mu_prime, typ) ->
      if is_at_least mu mu_prime then List.append (rgn_to_loans rgn) (work typ loans)
      else work typ loans
    | Fun (_, _, _, _) -> loans
    | Array (typ, _) -> work typ loans
    | Tup typs -> List.fold_right List.append (List.map (fun typ -> work typ []) typs) loans
  in List.fold_right (fun entry -> work (snd entry)) gamma []

(*  compute all subplaces from a given place *)
let all_subplaces (pi : place) : place list =
  let rec work (pi : place) (places : place list) : place list =
    match pi with
    | Var _ -> List.cons pi places
    | Deref pi_prime -> List.cons pi (work pi_prime places)
    | FieldProj (pi_prime, _) -> List.cons pi (work pi_prime places)
    | IndexProj (pi_prime, _) -> List.cons pi (work pi_prime places)
  in work pi []

(* find the root of a given place *)
let rec root_of (pi : place) : var =
  match pi with
  | Var root -> root
  | Deref pi_prime -> root_of pi_prime
  | FieldProj (pi_prime, _) -> root_of pi_prime
  | IndexProj (pi_prime, _) -> root_of pi_prime

(* find all at-least-mu loans in gamma that have to do with pi *)
let find_loans (mu : muta) (gamma : var_env) (pi : place) : loans =
  (* n.b. this is actually too permissive because of reborrowing and deref *)
  let root_of_pi = root_of pi
  in let relevant (pair : loan_id * place) : bool =
    (* a loan is relevant if it is a descendant of any subplace of pi *)
    let (_, pi_prime) = pair
       (* the easiest way to check is to check if their roots are the same *)
    in root_of_pi = root_of pi_prime
  in List.filter relevant (all_loans mu gamma)

(* given a gamma, determines whether it is safe to use pi according to mu *)
let is_safe (gamma : var_env) (mu : muta) (pi : place) : bool =
  let subplaces_of_pi = all_subplaces pi
  in let relevant (pair : loan_id * place) : bool =
    (* a loan is relevant if it is for either a subplace or an ancestor of pi *)
    let (_, pi_prime) = pair
        (* either pi is an ancestor of pi_prime *)
    in List.exists (fun x -> x = pi) (all_subplaces pi_prime)
        (* or pi_prime is a subplace of pi *)
        || List.exists (fun x -> x = pi_prime) subplaces_of_pi
  in match mu with
  | Unique -> (* for unique use to be safe, we need _no_ relevant loans *)
              is_empty (List.filter relevant (find_loans Shared gamma pi))
  | Shared -> (* for shared use, we only care that there are no relevant _unique_ loans *)
              is_empty (List.filter relevant (find_loans Unique gamma pi))

let print_is_safe (gamma : var_env) (mu : muta) (pi : place) =
  if is_safe gamma mu pi then
    Format.printf "%a is %a safe in@.  %a@." pp_place pi pp_muta mu pp_var_env gamma
  else
    Format.printf "%a is not %a safe in@.  %a@." pp_place pi pp_muta mu pp_var_env gamma

let main =
  let (x, y, _) = (1, 2, 3)
  in let pi1 = Var x
  in let pi2 = IndexProj (Var x, 0)
  in let ref_ty id from = Ref ([Loan (id, from)], Shared, BaseTy U32)
  in let env1 = [(x, Tup [BaseTy U32])]
  in let env2 = [(x, Tup [BaseTy U32]); (y, ref_ty 1 pi2)]
  in begin
    print_is_safe env1 Unique pi1;
    print_is_safe env1 Unique pi2;
    print_is_safe env2 Unique pi1;
    print_is_safe env2 Unique pi2;
    print_is_safe env2 Shared pi1;
    print_is_safe env2 Shared pi2;
  end
