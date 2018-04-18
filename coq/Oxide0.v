Require Import String.

Inductive immpath : Set :=
| Field : string -> immpath
| Proj : nat -> immpath
| Index : nat -> immpath.

Inductive path : Set :=
| Path : list immpath -> path.

Inductive muta : Set :=
| Imm : muta
| Mut : muta.

Inductive kind : Set :=
| KStar : kind
| KRgn : kind
| KFrac : kind.

Inductive basety : Set :=
| TBool : basety
| Tu32 : basety
| TUnit : basety.

Inductive rgn : Set :=
| RConcrete : nat -> rgn.
(* FIXME: type vars *)

Inductive frac : Set :=
| FConcrete : nat -> frac.
(* FIXME: type vars *)

Inductive struct : Set :=
| SId : string -> struct.

Inductive enum : Set :=
| EVar : struct -> string -> enum.

Inductive ty : Set :=
| TBase : basety -> ty
(* FIXME: type vars *)
| TRef : rgn -> frac -> ty -> ty
(* FIXME: univerals *)
| TFn : list (rgn * frac * ty) -> ty -> ty
| TMvFn : list (rgn * frac * ty) -> ty -> ty
| TArray : ty -> nat -> ty
| TSlice : ty -> ty
| TProd : list ty -> ty
| TStruct : struct -> list gty -> ty
with gty : Set :=
(* FIXME: type vars *)
| GType : ty -> gty
| GRgn : rgn -> gty
| GFrac : frac -> gty
| GRgnOf : string -> path -> gty
| GCapOf : string -> path -> gty.

Inductive pat : Set :=
| PWild : pat
| PEnumTup : enum -> list (muta * string) -> pat
| PEnumRec : enum -> list (string * muta * string) -> pat.

Inductive prim : Set :=
| EBool : bool -> prim
| ENum : nat -> prim
| EUnit : prim.

Inductive expr : Set :=
| EPrim : prim -> expr
| EAlloc : expr -> expr
| ECopy : string -> path -> expr
| EBorrow : muta -> string -> path -> expr
| ESlice : muta -> string -> path -> expr -> expr -> expr
| EDrop : string -> path -> expr
| ELet : muta -> string -> expr -> expr -> expr
| EAssign : string -> path -> expr
(* FIXME: type abstraction *)
| ETApp : expr -> gty -> expr
| EFn : list (string * rgn * frac * ty) -> expr -> expr
| EMvFn : list (string * rgn * frac * ty) -> expr -> expr
| EApp : expr -> expr -> expr
| ESeq : expr -> expr -> expr
| EIf : expr -> expr -> expr -> expr
| EMatch : expr -> list (pat * expr) -> expr
| EFor : muta -> string -> expr -> expr -> expr
| EProd : list expr -> expr
| EArray : list expr -> expr
| EStructRec : struct -> list gty -> list (string * expr) -> expr
| EStructTup : struct -> list gty -> list expr -> expr
| EEnumRec : enum -> list gty -> list (string * expr) -> expr
| EEnumTup : enum -> list gty -> list expr -> expr.