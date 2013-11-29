Require Import String.
Open Local Scope string_scope.

Require Import Lists.List.
Require Import Strings.String.
Require Import Structures.Equalities.

Definition option_dec
  (A : Type)
  (P : forall x y : A, {x = y} + {x <> y})
  (x y : option A)
  : {x = y} + {x <> y}.
decide equality.
Defined.

Definition var := string.
Definition var_dec := string_dec.

Inductive type : Set :=
| var_type : var -> type
| fun_type : type -> type -> type
.

Definition type_dec : forall A B : type, {A = B} + {A <> B}.
decide equality.
apply var_dec.
Defined.

Inductive term : Set :=
| var_term : var -> term
| abs_term : var -> term -> term
| app_term : term -> term -> term
.

Definition context := list (var * type).

Definition assoc
  (A B : Set)
  (l : list (A * B)) 
  (a : A)
  (b : B)
  : Prop :=
    In (a, b) l.

Lemma lookup_found_as_first
  (A B : Set)
  (ls : list (A * B))
  (a : A)
  (b : B)
  : assoc A B ((a, b) :: ls) a b.
Proof.
unfold assoc.
unfold In.
left.
reflexivity.
Qed.

Lemma assocr_move
  (A B : Set)
  (ls : list (A * B))
  (a x : A)
  (y : B)
  (e : {b : B | assoc A B ((a, y) :: ls) a b})
  (p : a = x)
  : {b : B | assoc A B ((x, y) :: ls) a b}.
Proof.
destruct e.
exists x0.
elim p.
exact a0.
Qed.

Definition assoc_cons
  (A B : Set)
  (x : A)
  (y : B)
  (ls : list (A * B))
  (a : A)
  (b : B)
  (p : assoc A B ls a b)
  : assoc A B ((x, y) :: ls) a b. 
Proof.
unfold assoc.
apply in_cons.
exact p.
Qed.

Definition sig_assoc_cons
  (A B : Set)
  (x : A)
  (y : B)
  (ls : list (A * B))
  (a : A)
  (b : {b : B | assoc A B ls a b})
  : {b : B | assoc A B ((x, y) :: ls) a b}.
Proof.
destruct b.
exists x0.
apply assoc_cons.
exact a0.
Qed.

Fixpoint lookup
  (A B : Set)
  (P : forall x y : A, {x = y} + {x <> y})
  (l : list (A * B))
  (a : A)
  {struct l}
  : option {b : B | assoc A B l a b} :=
    match l return option {b : B | assoc A B l a b} with
    | nil => None
    | (x, y) :: ls => match P a x with
        left p => Some (assocr_move A B ls a x y (
            @exist
              B
              (fun q => assoc A B ((a, y) :: ls) a q)
              y
              (lookup_found_as_first A B ls a y)
          ) p)
      | right _ => option_map (sig_assoc_cons A B x y ls a) (lookup A B P ls a)
      end
    end.

Inductive has_type (g : context) : term -> type -> Prop :=
| var_has_type : forall v : var, forall A : type,
  assoc var type g v A -> has_type g (var_term v) A
| abs_has_type : forall v : var, forall M : term, forall A B : type,
  has_type ((v, A) :: g) M B -> has_type g (abs_term v M) (fun_type A B)
| app_has_type : forall M N : term, forall A B : type,
  has_type g M (fun_type A B) -> has_type g N A -> has_type g (app_term M N) B
.

Definition assoc_translate (g : context) (v : var) (Asig : {A : type | assoc var type g v A})
 : {A : type | has_type g (var_term v) A} :=
 let (A, HA) := Asig in
   exist (fun A : type => has_type g (var_term v) A) A (var_has_type g v A HA).

Definition make_var_type (g : context) (v : var)
 : option {A : type | has_type g (var_term v) A} :=
 option_map (assoc_translate g v) (lookup var type var_dec g v).

Definition make_abs_type (g : context) (v : var) (F : term)
 (A : type)
 (HA : has_type g (var_term v) A)
 (Bopt : option {B : type | has_type ((v, A) :: g) F B})
 : option {C : type | has_type g (abs_term v F) C} :=
 match Bopt with
 | Some (exist B HB) => Some (exist
     (fun C : type => has_type g (abs_term v F) C)
     (fun_type A B)
     (abs_has_type g v F A B HB)
   )
 | _ => None
 end.

Fixpoint type_check (g : context) (T : term) {struct T}
 : option {A : type | has_type g T A} :=
 match T as T0 return option {A : type | has_type g T0 A} with
 | var_term v => make_var_type g v
 | abs_term v M =>
   match make_var_type g v with
   | Some (exist A HA) => make_abs_type g v M A HA (type_check ((v, A) :: g) M)
   | None => None
   end
 | app_term M N => 
   match (type_check g M, type_check g N) with
   | (Some (exist C HC as Msig), Some (exist A HA as Nsig)) =>
     match C as C0 return (has_type g M C0 -> option {C : type | has_type g (app_term M N) C}) with
     | var_type v => fun _ => None
     | fun_type CA CB => fun HCf : has_type g M (fun_type CA CB) =>
       match type_dec CA A with
       | left eq => Some (exist
           (fun C0 : type => has_type g (app_term M N) C0)
           CB
           (app_has_type g M N CA CB HCf (eq_ind_r (has_type g N) HA eq))
         )
       | right _ => None
       end
     end HC
   | _ => None
  end
 end.