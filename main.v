Require Import String.
Open Local Scope string_scope.

Require Import Lists.List.

Definition option_dec {A : Type}
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
| abs_term : (var * type) -> term -> term
| app_term : term -> term -> term
.

Definition context := list (var * type).

Definition assoc {A B : Set}
  (l : list (A * B)) 
  (a : A)
  (b : B)
  : Prop :=
    In (a, b) l.

Definition sig_assoc_cons {A B : Set}
  (x : A) (y : B)
  (ls : list (A * B)) (a : A) (bSig : {b : B | assoc ls a b})
  : {b : B | assoc ((x, y) :: ls) a b}.
Proof.
destruct bSig as (b, Hb).
exists b.
unfold assoc.
apply in_cons.
exact Hb.
Qed.

Fixpoint lookup {A B : Set}
  (P : forall x y : A, {x = y} + {x <> y})
  (l : list (A * B)) (a : A)
  {struct l}
  : option {b : B | assoc l a b} :=
match l as l0 return option {b : B | assoc l0 a b} with
| nil => None
| (x, y) :: ls =>
  match P x a with
  | left eq => Some (exist
    (assoc ((x, y) :: ls) a)
    y
    (eq_ind x (fun x0 : A => assoc ((x, y) :: ls) x0 y) (in_eq (x, y) ls) a eq))
  | right _ => option_map (sig_assoc_cons x y ls a) (lookup P ls a)
  end
end.

Inductive has_type (g : context) : term -> type -> Prop :=
| var_has_type : forall v : var, forall A : type,
  assoc g v A -> has_type g (var_term v) A
| abs_has_type : forall v : var, forall M : term, forall A B : type,
  has_type ((v, A) :: g) M B -> has_type g (abs_term (v, A) M) (fun_type A B)
| app_has_type : forall M N : term, forall A B : type,
  has_type g M (fun_type A B) -> has_type g N A -> has_type g (app_term M N) B
.

Definition assoc_translate (g : context) (v : var) (Asig : {A : type | assoc g v A})
 : {A : type | has_type g (var_term v) A} :=
 let (A, HA) := Asig in
   exist (fun A : type => has_type g (var_term v) A) A (var_has_type g v A HA).

Fixpoint type_check (g : context) (T : term) {struct T}
 : option {A : type | has_type g T A} :=
 match T as T0 return option {A : type | has_type g T0 A} with
 | var_term v => option_map (assoc_translate g v) (lookup var_dec g v)
 | abs_term (v, A) M => match type_check ((v, A) :: g) M with
   | Some (exist B HB) => Some (exist
       (fun C : type => has_type g (abs_term (v, A) M) C)
       (fun_type A B)
       (abs_has_type g v M A B HB)
     )
   | _ => None
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

Definition gamma := cons ("x", var_type "a") (cons ("n", var_type "Nat") nil).

Compute type_check gamma (app_term (abs_term ("x", var_type "A") (var_term "n")) (var_term "n")).