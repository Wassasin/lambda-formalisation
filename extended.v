Require Import String.
Open Local Scope string_scope.

Require Import FSets.FMapInterface.

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

Definition context := var -> option type.

Fixpoint assoc {A B : Set}
  (A_dec : forall x y : A, {x = y} + {x <> y})
  (B_dec : forall x y : B, {x = y} + {x <> y})
  (l : list (A * B)) 
  (a : A)
  (b : B)
  {struct l}
  : Prop :=
match l with
| nil => False
| (x, y) :: ls =>
  match A_dec x a with
  | right _ => assoc A_dec B_dec ls a b
  | left _ =>
    match B_dec b y with
    | left _ => True
    | right _ => False
    end
  end
end.

Definition sig_assoc_cons {A B : Set}
  (A_dec : forall x y : A, {x = y} + {x <> y})
  (B_dec : forall x y : B, {x = y} + {x <> y})
  (x : A) (y : B)
  (ls : list (A * B))
  (a : A)
  (bSig : {b : B | assoc A_dec B_dec ls a b})
  (neq : x <> a)
  : {b : B | assoc A_dec B_dec ((x, y) :: ls) a b}.
Proof.
destruct bSig as (b, Hb).
exists b.
unfold assoc.
destruct (A_dec x a).
elim neq.
exact e.
exact Hb.
Qed.

Definition neg_assoc_cons {A B : Set} {a : A} {b : B}
  (A_dec : forall x y : A, {x = y} + {x <> y})
  (B_dec : forall x y : B, {x = y} + {x <> y})
  (x : A) (y : B)
  (ls : list (A * B))
  (p : ~assoc A_dec B_dec ls a b)
  (neq : x <> a)
  : ~assoc A_dec B_dec ((x, y) :: ls) a b.
Proof.
intro.
unfold assoc in p.
unfold assoc in H.
destruct (A_dec x a).
elim neq.
exact e.

elim p.
exact H.
Qed.

Definition assoc_nil {A B : Set} {a : A} {b : B}
  {A_dec : forall x y : A, {x = y} + {x <> y}}
  {B_dec : forall x y : B, {x = y} + {x <> y}}
: ~assoc A_dec B_dec nil a b.
Proof.
unfold assoc.
intro.
contradiction.
Qed.

Fixpoint lookup {A B : Set}
  (A_dec : forall x y : A, {x = y} + {x <> y})
  (B_dec : forall x y : B, {x = y} + {x <> y})
  (l : list (A * B)) (a : A)
  {struct l}
  : {b : B | assoc A_dec B_dec l a b} + {forall b : B, ~assoc A_dec B_dec l a b}.
Proof.
refine
match l as l0 return {b : B | assoc A_dec B_dec l0 a b} + {forall b : B, ~assoc A_dec B_dec l0 a b} with
| nil => inright {b : B | assoc A_dec B_dec nil a b} (fun b : B => assoc_nil)
| (x, y) :: ls =>
  match A_dec x a with
  | left eq => inleft (forall b : B, ~ assoc A_dec B_dec ((x, y) :: ls) a b)
                   (exist (fun b : B => assoc A_dec B_dec ((x, y) :: ls) a b) y
                      (eq_ind x (fun a0 : A => assoc A_dec B_dec ((x, y) :: ls) a0 y)
                         (in_eq (x, y) ls) a eq))
  | right neq => match lookup A_dec B_dec ls a with
    | inleft result => inleft (forall b : B, ~ assoc ((x, y) :: ls) a b)
                       (let (b, Hb) := result in
                        exist (fun b0 : B => In (a, b0) ((x, y) :: ls)) b
                          (in_cons (x, y) (a, b) ls Hb))
    | inright result => inright {b : B | assoc ((x, y) :: ls) a b}
                       (fun b : B => neg_assoc_cons x y ls (result b) neq)
    end
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

Definition discriminate_has_type {g : context} {T : term} {A B : type} {v : var}
  (P : has_type g T (fun_type A B))
  (Q : has_type g T (var_type v))
  : False.
Proof.
destruct T.
inversion_clear Q.
inversion_clear P.
unfold assoc in H0.
unfold assoc in H.




Fixpoint type_check (g : context) (T : term) {struct T}
 : {A : type | has_type g T A} + {forall A : type, ~has_type g T A}.
Proof.
refine
 match T as T0 return {A : type | has_type g T0 A} + {forall A : type, ~has_type g T0 A} with
 | var_term v => _
 | abs_term (v, A) M => _
 | app_term M N =>
   match (type_check g M, type_check g N) with
   | (inleft (exist C HC as Msig), inleft (exist A HA as Nsig)) =>
     match C as C0 return (has_type g M C0 -> {C : type | has_type g (app_term M N) C} + {forall C : type, ~has_type g (app_term M N) C}) with
     | var_type v => fun _ => _
     | fun_type CA CB => fun HCf : has_type g M (fun_type CA CB) =>
       match type_dec CA A with
       | left eq => _
       | right _ => _
       end
     end HC
   | _ => _
   end
 end.

destruct (lookup var_dec g v).
apply inleft.
destruct s.
exists x.
apply var_has_type.
exact a.

apply inright.
intro.
intro.
inversion H.
apply (n A).
exact H1.

destruct (type_check ((v, A) :: g) M).
apply inleft.
destruct s as (B, HB).
exists (fun_type A B).
apply (abs_has_type g v M A B).
exact HB.

Show Proof.

apply inright.
intro B.
intro.
inversion H.
apply (n B0).
exact H4.

apply inright.
intro.
intro.
inversion H.
inversion _H.

Print has_type_ind.

(*intro.
intro.
inversion H.*)






Definition gamma := cons ("x", var_type "a") (cons ("n", var_type "Nat") nil).

Compute type_check gamma (app_term (abs_term ("x", var_type "A") (var_term "n")) (var_term "n")).