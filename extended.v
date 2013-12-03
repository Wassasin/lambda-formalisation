Require Import String.
Open Local Scope string_scope.

Require Import List.

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

Lemma sig_assoc_cons {A B : Set}
  {A_dec : forall x y : A, {x = y} + {x <> y}}
  {B_dec : forall x y : B, {x = y} + {x <> y}}
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
Defined.

Lemma neg_assoc_cons {A B : Set} {a : A} {b : B}
  {A_dec : forall x y : A, {x = y} + {x <> y}}
  {B_dec : forall x y : B, {x = y} + {x <> y}}
  (x : A) (y : B)
  (ls : list (A * B))
  (np : ~assoc A_dec B_dec ls a b)
  (neq : x <> a)
  : ~assoc A_dec B_dec ((x, y) :: ls) a b.
Proof.
intro q.
unfold assoc in np.
unfold assoc in q.
destruct (A_dec x a) as [eq | ?].
elim neq.
exact eq.

elim np.
exact q.
Defined.

Lemma assoc_nil {A B : Set} {a : A} {b : B}
  {A_dec : forall x y : A, {x = y} + {x <> y}}
  {B_dec : forall x y : B, {x = y} + {x <> y}}
: ~assoc A_dec B_dec nil a b.
Proof.
unfold assoc.
intro.
contradiction.
Defined.

Lemma assoc_B_unique {A B : Set} {l : list (A * B)} {a : A} {b1 b2 : B}
  {A_dec : forall x y : A, {x = y} + {x <> y}}
  {B_dec : forall x y : B, {x = y} + {x <> y}}
  (P1 : assoc A_dec B_dec l a b1)
  (P2 : assoc A_dec B_dec l a b2)
  : b1 = b2.
Proof.

induction l.

unfold assoc in *.
contradiction.

destruct a0 as (x, y).

unfold assoc in P1.
unfold assoc in P2.
destruct (A_dec x a).
destruct (B_dec b1 y).
destruct (B_dec b2 y).

rewrite e0.
rewrite e1.
reflexivity.

contradiction.
contradiction.

apply IHl.
exact P1.
exact P2.
Defined.

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
  | left eq => _
  | right neq => match lookup A B A_dec B_dec ls a with
    | inleft result => inleft
      (forall b : B, ~ assoc A_dec B_dec ((x, y) :: ls) a b)
      (sig_assoc_cons x y ls a result neq)
    | inright result => inright
      {b : B | assoc A_dec B_dec ((x, y) :: ls) a b}
      (fun b : B => neg_assoc_cons x y ls (result b) neq)
    end
  end
end.

apply inleft.
exists y.
unfold assoc.
destruct (A_dec x a).
destruct (B_dec y y).
exact I.
elim n.
reflexivity.
elim n.
exact eq.
Defined.

Inductive has_type (g : context) : term -> type -> Prop :=
| var_has_type : forall v : var, forall A : type,
  assoc var_dec type_dec g v A -> has_type g (var_term v) A
| abs_has_type : forall v : var, forall M : term, forall A B : type,
  has_type ((v, A) :: g) M B -> has_type g (abs_term (v, A) M) (fun_type A B)
| app_has_type : forall M N : term, forall A B : type,
  has_type g M (fun_type A B) -> has_type g N A -> has_type g (app_term M N) B
.

Fixpoint term_has_unique_type {g : context} {A B : type}
  (T : term)
  (P : has_type g T A)
  (Q : has_type g T B)
  {struct T}
  : A = B.
Proof.
destruct T as [v | p M | M N].

inversion_clear P as [? ? P' | ? | ?].
inversion_clear Q as [? ? Q' | ? | ?].
rewrite (assoc_B_unique P' Q').
reflexivity.

destruct p as (v, C).
inversion_clear P as [? | ? ? ? B0 P' | ?].
inversion_clear Q as [? | ? ? ? B1 Q' | ?].
rewrite (term_has_unique_type ((v, C) :: g) B0 B1 M P' Q').
reflexivity.

inversion_clear P as [? | ? | ? ? C0 ? PM PN].
inversion_clear Q as [? | ? | ? ? C1 ? QM QN].
assert (fun_type C0 A = fun_type C1 B) as eq.
apply (term_has_unique_type g (fun_type C0 A) (fun_type C1 B) M PM QM).
inversion_clear eq.
reflexivity.
Defined.

Lemma type_inconsistency {g : context} {T : term} {A B : type} {v : var}
  (P : has_type g T (fun_type A B))
  (Q : has_type g T (var_type v))
  : False.
Proof.
elim (type_dec (fun_type A B) (var_type v)).

intro eq.
inversion eq.

intro neq.
elim neq.
apply (term_has_unique_type T P Q).
Defined.


Lemma type_check_var_lookup_failure {g : context} {v : var} {A : type}
  (NP : forall b : type, ~ assoc var_dec type_dec g v b)
  (P : has_type g (var_term v) A)
  : False.
Proof.
inversion_clear P as [? ? P' | ? | ?].
apply (NP A).
exact P'.
Defined.

Fixpoint type_check (g : context) (T : term) {struct T}
 : {A : type | has_type g T A} + {forall A : type, ~has_type g T A}.
refine
 match T as T0 return {A : type | has_type g T0 A} + {forall A : type, ~has_type g T0 A} with
 | var_term v =>
   match lookup var_dec type_dec g v with
   | inleft (exist A P) => inleft
     (forall A : type, ~ has_type g (var_term v) A)
     (exist (fun A : type => has_type g (var_term v) A) A (var_has_type g v A P))
   | inright NP => inright
     {A : type | has_type g (var_term v) A}
     (fun (A : type) (H : has_type g (var_term v) A) => type_check_var_lookup_failure NP H)
   end
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

destruct (type_check ((v, A) :: g) M).

Show Proof.

apply inleft.
destruct s as (B, HB).
exists (fun_type A B).
apply (abs_has_type g v M A B).
exact HB.

apply inright.
intro B.
intro.
inversion_clear H.
apply (n B0).
exact H0.

apply inright.
intro.
intro.
inversion_clear H.
apply (type_inconsistency H0 _H).

apply inleft.
exists CB.
apply (app_has_type g M N CA CB).
exact HCf.
rewrite eq.
exact HA.

apply inright.
intro CB0.
intro.

inversion_clear H.
rewrite (term_has_unique_type N H1 HA) in H0.
elim n.
assert (fun_type CA CB = fun_type A CB0) as eq.
apply (term_has_unique_type M HCf H0).
inversion_clear eq.
reflexivity.

apply inright.
intro B.
intro.
inversion_clear H.
destruct (n A).
exact H1.

apply inright.
intro.
intro.
inversion_clear H.
destruct (n (fun_type A0 A)).
exact H0.
Defined.

Definition type_check_simple (g : context) (T : term)
 : option type :=
 match type_check g T with
 | inleft (exist x _) => Some x
 | inright _ => None
 end.

Definition nat_type := var_type "Nat".
Definition gamma := cons ("x", nat_type) (cons ("n", nat_type) nil).

Compute type_check_simple gamma (app_term (abs_term ("x", nat_type) (var_term "n")) (var_term "n")).