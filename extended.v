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
| fun_type : type -> type -> type.

Definition type_dec : forall A B : type, {A = B} + {A <> B}.
decide equality.
apply var_dec.
Defined.

Inductive term : Set :=
| var_term : var -> term
| abs_term : (var * type) -> term -> term
| app_term : term -> term -> term.

Definition context := list (var * type).

Inductive assoc {A B : Set} (a : A) (b : B) : list (A * B) -> Prop :=
| assoc_base l : assoc a b ((a, b) :: l)
| assoc_step a' b' l : a <> a' -> assoc a b l -> assoc a b ((a', b') :: l).

Lemma assoc_B_unique {A B : Set} {l : list (A * B)} {a : A} {b1 b2 : B}
  (P1 : assoc a b1 l)
  (P2 : assoc a b2 l)
  : b1 = b2.
Proof.
induction l.

(* l = nil *)
inversion_clear P1.

(* l = (a0 :: l) *)
inversion P1 as [l' [eq_a_b1 eq_l'] | a' b' l' neq_a_a' P1' [eq_a'_b' eq_l'_l]].
  (* P1 is an assoc_base *)
  inversion P2 as [l'' [eq_a_b2 eq_ll'] | a' b' l'' neq_a_a' P2' [eq_a'_b' eq_l''_l]].
    (* P2 is an assoc_base *)
    rewrite <- eq_a_b2 in eq_a_b1.
    inversion_clear eq_a_b1.
    reflexivity.

    (* P2 is an assoc_step, which is impossible *)
    elim neq_a_a'.
    rewrite <- eq_a'_b' in eq_a_b1.
    inversion_clear eq_a_b1.
    reflexivity.

  (* P2 is an assoc_step *)
  inversion P2 as [l'' [eq_a_b2 eq_l''] | a'' b'' l'' neq_a'_a'' P2' [eq_a''_b'' eq_l''_l]].
    (* P2 is an assoc_base, which is impossible *)
    elim neq_a_a'.
    rewrite <- eq_a'_b' in eq_a_b2.
    inversion_clear eq_a_b2.
    reflexivity.

    (* P2 is an assoc_step, thus use induction step *)
    apply IHl.
      exact P1'.
      exact P2'.
Defined.

Lemma assoc_nil {A B : Set} {a : A} {b : B}
: ~assoc a b nil.
Proof.
intro P.
inversion_clear P.
Defined.

Lemma neg_assoc_cons {A B : Set} {a : A} {b : B}
  (x : A) (y : B)
  (ls : list (A * B))
  (np : ~assoc a b ls)
  (neq : x <> a)
  : ~assoc a b ((x, y) :: ls).
Proof.
intro ps.
inversion ps as [? eq | ? ? ? ? p].
  elim neq.
  symmetry.
  exact eq.

  elim np.
  exact p.
Defined.

Fixpoint lookup {A B : Set}
  (A_dec : forall x y : A, {x = y} + {x <> y})
  (l : list (A * B)) (a : A)
  {struct l}
  : {b : B | assoc a b l} + {forall b : B, ~assoc a b l} :=
match l as l0 return {b | assoc a b l0} + {forall b, ~assoc a b l0} with
| nil => inright _ (fun b => assoc_nil)
| (x, y) :: ls =>
  match A_dec x a with
  | left eq => inleft _ (exist _ y (eq_ind x (fun x' => assoc x' y ((x, y) :: ls)) (assoc_base x y ls) a eq))
  | right neq => match lookup A_dec ls a with
    | inleft (exist b Hb) => inleft _ (exist _ b (assoc_step a b x y ls (fun eq => False_ind False (neq (eq_sym eq))) Hb))
    | inright result => inright _ (fun b => neg_assoc_cons x y ls (fun p' => match result b p' return False with end) neq)
    end
  end
end.

Inductive has_type (g : context) : term -> type -> Prop :=
| var_has_type : forall v : var, forall A : type,
  assoc v A g -> has_type g (var_term v) A
| abs_has_type : forall v : var, forall M : term, forall A B : type,
  has_type ((v, A) :: g) M B -> has_type g (abs_term (v, A) M) (fun_type A B)
| app_has_type : forall M N : term, forall A B : type,
  has_type g M (fun_type A B) -> has_type g N A -> has_type g (app_term M N) B.

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

Lemma type_check_var_lookup_failure {g : context} {v : var}
  (NP : forall A : type, ~ assoc v A g)
  : forall A : type, ~ has_type g (var_term v) A.
Proof.
intro A.
intro Q.
inversion_clear Q as [? ? Q' | ? | ?].
apply (NP A).
exact Q'.
Defined.

Lemma type_check_abs_failure {g : context} {M : term} {v : var} {A : type}
  (NP : forall B : type, ~ has_type ((v, A) :: g) M B)
  : forall B : type, ~ has_type g (abs_term (v, A) M) B.
Proof.
intro B.
intro Q.
inversion_clear Q as [? | ? ? ? C Q' | ?].
apply (NP C).
exact Q'.
Defined.

Lemma type_check_app_failure_var {g : context} {M N : term} {v : var}
  (P : has_type g M (var_type v))
  : forall B : type, ~ has_type g (app_term M N) B.
Proof.
intro B.
intro Q.
inversion_clear Q as [? | ? | ? ? A ? QM QN].
apply (type_inconsistency QM P).
Defined.

Lemma type_check_app_failure_eq {g : context} {M N : term} {A CA CB : type}
  (HN : has_type g N A)
  (HM : has_type g M (fun_type CA CB))
  (neq : CA <> A)
  : forall B : type, ~ has_type g (app_term M N) B.
Proof.
intro B.
intro HMN.
inversion_clear HMN as [? | ? | ? ? A' ? HM' HN'].
rewrite (term_has_unique_type N HN' HN) in HM'.
elim neq.
assert (fun_type CA CB = fun_type A B) as eq.
apply (term_has_unique_type M HM HM').
inversion_clear eq.
reflexivity.
Defined.

Lemma type_check_app_failure_N {g : context} {M N : term}
  (NHN : forall A : type, ~ has_type g N A)
  : forall B : type, ~ has_type g (app_term M N) B.
Proof.
intro B.
intro HMN.
inversion_clear HMN as [? | ? | ? ? A ? HM HN].
destruct (NHN A).
exact HN.
Defined.

Lemma type_check_app_failure_M {g : context} {M N : term}
  (NHM : forall A : type, ~ has_type g M A)
  : forall A : type, ~ has_type g (app_term M N) A.
Proof.
intro B.
intro HMN.
inversion_clear HMN as [? | ? | ? ? A ? HM HN].
destruct (NHM (fun_type A B)).
exact HM.
Defined.

Fixpoint type_check (g : context) (T : term) {struct T}
: {A : type | has_type g T A} + {forall A : type, ~has_type g T A} :=
match T as T0 return {A : type | has_type g T0 A} + {forall A : type, ~has_type g T0 A} with
| var_term v =>
  match lookup var_dec g v with
  | inleft (exist A P) => inleft _ (exist _ _ (var_has_type g v A P))
  | inright NP => inright _ (type_check_var_lookup_failure NP)
  end
| abs_term (v, A) M =>
  match type_check ((v, A) :: g) M with
  | inleft (exist B HB) => inleft _ (exist _ _ (abs_has_type g v M A B HB))
  | inright NP => inright _ (type_check_abs_failure NP)
  end
| app_term M N =>
  match type_check g M with
  | inleft (exist C HM as Msig) =>
    match type_check g N with
    | inleft (exist A HN as Nsig) =>
      match C as C0 return (has_type g M C0 -> {C : type | has_type g (app_term M N) C} + {forall C : type, ~has_type g (app_term M N) C}) with
      | var_type v => fun HM : has_type g M (var_type v) => inright _ (type_check_app_failure_var HM)
      | fun_type CA CB => fun HM' : has_type g M (fun_type CA CB) =>
        match type_dec CA A with
        | left eq => inleft _
          (exist _ _
            (app_has_type g M N CA CB HM'
              (eq_ind_r _ HN eq)
            ))
        | right neq => inright _ (type_check_app_failure_eq HN HM' neq)
        end
      end HM
    | inright NHN => inright _ (type_check_app_failure_N NHN)
    end
  | inright NHM => inright _ (type_check_app_failure_M NHM)
  end
end.

Definition type_check_simple (g : context) (T : term) : option type :=
match type_check g T with
| inleft (exist x _) => Some x
| inright _ => None
end.

Definition nat_type := var_type "Nat".
Definition gamma := cons ("n", nat_type) nil.

Compute type_check_simple gamma (app_term (abs_term ("x", nat_type) (var_term "n")) (var_term "n")).