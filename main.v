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

Lemma it_is
  (A B : Set)
  (l : list (A * B))
  (a : A)
  (b : B)
  (p : assoc A B l a b)
  : {b : B | assoc A B l a b}.
Proof.
exists b.
exact p.
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

Fixpoint has_type
  (g : context)
  (t : term)
  (A : type)
  {struct t}
  : Prop :=
    match t with
    | var_term v => assoc var type g v A
    | abs_term v abst =>
        match A with
        | fun_type B C => assoc var type g v B /\ has_type g abst C
        | _ => False
        end
    | app_term ft appt =>
        exists B : type,
          has_type g appt B /\ has_type g ft (fun_type B A)
    end.

Definition type_lookup
  (g : context)
  (v : var)
  : option {A : type | has_type g (var_term v) A} :=
    lookup var type var_dec g v.

Definition make_fun
  (g : context)
  (v : var)
  (Aopt : option {A : type | has_type g (var_term v) A})
  (r : term)
  (Bopt : option {B : type | has_type g r B})
  : option {C : type | has_type g (abs_term v r) C} :=
    match (Aopt, Bopt) with
    | (Some (exist A HA), Some (exist B HB)) => Some (
        exist
          (fun C : type => has_type g (abs_term v r) C)
          (fun_type A B)
          (conj HA HB)
      )
    | _ => None
  end.

Fixpoint type_check
  (g : context)
  (t : term)
  {struct t}
  : option {A : type | has_type g t A}.
Proof.
refine
 match t as t0 return option {A : type | has_type g t0 A} with
 | var_term v => type_lookup g v
 | abs_term v ft => make_fun g v (type_lookup g v) ft (type_check g ft)
 | app_term M N => 
   match (type_check g M, type_check g N) with
   | (Some (exist C HC as Msig), Some (exist B HB as Nsig)) =>
     match C as C0 return has_type g M C0 -> option {A : type | has_type g (app_term M N) A} with
     | fun_type CB CA =>
         (* force type of HCf via this subfunction *)
         fun HCf : has_type g M (fun_type CB CA) =>
           match type_dec CB B with
           | left e => Some (exist
               (fun A : type => has_type g (app_term M N) A)
                 CA
                 (ex_intro 
                   (fun B0 : type => has_type g N B0 /\ has_type g M (fun_type B0 CA)) CB
                   (conj (eq_ind_r (has_type g N) HB e) HCf)
                 )
               )
           | right _ => None
           end
     | var_type _ => fun _ => None
     end HC
   | _ => None
  end
 end.