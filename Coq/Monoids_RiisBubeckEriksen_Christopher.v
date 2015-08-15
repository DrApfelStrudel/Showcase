(* Monoids.v *)
(* dTFP 2014-2015, Q3 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: Christopher Riis Bubeck Eriksen *)
(* Student number: 201206065 *)

(* Contents in line numbers:

   -- About monoids --

   Equivalence relations :::::::::::::::::: 45
   Monoids :::::::::::::::::::::::::::::::: 106

   -- Types and relations --

   Natural numbers :::::::::::::::::::::::: 188
   Booleans ::::::::::::::::::::::::::::::: 1014
   2x2 matrices with natural numbers :::::: 2137 
   Polymorphic endofunctions :::::::::::::: 2972
   Polymorphic lists :::::::::::::::::::::: 3247
   Polymorphic lazy lists ::::::::::::::::: 3650
   Co-inductive natural numbers ::::::::::: 4094
   Polymorphic 2x2 matrices ::::::::::::::: 4395

   -- Binary operations --

   Addition ::::::::::::::::::::::::::::::: 417
   Multiplication ::::::::::::::::::::::::: 644
   LEQ :::::::::::::::::::::::::::::::::::: 1162
   Minimum :::::::::::::::::::::::::::::::: 1311
   Maximum :::::::::::::::::::::::::::::::: 1615
   Conjunction :::::::::::::::::::::::::::: 1839
   Disjunction :::::::::::::::::::::::::::: 1985
   Matrix addition :::::::::::::::::::::::: 2221
   Matrix multiplication :::::::::::::::::: 2433
   Composition :::::::::::::::::::::::::::: 3076
   List append :::::::::::::::::::::::::::: 3421
   Lazy list append ::::::::::::::::::::::: 3802
   Co-recursive minimum ::::::::::::::::::: 4215
   Polymorphic matrix addition :::::::::::: 4520

*)

(* An equality relation on T is an equivalence relation if it is reflexive, 
   symmetric and transitive. *)

Definition specification_of_a_reflexive_relation (T : Type)
                    (eqT : T -> T -> Prop) :=
  forall a : T,
    eqT a a.

Definition specification_of_a_symmetric_relation (T : Type)
                    (eqT : T -> T -> Prop) :=
  forall a b : T,
    eqT a b -> eqT b a.

Definition specification_of_a_transitive_relation (T : Type) 
                (eqT : T -> T -> Prop) :=
  forall x y z : T,
    eqT x y ->
    eqT y z ->
    eqT x z.

Definition specification_of_an_equivalence_relation 
           (T : Type)
           (eqT : T -> T -> Prop) :=
  specification_of_a_reflexive_relation T eqT /\ 
  specification_of_a_symmetric_relation T eqT /\ 
  specification_of_a_transitive_relation T eqT.

(* A binary operation . on T preserves an equality relation ~ at T if
   for all a b c d in T, (a ~ b /\ c ~ d) -> a . c ~ b . d. This
   also mean that we can 'rewrite' under ~. *)   

Definition specification_of_preservation (T : Type)
                             (eqT : T -> T -> Prop)
                             (Dot : T -> T -> T) :=
  forall a b c d : T,
    eqT a b ->
    eqT c d ->
    eqT (Dot a c) (Dot b d).

(* Using . as infix for a binary operation on T, . is associative for a
   equality relation ~ on T if (a . b) . c ~ a . (b . c) *)  

Definition specification_of_associativity
           (T : Type)
           (eqT : T -> T -> Prop)
           (Dot : T -> T -> T) :=
  forall a b c : T,
    eqT (Dot (Dot a b) c) (Dot a (Dot b c)).

(* Using . as infix for a binary operation on T, e of Type T is a neutral element
   for . and a equality relation ~ on T if a . e ~ a and e . a ~ a for any a 
   of type T. *)

Definition specification_of_neutrality 
           (T : Type)
           (eqT : T -> T -> Prop)
           (Dot : T -> T -> T)
           (e : T) :=
  (forall a : T, eqT (Dot a e) a) /\
  (forall a : T, eqT (Dot e a) a).

(* A type T form a Monoid with a binary operation . on T and a relation ~ on T if
   . is associative for ~ and there exists an element e of Type T such that e is
   neutral for . and ~. Furthermore ~ needs to be an equivalence relation and
   . must preserve ~. *) 

Definition T_and_Dot_form_a_Monoid_under_eqT 
           (T : Type)
           (eqT : T -> T -> Prop)
           (Dot : T -> T -> T) :=
  specification_of_an_equivalence_relation T eqT
  /\
  specification_of_preservation T eqT Dot
  /\
  (specification_of_associativity T eqT Dot)
  /\
  (exists e : T, specification_of_neutrality T eqT Dot e).

(* It can be shown that if T is a monoid with . and ~ then there exists one and 
   only one neutral element e of type T. This follows from the symmetric and 
   transitive properties of ~. *)

Lemma the_neutral_element_in_a_Monoid_is_unique :
  forall T : Type,
    forall eqT : T -> T -> Prop,
    forall Dot : T -> T -> T,
      T_and_Dot_form_a_Monoid_under_eqT T eqT Dot ->
      forall e1 e2 : T,
        specification_of_neutrality T eqT Dot e1 ->
        specification_of_neutrality T eqT Dot e2 ->
        eqT e1 e2.
Proof.
  intros T eqT Dot H_Monoid e1 e2 H_e1 H_e2.

  unfold specification_of_neutrality in H_e1.
  destruct H_e1 as [H_e2_e1 _].
  unfold specification_of_neutrality in H_e2.
  destruct H_e2 as [_ H_e2_e1'].

  unfold T_and_Dot_form_a_Monoid_under_eqT in H_Monoid.
  destruct H_Monoid as [H_eqT _].
  unfold specification_of_an_equivalence_relation in H_eqT.
  destruct H_eqT as [_ [H_eqT_s H_eqT_t]].
  unfold specification_of_a_symmetric_relation in H_eqT_s.
  unfold specification_of_a_transitive_relation in H_eqT_t.

  assert (H_e2_e1'' := H_e2_e1 e2).
  assert (H_e2_e1''' := H_e2_e1' e1).
  apply H_eqT_s in H_e2_e1'''.
  exact (H_eqT_t e1 (Dot e2 e1) e2 H_e2_e1''' H_e2_e1'').
Qed.

(* If . is a binary operation on T; ~ is an equivalence relation at T;
   and . preserves ~, then for any element e which is neutral for . and ~,
   (x . e) . y ~ x . y. This follows from the preservation of . and the
   reflexive property of ~. *)

Lemma about_the_neutral_element_in_a_Monoid :
  forall T : Type,
  forall eqT : T -> T -> Prop,
  forall Dot : T -> T -> T,
    T_and_Dot_form_a_Monoid_under_eqT T eqT Dot ->
    forall e : T, 
      specification_of_neutrality T eqT Dot e ->
      forall x y : T,
        eqT (Dot (Dot x e) y) (Dot x y).
Proof.                
  intros T eqT Dot H_Monoid e H_e x y.
  unfold specification_of_neutrality in H_e.
  destruct H_e as [H_e_x _].

  unfold T_and_Dot_form_a_Monoid_under_eqT in H_Monoid.
  destruct H_Monoid as [H_eqT [H_Dot _]].
  unfold specification_of_preservation in H_Dot.
  apply (H_Dot (Dot x e) x y y).
    exact (H_e_x x).
  
    unfold specification_of_an_equivalence_relation in H_eqT.
    destruct H_eqT as [H_eqT_r [H_eqT_s H_eqT_t]].
    unfold specification_of_a_reflexive_relation in H_eqT_r.
    exact (H_eqT_r y).
Qed.
 
(* A natural number is either Zero or 
   the successor of another natural number. *)

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

(* Two natural numbers are equal if they both have the same amount of 
   successor applications. *)

Fixpoint eq_Nat (m n : Nat) : Prop :=
  match m with
      | O => match n with
                 | O => True
                 | S n' => False
             end
      | S m' => match n with
                    | O => False
                    | S n' => eq_Nat m' n'
                end
  end.

Notation "A =N= B" := (eq_Nat A B) (at level 70, right associativity).

(* Unfolding eq_Nat lemmas *)

Lemma unfold_eq_Nat_O_O :
  O =N= O.
Proof.
  unfold eq_Nat.
  exact I.
Qed.

Lemma unfold_eq_Nat_O_S :
  forall n' : Nat,
    ~(O =N= S n').
Proof.
  intros n' H_eq_Nat.
  unfold eq_Nat in H_eq_Nat.
  exact H_eq_Nat.
Qed.

Lemma unfold_eq_Nat_S_O :
  forall m' : Nat,
    ~ (S m' =N= O).
Proof.
  intros n' H_eq_Nat.
  unfold eq_Nat in H_eq_Nat.
  exact H_eq_Nat.
Qed.

Lemma unfold_eq_Nat_S_S :
  forall m n : Nat,
    (m =N= n) <-> (S m =N= S n).
Proof.
  intros m n.
  unfold eq_Nat; fold eq_Nat.
  split; intro H; exact H.
Qed.

(* It follows from induction that eq_Nat is reflexive since
   O =N= O; and S n =N= S n if n =N= n. *)

Lemma eq_Nat_is_reflexive :
  specification_of_a_reflexive_relation Nat eq_Nat.
Proof.
  unfold specification_of_a_reflexive_relation.
  intro a.
  induction a as [ | a' IHa'].
    exact unfold_eq_Nat_O_O.

    apply -> (unfold_eq_Nat_S_S a' a') in IHa'.
    exact IHa'.
Qed.

(* It follows from induction that eq_Nat is symmetric. It is noteworthy that
   if b =N= O, then b must be O, and if b =N= S n, then b must be S b' for some
   b'. *)

Lemma eq_Nat_is_symmetric :
  specification_of_a_symmetric_relation Nat eq_Nat.
Proof.
  unfold specification_of_a_symmetric_relation.
  intro a.
  induction a as [ | a' IHa'].
    intros b H_eq.
    destruct b as [ | b'].
      exact H_eq.

      contradiction (unfold_eq_Nat_O_S b' H_eq).
    
    intros b H_eq.
    destruct b as [ | b'].
      contradiction (unfold_eq_Nat_S_O a' H_eq).

      apply (unfold_eq_Nat_S_S a' b') in H_eq.
      apply (IHa' b') in H_eq.
      apply -> (unfold_eq_Nat_S_S b' a') in H_eq.
      exact H_eq.
Qed.

(* It also follows from induction that eq_Nat is transitive. *)

Lemma eq_Nat_is_transitive :
  specification_of_a_transitive_relation Nat eq_Nat.
Proof.
  unfold specification_of_a_transitive_relation.
  intro x.
  induction x as [ | x' IHx'].
    intros y z H_xy H_yz.
    destruct y as [ | y'].
      exact H_yz.
      contradiction (unfold_eq_Nat_O_S y' H_xy).

    intros y z H_xy H_yz.
    destruct y as [ | y'].
      contradiction (unfold_eq_Nat_S_O x' H_xy).

      destruct z as [ | z'].
        contradiction (unfold_eq_Nat_S_O y' H_yz).

        apply -> (unfold_eq_Nat_S_S x' z').
        apply (unfold_eq_Nat_S_S x' y') in H_xy.
        apply (unfold_eq_Nat_S_S y' z') in H_yz.
        exact (IHx' y' z' H_xy H_yz).
Qed.

(* Because of these three properties, eq_Nat is an equivalence relation
   at natural numbers. *)

Lemma eq_Nat_is_an_equivalence_relation_at_Nat :
  specification_of_an_equivalence_relation Nat eq_Nat.
Proof.
  unfold specification_of_an_equivalence_relation.
  split.
    exact (eq_Nat_is_reflexive).
    split.
      exact (eq_Nat_is_symmetric).
      exact (eq_Nat_is_transitive).
Qed.

(* Any binary operation on the natural numbers will preserve the equality
   relation. The logical reason for this is that eq_Nat is defined to be 
   a one-to-one relation. A natural number is only equivalent to itself. 

   The lemma follows by double induction. *)

Lemma Dot_Nat_preserves_eq_Nat :
  forall f : Nat -> Nat -> Nat,
    specification_of_preservation Nat eq_Nat f.
Proof.
  intro f.
  unfold specification_of_preservation.
  intro a; revert f.
  induction a as [ | a' IHa'].
    intros f b c; revert f b.   
    induction c as [ | c' IHc'].
      intros f b d H_ab H_cd.
      destruct b as [ | b'].
        destruct d as [ | d'].
          exact (eq_Nat_is_reflexive (f O O)).

          contradiction (unfold_eq_Nat_O_S d' H_cd).
          
        contradiction (unfold_eq_Nat_O_S b' H_ab).

      intros f b d H_ab H_cd.
      destruct b as [ | b'].
        destruct d as [ | d'].
          contradiction (unfold_eq_Nat_S_O c' H_cd).

          apply (unfold_eq_Nat_S_S c' d') in H_cd.
          apply (IHc' (fun x y => f x (S y)) O d' H_ab H_cd).

        contradiction (unfold_eq_Nat_O_S b' H_ab).
        
    intros f b c d H_ab H_cd.
    destruct c as [ | c'].
      destruct b as [ | b'].
        contradiction (unfold_eq_Nat_S_O a' H_ab).

        destruct d as [ | d'].
          apply (unfold_eq_Nat_S_S a' b') in H_ab.
          exact (IHa' (fun x y => f (S x) y) b' O O H_ab H_cd).

          contradiction (unfold_eq_Nat_O_S d' H_cd).

      destruct b as [ | b'].
        contradiction (unfold_eq_Nat_S_O a' H_ab).

        destruct d as [ | d'].
          contradiction (unfold_eq_Nat_S_O c' H_cd).

          apply (unfold_eq_Nat_S_S a' b') in H_ab.
          apply (unfold_eq_Nat_S_S c' d') in H_cd.
          Check (IHa' _ b' c' d' H_ab H_cd).
          exact (IHa' (fun x y => f (S x) (S y)) b' c' d' H_ab H_cd).
Qed.

(* To avoid having to apply eq_Nat_is_reflexive anytime one wants
   to apply Dot_Nat_preserves_eq_Nat, here follows two lemmas that makes
   rewriting under eq_Nat easier. *)

Lemma Dot_Nat_preserves_eq_Nat_RR :
  forall f : Nat -> Nat -> Nat,
    forall a b c : Nat,
      a =N= b ->
      f a c =N= f b c.
Proof.
  intros f a b c H_ab.
  apply (Dot_Nat_preserves_eq_Nat f a b c c).
    exact H_ab.
   
    exact (eq_Nat_is_reflexive c).
Qed.             

Lemma Dot_Nat_preserves_eq_Nat_LR :
  forall f : Nat -> Nat -> Nat,
    forall a b c : Nat,
      a =N= b ->
      f c a =N= f c b.
Proof.
  intros f a b c H_ab.
  apply (Dot_Nat_preserves_eq_Nat f c c a b).
    exact (eq_Nat_is_reflexive c).
    
    exact H_ab.
Qed.             

(* Addition of two natural numbers *)

Definition specification_of_addition (NAdd : Nat -> Nat -> Nat) :=
  (forall n : Nat,
     NAdd O n =N= n)
  /\
  (forall m' n : Nat,
     NAdd (S m') n =N= S (NAdd m' n)).

(* It can be proven that the specification of addition is unique under
   eq_Nat by induction. *)

Lemma addition_is_unique :
  forall f g : Nat -> Nat -> Nat,
    specification_of_addition f ->
    specification_of_addition g ->
    forall m n : Nat,
      f m n =N= g m n.
Proof.
  intros f g H_Sf H_Sg m.

  unfold specification_of_addition in H_Sf.
  destruct H_Sf as [H_Sf_O H_Sf_S].
  unfold specification_of_addition in H_Sg.
  destruct H_Sg as [H_Sg_O H_Sg_S].

  induction m as [ | m' IHm'].
    intro n.
    assert (H_Sf_O_n := H_Sf_O n).
    assert (H_Sg_O_n := H_Sg_O n).
    apply (eq_Nat_is_symmetric) in H_Sg_O_n.
    exact (eq_Nat_is_transitive (f O n) n (g O n) H_Sf_O_n H_Sg_O_n).

    intro n.
    assert (H_Sf_Sm'_n := H_Sf_S m' n).
    apply (eq_Nat_is_transitive 
             (f (S m') n) (S (f m' n)) (g (S m') n) H_Sf_Sm'_n).
    assert (H_Sg_Sm'_n := H_Sg_S m' n).
    apply (eq_Nat_is_symmetric).
    apply (eq_Nat_is_transitive
             (g (S m') n) (S (g m' n)) (S (f m' n)) H_Sg_Sm'_n).
    apply -> (unfold_eq_Nat_S_S (g m' n) (f m' n)).
    apply (eq_Nat_is_symmetric).
    exact (IHm' n).
Qed.

(* Zero is left neutral for addition and eq_Nat. This
   follows from the specification of addition. *)

Lemma Zero_is_left_neutral_for_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall n : Nat,
      NAdd O n =N= n.
Proof.
  intros NAdd H_SNA n.
  unfold specification_of_addition in H_SNA.
  destruct H_SNA as [H_SNA_O _].
  exact (H_SNA_O n).
Qed.

(* Zero is right neutral for addition and eq_Nat. This
   follows from induction on the natural numbers. *)

Lemma Zero_is_right_neutral_for_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall n : Nat,
      NAdd n O =N= n.
Proof.
  intros NAdd H_SNA n.

  unfold specification_of_addition in H_SNA.
  destruct H_SNA as [H_SNA_O H_SNA_S].

  induction n as [ | n' IHn'].
    exact (H_SNA_O O).

    Check (eq_Nat_is_transitive (NAdd (S n') O) (S (NAdd n' O))).

    apply (eq_Nat_is_transitive (NAdd (S n') O) (S (NAdd n' O))).
    exact (H_SNA_S n' O).
    apply -> (unfold_eq_Nat_S_S (NAdd n' O) n').
    exact IHn'.
Qed.

(* The two lemmas above implies that there exists a neutral natural 
   number for addition and eq_Nat, namely Zero. *)

Corollary there_exists_a_neutral_element_for_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    exists e : Nat, specification_of_neutrality Nat eq_Nat NAdd e.
Proof.
  intros NAdd H_SNA.
  exists O.
  unfold specification_of_neutrality.
  split.
    exact (Zero_is_right_neutral_for_addition NAdd H_SNA).
    exact (Zero_is_left_neutral_for_addition NAdd H_SNA).
Qed.

(* It follows from induction that addition is associative under
   eq_Nat. *)

Lemma addition_is_associative :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    specification_of_associativity Nat eq_Nat NAdd.
Proof.
  intros NAdd H_SNA.

  unfold specification_of_addition in H_SNA.
  destruct H_SNA as [H_SNA_O H_SNA_S].

  unfold specification_of_associativity.
  intro a.
  induction a as [ | a' IHa'].
    intros b c.
    apply (eq_Nat_is_transitive (NAdd (NAdd O b) c)
                                (NAdd b c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (H_SNA_O b).
    apply (eq_Nat_is_symmetric).
    exact (H_SNA_O (NAdd b c)).

    intros b c.
    apply (eq_Nat_is_transitive (NAdd (NAdd (S a') b) c)
                                (NAdd (S (NAdd a' b)) c)).
      apply Dot_Nat_preserves_eq_Nat_RR.
  
      exact (H_SNA_S a' b).
    apply (eq_Nat_is_transitive (NAdd (S (NAdd a' b)) c) 
                                (S (NAdd (NAdd a' b) c))).
      exact (H_SNA_S (NAdd a' b) c).
    apply (eq_Nat_is_transitive (S (NAdd (NAdd a' b) c))
                                (S (NAdd a' (NAdd b c)))).
      apply -> (unfold_eq_Nat_S_S).
      exact (IHa' b c).
    apply (eq_Nat_is_symmetric).
    exact (H_SNA_S a' (NAdd b c)).
Qed.

(* The existence of the neutral element Zero and the associativity of
   addition under eq_Nat implies that natural numbers
   and addition form a monoid under eq_Nat. *)

Theorem Natural_numbers_and_addition_form_a_Monoid_under_eq_Nat :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    T_and_Dot_form_a_Monoid_under_eqT Nat eq_Nat NAdd.
Proof.
  intros NAdd H_SNA.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Nat_is_an_equivalence_relation_at_Nat).
    split.
      exact (Dot_Nat_preserves_eq_Nat NAdd).
      split.
        exact (addition_is_associative NAdd H_SNA).
        exact (there_exists_a_neutral_element_for_addition NAdd H_SNA).
Qed.

(* One can move the successor function in addition directly from
   the left natural number over to the right natural number and back instead 
   of moving it out. This follows from induction on the left side. *)

Lemma addition_has_a_distributive_property :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall m n : Nat,
      NAdd (S m) n =N= NAdd m (S n).
Proof.
  intros NAdd H_SNA m.
  unfold specification_of_addition in H_SNA.
  destruct H_SNA as [H_SNA_O H_SNA_S].
  induction m as [ | m' IHm'].
    intro n.    
    assert (H_SNA_S_O := H_SNA_S O n).
    apply (eq_Nat_is_transitive 
             (NAdd (S O) n) (S (NAdd O n)) (NAdd O (S n)) H_SNA_S_O).
    apply (eq_Nat_is_transitive
             (S (NAdd O n)) (S n)).
      apply -> (unfold_eq_Nat_S_S).
      exact (H_SNA_O n).
    apply (eq_Nat_is_symmetric).
    exact (H_SNA_O (S n)).
    
    intro n.
    assert (H_SNA_Sm'_n := H_SNA_S (S m') n).
    apply (eq_Nat_is_transitive (NAdd (S (S m')) n) (S (NAdd (S m') n)) 
                                (NAdd (S m') (S n)) H_SNA_Sm'_n).
    apply (eq_Nat_is_transitive (S (NAdd (S m') n)) (S (NAdd m' (S n)))).
      apply -> (unfold_eq_Nat_S_S).
      exact (IHm' n).
    apply (eq_Nat_is_symmetric).
    exact (H_SNA_S m' (S n)).
Qed.

(* Since Zero is neutral for addition and because of the distributive
   property shown above, one can prove through induction that addition
   is commutative under eq_Nat. *)

Lemma addition_is_commutative :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall m n : Nat,
      NAdd m n =N= NAdd n m.
Proof.
  intros NAdd H_SNA.
  intro m.
  induction m as [ | m' IHm'].
    intro n.
    assert (H_On := Zero_is_left_neutral_for_addition NAdd H_SNA n).
    apply (eq_Nat_is_transitive (NAdd O n) n (NAdd n O) H_On).
    apply (eq_Nat_is_symmetric).
    exact (Zero_is_right_neutral_for_addition NAdd H_SNA n).

    intro n.
    assert (H_D := addition_has_a_distributive_property NAdd H_SNA m' n).
    apply (eq_Nat_is_transitive (NAdd (S m') n) (NAdd m' (S n)) 
                                (NAdd n (S m')) H_D).
    apply (eq_Nat_is_transitive (NAdd m' (S n)) (NAdd (S n) m') 
                                (NAdd n (S m')) (IHm' (S n))).
    exact (addition_has_a_distributive_property NAdd H_SNA n m').
Qed.

(* Multiplication with m and n is specified as recursively 
   summing m n's. *)

Definition specification_of_multiplication (NMul : Nat -> Nat -> Nat) :=
  (forall n : Nat,
     NMul O n =N= O)
    /\
  (forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall m' n : Nat,
      NMul (S m') n =N= NAdd n (NMul m' n)).

(* One can prove that any function satisfying the specification of 
   multiplication yield nat equivalent output on the same input. 
   This can be shown by induction. *)

Lemma multiplication_is_unique :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall f g : Nat -> Nat -> Nat,
      specification_of_multiplication f ->
      specification_of_multiplication g ->
      forall m n : Nat,
        f m n =N= g m n.
Proof.
  intros NAdd H_SNA f g H_Sf H_Sg.

  unfold specification_of_multiplication in H_Sf.
  destruct H_Sf as [H_Sf_O H_Sf_S].
  unfold specification_of_multiplication in H_Sg.
  destruct H_Sg as [H_Sg_O H_Sg_S].

  intro m.
  induction m as [ | m' IHm'].
    intro n.
    assert (H_Sf_O' := H_Sf_O n).
    assert (H_Sg_O' := H_Sg_O n).
    apply (eq_Nat_is_symmetric) in H_Sg_O'.
    exact (eq_Nat_is_transitive (f O n) O (g O n) H_Sf_O' H_Sg_O').
    
    intro n.
    assert (H_Sf_S' := H_Sf_S NAdd H_SNA m' n).
    assert (H_Sg_S' := H_Sg_S NAdd H_SNA m' n).
    apply (eq_Nat_is_transitive (f (S m') n) (NAdd n (f m' n))
                                (g (S m') n) H_Sf_S').
    apply (eq_Nat_is_symmetric).
    apply (eq_Nat_is_transitive (g (S m') n) (NAdd n (g m' n))
                                (NAdd n (f m' n)) H_Sg_S').
    apply (Dot_Nat_preserves_eq_Nat_LR).
    apply (eq_Nat_is_symmetric).
    exact (IHm' n).
Qed.

(* The successor of zero multiplied with n is the addition of n and O. But
   since O is right neutral for addition, S O must be left neutral for 
   multiplication. *)

Lemma successor_of_Zero_is_left_neutral_for_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall n : Nat,
        NMul (S O) n =N= n.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  unfold specification_of_multiplication in H_SNM.
  destruct H_SNM as [H_SNM_O H_SNM_S].
  intro n.
  assert (H_n := H_SNM_S NAdd H_SNA O n).
  apply (eq_Nat_is_transitive (NMul (S O) n) (NAdd n (NMul O n)) n H_n).
  apply (eq_Nat_is_transitive (NAdd n (NMul O n)) (NAdd n O) n).
    apply (Dot_Nat_preserves_eq_Nat_LR).
    exact (H_SNM_O n).
  exact (Zero_is_right_neutral_for_addition NAdd H_SNA n).
Qed.

(* Since addition has the distributive property and Zero is left 
   neutral for addition, it follows from induction that the successor
   of zero is right neutral for multiplication. *)

Lemma successor_of_Zero_is_right_neutral_for_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall n : Nat,
        NMul n (S O) =N= n.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  unfold specification_of_multiplication in H_SNM.
  destruct H_SNM as [H_SNM_O H_SNM_S].
  intro n.
  induction n as [ | n' IHn'].
    exact (H_SNM_O (S O)).

    assert (H_SNM_n'SO := H_SNM_S NAdd H_SNA n' (S O)).
    apply (eq_Nat_is_transitive (NMul (S n') (S O)) (NAdd (S O) (NMul n' (S O)))
                                (S n') H_SNM_n'SO).
    apply (eq_Nat_is_transitive (NAdd (S O) (NMul n' (S O))) (NAdd (S O) n')).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact IHn'.
    assert (H_D := addition_has_a_distributive_property NAdd H_SNA O n').
    apply (eq_Nat_is_transitive (NAdd (S O) n') (NAdd O (S n')) (S n') H_D).
    exact (Zero_is_left_neutral_for_addition NAdd H_SNA (S n')).
Qed.

(* It follows from the specification of multiplication that O is
   left absorbent. *)

Lemma Zero_is_left_absorbent_for_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall n : Nat,
        NMul O n =N= O.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  unfold specification_of_multiplication in H_SNM.
  destruct H_SNM as [H_SNM_O _].
  exact H_SNM_O.
Qed.

(* It can be proved through induction that O is also right absorbent. *)

Lemma Zero_is_right_absorbent_for_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall n : Nat,
        NMul n O =N= O.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  unfold specification_of_multiplication in H_SNM.
  destruct H_SNM as [H_SNM_O H_SNM_S].
  intro n.
  induction n as [ | n' IHn'].
    exact (H_SNM_O O).

    assert (H_n' := H_SNM_S NAdd H_SNA n' O).
    apply (eq_Nat_is_transitive (NMul (S n') O) (NAdd O (NMul n' O))
                                O H_n').
    apply (eq_Nat_is_transitive (NAdd O (NMul n' O)) (NAdd O O) O).
      apply Dot_Nat_preserves_eq_Nat_LR.
      exact IHn'.
    exact (Zero_is_right_neutral_for_addition NAdd H_SNA O).
Qed.

Lemma there_exists_a_neutral_element_for_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      exists e : Nat, specification_of_neutrality Nat eq_Nat NMul e.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  exists (S O).
  unfold specification_of_neutrality.
  split.
    exact (successor_of_Zero_is_right_neutral_for_multiplication
             NAdd H_SNA NMul H_SNM).
    exact (successor_of_Zero_is_left_neutral_for_multiplication
             NAdd H_SNA NMul H_SNM).
Qed.

(* Multiplication is right distributive over addition. That is,
   (a + b) * c = (a * c) + (b * c). This follows by induction and some
   properties of addition. *)

Lemma multiplication_is_right_distributive_over_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a b c : Nat,
        NMul (NAdd a b) c =N= NAdd (NMul a c) (NMul b c).
Proof.
  intros NAdd H_SNA NMul H_SNM.

  intros a.
  induction a as [ | a' IHa'].

    (* Base case *)

    intros b c.
    apply (eq_Nat_is_transitive (NMul (NAdd O b) c) (NMul b c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
    exact (Zero_is_left_neutral_for_addition NAdd H_SNA b).
    apply (eq_Nat_is_symmetric).
    apply (eq_Nat_is_transitive 
             (NAdd (NMul O c) (NMul b c)) (NAdd O (NMul b c))).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (Zero_is_left_absorbent_for_multiplication 
               NAdd H_SNA NMul H_SNM c).
    exact (Zero_is_left_neutral_for_addition NAdd H_SNA (NMul b c)).

    (* Induction *)

    intros b c.
    assert (H_SNA' := H_SNA).
    unfold specification_of_addition in H_SNA'.
    destruct H_SNA' as [ H_SNA_O H_SNA_S ].
    assert (H_a'b := H_SNA_S a' b).
    apply (eq_Nat_is_transitive (NMul (NAdd (S a') b) c) 
                                (NMul (S (NAdd a' b)) c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact H_a'b.
    assert (H_SNM' := H_SNM).
    unfold specification_of_multiplication in H_SNM'.
    destruct H_SNM' as [H_SNM_O H_SNM_S].
    assert (H_a'bc := H_SNM_S NAdd H_SNA (NAdd a' b) c).
    apply (eq_Nat_is_transitive (NMul (S (NAdd a' b)) c) 
                                (NAdd c (NMul (NAdd a' b) c))
                                (NAdd (NMul (S a') c) (NMul b c)) H_a'bc).
    apply (eq_Nat_is_transitive (NAdd c (NMul (NAdd a' b) c))
                                (NAdd c (NAdd (NMul a' c) (NMul b c)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact (IHa' b c).
    assert (H_A := addition_is_associative NAdd H_SNA c
                                                   (NMul a' c) (NMul b c)).
    apply (eq_Nat_is_symmetric) in H_A.
    apply (eq_Nat_is_transitive (NAdd c (NAdd (NMul a' c) (NMul b c)))
                                (NAdd (NAdd c (NMul a' c)) (NMul b c))
                                (NAdd (NMul (S a') c) (NMul b c)) H_A).
    apply (Dot_Nat_preserves_eq_Nat_RR).
    apply (eq_Nat_is_symmetric).
    exact (H_SNM_S NAdd H_SNA a' c).
Qed.

(* Multiplication is also left distributive. That is, a * (b + c) =
   (a * b) + (a * c). This proof is standalone and by induction, but
   one could also prove commutativity of multiplication and then use 
   the lemma about right distribution. *)

Lemma multiplication_is_left_distributive_over_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a b c : Nat,
        NMul a (NAdd b c) =N= NAdd (NMul a b) (NMul a c).
Proof.
  intros NAdd H_SNA NMul H_SNM.
  intro a.
  induction a as [ | a' IHa'].
    intros b c.
    assert (H_ZA := Zero_is_left_absorbent_for_multiplication
                      NAdd H_SNA NMul H_SNM).
    apply (eq_Nat_is_transitive (NMul O (NAdd b c)) O 
                                (NAdd (NMul O b) (NMul O c)) (H_ZA (NAdd b c))).
    apply (eq_Nat_is_symmetric).
    apply (eq_Nat_is_transitive (NAdd (NMul O b) (NMul O c)) (NAdd O O) O).
      apply (Dot_Nat_preserves_eq_Nat).
        exact (H_ZA b).
        exact (H_ZA c).
    exact (Zero_is_left_neutral_for_addition NAdd H_SNA O).

    intros b c.
    unfold specification_of_multiplication in H_SNM.
    destruct H_SNM as [_ H_SNMul_S].
    assert (H_S := H_SNMul_S NAdd H_SNA).
    apply (eq_Nat_is_transitive (NMul (S a') (NAdd b c)) 
                                (NAdd (NAdd b c) (NMul a' (NAdd b c)))).
      exact (H_S a' (NAdd b c)).
    apply (eq_Nat_is_transitive (NAdd (NAdd b c) (NMul a' (NAdd b c)))
                                (NAdd (NAdd b c) (NAdd (NMul a' b) (NMul a' c)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact (IHa' b c).
    assert (H_assoc := addition_is_associative NAdd H_SNA).
    unfold specification_of_associativity in H_assoc.
    assert (H_comm := addition_is_commutative NAdd H_SNA).
    apply (eq_Nat_is_transitive (NAdd (NAdd b c) (NAdd (NMul a' b) (NMul a' c)))
                                (NAdd b (NAdd c (NAdd (NMul a' b) (NMul a' c))))).
      exact (H_assoc b c (NAdd (NMul a' b) (NMul a' c))).
    apply (eq_Nat_is_transitive (NAdd b (NAdd c (NAdd (NMul a' b) (NMul a' c))))
                                (NAdd b (NAdd (NAdd c (NMul a' b)) (NMul a' c)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      apply (eq_Nat_is_symmetric).
      exact (H_assoc c (NMul a' b) (NMul a' c)).
    apply (eq_Nat_is_transitive (NAdd b (NAdd (NAdd c (NMul a' b)) (NMul a' c)))
                                (NAdd b (NAdd (NAdd (NMul a' b) c) (NMul a' c)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      apply (Dot_Nat_preserves_eq_Nat_RR).    
      exact (H_comm c (NMul a' b)).
    apply (eq_Nat_is_transitive (NAdd b (NAdd (NAdd (NMul a' b) c) (NMul a' c)))
                                (NAdd b (NAdd (NMul a' b) (NAdd c (NMul a' c))))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact (H_assoc (NMul a' b) c (NMul a' c)).
    apply (eq_Nat_is_transitive (NAdd b (NAdd (NMul a' b) (NAdd c (NMul a' c))))
                                (NAdd (NAdd b (NMul a' b)) (NAdd c (NMul a' c)))).
      apply (eq_Nat_is_symmetric).
      exact (H_assoc b (NMul a' b) (NAdd c (NMul a' c))).
    apply (Dot_Nat_preserves_eq_Nat).
      apply (eq_Nat_is_symmetric).
      exact (H_SNMul_S NAdd H_SNA a' b).
    apply (eq_Nat_is_symmetric).
    exact (H_SNMul_S NAdd H_SNA a' c).
Qed.

(* Associativity of multiplication follows from induction and the
   right distributive property. *)

Lemma multiplication_is_associative :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      specification_of_associativity Nat eq_Nat NMul.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  unfold specification_of_associativity.

  assert (H_SNM' := H_SNM).
  unfold specification_of_multiplication in H_SNM'.
  destruct H_SNM' as [H_SNM_O H_SNM_S].

  intro a.
  induction a as [ | a' IHa'].
    intros b c.
    apply (eq_Nat_is_transitive (NMul (NMul O b) c) (NMul O c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (H_SNM_O b).
    apply (eq_Nat_is_transitive (NMul O c) O).
      exact (H_SNM_O c).
    apply (eq_Nat_is_symmetric).
    exact (H_SNM_O (NMul b c)).

    intros b c.
    apply (eq_Nat_is_transitive (NMul (NMul (S a') b) c)
                                (NMul (NAdd b (NMul a' b)) c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (H_SNM_S NAdd H_SNA a' b).
    apply (eq_Nat_is_transitive (NMul (NAdd b (NMul a' b)) c)
                                (NAdd (NMul b c) (NMul (NMul a' b) c))).
      exact (multiplication_is_right_distributive_over_addition
               NAdd H_SNA NMul H_SNM b (NMul a' b) c).
    apply (eq_Nat_is_transitive (NAdd (NMul b c) (NMul (NMul a' b) c))
                                (NAdd (NMul b c) (NMul a' (NMul b c)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact (IHa' b c).
    apply (eq_Nat_is_symmetric).
    exact (H_SNM_S NAdd H_SNA a' (NMul b c)).
Qed.

(* The existence of the neutral element S O and the associativity of 
   multiplication implies that natural numbers and multiplication
   form a monoid under the equivalence of natural numbers. *)

Theorem Natural_numbers_and_multiplication_form_a_Monoid_under_eq_Nat :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      T_and_Dot_form_a_Monoid_under_eqT Nat eq_Nat NMul.
Proof.
  intros NAdd H_SNA NMul H_SNM.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Nat_is_an_equivalence_relation_at_Nat).
    split.
      exact (Dot_Nat_preserves_eq_Nat NMul).
    split.
      exact (multiplication_is_associative
               NAdd H_SNA NMul H_SNM).    
      exact (there_exists_a_neutral_element_for_multiplication
               NAdd H_SNA NMul H_SNM).
Qed.

(* A boolean is true or false. *)

Inductive Boolean : Set :=
  | FALSE : Boolean
  | TRUE : Boolean.

(* Two booleans are equal if they are the same inductive. Trivial. *)

Definition eq_Bool (p q : Boolean) :=
  match p with
      | TRUE => match q with
                    | TRUE => True
                    | FALSE => False
                end
      | FALSE => match q with
                     | TRUE => False
                     | FALSE => True
                 end
  end.

Notation "A =B= B" := (eq_Bool A B) (at level 70, right associativity).

(* Some unfold lemmas for eq_Bool. *)

Lemma unfold_eq_Bool_F_F :
  FALSE =B= FALSE.
Proof.
  unfold eq_Bool.
  exact I.
Qed.

Lemma unfold_eq_Bool_F_T :
  ~ (FALSE =B= TRUE).
Proof.
  intro H_eq.
  unfold eq_Bool in H_eq.
  exact H_eq.
Qed.

Lemma unfold_eq_Bool_T_F :
  ~ (TRUE =B= FALSE).
Proof.
  intro H_eq.
  unfold eq_Bool in H_eq.
  exact H_eq.
Qed.

Lemma unfold_eq_Bool_T_T :
  TRUE =B= TRUE.
Proof.
  unfold eq_Bool.
  exact I.
Qed.

Lemma eq_Bool_is_reflexive :
  specification_of_a_reflexive_relation Boolean eq_Bool.
Proof.
  unfold specification_of_a_reflexive_relation.
  intro a.
  destruct a as [ | ].
    exact unfold_eq_Bool_F_F.
    exact unfold_eq_Bool_T_T.
Qed.

(* eq_Bool is symmetric since a =B= b iff. a and b are TRUE or
   a and b are FALSE. *)

Lemma eq_Bool_is_symmetric :
  specification_of_a_symmetric_relation Boolean eq_Bool.
Proof.
  unfold specification_of_a_symmetric_relation.
  intros a b H_ab.
  destruct a as [ | ].
    destruct b as [ | ].
      exact unfold_eq_Bool_F_F.
      contradiction (unfold_eq_Bool_F_T H_ab).
    destruct b as [ | ].
      contradiction (unfold_eq_Bool_T_F H_ab).
      exact unfold_eq_Bool_T_T.
Qed.

(* eq_Bool is also transitive since if a =B= b and b =B= c, a, b, and c must all    be true or they all must be false. *)

Lemma eq_Bool_is_transitive :
  specification_of_a_transitive_relation Boolean eq_Bool.
Proof.
  unfold specification_of_a_transitive_relation.
  intros [ | ] [ | ] [ | ] H_xy H_yz;
  (exact H_xy || exact H_yz || 
   contradiction (unfold_eq_Bool_F_T H_xy) ||
   contradiction (unfold_eq_Bool_T_F H_xy)).
Qed.

Lemma eq_Bool_is_an_equivalence_relation :
  specification_of_an_equivalence_relation Boolean eq_Bool.
Proof.
  unfold specification_of_an_equivalence_relation.
  split.
    exact (eq_Bool_is_reflexive).
    split.
      exact (eq_Bool_is_symmetric).
      exact (eq_Bool_is_transitive).
Qed.

(* Any boolean binary operator will preserve eq_Bool. The logical reason
   is that a =B= b only if a and b are true or a and b are false. *)

Lemma Dot_Boolean_preserves_eq_Bool :
  forall Dot : Boolean -> Boolean -> Boolean,
    specification_of_preservation Boolean eq_Bool Dot.
Proof.
  intros Dot.
  unfold specification_of_preservation.
  intros [ | ] [ | ] [ | ] [ | ] H_ab H_cd;
  (apply eq_Bool_is_reflexive || 
   contradiction (unfold_eq_Bool_F_T H_ab) ||
   contradiction (unfold_eq_Bool_T_F H_ab) ||
   contradiction (unfold_eq_Bool_F_T H_cd) ||
   contradiction (unfold_eq_Bool_T_F H_cd)).
Qed.

(* Since the above lemma will result in a lot of eq_Bool_is_reflexive 
   applications, the two lemmas down under are created and proved. *)

Lemma Dot_Boolean_preserves_eq_Bool_LR :
  forall Dot : Boolean -> Boolean -> Boolean,
    forall a b c : Boolean,
      a =B= b ->
      Dot c a =B= Dot c b.
Proof.
  intros Dot a b c H_ab.
  apply (Dot_Boolean_preserves_eq_Bool).
    exact (eq_Bool_is_reflexive c).
    exact H_ab.
Qed.

Lemma Dot_Boolean_preserves_eq_Bool_RR :
  forall Dot : Boolean -> Boolean -> Boolean,
    forall a b c : Boolean,
      a =B= b ->
      Dot a c =B= Dot b c.
Proof.
  intros Dot a b c H_ab.
  apply (Dot_Boolean_preserves_eq_Bool).
    exact H_ab.
    exact (eq_Bool_is_reflexive c).
Qed.

(* A natural is less or equal to another natural iff. it has at most the same
    successor applications as the other natural. *)

Definition specification_of_LEQ (LEQ : Nat -> Nat -> Boolean) := 
  (forall n : Nat,
     LEQ O n =B= TRUE)
  /\
  (forall m' : Nat,
     LEQ (S m') O =B= FALSE)
  /\
  (forall m' n' : Nat,
     LEQ (S m') (S n') =B= LEQ m' n').

(* Since LEQ has a different co-domain than domain its preservation
   is a bit different. *)

Lemma about_preservation_of_LEQ :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall a b c d : Nat,
      a =N= b ->
      c =N= d ->
      LEQ a c =B= LEQ b d.
Proof.
  intros LEQ H_SL a.
  unfold specification_of_LEQ in H_SL.
  destruct H_SL as [H_SL_T [H_SL_F H_SL_S]].
  induction a as [ | a' IHa'].
    intros b c d H_ab H_cd.
    destruct b as [ | b'].
      apply (eq_Bool_is_transitive (LEQ O c) TRUE).
        exact (H_SL_T c).
      apply (eq_Bool_is_symmetric).
      exact (H_SL_T d).

      contradiction (unfold_eq_Nat_O_S b' H_ab).

    intros b c d H_ab H_cd.
    destruct b as [ | b'].
      contradiction (unfold_eq_Nat_S_O a' H_ab).

      destruct c as [ | c'].
        destruct d as [ | d'].
          apply (eq_Bool_is_transitive (LEQ (S a') O) FALSE).
            exact (H_SL_F a').
          apply (eq_Bool_is_symmetric).
          exact (H_SL_F b').

          contradiction (unfold_eq_Nat_O_S d' H_cd).

        destruct d as [ | d'].
          contradiction (unfold_eq_Nat_S_O c' H_cd).

          apply (unfold_eq_Nat_S_S) in H_ab.
          apply (unfold_eq_Nat_S_S) in H_cd.
          apply (eq_Bool_is_transitive (LEQ (S a') (S c')) (LEQ a' c')).
            exact (H_SL_S a' c').
          apply (eq_Bool_is_symmetric).
          apply (eq_Bool_is_transitive (LEQ (S b') (S d')) (LEQ b' d')).
            exact (H_SL_S b' d').
          apply (eq_Bool_is_symmetric).
          exact (IHa' b' c' d' H_ab H_cd).
Qed.

Lemma LEQ_is_unique :
  forall f g : Nat -> Nat -> Boolean,
    specification_of_LEQ f ->
    specification_of_LEQ g ->
    forall m n : Nat,
      f m n =B= g m n.
Proof.
  intros f g H_Sf H_Sg.

  unfold specification_of_LEQ in H_Sf.
  destruct H_Sf as [H_Sf_T [H_Sf_F H_Sf_S]].
  unfold specification_of_LEQ in H_Sg.
  destruct H_Sg as [H_Sg_T [H_Sg_F H_Sg_S]].

  intro m.
  induction m as [ | m' IHm'].
    intro n.
    assert (H_f := H_Sf_T n).
    assert (H_g := H_Sg_T n).
    apply (eq_Bool_is_symmetric) in H_g.
    exact (eq_Bool_is_transitive (f O n) TRUE (g O n) H_f H_g).

    intro n.
    destruct n as [ | n'].
      assert (H_f := H_Sf_F m').
      assert (H_g := H_Sg_F m').
      apply (eq_Bool_is_symmetric) in H_g.
      exact (eq_Bool_is_transitive (f (S m') O) FALSE (g (S m') O) H_f H_g).

      apply (eq_Bool_is_transitive (f (S m') (S n')) (f m' n')).
        exact (H_Sf_S m' n').
      apply (eq_Bool_is_transitive (f m' n') (g m' n')).
        exact (IHm' n').
      apply (eq_Bool_is_symmetric).
      exact (H_Sg_S m' n').
Qed.

Lemma LEQ_is_either_true_or_false :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall m n : Nat,
      (LEQ m n =B= TRUE) \/ (LEQ m n =B= FALSE).
Proof.
  intros LEQ H_SL m.
  unfold specification_of_LEQ in H_SL.
  destruct H_SL as [H_SL_T [H_SL_F H_SL_S]].
  induction m as [ | m' IHm'].
    intro n.
    left.
    exact (H_SL_T n).

    intro n.
    destruct n as [ | n'].
      right.
      exact (H_SL_F m').

      destruct (IHm' n') as [IH_T | IH_F].
        left.
        apply (eq_Bool_is_transitive (LEQ (S m') (S n'))
                                     (LEQ m' n') TRUE (H_SL_S m' n')).
        exact IH_T.

        right.
        apply (eq_Bool_is_transitive (LEQ (S m') (S n'))
                                     (LEQ m' n') FALSE (H_SL_S m' n')).
        exact IH_F.
Qed.

(* apply (destruct_LEQ LEQ H_Spec_LEQ m n); split; intro H_LEQ
   will act like normal destruct of (LEQ m n) but with eq_Bool instead. *)

Lemma destruct_LEQ :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall m n : Nat,
    forall P : Prop,
      ((LEQ m n =B= TRUE -> P) /\ (LEQ m n =B= FALSE -> P)) -> P.
Proof.
  intros LEQ H_SL m n P H_L.
  destruct H_L as [H_LT H_LF].
  destruct (LEQ_is_either_true_or_false LEQ H_SL m n) as [H_T | H_F].
    exact (H_LT H_T).
    exact (H_LF H_F).
Qed.

(* Minimum is a binary operation which, given two natural numbers,
   yields the left one if it is less or equal to the second and yields the
   right one if not. *)

Definition specification_of_minimum (Min : Nat -> Nat -> Nat) :=
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    (forall m n : Nat,
       LEQ m n =B= TRUE ->
       Min m n =N= m)
    /\
    (forall m n : Nat,
       LEQ m n =B= FALSE ->
       Min m n =N= n).

(* It can be shown that the minimum of two non-zero natural numbers must be
   the predecessor of the minimum of the predecessors of the two natural 
   numbers. *)

Lemma about_minimum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      forall a b : Nat,
        Min (S a) (S b) =N= S (Min a b).
Proof.
  intros LEQ H_SL Min H_SM.
  intros a b.
  unfold specification_of_minimum in H_SM.
  destruct (H_SM LEQ H_SL) as [H_SM_L H_SM_R]; clear H_SM.
  apply (destruct_LEQ LEQ H_SL (S a) (S b)); split; intro H_LEQ.
    unfold specification_of_LEQ in H_SL.
    destruct H_SL as [H_SL_T [H_SL_F H_SL_S]].
    assert (H_LEQ' := H_SL_S a b).
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_transitive TRUE (LEQ (S a) (S b)) (LEQ a b) H_LEQ) in H_LEQ'.
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_symmetric) in H_LEQ'.
    apply (eq_Nat_is_transitive (Min (S a) (S b)) (S a)).
      exact (H_SM_L (S a) (S b) H_LEQ).
    apply -> (unfold_eq_Nat_S_S).
    apply (eq_Nat_is_symmetric).
    exact (H_SM_L a b H_LEQ').
    
    unfold specification_of_LEQ in H_SL.
    destruct H_SL as [H_SL_T [H_SL_F H_SL_S]].
    assert (H_LEQ' := H_SL_S a b).
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_transitive FALSE (LEQ (S a) (S b)) (LEQ a b) H_LEQ) in H_LEQ'.
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_symmetric) in H_LEQ'.
    apply (eq_Nat_is_transitive (Min (S a) (S b)) (S b)).
      exact (H_SM_R (S a) (S b) H_LEQ).
    apply -> (unfold_eq_Nat_S_S).
    apply (eq_Nat_is_symmetric).
    exact (H_SM_R a b H_LEQ').
Qed.
      
Lemma minimum_is_unique :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall f g : Nat -> Nat -> Nat,
      specification_of_minimum f ->
      specification_of_minimum g ->
      forall m n : Nat,
        f m n =N= g m n.
Proof.
  intros LEQ H_SL f g H_Sf H_Sg m n.

  unfold specification_of_minimum in H_Sf.
  destruct (H_Sf LEQ H_SL) as [H_Sf_L H_Sf_R].
  unfold specification_of_minimum in H_Sg.
  destruct (H_Sg LEQ H_SL) as [H_Sg_L H_Sg_R].
  clear H_Sf H_Sg.

  apply (destruct_LEQ LEQ H_SL m n); split; intro H_LEQ.
    apply (eq_Nat_is_transitive (f m n) m).
    exact (H_Sf_L m n H_LEQ).
    apply (eq_Nat_is_symmetric).
    exact (H_Sg_L m n H_LEQ).
    
    apply (eq_Nat_is_transitive (f m n) n).
    exact (H_Sf_R m n H_LEQ).
    apply (eq_Nat_is_symmetric).
    exact (H_Sg_R m n H_LEQ).
Qed.

(* Zero is left absorbent in minimum since it is always less or
   equal to any other number. *)

Lemma Zero_is_left_absorbent_in_minimum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      forall b : Nat,
        Min O b =N= O.
Proof.
  intros LEQ H_SLEQ Min H_SM b.
  unfold specification_of_minimum in H_SM.
  destruct (H_SM LEQ H_SLEQ) as [H_SM_L _]; clear H_SM.
  unfold specification_of_LEQ in H_SLEQ.
  destruct H_SLEQ as [H_SLEQ_T _].
  exact (H_SM_L O b (H_SLEQ_T b)).
Qed.

(* Zero is right absorbent in minimum since the it will be chosen
   as the minimum if the left hand side is not Zero. If the left hand
   side is zero, it will absorb instead, but the result is still zero. *)

Lemma Zero_is_right_absorbent_in_minimum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      forall b : Nat,
        Min b O =N= O.
Proof.
  intros LEQ H_SLEQ Min H_SM b.
  unfold specification_of_minimum in H_SM.
  destruct (H_SM LEQ H_SLEQ) as [H_SM_L H_SM_R]; clear H_SM.
  unfold specification_of_LEQ in H_SLEQ.
  destruct H_SLEQ as [H_SLEQ_T [H_SLEQ_F _]].
  destruct b as [ | b'].
    exact (H_SM_L O O (H_SLEQ_T O)).
    exact (H_SM_R (S b') O (H_SLEQ_F b')).
Qed.

(* It can be shown by induction that minimum is associative. In the base case, 
   zero will absorb everything. In the induction case, we can without loss of 
   generality assume that the three natural numbers are non-zero
   since Zero will absorb everything. But then we can use the lemma
   about minimum to move the successor out, apply the induction 
   hypothesis and move the successor back in. *)

Lemma minimum_is_associative :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      specification_of_associativity Nat eq_Nat Min.
Proof.
  intros LEQ H_SLEQ Min H_SM.
  unfold specification_of_associativity.
  intro a.
  induction a as [ | a' IHa'].
    intros b c.
    apply (eq_Nat_is_transitive (Min (Min O b) c) (Min O c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).      
      exact (Zero_is_left_absorbent_in_minimum LEQ H_SLEQ Min H_SM b).
    apply (eq_Nat_is_transitive (Min O c) O).
      exact (Zero_is_left_absorbent_in_minimum LEQ H_SLEQ Min H_SM c).
    apply (eq_Nat_is_symmetric).
    exact (Zero_is_left_absorbent_in_minimum LEQ H_SLEQ Min H_SM (Min b c)).

    intros b c.
    destruct b as [ | b'].
      apply (eq_Nat_is_transitive (Min (Min (S a') O) c) (Min O c)).
        apply (Dot_Nat_preserves_eq_Nat_RR).
        exact (Zero_is_right_absorbent_in_minimum LEQ H_SLEQ Min H_SM (S a')).
      apply (eq_Nat_is_transitive (Min O c) O).
        exact (Zero_is_left_absorbent_in_minimum LEQ H_SLEQ Min H_SM c).
      apply (eq_Nat_is_symmetric).
      apply (eq_Nat_is_transitive (Min (S a') (Min O c)) (Min (S a') O)).
        apply (Dot_Nat_preserves_eq_Nat_LR).
        exact (Zero_is_left_absorbent_in_minimum LEQ H_SLEQ Min H_SM c).
      exact (Zero_is_right_absorbent_in_minimum LEQ H_SLEQ Min H_SM (S a')).

      apply (eq_Nat_is_transitive (Min (Min (S a') (S b')) c) 
                                  (Min (S (Min a' b')) c)).
        apply (Dot_Nat_preserves_eq_Nat_RR).
        exact (about_minimum LEQ H_SLEQ Min H_SM a' b').
      destruct c as [ | c'].
        apply (eq_Nat_is_transitive (Min (S (Min a' b')) O) O).
          exact (Zero_is_right_absorbent_in_minimum 
                   LEQ H_SLEQ Min H_SM (S (Min a' b'))).
        apply (eq_Nat_is_symmetric).
        apply (eq_Nat_is_transitive (Min (S a') (Min (S b') O)) 
                                    (Min (S a') O)).
          apply (Dot_Nat_preserves_eq_Nat_LR).
          exact (Zero_is_right_absorbent_in_minimum LEQ H_SLEQ Min H_SM (S b')).
        exact (Zero_is_right_absorbent_in_minimum LEQ H_SLEQ Min H_SM (S a')).

        apply (eq_Nat_is_transitive (Min (S (Min a' b')) (S c'))
                                    (S (Min (Min a' b') c'))).
          exact (about_minimum LEQ H_SLEQ Min H_SM (Min a' b') c').
        apply (eq_Nat_is_transitive (S (Min (Min a' b') c')) 
                                    (S (Min a' (Min b' c')))).
          apply -> (unfold_eq_Nat_S_S).
          exact (IHa' b' c').
        apply (eq_Nat_is_transitive (S (Min a' (Min b' c')))
                                    (Min (S a') (S (Min b' c')))).
          apply (eq_Nat_is_symmetric).
          exact (about_minimum LEQ H_SLEQ Min H_SM a' (Min b' c')).
        apply (Dot_Nat_preserves_eq_Nat_LR).
        apply (eq_Nat_is_symmetric).
        exact (about_minimum LEQ H_SLEQ Min H_SM b' c').
Qed.

(* It follows from the definition of natural numbers, eq_Nat and induction
   that a natural can not be the successor of itself. *)

Lemma a_natural_number_can_not_be_the_successor_of_itself :
  forall n : Nat,
    ~(n =N= S n).
Proof.
  intros n H_Sn_n.
  induction n as [ | n' IHn'].
    apply (unfold_eq_Nat_O_S O) in H_Sn_n.
    contradiction (unfold_eq_Nat_O_S O H_Sn_n).

    apply (unfold_eq_Nat_S_S n' (S n')) in H_Sn_n.
    exact (IHn' H_Sn_n).
Qed.

(* Furthermore, the minimum of any natural number and it's successor is always
   the number. This follows from left zero absorbency; the lemma
   about minimum; and induction. *)

Lemma the_minimum_of_n_and_Sn_is_n :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      forall n : Nat,
         Min n (S n) =N= n.
Proof.
  intros LEQ H_SL Min H_SM n.

  induction n as [ | n' IHn'].
    exact (Zero_is_left_absorbent_in_minimum 
             LEQ H_SL Min H_SM (S O)).

    apply (eq_Nat_is_transitive (Min (S n') (S (S n'))) (S (Min n' (S n')))).
      exact (about_minimum LEQ H_SL Min H_SM n' (S n')).
    apply -> (unfold_eq_Nat_S_S).
    exact IHn'.
Qed.    

(* Because of this there must be no upper bound on the natural numbers. 
   The biggest number must be bigger than every natural number which means that
   the successor must be the minimum of the two, but the number itself 
   must also be the minimum of the two. If such an upper bound exists it must
   therefore be equal to its successor, but alas it can not. *)

Lemma the_naturals_are_not_left_upper_bounded :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      ~ (exists M : Nat,
           forall a : Nat,
             Min M a =N= a).           
Proof.
  intros LEQ H_SL Min H_SM.
  intro H_exists_max.
  destruct H_exists_max as [M H_M].
  assert (H_M' := H_M (S M)).
  assert (H_Con := the_minimum_of_n_and_Sn_is_n LEQ H_SL Min H_SM M).
  apply (eq_Nat_is_symmetric) in H_M'.
  apply (eq_Nat_is_transitive (S M) (Min M (S M)) M H_M') in H_Con.
  apply (eq_Nat_is_symmetric) in H_Con.
  apply (a_natural_number_can_not_be_the_successor_of_itself M).
  exact H_Con.
Qed.
   
(* This lemma primarily serves as an eyeopener! The only neutral element
   for minimum would be the upper bound, but it does not exist. *)
 
Lemma There_is_no_left_neutral_element_for_minimum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      ~ (exists e : Nat,
           forall a : Nat,
             Min e a =N= a).
Proof.
  intros LEQ H_SL Min H_SM.
  exact (the_naturals_are_not_left_upper_bounded LEQ H_SL Min H_SM).
Qed.

(* Because there is no left neutral element, natural numbers and
   minimum does not have the properties of a monoid. *)

Theorem Natural_numbers_and_minimum_does_NOT_form_a_Monoid :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Min : Nat -> Nat -> Nat,
      specification_of_minimum Min ->
      ~ (T_and_Dot_form_a_Monoid_under_eqT Nat eq_Nat Min).
Proof.
  intros LEQ H_SLEQ Min H_SM.
  intro H_Monoid.
  unfold T_and_Dot_form_a_Monoid_under_eqT in H_Monoid.
  destruct H_Monoid as [_ [_ [_ [e H_e]]]].
  unfold specification_of_neutrality in H_e.
  destruct H_e as [_ H_e_L].
  apply (There_is_no_left_neutral_element_for_minimum LEQ H_SLEQ Min H_SM).
  exists e.
  exact H_e_L.
Qed.

(* If a natural number is less or equal to a another natural, the first natural
   number is not the maximum - the other is. On the converse the first natural 
   number is the maximum. *)

Definition specification_of_maximum (Max : Nat -> Nat -> Nat) :=
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    (forall m n : Nat,
       LEQ m n =B= TRUE ->
       Max m n =N= n)
    /\
    (forall m n : Nat,
       LEQ m n =B= FALSE ->
       Max m n =N= m).

(* Much like with minimum, one can move the successors out of the
   recursive call. One could properly just have defined Max as
  
   Max (S a) O = (S a)
   Max O (S b) = (S b)
   Max (S a) (S b) = S (Max a b) 

   instead of involving leq. The same goes with minimum. It is just more
   intuitive to use leq. *)

Lemma about_maximum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Max : Nat -> Nat -> Nat,
      specification_of_maximum Max ->
      forall a b : Nat,
        Max (S a) (S b) =N= S (Max a b).
Proof.
  intros LEQ H_SL Max H_SM.
  intros a b.
  unfold specification_of_maximum in H_SM.
  destruct (H_SM LEQ H_SL) as [H_SM_R H_SM_L]; clear H_SM.
  apply (destruct_LEQ LEQ H_SL (S a) (S b)); split; intro H_LEQ.
    unfold specification_of_LEQ in H_SL.
    destruct H_SL as [H_SL_T [H_SL_F H_SL_S]].
    assert (H_LEQ' := H_SL_S a b).
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_transitive TRUE (LEQ (S a) (S b)) (LEQ a b) H_LEQ) in H_LEQ'.
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_symmetric) in H_LEQ'.
    apply (eq_Nat_is_transitive (Max (S a) (S b)) (S b)).
      exact (H_SM_R (S a) (S b) H_LEQ).
    apply -> (unfold_eq_Nat_S_S).
    apply (eq_Nat_is_symmetric).
    exact (H_SM_R a b H_LEQ').
    
    unfold specification_of_LEQ in H_SL.
    destruct H_SL as [H_SL_T [H_SL_F H_SL_S]].
    assert (H_LEQ' := H_SL_S a b).
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_transitive FALSE (LEQ (S a) (S b)) (LEQ a b) H_LEQ) in H_LEQ'.
    apply (eq_Bool_is_symmetric) in H_LEQ.
    apply (eq_Bool_is_symmetric) in H_LEQ'.
    apply (eq_Nat_is_transitive (Max (S a) (S b)) (S a)).
      exact (H_SM_L (S a) (S b) H_LEQ).
    apply -> (unfold_eq_Nat_S_S).
    apply (eq_Nat_is_symmetric).
    exact (H_SM_L a b H_LEQ').
Qed.

Lemma maximum_is_unique :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall f g : Nat -> Nat -> Nat,
      specification_of_maximum f ->
      specification_of_maximum g ->
      forall m n : Nat,
        f m n =N= g m n.
Proof.
  intros LEQ H_SL f g H_Sf H_Sg m n.

  unfold specification_of_maximum in H_Sf.
  destruct (H_Sf LEQ H_SL) as [H_Sf_R H_Sf_L].
  unfold specification_of_maximum in H_Sg.
  destruct (H_Sg LEQ H_SL) as [H_Sg_R H_Sg_L].
  clear H_Sf H_Sg.

  apply (destruct_LEQ LEQ H_SL m n); split; intro H_LEQ.
    apply (eq_Nat_is_transitive (f m n) n).
      exact (H_Sf_R m n H_LEQ).
    apply (eq_Nat_is_symmetric).
    exact (H_Sg_R m n H_LEQ).
    
    apply (eq_Nat_is_transitive (f m n) m).
      exact (H_Sf_L m n H_LEQ).
    apply (eq_Nat_is_symmetric).
    exact (H_Sg_L m n H_LEQ).
Qed.

(* Zero is left neutral for maximum since Zero is less or equal
   to everything else. If Zero is on the left side, the right side will be
   chosen in maximum. This closely resembles the fact that the natural numbers
   has a lower bound, namely Zero. *)

Lemma Zero_is_left_neutral_in_maximum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Max : Nat -> Nat -> Nat,
      specification_of_maximum Max ->
      forall b : Nat,
        Max O b =N= b.
Proof.
  intros LEQ H_SLEQ Max H_SM b.
  unfold specification_of_maximum in H_SM.
  destruct (H_SM LEQ H_SLEQ) as [H_SM_R _]; clear H_SM.
  unfold specification_of_LEQ in H_SLEQ.
  destruct H_SLEQ as [H_SLEQ_T _].
  exact (H_SM_R O b (H_SLEQ_T b)).
Qed.

(* It is also the case that Zero is right neutral for Maximum. *)

Lemma Zero_is_right_neutral_in_maximum :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Max : Nat -> Nat -> Nat,
      specification_of_maximum Max ->
      forall b : Nat,
        Max b O =N= b.
Proof.
  intros LEQ H_SLEQ Max H_SM b.
  destruct b as [ | b'].
    exact (Zero_is_left_neutral_in_maximum LEQ H_SLEQ Max H_SM O).

    unfold specification_of_maximum in H_SM.
    destruct (H_SM LEQ H_SLEQ) as [_ H_SM_L]; clear H_SM.
    unfold specification_of_LEQ in H_SLEQ.
    destruct H_SLEQ as [_ [H_SLEQ_F _]].
    exact (H_SM_L (S b') O (H_SLEQ_F b')).
Qed.

(* Maximum is associative. This follows from the property about
   putting the successor outside the function, the neutral properties of
   Zero, preservation, and induction. *)

Lemma maximum_is_associative :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Max : Nat -> Nat -> Nat,
      specification_of_maximum Max ->
      specification_of_associativity Nat eq_Nat Max.
Proof.
  intros LEQ H_SL Max H_SM.
  unfold specification_of_associativity.
  intro a.
  induction a as [ | a' IHa'].
    intros b c.
    apply (eq_Nat_is_transitive (Max (Max O b) c) (Max b c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (Zero_is_left_neutral_in_maximum LEQ H_SL Max H_SM b).
    apply (eq_Nat_is_symmetric).
    exact (Zero_is_left_neutral_in_maximum LEQ H_SL Max H_SM (Max b c)).

    intros b c.
    destruct b as [ | b'].
      apply (eq_Nat_is_transitive (Max (Max (S a') O) c) (Max (S a') c)).
        apply (Dot_Nat_preserves_eq_Nat_RR).
        exact (Zero_is_right_neutral_in_maximum LEQ H_SL Max H_SM (S a')).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      apply (eq_Nat_is_symmetric).
      exact (Zero_is_left_neutral_in_maximum LEQ H_SL Max H_SM c).

      apply (eq_Nat_is_transitive (Max (Max (S a') (S b')) c)
                                  (Max (S (Max a' b')) c)).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (about_maximum LEQ H_SL Max H_SM a' b').
      destruct c as [ | c'].
        apply (eq_Nat_is_transitive (Max (S (Max a' b')) O) (S (Max a' b'))).
          exact (Zero_is_right_neutral_in_maximum 
                   LEQ H_SL Max H_SM (S (Max a' b'))).
        apply (eq_Nat_is_symmetric).
        apply (eq_Nat_is_transitive (Max (S a') (Max (S b') O)) 
                                    (Max (S a') (S b'))).
          apply (Dot_Nat_preserves_eq_Nat_LR).
          exact (Zero_is_right_neutral_in_maximum LEQ H_SL Max H_SM (S b')).
        exact (about_maximum LEQ H_SL Max H_SM a' b').

        apply (eq_Nat_is_transitive (Max (S (Max a' b')) (S c'))
                                    (S (Max (Max a' b') c'))).
          exact (about_maximum LEQ H_SL Max H_SM (Max a' b') c').
        apply (eq_Nat_is_transitive (S (Max (Max a' b') c'))
                                    (S (Max a' (Max b' c')))).
          apply -> (unfold_eq_Nat_S_S).
          exact (IHa' b' c').
        apply (eq_Nat_is_transitive (S (Max a' (Max b' c')))
                                    (Max (S a') (S (Max b' c')))).
          apply (eq_Nat_is_symmetric).
          exact (about_maximum LEQ H_SL Max H_SM a' (Max b' c')).
        apply (Dot_Nat_preserves_eq_Nat_LR).
        apply (eq_Nat_is_symmetric).
        exact (about_maximum LEQ H_SL Max H_SM b' c').
Qed.

(* Natural numbers and maximum form a monoid under eq_Nat. This
   follows from the neutral natural number/lower bound O and associativity. *)

Theorem Natural_Numbers_and_maximum_form_a_Monoid :
  forall LEQ : Nat -> Nat -> Boolean,
    specification_of_LEQ LEQ ->
    forall Max : Nat -> Nat -> Nat,
      specification_of_maximum Max ->
      T_and_Dot_form_a_Monoid_under_eqT Nat eq_Nat Max.
Proof.
  intros LEQ H_SL Max H_SM.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Nat_is_an_equivalence_relation_at_Nat).
    split.
      exact (Dot_Nat_preserves_eq_Nat Max).
      split.
        exact (maximum_is_associative LEQ H_SL Max H_SM).

        exists O.
        unfold specification_of_neutrality.
        split.
          exact (Zero_is_right_neutral_in_maximum LEQ H_SL Max H_SM).
          exact (Zero_is_left_neutral_in_maximum LEQ H_SL Max H_SM).
Qed.

(* Boolean Conjunction. Also known as the and operator. It returns
   TRUE iff. both input booleans are TRUE, else FALSE. *)

Definition specification_of_conjunction 
           (conj : Boolean -> Boolean -> Boolean) :=
  (forall b : Boolean,
     conj FALSE b =B= FALSE)
  /\
  (forall b : Boolean,
     conj TRUE b =B= b).

Lemma conjunction_is_unique :
  forall f g : Boolean -> Boolean -> Boolean,
    specification_of_conjunction f ->
    specification_of_conjunction g ->
    forall a b : Boolean,
      f a b =B= g a b.
Proof.
  intros f g H_Sf H_Sg.

  unfold specification_of_conjunction in H_Sf.
  destruct H_Sf as [H_Sf_F H_Sf_T].
  unfold specification_of_conjunction in H_Sg.
  destruct H_Sg as [H_Sg_F H_Sg_T].

  intros [ | ] b.
    apply (eq_Bool_is_transitive (f FALSE b) FALSE).
    exact (H_Sf_F b).
    apply (eq_Bool_is_symmetric).
    exact (H_Sg_F b).

    apply (eq_Bool_is_transitive (f TRUE b) b).
    exact (H_Sf_T b).
    apply (eq_Bool_is_symmetric).
    exact (H_Sg_T b).
Qed.

(* If the left side is true, the value of conjunction depends solely on the right
   boolean. This follows from the specification. *)

Lemma TRUE_is_left_neutral_for_conjunction :
  forall conj : Boolean -> Boolean -> Boolean,
    specification_of_conjunction conj ->
    forall b : Boolean,
      conj TRUE b =B= b.
Proof.
  intros conj H_SC.
  unfold specification_of_conjunction in H_SC.
  destruct H_SC as [_ H_SC_T].
  exact H_SC_T.
Qed.

(* However, TRUE is also neutral for the right side. *)

Lemma TRUE_is_right_neutral_for_conjunction :
  forall conj : Boolean -> Boolean -> Boolean,
    specification_of_conjunction conj ->
    forall b : Boolean,
      conj b TRUE =B= b.
Proof.
  intros conj H_SC.
  unfold specification_of_conjunction in H_SC.
  destruct H_SC as [H_SC_F H_SC_T].
  intros [ | ].
    exact (H_SC_F TRUE).
    exact (H_SC_T TRUE).
Qed.

(* For completeness, FALSE is both absorbent from the left and right side. *)

Lemma FALSE_is_left_absorbent_for_conjunction :
  forall conj : Boolean -> Boolean -> Boolean,
    specification_of_conjunction conj ->
    forall b : Boolean,
      conj FALSE b =B= FALSE. 
Proof.
  intros conj H_SC.
  unfold specification_of_conjunction in H_SC.
  destruct H_SC as [H_SC_F _].
  exact H_SC_F.
Qed.

Lemma FALSE_is_right_absorbent_for_conjunction :
  forall conj : Boolean -> Boolean -> Boolean,
    specification_of_conjunction conj ->
    forall b : Boolean,
      conj b FALSE =B= FALSE. 
Proof.
  intros conj H_SC.
  unfold specification_of_conjunction in H_SC.
  destruct H_SC as [H_SC_F H_SC_T].
  intros [ | ].
    exact (H_SC_F FALSE).
    exact (H_SC_T FALSE).
Qed.

(* It follows easily from the neutrality of TRUE and the absorbency of FALSE
   together with preservation that conjunction is associative. *)

Lemma conjunction_is_associative :
  forall conj : Boolean -> Boolean -> Boolean,
    specification_of_conjunction conj ->
    specification_of_associativity Boolean eq_Bool conj.
Proof.
  intros conj H_SC.
  unfold specification_of_associativity.
  intros [ | ] b c.
    apply (eq_Bool_is_transitive (conj (conj FALSE b) c) (conj FALSE c)).
      apply (Dot_Boolean_preserves_eq_Bool_RR).
      exact (FALSE_is_left_absorbent_for_conjunction conj H_SC b).
    apply (eq_Bool_is_transitive (conj FALSE c) FALSE).
      exact (FALSE_is_left_absorbent_for_conjunction conj H_SC c).
    apply (eq_Bool_is_symmetric).
    exact (FALSE_is_left_absorbent_for_conjunction conj H_SC (conj b c)).

    apply (eq_Bool_is_transitive (conj (conj TRUE b) c) (conj b c)).
      apply (Dot_Boolean_preserves_eq_Bool_RR).
      exact (TRUE_is_left_neutral_for_conjunction conj H_SC b).
    apply (eq_Bool_is_symmetric).
    exact (TRUE_is_left_neutral_for_conjunction conj H_SC (conj b c)).
Qed.

(* All these lemmas combined implies that booleans and conjunction 
   form a monoid under eq_Bool. *)

Theorem Booleans_and_conjunction_form_a_Monoid :
  forall conj : Boolean -> Boolean -> Boolean,
    specification_of_conjunction conj ->
    T_and_Dot_form_a_Monoid_under_eqT Boolean eq_Bool conj.
Proof.
  intros conj H_SC.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Bool_is_an_equivalence_relation).
    split.
      exact (Dot_Boolean_preserves_eq_Bool conj).
      split.
        exact (conjunction_is_associative conj H_SC).

        exists TRUE.
        unfold specification_of_neutrality.
        split.
          exact (TRUE_is_right_neutral_for_conjunction conj H_SC).
          exact (TRUE_is_left_neutral_for_conjunction conj H_SC).
Qed.

(* Boolean Disjunction, or 'or', returns true if either of the two input
   booleans are TRUE. *)

Definition specification_of_disjunction 
           (disj : Boolean -> Boolean -> Boolean) :=
  (forall b : Boolean,
     disj FALSE b =B= b)
  /\
  (forall b : Boolean,
     disj TRUE b =B= TRUE).

Lemma disjunction_is_unique :
  forall f g : Boolean -> Boolean -> Boolean,
    specification_of_disjunction f ->
    specification_of_disjunction g ->
    forall a b : Boolean,
      f a b =B= g a b.
Proof.
  intros f g H_Sf H_Sg.

  unfold specification_of_disjunction in H_Sf.
  destruct H_Sf as [H_Sf_F H_Sf_T].
  unfold specification_of_disjunction in H_Sg.
  destruct H_Sg as [H_Sg_F H_Sg_T].

  intros [ | ] b.
    apply (eq_Bool_is_transitive (f FALSE b) b).
      exact (H_Sf_F b).
    apply (eq_Bool_is_symmetric).
    exact (H_Sg_F b).

    apply (eq_Bool_is_transitive (f TRUE b) TRUE).
      exact (H_Sf_T b).
    apply (eq_Bool_is_symmetric).
    exact (H_Sg_T b).
Qed.  

(* FALSE is left neutral for disjunction, since if the left side is false,
   the result must be determined by the right side. 

   This follows from the specification. *)

Lemma FALSE_is_left_neutral_for_disjunction :
  forall disj : Boolean -> Boolean -> Boolean,
    specification_of_disjunction disj ->
    forall b : Boolean,
      disj FALSE b =B= b.
Proof.
  intros disj H_SD.
  unfold specification_of_disjunction in H_SD.
  destruct H_SD as [H_SD_F _].
  exact H_SD_F.
Qed.  

(* FALSE is also right neutral. This follows from a destruction on the left
   side and the specification. *)

Lemma FALSE_is_right_neutral_for_disjunction :
  forall disj : Boolean -> Boolean -> Boolean,
    specification_of_disjunction disj ->
    forall b : Boolean,
      disj b FALSE =B= b.
Proof.
  intros disj H_SD.
  unfold specification_of_disjunction in H_SD.
  destruct H_SD as [H_SD_F H_SD_T].
  intros [ | ].
    exact (H_SD_F FALSE).
    exact (H_SD_T FALSE).
Qed.  

(* TRUE is left absorbent for boolean disjunction. If a or b and
   a is true, then a or b. That is how it should be, and it follows from
   the specification. *)

Lemma TRUE_is_left_absorbent_for_disjunction :
  forall disj : Boolean -> Boolean -> Boolean,
    specification_of_disjunction disj ->
    forall b : Boolean,
      disj TRUE b =B= TRUE.
Proof.
  intros disj H_SD.
  unfold specification_of_disjunction in H_SD.
  destruct H_SD as [_ H_SD_T].
  exact H_SD_T.
Qed.

(* From a destruction and the specification it also follows that TRUE is
   right absorbent. *)

Lemma TRUE_is_right_absorbent_for_disjunction :
  forall disj : Boolean -> Boolean -> Boolean,
    specification_of_disjunction disj ->
    forall b : Boolean,
      disj b TRUE =B= TRUE.
Proof.
  intros disj H_SD.
  unfold specification_of_disjunction in H_SD.
  destruct H_SD as [H_SD_F H_SD_T].
  intros [ | ].
    exact (H_SD_F TRUE).
    exact (H_SD_T TRUE).
Qed.

(* From preservation, the neutral property of FALSE and the absorbent
   property of TRUE it follows that disjunction is associative. *)

Lemma disjunction_is_associative :
  forall disj : Boolean -> Boolean -> Boolean,
    specification_of_disjunction disj ->
    specification_of_associativity Boolean eq_Bool disj.
Proof.
  intros disj H_SD.
  unfold specification_of_associativity.
  intros [ | ] b c.
    apply (eq_Bool_is_transitive (disj (disj FALSE b) c) (disj b c)).
      apply (Dot_Boolean_preserves_eq_Bool_RR).
      exact (FALSE_is_left_neutral_for_disjunction disj H_SD b).
    apply (eq_Bool_is_symmetric).
    exact (FALSE_is_left_neutral_for_disjunction disj H_SD (disj b c)).

    apply (eq_Bool_is_transitive (disj (disj TRUE b) c) (disj TRUE c)).
      apply (Dot_Boolean_preserves_eq_Bool_RR).
      exact (TRUE_is_left_absorbent_for_disjunction disj H_SD b).
    apply (eq_Bool_is_transitive (disj TRUE c) TRUE).
      exact (TRUE_is_left_absorbent_for_disjunction disj H_SD c).
    apply (eq_Bool_is_symmetric).
    exact (TRUE_is_left_absorbent_for_disjunction disj H_SD (disj b c)).
Qed.

(* Therefore Booleans with boolean disjunction form a monoid under eq_Bool. *)

Theorem Booleans_and_disjunction_form_a_Monoid :
  forall disj : Boolean -> Boolean -> Boolean,
    specification_of_disjunction disj ->
    T_and_Dot_form_a_Monoid_under_eqT Boolean eq_Bool disj.
Proof.
  intros disj H_SD.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Bool_is_an_equivalence_relation).
    split.
      exact (Dot_Boolean_preserves_eq_Bool disj).
      split.
        exact (disjunction_is_associative disj H_SD).
        exists FALSE.
        unfold specification_of_neutrality.
        split.
          exact (FALSE_is_right_neutral_for_disjunction disj H_SD).
          exact (FALSE_is_left_neutral_for_disjunction disj H_SD).
Qed.

(* A 2x2 Matrix with natural numbers contains four naturals:
   a11, a12, a21 and a22. *)

Inductive M22 : Set :=
  | m22 : Nat -> Nat -> Nat -> Nat -> M22.

(* Two matrices are equal if all their natural numbers are equal at the right
   locations. *)

Definition eq_Matrix (A B : M22) :=
  match A with
      | m22 a11 a12 a21 a22 => match B with
                                   | m22 b11 b12 b21 b22 => a11 =N= b11 /\
                                                            a12 =N= b12 /\
                                                            a21 =N= b21 /\
                                                            a22 =N= b22
                               end
  end.

Notation "A =M= B" := (eq_Matrix A B) (at level 70, right associativity).

(* eq_Matrix is an equivalence relation since eq_Nat is. *)

Lemma eq_Matrix_is_reflexive :
  specification_of_a_reflexive_relation M22 eq_Matrix.
Proof.
  unfold specification_of_a_reflexive_relation.
  intros [ a11 a12 a21 a22 ].
  unfold eq_Matrix.
  split.
    apply eq_Nat_is_reflexive.
    split.
      apply eq_Nat_is_reflexive.
      split.
        apply eq_Nat_is_reflexive.
        apply eq_Nat_is_reflexive.
Qed.

Lemma eq_Matrix_is_symmetric :
  specification_of_a_symmetric_relation M22 eq_Matrix.
Proof.
  unfold specification_of_a_symmetric_relation.
  intros [ a11 a12 a21 a22 ] [ b11 b12 b21 b22] H_AB.
  unfold eq_Matrix in H_AB.
  destruct H_AB as [H_11 [H_12 [H_21 H_22]]].
  unfold eq_Matrix.
  split.
    exact (eq_Nat_is_symmetric a11 b11 H_11).
    split.
      exact (eq_Nat_is_symmetric a12 b12 H_12).
      split.
        exact (eq_Nat_is_symmetric a21 b21 H_21).
        exact (eq_Nat_is_symmetric a22 b22 H_22).
Qed.

Lemma eq_Matrix_is_transitive :
  specification_of_a_transitive_relation M22 eq_Matrix.
Proof.
  unfold specification_of_a_transitive_relation.
  intros [ a11 a12 a21 a22 ] [ b11 b12 b21 b22 ] [ c11 c12 c21 c22 ] H_AB H_BC.
  unfold eq_Matrix in H_AB, H_BC.
  destruct H_AB as [H_AB_11 [H_AB_12 [H_AB_21 H_AB_22]]].
  destruct H_BC as [H_BC_11 [H_BC_12 [H_BC_21 H_BC_22]]].
  unfold eq_Matrix.
  split.
    exact (eq_Nat_is_transitive a11 b11 c11 H_AB_11 H_BC_11).
    split.
      exact (eq_Nat_is_transitive a12 b12 c12 H_AB_12 H_BC_12).
      split.
        exact (eq_Nat_is_transitive a21 b21 c21 H_AB_21 H_BC_21).
        exact (eq_Nat_is_transitive a22 b22 c22 H_AB_22 H_BC_22).
Qed. 

Lemma eq_Matrix_is_an_equivalence_relation_under_M22 :
  specification_of_an_equivalence_relation M22 eq_Matrix.
Proof.
  unfold specification_of_an_equivalence_relation.
  split.
    exact eq_Matrix_is_reflexive.
    split.
      exact eq_Matrix_is_symmetric.
      exact eq_Matrix_is_transitive.
Qed.

(* Matrix addition is done by adding each natural numbers together at their 
   respective positions into a new matrix. *)

Definition specification_of_matrix_addition 
           (NMAdd : M22 -> M22 -> M22) :=
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    (forall a11 a12 a21 a22 b11 b12 b21 b22 : Nat,
       NMAdd (m22 a11 a12 a21 a22) (m22 b11 b12 b21 b22) =M=
       m22 (NAdd a11 b11) (NAdd a12 b12) (NAdd a21 b21) (NAdd a22 b22)).

(* It is not easy to show that any binary operation on matrices preserves
   eq_Matrix. But it can be shown easily for matrix addition because
   of addition's preservation of eq_Nat. *)

Lemma matrix_addition_preserves_eq_Matrix :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMAdd : M22 -> M22 -> M22,
      specification_of_matrix_addition NMAdd ->
      specification_of_preservation M22 eq_Matrix NMAdd.
Proof.
  intros NAdd H_SA NMAdd H_SMA.
  unfold specification_of_preservation.
  unfold specification_of_matrix_addition in H_SMA.
  assert (H_SMA' := H_SMA NAdd H_SA); clear H_SMA.
  intros [ a11 a12 a21 a22 ] [ b11 b12 b21 b22 ] 
         [ c11 c12 c21 c22 ] [ d11 d12 d21 d22 ] H_ab H_cd.
  unfold eq_Matrix in H_ab.
  destruct H_ab as [H_ab_11 [H_ab_12 [H_ab_21 H_ab_22]]].
  unfold eq_Matrix in H_cd.
  destruct H_cd as [H_cd_11 [H_cd_12 [H_cd_21 H_cd_22]]].
  apply (eq_Matrix_is_transitive 
           (NMAdd (m22 a11 a12 a21 a22) (m22 c11 c12 c21 c22))
           (m22 (NAdd a11 c11) (NAdd a12 c12) (NAdd a21 c21) (NAdd a22 c22))).
    exact (H_SMA' a11 a12 a21 a22 c11 c12 c21 c22).
  apply (eq_Matrix_is_symmetric).
  apply (eq_Matrix_is_transitive 
           (NMAdd (m22 b11 b12 b21 b22) (m22 d11 d12 d21 d22))
           (m22 (NAdd b11 d11) (NAdd b12 d12) (NAdd b21 d21) (NAdd b22 d22))).
    exact (H_SMA' b11 b12 b21 b22 d11 d12 d21 d22).
  apply (eq_Matrix_is_symmetric).
  unfold eq_Matrix.
  split.
    exact (Dot_Nat_preserves_eq_Nat NAdd a11 b11 c11 d11 H_ab_11 H_cd_11).
    split.
      exact (Dot_Nat_preserves_eq_Nat NAdd a12 b12 c12 d12 H_ab_12 H_cd_12).
      split.
        exact (Dot_Nat_preserves_eq_Nat NAdd a21 b21 c21 d21 H_ab_21 H_cd_21).
        exact (Dot_Nat_preserves_eq_Nat NAdd a22 b22 c22 d22 H_ab_22 H_cd_22).
Qed.

Lemma matrix_addition_is_unique :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall f g : M22 -> M22 -> M22,
      specification_of_matrix_addition f ->
      specification_of_matrix_addition g ->
      forall A B : M22,
        f A B =M= g A B.
Proof.
  intros NAdd H_SNA f g H_Sf H_Sg [a11 a12 a21 a22] [b11 b12 b21 b22].
  unfold specification_of_matrix_addition in H_Sf.
  unfold specification_of_matrix_addition in H_Sg.
  apply (eq_Matrix_is_transitive 
           (f (m22 a11 a12 a21 a22) (m22 b11 b12 b21 b22))
           (m22 (NAdd a11 b11) (NAdd a12 b12) (NAdd a21 b21) (NAdd a22 b22))).
    exact (H_Sf NAdd H_SNA a11 a12 a21 a22 b11 b12 b21 b22).
  apply (eq_Matrix_is_symmetric).
  exact (H_Sg NAdd H_SNA a11 a12 a21 a22 b11 b12 b21 b22).
Qed.

(* If Zero is added to every position in a matrix, all positions in the
   new matrix will have the same natural numbers in each position. *)

Lemma the_zero_matrix_is_left_neutral_for_matrix_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMAdd : M22 -> M22 -> M22,
      specification_of_matrix_addition NMAdd ->
      forall A : M22,
        NMAdd (m22 O O O O) A =M= A.
Proof.
  intros NAdd H_SNA NMAdd H_SNMA [a11 a12 a21 a22].
  unfold specification_of_matrix_addition in H_SNMA.
  apply (eq_Matrix_is_transitive 
           (NMAdd (m22 O O O O) (m22 a11 a12 a21 a22))
           (m22 (NAdd O a11) (NAdd O a12) (NAdd O a21) (NAdd O a22))).
    exact (H_SNMA NAdd H_SNA O O O O a11 a12 a21 a22).
  unfold eq_Matrix.
  split.
    exact (Zero_is_left_neutral_for_addition NAdd H_SNA a11).
    split.
      exact (Zero_is_left_neutral_for_addition NAdd H_SNA a12).
      split.
        exact (Zero_is_left_neutral_for_addition NAdd H_SNA a21).
        exact (Zero_is_left_neutral_for_addition NAdd H_SNA a22).
Qed.

(* This is also the case if zero is added from the right side since
   addition also has zero as a neutral element on the right. *)

Lemma the_zero_matrix_is_right_neutral_for_matrix_addition :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMAdd : M22 -> M22 -> M22,
      specification_of_matrix_addition NMAdd ->
      forall A : M22,
        NMAdd A (m22 O O O O) =M= A.
Proof.
  intros NAdd H_SNA NMAdd H_SNMA [a11 a12 a21 a22].
  unfold specification_of_matrix_addition in H_SNMA.
  apply (eq_Matrix_is_transitive 
           (NMAdd (m22 a11 a12 a21 a22) (m22 O O O O))
           (m22 (NAdd a11 O) (NAdd a12 O) (NAdd a21 O) (NAdd a22 O))).
    exact (H_SNMA NAdd H_SNA a11 a12 a21 a22 O O O O).
  unfold eq_Matrix.
  split.
    exact (Zero_is_right_neutral_for_addition NAdd H_SNA a11).
    split.
      exact (Zero_is_right_neutral_for_addition NAdd H_SNA a12).
      split.
        exact (Zero_is_right_neutral_for_addition NAdd H_SNA a21).
        exact (Zero_is_right_neutral_for_addition NAdd H_SNA a22).
Qed.

(* Because of the associative properties of addition, matrix
   addition is also associative. *)

Lemma matrix_addition_is_associative :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMAdd : M22 -> M22 -> M22,
      specification_of_matrix_addition NMAdd ->
      specification_of_associativity M22 eq_Matrix NMAdd.
Proof.
  unfold specification_of_associativity.
  intros NAdd H_SNA NMAdd H_SNMA [a11 a12 a21 a22]
                                 [b11 b12 b21 b22]
                                 [c11 c12 c21 c22].
  unfold specification_of_matrix_addition in H_SNMA.
  apply (eq_Matrix_is_transitive
        (NMAdd (NMAdd (m22 a11 a12 a21 a22) (m22 b11 b12 b21 b22)) 
               (m22 c11 c12 c21 c22))
        (NMAdd (m22 (NAdd a11 b11) (NAdd a12 b12) (NAdd a21 b21) (NAdd a22 b22))
               (m22 c11 c12 c21 c22))).
    apply (matrix_addition_preserves_eq_Matrix NAdd H_SNA NMAdd H_SNMA).
    exact (H_SNMA NAdd H_SNA a11 a12 a21 a22 b11 b12 b21 b22).
    exact (eq_Matrix_is_reflexive (m22 c11 c12 c21 c22)).
  apply (eq_Matrix_is_transitive
        (NMAdd (m22 (NAdd a11 b11) (NAdd a12 b12) (NAdd a21 b21) (NAdd a22 b22))
               (m22 c11 c12 c21 c22))
        (m22 (NAdd (NAdd a11 b11) c11) (NAdd (NAdd a12 b12) c12)
             (NAdd (NAdd a21 b21) c21) (NAdd (NAdd a22 b22) c22))).
    exact (H_SNMA NAdd H_SNA (NAdd a11 b11) (NAdd a12 b12) (NAdd a21 b21)
                             (NAdd a22 b22) c11 c12 c21 c22).
  apply (eq_Matrix_is_symmetric).
  apply (eq_Matrix_is_transitive
        (NMAdd (m22 a11 a12 a21 a22) 
           (NMAdd (m22 b11 b12 b21 b22) (m22 c11 c12 c21 c22)))
        (NMAdd (m22 a11 a12 a21 a22)
           (m22 (NAdd b11 c11) (NAdd b12 c12) (NAdd b21 c21) (NAdd b22 c22)))).
    apply (matrix_addition_preserves_eq_Matrix NAdd H_SNA NMAdd H_SNMA).
    exact (eq_Matrix_is_reflexive (m22 a11 a12 a21 a22)).
    exact (H_SNMA NAdd H_SNA b11 b12 b21 b22 c11 c12 c21 c22).
  apply (eq_Matrix_is_transitive
        (NMAdd (m22 a11 a12 a21 a22)
               (m22 (NAdd b11 c11) (NAdd b12 c12) (NAdd b21 c21) (NAdd b22 c22)))
        (m22 (NAdd a11 (NAdd b11 c11)) (NAdd a12 (NAdd b12 c12))
             (NAdd a21 (NAdd b21 c21)) (NAdd a22 (NAdd b22 c22)))).
    exact (H_SNMA NAdd H_SNA a11 a12 a21 a22 (NAdd b11 c11) (NAdd b12 c12)
                  (NAdd b21 c21) (NAdd b22 c22)).
  apply (eq_Matrix_is_symmetric).
  unfold eq_Matrix.
  split.
    exact (addition_is_associative NAdd H_SNA a11 b11 c11).
    split.
      exact (addition_is_associative NAdd H_SNA a12 b12 c12).
      split.
        exact (addition_is_associative NAdd H_SNA a21 b21 c21).
        exact (addition_is_associative NAdd H_SNA a22 b22 c22).
Qed.

(* These lemmas implies that natural 2x2 matrices and matrix addition
   form a monoid under eq_Matrix. The neutral element is the matrix containing
   all zeroes. *)

Theorem Natural_Matrices_and_matrix_addition_form_a_Monoid :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMAdd : M22 -> M22 -> M22,
      specification_of_matrix_addition NMAdd ->
      T_and_Dot_form_a_Monoid_under_eqT M22 eq_Matrix NMAdd.
Proof.
  intros NAdd H_SNA NMAdd H_SNMA.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Matrix_is_an_equivalence_relation_under_M22).
    split.
      exact (matrix_addition_preserves_eq_Matrix NAdd H_SNA NMAdd H_SNMA).
      split.
        exact (matrix_addition_is_associative NAdd H_SNA NMAdd H_SNMA).
        
        exists (m22 O O O O).
        unfold specification_of_neutrality.
        split.
          exact (the_zero_matrix_is_right_neutral_for_matrix_addition
                   NAdd H_SNA NMAdd H_SNMA).
          exact (the_zero_matrix_is_left_neutral_for_matrix_addition
                   NAdd H_SNA NMAdd H_SNMA).
Qed.

(* 2x2 Matrix Multiplication is defined like this because it makes
   sense for linear transformations. *)

Definition specification_of_matrix_multiplication 
           (NMMul : M22 -> M22 -> M22) :=
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a11 a12 a21 a22 b11 b12 b21 b22 : Nat,
        NMMul (m22 a11 a12 a21 a22) (m22 b11 b12 b21 b22) =M=
        (m22 (NAdd (NMul a11 b11) (NMul a12 b21))
             (NAdd (NMul a11 b12) (NMul a12 b22))
             (NAdd (NMul a21 b11) (NMul a22 b21))
             (NAdd (NMul a21 b12) (NMul a22 b22))).

Lemma matrix_multiplication_preserves_eq_Matrix :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall NMMul : M22 -> M22 -> M22,
        specification_of_matrix_multiplication NMMul ->
        specification_of_preservation M22 eq_Matrix NMMul.
Proof.
  intros NAdd H_SA NMul H_SM NMMul H_SMM.
  unfold specification_of_preservation.
  intros [ a11 a12 a21 a22 ] [ b11 b12 b21 b22 ] [ c11 c12 c21 c22]
         [ d11 d12 d21 d22 ] H_AB H_CD.
  unfold eq_Matrix in H_AB, H_CD.
  destruct H_AB as [H_AB_11 [H_AB_12 [H_AB_21 H_AB_22]]].
  destruct H_CD as [H_CD_11 [H_CD_12 [H_CD_21 H_CD_22]]].
  unfold specification_of_matrix_multiplication in H_SMM.
  assert (H_SMM' := H_SMM NAdd H_SA NMul H_SM); clear H_SMM.
  apply (eq_Matrix_is_transitive 
           (NMMul (m22 a11 a12 a21 a22) (m22 c11 c12 c21 c22))
           (m22 (NAdd (NMul a11 c11) (NMul a12 c21))
                (NAdd (NMul a11 c12) (NMul a12 c22))
                (NAdd (NMul a21 c11) (NMul a22 c21))
                (NAdd (NMul a21 c12) (NMul a22 c22)))).
    exact (H_SMM' a11 a12 a21 a22 c11 c12 c21 c22).
  apply (eq_Matrix_is_symmetric).
  apply (eq_Matrix_is_transitive 
           (NMMul (m22 b11 b12 b21 b22) (m22 d11 d12 d21 d22))
           (m22 (NAdd (NMul b11 d11) (NMul b12 d21))
                (NAdd (NMul b11 d12) (NMul b12 d22))
                (NAdd (NMul b21 d11) (NMul b22 d21))
                (NAdd (NMul b21 d12) (NMul b22 d22)))).
    exact (H_SMM' b11 b12 b21 b22 d11 d12 d21 d22).
  apply (eq_Matrix_is_symmetric).
  unfold eq_Matrix.
  split.

  apply (Dot_Nat_preserves_eq_Nat).
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_11.
  exact H_CD_11.
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_12.
  exact H_CD_21.
  split.

  apply (Dot_Nat_preserves_eq_Nat).
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_11.
  exact H_CD_12.
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_12.
  exact H_CD_22.
  split.

  apply (Dot_Nat_preserves_eq_Nat).
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_21.
  exact H_CD_11.
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_22.
  exact H_CD_21.

  apply (Dot_Nat_preserves_eq_Nat).
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_21.
  exact H_CD_12.
  apply (Dot_Nat_preserves_eq_Nat).
  exact H_AB_22.
  exact H_CD_22.
Qed.

Lemma matrix_multiplication_is_unique :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall f g : M22 -> M22 -> M22,
        specification_of_matrix_multiplication f ->
        specification_of_matrix_multiplication g ->
        forall A B : M22,
          f A B =M= g A B.
Proof.
  intros NAdd H_SNA NMul H_SNM f g H_Sf H_Sg.

  unfold specification_of_matrix_multiplication in H_Sf.
  assert (H_Sf' := H_Sf NAdd H_SNA NMul H_SNM); clear H_Sf.
  unfold specification_of_matrix_multiplication in H_Sg.
  assert (H_Sg' := H_Sg NAdd H_SNA NMul H_SNM); clear H_Sg.

  intros [a11 a12 a21 a22] [b11 b12 b21 b22].
  apply (eq_Matrix_is_transitive
           (f (m22 a11 a12 a21 a22) (m22 b11 b12 b21 b22))
           (m22 (NAdd (NMul a11 b11) (NMul a12 b21))
            (NAdd (NMul a11 b12) (NMul a12 b22))
            (NAdd (NMul a21 b11) (NMul a22 b21))
            (NAdd (NMul a21 b12) (NMul a22 b22)))).
    exact (H_Sf' a11 a12 a21 a22 b11 b12 b21 b22).
  apply (eq_Matrix_is_symmetric).
  exact (H_Sg' a11 a12 a21 a22 b11 b12 b21 b22).
Qed.

(* It can be proved that the identity matrix (1 0 0 1) is neutral for matrix
   multiplication. In principle it selects every one element from the other
   matrix. It is neutral on both the left and the right side. *)

Lemma about_one_and_zero_in_addition_and_multiplication_l :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a b : Nat,
        NAdd (NMul (S O) a) (NMul O b) =N= a.
Proof.
  intros NAdd H_SA NMul H_SM.
  intros a b.
  apply (eq_Nat_is_transitive (NAdd (NMul (S O) a) (NMul O b)) 
                              (NAdd (NMul (S O) a) O)).
    apply (Dot_Nat_preserves_eq_Nat_LR).
    exact (Zero_is_left_absorbent_for_multiplication 
             NAdd H_SA NMul H_SM b).
  apply (eq_Nat_is_transitive (NAdd (NMul (S O) a) O) (NAdd a O)).
    apply (Dot_Nat_preserves_eq_Nat_RR).
    exact (successor_of_Zero_is_left_neutral_for_multiplication
             NAdd H_SA NMul H_SM a).
  exact (Zero_is_right_neutral_for_addition NAdd H_SA a).
Qed.

Lemma about_one_and_zero_in_addition_and_multiplication_r :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a b : Nat,
        NAdd (NMul a (S O)) (NMul b O) =N= a.
Proof.
  intros NAdd H_SA NMul H_SM.
  intros a b.
  apply (eq_Nat_is_transitive (NAdd (NMul a (S O)) (NMul b O)) 
                              (NAdd (NMul (S O) a) (NMul O b))).
    apply (Dot_Nat_preserves_eq_Nat).
      apply (eq_Nat_is_transitive (NMul a (S O)) a).
        exact (successor_of_Zero_is_right_neutral_for_multiplication
                 NAdd H_SA NMul H_SM a).
      apply (eq_Nat_is_symmetric).
      exact (successor_of_Zero_is_left_neutral_for_multiplication
               NAdd H_SA NMul H_SM a).
    apply (eq_Nat_is_transitive (NMul b O) O).
      exact (Zero_is_right_absorbent_for_multiplication
               NAdd H_SA NMul H_SM b).
    apply (eq_Nat_is_symmetric).
    exact (Zero_is_left_absorbent_for_multiplication
             NAdd H_SA NMul H_SM b).
  exact (about_one_and_zero_in_addition_and_multiplication_l
           NAdd H_SA NMul H_SM a b).
Qed.

Lemma about_zero_and_one_in_addition_and_multiplication_l :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a b : Nat,
        NAdd (NMul O a) (NMul (S O) b) =N= b.
Proof.
  intros NAdd H_SA NMul H_SM.
  intros a b.
  apply (eq_Nat_is_transitive (NAdd (NMul O a) (NMul (S O) b))
                              (NAdd (NMul (S O) b) (NMul O a))).
    exact (addition_is_commutative NAdd H_SA (NMul O a) (NMul (S O) b)).
  exact (about_one_and_zero_in_addition_and_multiplication_l 
           NAdd H_SA NMul H_SM b a).
Qed.

Lemma about_zero_and_one_in_addition_and_multiplication_r :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a b : Nat,
        NAdd (NMul a O) (NMul b (S O)) =N= b.
Proof.
  intros NAdd H_SA NMul H_SM.
  intros a b.
  apply (eq_Nat_is_transitive (NAdd (NMul a O) (NMul b (S O)))
                              (NAdd (NMul b (S O)) (NMul a O))).
    exact (addition_is_commutative NAdd H_SA (NMul a O) (NMul b (S O))).
  exact (about_one_and_zero_in_addition_and_multiplication_r
           NAdd H_SA NMul H_SM b a).
Qed.

Lemma identity_matrix_is_left_neutral_for_matrix_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall NMMul : M22 -> M22 -> M22,
        specification_of_matrix_multiplication NMMul ->
        forall A : M22,
          NMMul (m22 (S O) O O (S O)) A =M= A.
Proof.
  intros NAdd H_SNA NMul H_SNM NMMul H_SNMM [a11 a12 a21 a22].
  unfold specification_of_matrix_multiplication in H_SNMM.
  assert (H_SNMM' := H_SNMM NAdd H_SNA NMul H_SNM); clear H_SNMM.
  apply (eq_Matrix_is_transitive 
           (NMMul (m22 (S O) O O (S O)) (m22 a11 a12 a21 a22))
           (m22 (NAdd (NMul (S O) a11) (NMul O a21))
                (NAdd (NMul (S O) a12) (NMul O a22))
                (NAdd (NMul O a11) (NMul (S O) a21))
                (NAdd (NMul O a12) (NMul (S O) a22)))).
    exact (H_SNMM' (S O) O O (S O) a11 a12 a21 a22).
  unfold eq_Matrix.
  split.
    exact (about_one_and_zero_in_addition_and_multiplication_l 
             NAdd H_SNA NMul H_SNM a11 a21).
  split.
    exact (about_one_and_zero_in_addition_and_multiplication_l 
             NAdd H_SNA NMul H_SNM a12 a22).
  split.
    exact (about_zero_and_one_in_addition_and_multiplication_l
             NAdd H_SNA NMul H_SNM a11 a21).
    exact (about_zero_and_one_in_addition_and_multiplication_l 
             NAdd H_SNA NMul H_SNM a12 a22).
Qed. 

Lemma identity_matrix_is_right_neutral_for_matrix_multiplication :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall NMMul : M22 -> M22 -> M22,
        specification_of_matrix_multiplication NMMul ->
        forall A : M22,
          NMMul A (m22 (S O) O O (S O)) =M= A.
Proof.
  intros NAdd H_SNA NMul H_SNM NMMul H_SNMM [a11 a12 a21 a22].
  unfold specification_of_matrix_multiplication in H_SNMM.
  assert (H_SNMM' := H_SNMM NAdd H_SNA NMul H_SNM); clear H_SNMM.
  apply (eq_Matrix_is_transitive 
           (NMMul (m22 a11 a12 a21 a22) (m22 (S O) O O (S O)))
           (m22 (NAdd (NMul a11 (S O)) (NMul a12 O))
                (NAdd (NMul a11 O) (NMul a12 (S O)))
                (NAdd (NMul a21 (S O)) (NMul a22 O))
                (NAdd (NMul a21 O) (NMul a22 (S O))))).
    exact (H_SNMM' a11 a12 a21 a22 (S O) O O (S O)).
  unfold eq_Matrix.
  split.
    exact (about_one_and_zero_in_addition_and_multiplication_r 
             NAdd H_SNA NMul H_SNM a11 a12).
  split.
    exact (about_zero_and_one_in_addition_and_multiplication_r 
             NAdd H_SNA NMul H_SNM a11 a12).
  split.
    exact (about_one_and_zero_in_addition_and_multiplication_r 
             NAdd H_SNA NMul H_SNM a21 a22).
    exact (about_zero_and_one_in_addition_and_multiplication_r 
             NAdd H_SNA NMul H_SNM a21 a22).
Qed.

(* This is a lemma that helps a lot in proving the associativity of matrix
   multiplication. It is pure arithmetic relying on the properties of multi-
   plication and addition. If * is multiplication in infix and + is addition, 
   this lemma shows that

   (a11*b11 + a12*b21)*c11 + (a11*b12 + a12*b22)*c21 =N=
   a11*(b11*c11 + b12*c21) + a12*(b21*c11 + b22*c21) 

   Since this is not polymorphic equality, I can not use rewrites. This makes
   the lemma very bulky since I work directly with the lemmas about the
   equivalence relations. *)  

Lemma about_distributivity_in_each_matrix_point :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall a11 b11 a12 b21 c11 b12 b22 c21 : Nat,
        NAdd (NMul (NAdd (NMul a11 b11) (NMul a12 b21)) c11)
             (NMul (NAdd (NMul a11 b12) (NMul a12 b22)) c21) =N=
        NAdd (NMul a11 (NAdd (NMul b11 c11) (NMul b12 c21)))
             (NMul a12 (NAdd (NMul b21 c11) (NMul b22 c21))).
Proof.
  intros NAdd H_SA NMul H_SM a11 b11 a12 b21 c11 b12 b22 c21.

  apply (eq_Nat_is_transitive 
           (NAdd (NMul (NAdd (NMul a11 b11) (NMul a12 b21)) c11)
                 (NMul (NAdd (NMul a11 b12) (NMul a12 b22)) c21))
           (NAdd (NAdd (NMul (NMul a11 b11) c11) (NMul (NMul a12 b21) c11))
                 (NMul (NAdd (NMul a11 b12) (NMul a12 b22)) c21))).
    apply (Dot_Nat_preserves_eq_Nat_RR).
    exact (multiplication_is_right_distributive_over_addition
             NAdd H_SA NMul H_SM (NMul a11 b11) (NMul a12 b21) c11).

  apply (eq_Nat_is_transitive 
          (NAdd (NAdd (NMul (NMul a11 b11) c11) (NMul (NMul a12 b21) c11))
                (NMul (NAdd (NMul a11 b12) (NMul a12 b22)) c21))
          (NAdd (NAdd (NMul (NMul a11 b11) c11) (NMul (NMul a12 b21) c11))
                (NAdd (NMul (NMul a11 b12) c21) (NMul (NMul a12 b22) c21)))).
    apply (Dot_Nat_preserves_eq_Nat_LR).
    exact (multiplication_is_right_distributive_over_addition
             NAdd H_SA NMul H_SM (NMul a11 b12) (NMul a12 b22) c21).

  apply (eq_Nat_is_transitive
           (NAdd (NAdd (NMul (NMul a11 b11) c11) (NMul (NMul a12 b21) c11))
                 (NAdd (NMul (NMul a11 b12) c21) (NMul (NMul a12 b22) c21)))
           (NAdd (NMul (NMul a11 b11) c11) (NAdd (NMul (NMul a12 b21) c11)
                 (NAdd (NMul (NMul a11 b12) c21) (NMul (NMul a12 b22) c21))))).
    exact (addition_is_associative NAdd H_SA
          (NMul (NMul a11 b11) c11) (NMul (NMul a12 b21) c11)
          (NAdd (NMul (NMul a11 b12) c21) (NMul (NMul a12 b22) c21))).

  apply (eq_Nat_is_transitive
           (NAdd (NMul (NMul a11 b11) c11) (NAdd (NMul (NMul a12 b21) c11)
                 (NAdd (NMul (NMul a11 b12) c21) (NMul (NMul a12 b22) c21))))
           (NAdd (NMul (NMul a11 b11) c11) (NAdd (NAdd (NMul (NMul a12 b21) c11)
                 (NMul (NMul a11 b12) c21)) (NMul (NMul a12 b22) c21)))).
    apply (Dot_Nat_preserves_eq_Nat_LR).
    apply (eq_Nat_is_symmetric).
    exact (addition_is_associative NAdd H_SA
           (NMul (NMul a12 b21) c11) (NMul (NMul a11 b12) c21)
           (NMul (NMul a12 b22) c21)).

  apply (eq_Nat_is_transitive
           (NAdd (NMul (NMul a11 b11) c11)
                 (NAdd (NAdd (NMul (NMul a12 b21) c11) (NMul (NMul a11 b12) c21))
                       (NMul (NMul a12 b22) c21)))
           (NAdd (NMul (NMul a11 b11) c11)
                 (NAdd (NAdd (NMul (NMul a11 b12) c21) (NMul (NMul a12 b21) c11))
                 (NMul (NMul a12 b22) c21)))).
    apply (Dot_Nat_preserves_eq_Nat_LR).
    apply (Dot_Nat_preserves_eq_Nat_RR).
    exact (addition_is_commutative NAdd H_SA
             (NMul (NMul a12 b21) c11) (NMul (NMul a11 b12) c21)).

  apply (eq_Nat_is_transitive
           (NAdd (NMul (NMul a11 b11) c11) (NAdd (NAdd (NMul (NMul a11 b12) c21)
                 (NMul (NMul a12 b21) c11)) (NMul (NMul a12 b22) c21)))
           (NAdd (NMul (NMul a11 b11) c11) (NAdd (NMul (NMul a11 b12) c21)
                 (NAdd (NMul (NMul a12 b21) c11) (NMul (NMul a12 b22) c21))))).
    apply (Dot_Nat_preserves_eq_Nat_LR).
    exact (addition_is_associative NAdd H_SA
           (NMul (NMul a11 b12) c21) (NMul (NMul a12 b21) c11)
           (NMul (NMul a12 b22) c21)).

  apply (eq_Nat_is_transitive
           (NAdd (NMul (NMul a11 b11) c11) (NAdd (NMul (NMul a11 b12) c21)
                 (NAdd (NMul (NMul a12 b21) c11) (NMul (NMul a12 b22) c21))))
           (NAdd (NAdd (NMul (NMul a11 b11) c11) (NMul (NMul a11 b12) c21))
                 (NAdd (NMul (NMul a12 b21) c11) (NMul (NMul a12 b22) c21)))).
    apply (eq_Nat_is_symmetric).
    exact (addition_is_associative NAdd H_SA
          (NMul (NMul a11 b11) c11) (NMul (NMul a11 b12) c21)
          (NAdd (NMul (NMul a12 b21) c11) (NMul (NMul a12 b22) c21))).

  apply (Dot_Nat_preserves_eq_Nat).
    apply (eq_Nat_is_transitive
             (NAdd (NMul (NMul a11 b11) c11) (NMul (NMul a11 b12) c21))
             (NAdd (NMul a11 (NMul b11 c11)) (NMul (NMul a11 b12) c21))).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (multiplication_is_associative NAdd H_SA NMul H_SM a11 b11 c11).
    
    apply (eq_Nat_is_transitive
             (NAdd (NMul a11 (NMul b11 c11)) (NMul (NMul a11 b12) c21))
             (NAdd (NMul a11 (NMul b11 c11)) (NMul a11 (NMul b12 c21)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact (multiplication_is_associative NAdd H_SA NMul H_SM a11 b12 c21).
    apply (eq_Nat_is_symmetric).
    exact (multiplication_is_left_distributive_over_addition
             NAdd H_SA NMul H_SM a11 (NMul b11 c11) (NMul b12 c21)).

    apply (eq_Nat_is_transitive
             (NAdd (NMul (NMul a12 b21) c11) (NMul (NMul a12 b22) c21))
             (NAdd (NMul a12 (NMul b21 c11)) (NMul (NMul a12 b22) c21))).
      apply (Dot_Nat_preserves_eq_Nat_RR).
      exact (multiplication_is_associative NAdd H_SA NMul H_SM a12 b21 c11).  
    apply (eq_Nat_is_transitive
             (NAdd (NMul a12 (NMul b21 c11)) (NMul (NMul a12 b22) c21))
             (NAdd (NMul a12 (NMul b21 c11)) (NMul a12 (NMul b22 c21)))).
      apply (Dot_Nat_preserves_eq_Nat_LR).
      exact (multiplication_is_associative NAdd H_SA NMul H_SM a12 b22 c21).
    apply (eq_Nat_is_symmetric).
    exact (multiplication_is_left_distributive_over_addition
             NAdd H_SA NMul H_SM a12 (NMul b21 c11) (NMul b22 c21)).
Qed.

(* To prove associativity of matrix multiplication, one can unfold all the
   multiplications. This will lead to the objective of proving four equivalences
   on the form above. It is pretty bulky. *)

Lemma matrix_multiplication_is_associative :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall NMMul : M22 -> M22 -> M22,
        specification_of_matrix_multiplication NMMul ->
        specification_of_associativity M22 eq_Matrix NMMul.
Proof.
  intros NAdd H_SNA NMul H_SNM NMMul H_SNMM.
  unfold specification_of_associativity.
  intros [a11 a12 a21 a22] [b11 b12 b21 b22] [c11 c12 c21 c22].
  assert (H_SNMM' := H_SNMM).
  unfold specification_of_matrix_multiplication in H_SNMM'.
  assert (H_SNMMU := H_SNMM' NAdd H_SNA NMul H_SNM); clear H_SNMM'.
  apply (eq_Matrix_is_transitive 
           (NMMul (NMMul (m22 a11 a12 a21 a22) (m22 b11 b12 b21 b22))
                  (m22 c11 c12 c21 c22))
           (NMMul (m22 (NAdd (NMul a11 b11) (NMul a12 b21))
                       (NAdd (NMul a11 b12) (NMul a12 b22))
                       (NAdd (NMul a21 b11) (NMul a22 b21))
                       (NAdd (NMul a21 b12) (NMul a22 b22)))
                  (m22 c11 c12 c21 c22))).
    apply (matrix_multiplication_preserves_eq_Matrix
             NAdd H_SNA NMul H_SNM NMMul H_SNMM).
    exact (H_SNMM NAdd H_SNA NMul H_SNM a11 a12 a21 a22 b11 b12 b21 b22).
    exact (eq_Matrix_is_reflexive (m22 c11 c12 c21 c22)).

  apply (eq_Matrix_is_transitive
           (NMMul (m22 (NAdd (NMul a11 b11) (NMul a12 b21))
                       (NAdd (NMul a11 b12) (NMul a12 b22))
                       (NAdd (NMul a21 b11) (NMul a22 b21))
                       (NAdd (NMul a21 b12) (NMul a22 b22))) 
                  (m22 c11 c12 c21 c22))
           (m22
              (NAdd (NMul (NAdd (NMul a11 b11) (NMul a12 b21)) c11)
                    (NMul (NAdd (NMul a11 b12) (NMul a12 b22)) c21))
              (NAdd (NMul (NAdd (NMul a11 b11) (NMul a12 b21)) c12)
                    (NMul (NAdd (NMul a11 b12) (NMul a12 b22)) c22))
              (NAdd (NMul (NAdd (NMul a21 b11) (NMul a22 b21)) c11)
                    (NMul (NAdd (NMul a21 b12) (NMul a22 b22)) c21))
              (NAdd (NMul (NAdd (NMul a21 b11) (NMul a22 b21)) c12)
                    (NMul (NAdd (NMul a21 b12) (NMul a22 b22)) c22)))).
    exact (H_SNMMU (NAdd (NMul a11 b11) (NMul a12 b21))
                   (NAdd (NMul a11 b12) (NMul a12 b22))
                   (NAdd (NMul a21 b11) (NMul a22 b21))
                   (NAdd (NMul a21 b12) (NMul a22 b22))
                   c11 c12 c21 c22).

  apply (eq_Matrix_is_symmetric).

  apply (eq_Matrix_is_transitive 
           (NMMul (m22 a11 a12 a21 a22)
                  (NMMul (m22 b11 b12 b21 b22) (m22 c11 c12 c21 c22)))
           (NMMul (m22 a11 a12 a21 a22)
                  (m22 (NAdd (NMul b11 c11) (NMul b12 c21))
                       (NAdd (NMul b11 c12) (NMul b12 c22))
                       (NAdd (NMul b21 c11) (NMul b22 c21))
                       (NAdd (NMul b21 c12) (NMul b22 c22))))).
    apply (matrix_multiplication_preserves_eq_Matrix
             NAdd H_SNA NMul H_SNM NMMul H_SNMM).
    exact (eq_Matrix_is_reflexive (m22 a11 a12 a21 a22)).
    exact (H_SNMM NAdd H_SNA NMul H_SNM b11 b12 b21 b22 c11 c12 c21 c22).

  apply (eq_Matrix_is_transitive
           (NMMul (m22 a11 a12 a21 a22)
                  (m22 (NAdd (NMul b11 c11) (NMul b12 c21))
                       (NAdd (NMul b11 c12) (NMul b12 c22))
                       (NAdd (NMul b21 c11) (NMul b22 c21))
                       (NAdd (NMul b21 c12) (NMul b22 c22))))
           (m22
              (NAdd (NMul a11 (NAdd (NMul b11 c11) (NMul b12 c21)))
                    (NMul a12 (NAdd (NMul b21 c11) (NMul b22 c21))))
              (NAdd (NMul a11 (NAdd (NMul b11 c12) (NMul b12 c22)))
                    (NMul a12 (NAdd (NMul b21 c12) (NMul b22 c22))))
              (NAdd (NMul a21 (NAdd (NMul b11 c11) (NMul b12 c21)))
                    (NMul a22 (NAdd (NMul b21 c11) (NMul b22 c21))))
              (NAdd (NMul a21 (NAdd (NMul b11 c12) (NMul b12 c22)))
                    (NMul a22 (NAdd (NMul b21 c12) (NMul b22 c22)))))).

    exact (H_SNMMU a11 a12 a21 a22
                   (NAdd (NMul b11 c11) (NMul b12 c21))
                   (NAdd (NMul b11 c12) (NMul b12 c22))
                   (NAdd (NMul b21 c11) (NMul b22 c21))
                   (NAdd (NMul b21 c12) (NMul b22 c22))).

  apply (eq_Matrix_is_symmetric).
  unfold eq_Matrix.
  split.
    exact (about_distributivity_in_each_matrix_point 
             NAdd H_SNA NMul H_SNM a11 b11 a12 b21 c11 b12 b22 c21).
  split.
    exact (about_distributivity_in_each_matrix_point 
             NAdd H_SNA NMul H_SNM a11 b11 a12 b21 c12 b12 b22 c22).        
  split.
    exact (about_distributivity_in_each_matrix_point 
             NAdd H_SNA NMul H_SNM a21 b11 a22 b21 c11 b12 b22 c21).  
    exact (about_distributivity_in_each_matrix_point 
             NAdd H_SNA NMul H_SNM a21 b11 a22 b21 c12 b12 b22 c22).  
Qed.

(* Finally the associativity and existence of a neutral element (the identity
   matrix) implies that the natural matrices and matrix multiplication
   form a monoid under eq_Matrix. *)

Theorem Natural_Matrices_and_matrix_multiplication_form_a_Monoid :
  forall NAdd : Nat -> Nat -> Nat,
    specification_of_addition NAdd ->
    forall NMul : Nat -> Nat -> Nat,
      specification_of_multiplication NMul ->
      forall NMMul : M22 -> M22 -> M22,
        specification_of_matrix_multiplication NMMul ->
        T_and_Dot_form_a_Monoid_under_eqT M22 eq_Matrix NMMul.
Proof.
  intros NAdd H_SNA NMul H_SNM NMMul H_SNMM.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Matrix_is_an_equivalence_relation_under_M22).
    split.
      exact (matrix_multiplication_preserves_eq_Matrix 
               NAdd H_SNA NMul H_SNM NMMul H_SNMM).
      split.
        exact (matrix_multiplication_is_associative 
                 NAdd H_SNA NMul H_SNM NMMul H_SNMM).

        exists (m22 (S O) O O (S O)).
        unfold specification_of_neutrality.
        split.
        exact (identity_matrix_is_right_neutral_for_matrix_multiplication
                 NAdd H_SNA NMul H_SNM NMMul H_SNMM).
        exact (identity_matrix_is_left_neutral_for_matrix_multiplication
                 NAdd H_SNA NMul H_SNM NMMul H_SNMM).
Qed.

(* Two polymorphic endofunctions are defined to be equal with
   some equality relation if giving both functions related input 
   yields related output. *)

Definition eq_PE (T : Type)
                 (eqT : T -> T -> Prop)
                 (f g : T -> T) :=
     forall x y : T,
        eqT x y -> eqT (f x) (g y).

(* Furthermore, I will assume that all functions used are referentially
   transparent such that I can use the following property. *)

Property referential_transparency_for_functions :
  forall (T1 : Type)
         (T2 : Type)
         (eq_T1 : T1 -> T1 -> Prop)
         (eq_T2 : T2 -> T2 -> Prop),
    specification_of_an_equivalence_relation T1 eq_T1 ->
    specification_of_an_equivalence_relation T2 eq_T2 ->
    forall (f : T1 -> T2)
           (x1 y1 : T1),
      eq_T1 x1 y1 ->
      eq_T2 (f x1) (f y1).
Admitted.

(* The property above is assumed to be true if the underlying equality relation
   between elements of the given type is an equivalence relation. I will 
   therefore assume that this is the case. I can then show that functional
   equality is an equivalence relation.  *)
  
Lemma eq_PE_is_reflexive :
  forall T : Type,
  forall (eqT : T -> T -> Prop),
    specification_of_an_equivalence_relation T eqT ->
    specification_of_a_reflexive_relation (T -> T) (eq_PE T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_reflexive_relation.
  intro a.
  unfold eq_PE.
  intros x y H_xy.
  exact (referential_transparency_for_functions 
           T T eqT eqT H_eqT H_eqT a x y H_xy).
Qed.

Lemma eq_PE_is_symmetric :
  forall T : Type,
  forall (eqT : T -> T -> Prop),
    specification_of_an_equivalence_relation T eqT ->
    specification_of_a_symmetric_relation (T -> T) (eq_PE T eqT). 
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_symmetric_relation.
  intros a b H_ab.
  unfold eq_PE in H_ab.
  unfold eq_PE.
  intros x y H_xy.
  unfold specification_of_an_equivalence_relation in H_eqT.
  destruct H_eqT as [_ [H_symm _]].
  unfold specification_of_a_symmetric_relation in H_symm.
  apply H_symm in H_xy.
  apply (H_ab y x) in H_xy.
  apply (H_symm) in H_xy.
  exact H_xy.
Qed.

Lemma eq_PE_is_transitive :
  forall T : Type,
  forall (eqT : T -> T -> Prop),
    specification_of_an_equivalence_relation T eqT ->
    specification_of_a_transitive_relation (T -> T) (eq_PE T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_transitive_relation.
  intros x y z H_xy H_yz.
  unfold eq_PE in H_xy, H_yz.
  unfold eq_PE.
  intros x0 y0 H_x0y0.
  unfold specification_of_an_equivalence_relation in H_eqT.
  destruct H_eqT as [H_refl [_ H_trans]].
  unfold specification_of_a_reflexive_relation in H_refl.
  assert (H_x0 := H_refl x0).
  unfold specification_of_a_transitive_relation in H_trans.
  apply (H_xy x0 x0) in H_x0.
  apply (H_yz x0 y0) in H_x0y0.
  exact (H_trans (x x0) (y x0) (z y0) H_x0 H_x0y0).
Qed.

Lemma eq_PE_is_an_equivalence_relation :
  forall T : Type,
    forall (eqT : T -> T -> Prop),
      specification_of_an_equivalence_relation T eqT ->
      specification_of_an_equivalence_relation (T -> T) (eq_PE T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_an_equivalence_relation.
  split.
    exact (eq_PE_is_reflexive T eqT H_eqT).
    split.
      exact (eq_PE_is_symmetric T eqT H_eqT).
      exact (eq_PE_is_transitive T eqT H_eqT).
Qed.

(* Composition of two functions is to first apply the right function
   to the input and then apply the left function. *)

Definition specification_of_Compose_Polymorphic 
           (T : Type)
           (eqT : T -> T -> Prop)
           (PCom : (T -> T) -> (T -> T) -> (T -> T)) :=
  forall f g : T -> T,
    eq_PE T eqT (PCom f g) (fun x => f (g x)).
  
Lemma Compose_Polymorphic_preserves_eq_PE :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall PCom : (T -> T) -> (T -> T) -> (T -> T),
        specification_of_Compose_Polymorphic T eqT PCom ->
        specification_of_preservation (T -> T) (eq_PE T eqT) PCom.
Proof.
  intros T eqT H_eqT PCom H_PCom.
  unfold specification_of_preservation.
  intros a b c d H_ab H_cd.
  unfold specification_of_Compose_Polymorphic in H_PCom.
  apply (eq_PE_is_transitive T eqT H_eqT (PCom a c) (fun x : T => a (c x))).
    exact (H_PCom a c).
  apply (eq_PE_is_symmetric T eqT H_eqT).
  apply (eq_PE_is_transitive T eqT H_eqT (PCom b d) (fun x : T => b (d x))).
    exact (H_PCom b d).
  apply (eq_PE_is_symmetric T eqT H_eqT).

  unfold eq_PE in H_ab, H_cd.
  unfold eq_PE.
  intros x y H_xy.

  assert (H_eqT' := H_eqT).
  unfold specification_of_an_equivalence_relation in H_eqT'.
  destruct H_eqT' as [H_refl [H_symm H_trans]].
  unfold specification_of_a_reflexive_relation in H_refl.
  unfold specification_of_a_symmetric_relation in H_symm.
  unfold specification_of_a_transitive_relation in H_trans.

  apply (H_trans (a (c x)) (b (c x))).
    assert (H_dx := H_refl (c x)).
    exact (H_ab (c x) (c x) H_dx).
  apply (referential_transparency_for_functions T T eqT eqT H_eqT H_eqT).
  exact (H_cd x y H_xy).
Qed.

Lemma Compose_Polymorphic_is_unique :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall c1 c2 : (T -> T) -> (T -> T) -> T -> T,
        specification_of_Compose_Polymorphic T eqT c1 ->
        specification_of_Compose_Polymorphic T eqT c2 ->
        forall f g : T -> T,
          eq_PE T eqT (c1 f g) (c2 f g).
Proof.
  intros T eqT H_er c1 c2 H_Sc1 H_Sc2 f g.
  unfold specification_of_Compose_Polymorphic in H_Sc1.
  unfold specification_of_Compose_Polymorphic in H_Sc2.
  apply (eq_PE_is_transitive T eqT H_er (c1 f g) (fun x : T => f (g x))).
  exact (H_Sc1 f g).
  apply (eq_PE_is_symmetric T eqT H_er).
  exact (H_Sc2 f g).
Qed.

(* The identity function will be neutral. *)

Lemma identity_function_is_left_neutral_for_Compose_Polymorphic :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall PCom : (T -> T) -> (T -> T) -> (T -> T),
      specification_of_Compose_Polymorphic T eqT PCom ->
      forall g : T -> T,
        eq_PE T eqT (PCom (fun i => i) g) g.
Proof.
  intros T eqT H_eqT PCom H_SPC g.
  unfold specification_of_Compose_Polymorphic in H_SPC.
  apply (eq_PE_is_transitive T eqT H_eqT (PCom (fun i : T => i) g) 
                                (fun x : T => (fun i : T => i) (g x))).
    exact (H_SPC (fun i : T => i) g).
  unfold eq_PE.
  intros x y H_xy.
  exact (referential_transparency_for_functions T T eqT eqT H_eqT H_eqT
                                                g x y H_xy).
Qed.

Lemma identity_function_is_right_neutral_for_Compose_Polymorphic :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall PCom : (T -> T) -> (T -> T) -> (T -> T),
      specification_of_Compose_Polymorphic T eqT PCom ->
      forall f : T -> T,
        eq_PE T eqT (PCom f (fun i => i)) f.
Proof.
  intros T eqT H_eqT PCom H_SPC f.
  unfold specification_of_Compose_Polymorphic in H_SPC.
  apply (eq_PE_is_transitive T eqT H_eqT (PCom f (fun i : T => i)) 
                                (fun x : T => f ((fun i : T => i) x))).
    exact (H_SPC f (fun i : T => i)).
  unfold eq_PE.
  intros x y H_xy.
  exact (referential_transparency_for_functions T T eqT eqT H_eqT H_eqT
                                                f x y H_xy).
Qed.

(* Compose Polymorphic is associative. *)

Lemma Compose_Polymorphic_is_associative :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall PCom : (T -> T) -> (T -> T) -> (T -> T),
      specification_of_Compose_Polymorphic T eqT PCom ->
      specification_of_associativity (T -> T) (eq_PE T eqT) PCom.
Proof.
  intros T eqT H_eqT PCom H_SPC f g h.
  unfold specification_of_Compose_Polymorphic in H_SPC.
  apply (eq_PE_is_transitive T eqT H_eqT 
                                (PCom (PCom f g) h)
                                (PCom (fun x : T => f (g x)) h)).
    apply (Compose_Polymorphic_preserves_eq_PE T eqT H_eqT PCom H_SPC).
      exact (H_SPC f g).
      exact (eq_PE_is_reflexive T eqT H_eqT h).

  apply (eq_PE_is_transitive T eqT H_eqT
                                (PCom (fun x : T => f (g x)) h)
                                (fun y : T => (fun x : T => f (g x)) (h y))).
    exact (H_SPC (fun x : T => f (g x)) h).

  apply (eq_PE_is_transitive T eqT H_eqT
                                (fun y : T => f (g (h y)))
                                (PCom f (fun y : T => g (h y)))).
    apply (eq_PE_is_symmetric T eqT H_eqT).
    exact (H_SPC f (fun y : T => g (h y))).

  apply (Compose_Polymorphic_preserves_eq_PE T eqT H_eqT PCom H_SPC).
    exact (eq_PE_is_reflexive T eqT H_eqT f).
    

    apply (eq_PE_is_symmetric T eqT H_eqT).
    exact (H_SPC g h).
Qed.

Theorem Referentially_transparent_polymorphic_endofunctions_and_Compose_Polymorphic_form_a_Monoid :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall PCom : (T -> T) -> (T -> T) -> (T -> T),
      specification_of_Compose_Polymorphic T eqT PCom ->
      T_and_Dot_form_a_Monoid_under_eqT (T -> T) (eq_PE T eqT) PCom.
Proof.
  intros T eqT H_eqT PCom H_SP.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_PE_is_an_equivalence_relation T eqT H_eqT).
    split.
      exact (Compose_Polymorphic_preserves_eq_PE T eqT H_eqT PCom H_SP).
      split.
        exact (Compose_Polymorphic_is_associative T eqT H_eqT PCom H_SP).
        exists (fun i : T => i).
        unfold specification_of_neutrality.
        split.
          exact (identity_function_is_right_neutral_for_Compose_Polymorphic
                   T eqT H_eqT PCom H_SP).
          exact (identity_function_is_left_neutral_for_Compose_Polymorphic
                   T eqT H_eqT PCom H_SP).
Qed.

(* A list is either nothing or an element on top of another list. *)

Inductive ListT (T : Type) :=
  | Nil : ListT T
  | Cons : T -> ListT T -> ListT T.

(* Lists are equal if they have the same amount of elements and
   respective elements are equal from top to bottom according to some
   given equality relation. *)

Fixpoint eq_ListT (T : Type)
                  (eqT : T -> T -> Prop)
                  (xs ys : ListT T) :=
  match xs with
      | Nil => match ys with
                   | Nil => True
                   | Cons y ys' => False
               end
      | Cons x xs' => match ys with
                          | Nil => False
                          | Cons y ys' => eqT x y /\ eq_ListT T eqT xs' ys'
                      end
  end.

Lemma unfold_eq_ListT_N_N :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      eq_ListT T eqT (Nil T) (Nil T).
Proof.
  intros T eqT.
  unfold eq_ListT.
  exact I.
Qed.

Lemma unfold_eq_ListT_C_N :
  forall T : Type,
  forall eqT : T -> T -> Prop,
  forall x : T,
  forall xs' : ListT T,
    ~ (eq_ListT T eqT (Cons T x xs') (Nil T)).
Proof.
  intros T eqT x xs' H_eq.
  unfold eq_ListT in H_eq.
  exact H_eq.
Qed.

Lemma unfold_eq_ListT_N_C :
  forall T : Type,
  forall eqT : T -> T -> Prop,
  forall y : T,
  forall ys' : ListT T,
    ~ (eq_ListT T eqT (Nil T) (Cons T y ys')).
Proof.
  intros T eqT y ys' H_eq.
  unfold eq_ListT in H_eq.
  exact H_eq.
Qed.

Lemma unfold_eq_ListT_C_C :
  forall T : Type,
  forall eqT : T -> T -> Prop,
  forall x y : T,
  forall xs' ys' : ListT T,
    eq_ListT T eqT (Cons T x xs') (Cons T y ys') <->
    eqT x y /\ eq_ListT T eqT xs' ys'.
Proof.
  intros T eqT x y xs' ys'.
  unfold eq_ListT; fold eq_ListT.
  split; intro H; exact H.
Qed.

(* eq_ListT will be an equivalence relation at List T if the element relation is 
   an equivalence relation at type T. *)

Lemma eq_ListT_is_reflexive :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_a_reflexive_relation (ListT T) (eq_ListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_reflexive_relation.
  intro a.
  induction a as [ | a1 a' IHa'].
    exact (unfold_eq_ListT_N_N T eqT).
    apply (unfold_eq_ListT_C_C).
    split.
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl a1).
      
      exact IHa'.
Qed.    

Lemma eq_ListT_is_symmetric :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_a_symmetric_relation (ListT T) (eq_ListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_symmetric_relation.
  intro a.
  induction a as [ | a1 a' IHa'].
    intros b H_ab.
    destruct b as [ | b1 b'].
      exact (eq_ListT_is_reflexive T eqT H_eqT (Nil T)).
      contradiction (unfold_eq_ListT_N_C T eqT b1 b' H_ab).

    intros b H_ab.
    destruct b as [ | b1 b'].
      contradiction (unfold_eq_ListT_C_N T eqT a1 a' H_ab).

      apply -> (unfold_eq_ListT_C_C) in H_ab.
      apply (unfold_eq_ListT_C_C).
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [_ [H_specification_of_a_symmetric_relation _]].
      unfold specification_of_a_symmetric_relation in H_specification_of_a_symmetric_relation.
      destruct H_ab as [H_ab_H H_ab_T].
      split.
        exact (H_specification_of_a_symmetric_relation a1 b1 H_ab_H).
        exact (IHa' b' H_ab_T).
Qed.

Lemma eq_ListT_is_transitive :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_a_transitive_relation (ListT T) (eq_ListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_transitive_relation.
  intro x.
  induction x as [ | x1 x' IHx'].
    intros y z H_xy H_yz.
    destruct y as [ | y1 y'].
      exact H_yz.
      contradiction (unfold_eq_ListT_N_C T eqT y1 y' H_xy).
    
    intros y z H_xy H_yz.
    destruct y as [ | y1 y'].
      contradiction (unfold_eq_ListT_C_N T eqT x1 x' H_xy).
      destruct z as [ | z1 z'].
        contradiction (unfold_eq_ListT_C_N T eqT y1 y' H_yz).
        
        apply -> (unfold_eq_ListT_C_C) in H_xy.
        destruct H_xy as [H_xy H_x'y'].
        apply -> (unfold_eq_ListT_C_C) in H_yz.
        destruct H_yz as [H_yz H_y'z'].
        apply (unfold_eq_ListT_C_C).
        split.
          unfold specification_of_an_equivalence_relation in H_eqT.
          destruct H_eqT as [_ [_ H_specification_of_a_transitive_relation]].
          unfold specification_of_a_transitive_relation in H_specification_of_a_transitive_relation.
          exact (H_specification_of_a_transitive_relation x1 y1 z1 H_xy H_yz).
          exact (IHx' y' z' H_x'y' H_y'z').
Qed.

Lemma eq_ListT_is_an_equivalence_relation :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_an_equivalence_relation (ListT T) (eq_ListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_an_equivalence_relation.
  split.
    exact (eq_ListT_is_reflexive T eqT H_eqT).
    split.
      exact (eq_ListT_is_symmetric T eqT H_eqT).
      exact (eq_ListT_is_transitive T eqT H_eqT).
Qed.

(* List append acts a lot like addition, but here the left most element
   is recursively moved out until the left input is nil. The result is
   all the elements of the left input consed on the right input. *)

Definition specification_of_List_Append (T : Type)
                                        (eqT : T -> T -> Prop)
                                        (App : ListT T -> ListT T -> ListT T) :=
  (forall ys : ListT T,
     eq_ListT T eqT (App (Nil T) ys) ys) /\
  (forall x : T,
     forall xs' ys : ListT T,
       eq_ListT T eqT (App (Cons T x xs') ys) (Cons T x (App xs' ys))).

Lemma List_Append_preserves_eq_ListT :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall App : ListT T -> ListT T -> ListT T,
        specification_of_List_Append T eqT App ->
        specification_of_preservation (ListT T) (eq_ListT T eqT) App.
Proof.
  intros T eqT H_eqT App H_SA.
  unfold specification_of_List_Append in H_SA.
  destruct H_SA as [H_SA_nil H_SA_cons].
  unfold specification_of_preservation.
  intro a.
  induction a as [ | a1 a' IHa'].
    intros b c d H_ab H_cd.
    destruct b as [ | b1 b'].
      apply (eq_ListT_is_transitive T eqT H_eqT (App (Nil T) c) c).
      exact (H_SA_nil c).
      apply (eq_ListT_is_symmetric T eqT H_eqT).
      apply (eq_ListT_is_transitive T eqT H_eqT (App (Nil T) d) d).
      exact (H_SA_nil d).
      apply (eq_ListT_is_symmetric T eqT H_eqT).
      exact H_cd.

      contradiction (unfold_eq_ListT_N_C T eqT b1 b' H_ab).

    intros b c d H_ab H_cd.
    destruct b as [ | b1 b'].
      contradiction (unfold_eq_ListT_C_N T eqT a1 a' H_ab).

      apply (eq_ListT_is_transitive T eqT H_eqT (App (Cons T a1 a') c)
                                                (Cons T a1 (App a' c))).
      exact (H_SA_cons a1 a' c).
      apply (eq_ListT_is_symmetric T eqT H_eqT).
      apply (eq_ListT_is_transitive T eqT H_eqT (App (Cons T b1 b') d)
                                                (Cons T b1 (App b' d))).
      exact (H_SA_cons b1 b' d).
      apply (eq_ListT_is_symmetric T eqT H_eqT).
      apply (unfold_eq_ListT_C_C).
      apply -> (unfold_eq_ListT_C_C) in H_ab.
      destruct H_ab as [H_ab1 H_ab'].
      split.
        exact H_ab1.
        exact (IHa' b' c d H_ab' H_cd).
Qed.          

Lemma List_Append_is_unique :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall f g : ListT T -> ListT T -> ListT T,
        specification_of_List_Append T eqT f ->
        specification_of_List_Append T eqT g ->
        forall xs ys : ListT T,
          eq_ListT T eqT (f xs ys) (g xs ys).
Proof.
  intros T eqT H_eqT f g H_Sf H_Sg.

  unfold specification_of_List_Append in H_Sf.
  destruct H_Sf as [H_Sf_Nil H_Sf_Cons].
  unfold specification_of_List_Append in H_Sg.
  destruct H_Sg as [H_Sg_Nil H_Sg_Cons].

  intro xs.
  induction xs as [ | x xs' IHxs'].
    intro ys.
    assert (H_Sf' := H_Sf_Nil ys).
    assert (H_Sg' := H_Sg_Nil ys).
    apply (eq_ListT_is_symmetric T eqT H_eqT) in H_Sg'.
    exact (eq_ListT_is_transitive T eqT H_eqT (f (Nil T) ys) ys (g (Nil T) ys)
                                  H_Sf' H_Sg').

    intro ys.
    apply (eq_ListT_is_transitive T eqT H_eqT
                                  (f (Cons T x xs') ys) (Cons T x (f xs' ys))).
    exact (H_Sf_Cons x xs' ys).
    apply (eq_ListT_is_transitive T eqT H_eqT (Cons T x (f xs' ys))
                                              (Cons T x (g xs' ys))).
    apply (unfold_eq_ListT_C_C).
    split.
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl x).

      exact (IHxs' ys).

    apply (eq_ListT_is_symmetric T eqT H_eqT).
    exact (H_Sg_Cons x xs' ys).
Qed.

(* It follows from the specification of List append that Nil is left neutral. *)

Lemma Nil_is_left_neutral_for_List_Append :
  forall T : Type,
  forall eqT : T -> T -> Prop,
  forall App : ListT T -> ListT T -> ListT T,
    specification_of_List_Append T eqT App ->
    forall ys : ListT T,
      eq_ListT T eqT (App (Nil T) ys) ys.
Proof.
  intros T eqT App H_SA.
  unfold specification_of_List_Append in H_SA.
  destruct H_SA as [H_SA_Nil _].
  exact H_SA_Nil.
Qed.

(* It follows by induction on lists that Nil is also right neutral. *)

Lemma Nil_is_right_neutral_for_List_Append :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall App : ListT T -> ListT T -> ListT T,
      specification_of_List_Append T eqT App ->
      forall xs : ListT T,
        eq_ListT T eqT (App xs (Nil T)) xs.
Proof.
  intros T eqT H_eqT App H_SA.
  intro xs.
  induction xs as [ | x xs' IHxs'].
    exact (Nil_is_left_neutral_for_List_Append T eqT App H_SA (Nil T)).

    unfold specification_of_List_Append in H_SA.
    destruct H_SA as [_ H_SA_Cons].
    apply (eq_ListT_is_transitive T eqT H_eqT (App (Cons T x xs') (Nil T))
                                              (Cons T x (App xs' (Nil T)))).
    exact (H_SA_Cons x xs' (Nil T)).
    apply (unfold_eq_ListT_C_C).
    split.
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl x).
    exact IHxs'.
Qed.

(* It can be shown by induction that list append is associative. This also 
   makes a lot of sense since the left side will append all its elements to
   the right side. *)

Lemma List_Append_is_associative :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall App : ListT T -> ListT T -> ListT T,
      specification_of_List_Append T eqT App ->
      forall xs ys zs : ListT T,
        eq_ListT T eqT (App (App xs ys) zs) (App xs (App ys zs)).
Proof.
  intros T eqT H_eqT App H_SLA.
  intro xs.
  induction xs as [ | x xs' IHxs'].
    intros ys zs.
    apply (eq_ListT_is_transitive T eqT H_eqT (App (App (Nil T) ys) zs)
                                              (App ys zs)).
    apply (List_Append_preserves_eq_ListT T eqT H_eqT App H_SLA).
    exact (Nil_is_left_neutral_for_List_Append T eqT App H_SLA ys).
    exact (eq_ListT_is_reflexive T eqT H_eqT zs).
    apply (eq_ListT_is_symmetric T eqT H_eqT).
    exact (Nil_is_left_neutral_for_List_Append T eqT App H_SLA (App ys zs)).

    intros ys zs.
    assert (H_SLA' := H_SLA).
    unfold specification_of_List_Append in H_SLA'.
    destruct H_SLA' as [_ H_SLA_Cons].
    apply (eq_ListT_is_transitive T eqT H_eqT (App (App (Cons T x xs') ys) zs)
                                              (App (Cons T x (App xs' ys)) zs)).
    apply (List_Append_preserves_eq_ListT T eqT H_eqT App H_SLA).
    exact (H_SLA_Cons x xs' ys).
    exact (eq_ListT_is_reflexive T eqT H_eqT zs).
    apply (eq_ListT_is_transitive T eqT H_eqT (App (Cons T x (App xs' ys)) zs)
                                              (Cons T x (App (App xs' ys) zs))).
    exact (H_SLA_Cons x (App xs' ys) zs).
    apply (eq_ListT_is_symmetric T eqT H_eqT).
    apply (eq_ListT_is_transitive T eqT H_eqT (App (Cons T x xs') (App ys zs))
                                              (Cons T x (App xs' (App ys zs)))).
    exact (H_SLA_Cons x xs' (App ys zs)).
    apply (eq_ListT_is_symmetric T eqT H_eqT).
    apply (unfold_eq_ListT_C_C).
    split.
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl x).

      exact (IHxs' ys zs).
Qed.

(* Polymorphic lists and list append form a monoid if the underlying
   relation on the elements is an equivalence relation. *)

Theorem Polymorphic_Lists_and_List_Append_form_a_Monoid :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    forall App : ListT T -> ListT T -> ListT T,
      specification_of_List_Append T eqT App ->
      T_and_Dot_form_a_Monoid_under_eqT (ListT T) (eq_ListT T eqT) App.
Proof.
  intros T eqT H_eqT App H_SA.
  unfold T_and_Dot_form_a_Monoid_under_eqT  .
  split. 
    exact (eq_ListT_is_an_equivalence_relation T eqT H_eqT).
    split.
      exact (List_Append_preserves_eq_ListT T eqT H_eqT App H_SA).
      split.
        exact (List_Append_is_associative T eqT H_eqT App H_SA).

        exists (Nil T).
        unfold specification_of_neutrality.
        split.
          exact (Nil_is_right_neutral_for_List_Append T eqT H_eqT App H_SA).
          exact (Nil_is_left_neutral_for_List_Append T eqT App H_SA).
Qed.

(* A Lazy List has a guarded constructor. This means that we can potentially
   make a lazy list infinite. It can however also be finite. *)

CoInductive LazyListT (T : Type) :=
  | LNil : LazyListT T
  | LCons : T -> LazyListT T -> LazyListT T.

(* Two lazy lists can be bisimilar. If two elements are equal under some 
   given relation and two lazy lists are bisimilar, then the first element
   consed on the first list is bisimilar with the second element consed on
   the second list. *)

CoInductive bisimilar_LazyListT (T : Type) 
                                (eqT : T -> T -> Prop) : LazyListT T -> 
                                                         LazyListT T -> Prop :=
| Bisimilar_Nil : bisimilar_LazyListT T eqT (LNil T) (LNil T)
| Bisimilar_Cons :
    forall (x y : T) (xs ys : LazyListT T),
      eqT x y ->
      bisimilar_LazyListT T eqT xs ys ->
      bisimilar_LazyListT T eqT (LCons T x xs) (LCons T y ys).

(* If the relation on the elements is an equivalence relation, then bisimilar
   is also an equivalence relation. This can be shown by co-induction. *)

Lemma bisimilarity_is_reflexive :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    specification_of_a_reflexive_relation (LazyListT T) (bisimilar_LazyListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_reflexive_relation.
  cofix CoIH.
  Show Proof.
  intros [ | x xs'].
    exact (Bisimilar_Nil T eqT).

    apply (Bisimilar_Cons T eqT x x xs' xs').
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl x).

      apply (CoIH xs').
Qed.

Lemma bisimilarity_is_symmetric :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    specification_of_a_symmetric_relation (LazyListT T) (bisimilar_LazyListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_symmetric_relation.
  cofix CoIH.
  intros xs ys H_xsys.
  destruct H_xsys as [ | x y xs' ys' H_xy H_xsys'].
    exact (Bisimilar_Nil T eqT).

    apply (Bisimilar_Cons T eqT y x ys' xs').
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [_ [H_symm _]].
      unfold specification_of_a_symmetric_relation in H_symm.
      exact (H_symm x y H_xy).

      apply (CoIH xs' ys' H_xsys').
Qed.

Lemma not_nil_and_cons :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    forall y : T,
    forall ys' : LazyListT T,
      ~ (bisimilar_LazyListT T eqT (LNil T) (LCons T y ys')).
Proof.
  intros T eqT y ys' H_nil_and_cons.
  remember (LNil T) as xs eqn:H_xs.
  remember (LCons T y ys') as ys eqn:H_ys.
  destruct H_nil_and_cons as [ | x' y' xs' ys'' H_xy' H_xsys'].
    discriminate H_ys.
    discriminate H_xs.
Qed.

Lemma converse_of_bisimilar_cons :
  forall T : Type,
  forall eqT : T -> T -> Prop,
  forall x y : T,
  forall xs' ys' : LazyListT T,
    bisimilar_LazyListT T eqT (LCons T x xs') (LCons T y ys') ->
    (eqT x y) /\ (bisimilar_LazyListT T eqT xs' ys').
Proof.
  intros T eqT x y xs' ys' H_xsys.
  remember (LCons T x xs') as xs eqn:H_xs.
  remember (LCons T y ys') as ys eqn:H_ys.
  destruct H_xsys as [ | x' y' xs'' ys'' H_xy' H_xsys'].
    discriminate H_xs.

    injection H_ys as H_ys''ys' H_y'y.
    injection H_xs as H_xs''xs' H_x'x.
    split.
      rewrite <- H_x'x.
      rewrite <- H_y'y.
      exact H_xy'.

      rewrite <- H_xs''xs'.
      rewrite <- H_ys''ys'.
      exact H_xsys'.
Qed.

Lemma bisimilarity_is_transitive :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    specification_of_a_transitive_relation (LazyListT T) (bisimilar_LazyListT T eqT). 
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_transitive_relation.
  cofix CoIH.
  intros xs ys zs H_xsys H_yszs.
  destruct H_yszs as [ | y z ys' zs' H_yz H_yszs'].
    exact H_xsys.

    destruct xs as [ | x xs'].
      contradiction (not_nil_and_cons T eqT y ys' H_xsys).

      destruct (converse_of_bisimilar_cons T eqT x y xs' ys' H_xsys) 
        as [H_xy H_xs'ys'].
      apply (Bisimilar_Cons T eqT x z xs' zs').
        unfold specification_of_an_equivalence_relation in H_eqT.
        destruct H_eqT as [_ [_ H_trans]].
        unfold specification_of_a_transitive_relation in H_trans.
        exact (H_trans x y z H_xy H_yz).

        apply (CoIH xs' ys' zs' H_xs'ys' H_yszs').
Qed.

Lemma bisimilarity_is_an_equivalence_relation :
  forall T : Type,
  forall eqT : T -> T -> Prop,
    specification_of_an_equivalence_relation T eqT ->
    specification_of_an_equivalence_relation (LazyListT T) (bisimilar_LazyListT T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_an_equivalence_relation.
  split.
    exact (bisimilarity_is_reflexive T eqT H_eqT).
    split.
      exact (bisimilarity_is_symmetric T eqT H_eqT).
      exact (bisimilarity_is_transitive T eqT H_eqT).
Qed.

(* Appending lazy lists is like appending lists, but since the lists
   can be infinite, the left most lazy list has the potential of acting like
   an absorbing element even though it isn't. *)

Definition specification_of_Lazy_Append 
           (T : Type)
           (eqT : T -> T -> Prop)
           (LApp : LazyListT T -> LazyListT T -> LazyListT T) :=
  (forall ys : LazyListT T,
     bisimilar_LazyListT T eqT (LApp (LNil T) ys) ys)
  /\
  (forall x : T,
     forall xs' ys : LazyListT T,
       bisimilar_LazyListT T eqT (LApp (LCons T x xs') ys) 
                                 (LCons T x (LApp xs' ys))).

Lemma Nil_is_left_neutral_for_Lazy_Append :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      forall LApp : LazyListT T -> LazyListT T -> LazyListT T,
        specification_of_Lazy_Append T eqT LApp ->
        forall ys : LazyListT T,
          bisimilar_LazyListT T eqT (LApp (LNil T) ys) ys.
Proof.
  intros T eqT LApp H_SA ys.
  unfold specification_of_Lazy_Append in H_SA.
  destruct H_SA as [H_SA_nil _].
  exact (H_SA_nil ys).
Qed.
 
Lemma Nil_is_right_neutral_for_Lazy_Append :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall LApp : LazyListT T -> LazyListT T -> LazyListT T,
        specification_of_Lazy_Append T eqT LApp ->
        forall xs : LazyListT T,
          bisimilar_LazyListT T eqT (LApp xs (LNil T)) xs.
Proof.
  intros T eqT H_eqT LApp H_SA.
  cofix CoIH.
  intro xs.
  destruct xs as [ | x xs'].
    exact (Nil_is_left_neutral_for_Lazy_Append T eqT LApp H_SA (LNil T)).

    assert (H_SA' := H_SA).
    unfold specification_of_Lazy_Append in H_SA'.
    destruct H_SA' as [_ H_SA_cons].

    (* This is the end. I can not continue without using the transitive 
       properties of bisimilarity. The problem is that this lemma is not
       guarding. I will not be able to complete the proof. It is much like
       the rewrite at x problem from the lectures. *)

    apply (bisimilarity_is_transitive T eqT H_eqT (LApp (LCons T x xs') (LNil T))
                           (LCons T x (LApp xs' (LNil T)))).
    exact (H_SA_cons x xs' (LNil T)).
    apply (Bisimilar_Cons).
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl x).

      apply (CoIH).
      (* Running Guarded yields an Error here. *)
Abort.

(* For some reason Coq can not infer that transitivity is guarded. However,
   Coq can infer that eq_ind (the lemma used by the rewriting tactic) is
   guarded. I resort to a concrete implementation of lazy append. *)

CoFixpoint LApp (T : Type) (xs ys : LazyListT T) :=
  match xs with
      | LNil => ys
      | LCons x xs' => LCons T x (LApp T xs' ys)
  end.

(* To unfold this I need a special trick - I will use something called
   decomposition. Since the constructors in co-fixpoints and co-inductives
   are guarded, I need something that can push them one step. *)

Definition decompose_LazyListT (T : Type) (xs : LazyListT T) :=
  match xs with
      | LNil => LNil T
      | LCons x xs' => LCons T x xs'
  end.

(* It can be proved that a decomposed stream is Leibniz equal to the stream
   itself: *)

Lemma decomposition_of_LazyListT :
  forall T : Type,
    forall xs : LazyListT T,
      xs = decompose_LazyListT T xs.
Proof.
  intros T xs.
  destruct xs as [ | x xs'].
    unfold decompose_LazyListT; fold decompose_LazyListT.
    reflexivity.

    unfold decompose_LazyListT; fold decompose_LazyListT.
    reflexivity.
Qed.

(* I want to use the rewrite tactic in my proofs since eq_ind_r and eq_ind
   will guard the co-induction hypothesis. It is the case that the result of
   appending nil to any lazy list is Leibniz equal to that list: *)

Lemma unfold_LApp_nil :
  forall T : Type,
    forall ys : LazyListT T,
      LApp T (LNil T) ys = ys.
Proof.
  intros T ys.
  rewrite -> (decomposition_of_LazyListT T (LApp T (LNil T) ys)).
  unfold decompose_LazyListT; unfold LApp; fold LApp.
  destruct ys as [ | y ys']; reflexivity.
Qed.

(* Also appending a lazy list with at least one element to another is Leibniz
   equal to appending that element to a co-recursive call of appending the
   rest of the first list to the second list: *)

Lemma unfold_LApp_cons :
  forall T : Type,
    forall x : T,
      forall xs' ys : LazyListT T,
        LApp T (LCons T x xs') ys =
        LCons T x (LApp T xs' ys).
Proof.
  intros T x xs' ys.
  rewrite -> (decomposition_of_LazyListT T (LApp T (LCons T x xs') ys)).
  unfold decompose_LazyListT; unfold LApp; fold LApp.
  reflexivity.
Qed.

(* I can now proceed to prove that polymorphic lazy lists and the concrete
   implementation of lazy append form a monoid under bisimilarity. *)

(* That nil is left neutral follows from unfolding LApp and reflexivity
   of bisimilarity. *)

Lemma Nil_is_left_neutral_for_LApp :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
        forall ys : LazyListT T,
          bisimilar_LazyListT T eqT (LApp T (LNil T) ys) ys.
Proof.
  intros T eqT H_eqT ys.
  rewrite -> (unfold_LApp_nil T ys).
  exact (bisimilarity_is_reflexive T eqT H_eqT ys).
Qed.

(* It can be shown through co-induction that nil is also right neutral. *)

Lemma Nil_is_right_neutral_for_LApp :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
        forall xs : LazyListT T,
          bisimilar_LazyListT T eqT (LApp T xs (LNil T)) xs.
Proof.
  intros T eqT H_eqT.
  cofix CoIH.
  intro xs.
  destruct xs as [ | x xs'].
    rewrite -> (unfold_LApp_nil T (LNil T)).
    exact (Bisimilar_Nil T eqT).

    rewrite -> (unfold_LApp_cons T x xs' (LNil T)).
    apply (Bisimilar_Cons T eqT).
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl x).

      exact (CoIH xs').
      Show Proof. (* Notice 
                     | LCons x xs' =>
                        eq_ind_r
                         (fun l : LazyListT T => 
                          bisimilar_LazyListT T eqT l (LCons T x xs'))
                         (Bisimilar_Cons T eqT x x (LApp T xs' (LNil T)) xs'
                           match H_eqT with
                             | conj H_refl _ => H_refl x
                             end (CoIH xs')) (unfold_LApp_cons T x xs' (LNil T)) 

                     For some weird reason eq_ind_r, which is applied using the
                     rewrite tactic, is guarding the co-induction hypothesis.
                     Why eq_ind_r is guarded and e.g. bisimilarity_is_transitive
                     is not is a mystery to me. *)
Qed.

(* It can be shown through co-induction that the concrete implementation 
   of lazy append preserves bisimilarity for any type and relation in the 
   lazy lists if that relation is an equivalence relation. *)

Lemma LApp_preserves_bisimilarity :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_preservation (LazyListT T) (bisimilar_LazyListT T eqT) (LApp T).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_preservation.
  cofix CoIH.
  intros a b c d H_ab H_cd.
  destruct a as [ | a1 a'].
    destruct b as [ | b1 b'].
      rewrite -> (unfold_LApp_nil T c).
      rewrite -> (unfold_LApp_nil T d).
      exact H_cd.
      
      contradiction (not_nil_and_cons T eqT b1 b' H_ab).

    destruct b as [ | b1 b'].
      apply (bisimilarity_is_symmetric T eqT H_eqT) in H_ab.
      contradiction (not_nil_and_cons T eqT a1 a' H_ab).

      rewrite -> (unfold_LApp_cons T a1 a' c).
      rewrite -> (unfold_LApp_cons T b1 b' d).
      apply (converse_of_bisimilar_cons) in H_ab.
      destruct H_ab as [H_a1b1 H_a'b'].
      apply (Bisimilar_Cons T eqT).
        exact H_a1b1.

        exact (CoIH a' b' c d H_a'b' H_cd).
Qed.

(* It follows easily from co-induction that lazy append is associative. *)

Lemma LApp_is_associative :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_associativity (LazyListT T) 
                                 (bisimilar_LazyListT T eqT) (LApp T).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_associativity.
  cofix CoIH.
  intros a b c.
  destruct a as [ | a1 a'].
    rewrite -> (unfold_LApp_nil T b).
    rewrite -> (unfold_LApp_nil T (LApp T b c)).
    exact (bisimilarity_is_reflexive T eqT H_eqT (LApp T b c)).

    rewrite -> (unfold_LApp_cons T a1 a' b).
    rewrite -> (unfold_LApp_cons T a1 (LApp T a' b) c).
    rewrite -> (unfold_LApp_cons T a1 a' (LApp T b c)).
    apply (Bisimilar_Cons T eqT).
      unfold specification_of_an_equivalence_relation in H_eqT.
      destruct H_eqT as [H_refl _].
      unfold specification_of_a_reflexive_relation in H_refl.
      exact (H_refl a1).

      exact (CoIH a' b c).
      (* Again, if one takes a look at the proof by using Show Proof, one
         sees that the co-induction hypothesis is in the arguments to eq_ind_r. 
         Coq is still able to complete the proof. Why is eq_ind_r guarding? *)
Qed.

(* The biggest problem is that for some reason eq_ind_r is guarding but
   my transitivity lemma is not. I can not figure out the reason. Anyways,
   I can show that polymorphic lazy lists and the concrete implementation of
   lazy append form a monoid under bisimilarity if the element relation is 
   an equivalence relation. *)

Theorem Lazy_Lists_and_LApp_form_a_Monoid :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      T_and_Dot_form_a_Monoid_under_eqT (LazyListT T)
                                        (bisimilar_LazyListT T eqT) (LApp T).
Proof.
  intros T eqT H_eqT.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (bisimilarity_is_an_equivalence_relation T eqT H_eqT).
    split.
      exact (LApp_preserves_bisimilarity T eqT H_eqT).
      split.
        exact (LApp_is_associative T eqT H_eqT).
        
        exists (LNil T).
        unfold specification_of_neutrality.
        split.
          exact (Nil_is_right_neutral_for_LApp T eqT H_eqT).
          exact (Nil_is_left_neutral_for_LApp T eqT H_eqT).
Qed.

(* The co-inductive natural numbers are similar to the inductive natural numbers
   except for the fact that there can be a number with only successors. That is,
   co-inductive naturals is a union of natural numbers and the infinite element. 
*)

CoInductive Natc :=
  | Oc : Natc
  | Sc : Natc -> Natc.

(* Two co-inductive natural numbers are equivalent if they are both zero or if 
   their predecessors are equal. *)

CoInductive eq_Natc : Natc -> Natc -> Prop :=
  | eq_Oc : eq_Natc Oc Oc
  | eq_Sc : forall m n : Natc,
              eq_Natc m n ->
              eq_Natc (Sc m) (Sc n).

(* This relation can be shown to be an equivalence relation through
   co-induction. *)

Lemma eq_Natc_is_reflexive :
  specification_of_a_reflexive_relation Natc eq_Natc.
Proof.
  unfold specification_of_a_reflexive_relation.
  cofix CoIH.
  intros [ | a'].
    exact eq_Oc.
    
    apply eq_Sc.
    exact (CoIH a').
Qed.

Lemma eq_Natc_is_symmetric :
  specification_of_a_symmetric_relation Natc eq_Natc.
Proof.
  unfold specification_of_a_symmetric_relation.
  cofix CoIH.
  intros a b H_ab.
  destruct H_ab as [ | a' b' H_a'b'].
    exact eq_Oc.

    apply eq_Sc.
    exact (CoIH a' b' H_a'b').
Qed.

Lemma Oc_is_not_Sc :
  forall n' : Natc,
    ~ (eq_Natc Oc (Sc n')).
Proof.
  intros n' H_eq.
  remember Oc as m eqn:H_m.
  remember (Sc n') as n eqn:H_n.
  destruct H_eq as [ | m'' n'' H_m''n''].
    discriminate H_n.
    discriminate H_m.
Qed.

Lemma converse_of_eq_Natc :
  forall m' n' : Natc,
    eq_Natc (Sc m') (Sc n') ->
    eq_Natc m' n'.
Proof.
  intros m' n' H_Sm'Sn'.
  remember (Sc m') as m eqn:H_m.
  remember (Sc n') as n eqn:H_n.
  destruct H_Sm'Sn' as [ | m'' n'' H_m''n''].
    discriminate H_m.

    injection H_m as H_m'.
    injection H_n as H_n'.
    rewrite <- H_m'.
    rewrite <- H_n'.
    exact H_m''n''.
Qed.

Lemma eq_Natc_is_transitive :
  specification_of_a_transitive_relation Natc eq_Natc.
Proof.
  unfold specification_of_a_transitive_relation.
  cofix CoIH.
  intros x y z H_xy H_yz.
  destruct H_xy as [ | x' y' H_x'y'].
    exact H_yz.
    destruct z as [ | z'].
      apply eq_Natc_is_symmetric in H_yz.
      contradiction (Oc_is_not_Sc y' H_yz).

      apply converse_of_eq_Natc in H_yz.
      apply eq_Sc.
      exact (CoIH x' y' z' H_x'y' H_yz).
Qed.    

Lemma eq_Natc_is_an_equivalence_relation :
  specification_of_an_equivalence_relation Natc eq_Natc.
Proof.
  unfold specification_of_an_equivalence_relation.
  split.
    exact eq_Natc_is_reflexive.
    split.
      exact eq_Natc_is_symmetric.
      exact eq_Natc_is_transitive.
Qed.

(* This is used to decompose a co-inductive natural number in a lemma. 
   We have to force every single step since the successor constructors 
   are guarding. *)

Definition decompose_Natc (m : Natc) :=
  match m with
      | Oc => Oc
      | Sc m' => Sc m'
  end.

Lemma decomposition_of_Natc :
  forall m : Natc,
    decompose_Natc m = m.
Proof.
  intros [ | m']; unfold decompose_Natc; reflexivity.
Qed.

(* This is minimum as a cofix point. Oc will be absorbent in any case.
   The minimum of two numbers which are not Oc is defined to be the successor
   of the minimum of their predecessors. *)

CoFixpoint Minc (m n : Natc) :=
  match m with
      | Oc => Oc
      | Sc m' => match n with
                     | Oc => Oc
                     | Sc n' => Sc (Minc m' n')
                 end
  end.

(* Some necessarily unfolding lemmas that can be proved using decomposition. *)

Lemma unfold_Minc_Oc :
  forall n : Natc,
    Minc Oc n = Oc.
Proof.
  intro n.
  rewrite <- (decomposition_of_Natc (Minc Oc n)).
  unfold decompose_Natc.
  unfold Minc.
  reflexivity.
Qed.

Lemma unfold_Minc_Sc_Oc :
  forall m' : Natc,
    Minc (Sc m') Oc = Oc.
Proof.
  intro m'.
  rewrite <- (decomposition_of_Natc (Minc (Sc m') Oc)).
  unfold decompose_Natc; unfold Minc.
  reflexivity.
Qed.

Lemma unfold_Minc_Sc_Sc :
  forall m' n' : Natc,
    Minc (Sc m') (Sc n') = Sc (Minc m' n').
Proof.
  intros m' n'.
  rewrite <- (decomposition_of_Natc (Minc (Sc m') (Sc n'))).
  unfold decompose_Natc; unfold Minc; fold Minc.
  reflexivity.
Qed.

(* Minimum preserves the equivalence as shown through co-induction. *)

Lemma Minc_preserves_eq_Natc :
  specification_of_preservation Natc eq_Natc Minc.
Proof.
  unfold specification_of_preservation.
  cofix CoIH.
  intros a b c d H_ab H_cd.
  destruct H_ab as [ | a' b' H_a'b'].
    rewrite -> (unfold_Minc_Oc c).
    rewrite -> (unfold_Minc_Oc d).
    exact eq_Oc.

    destruct H_cd as [ | c' d' H_c'd'].
      rewrite -> (unfold_Minc_Sc_Oc a').
      rewrite -> (unfold_Minc_Sc_Oc b').
      exact eq_Oc.

      rewrite -> (unfold_Minc_Sc_Sc a' c').
      rewrite -> (unfold_Minc_Sc_Sc b' d').
      apply eq_Sc.
      exact (CoIH a' b' c' d' H_a'b' H_c'd').
Qed.

(* The infinite co-inductive natural number consisting of only successors. *)

CoFixpoint infinite : Natc := Sc infinite.

(* Required to do one single 'rewrite at' command. *)

Require Import Arith.

Lemma unfold_infinite :
  infinite = Sc infinite.
Proof.
  rewrite <- (decomposition_of_Natc infinite) at 1.
  unfold decompose_Natc at 1.
  unfold infinite; fold infinite.
  reflexivity.
Qed.

(* There is no element which is neutral for minimum and inductive
   natural numbers, since the inductive natural numbers does not have an 
   upper bound. But the co-inductive naturals numbers has the infinite element 
   which is greater than everything. That infinite is neutral for co-recursive 
   minimum follows from co-induction. *)

Lemma infinite_is_left_neutral_for_Minc :
  forall n : Natc,
    eq_Natc (Minc infinite n) n.
Proof.
  cofix CoIH.
  intro n.
  rewrite -> unfold_infinite.
  destruct n as [ | n'].
    rewrite -> (unfold_Minc_Sc_Oc infinite).
    exact eq_Oc.

    rewrite -> (unfold_Minc_Sc_Sc infinite n').
    apply eq_Sc.
    exact (CoIH n').
Qed.

Lemma infinite_is_right_neutral_for_Minc :
  forall m : Natc,
    eq_Natc (Minc m infinite) m.
Proof.
  cofix CoIH.
  intro m.
  rewrite -> unfold_infinite.
  destruct m as [ | m'].
    rewrite -> (unfold_Minc_Oc (Sc infinite)).
    exact eq_Oc.

    rewrite -> (unfold_Minc_Sc_Sc m' infinite).
    apply eq_Sc.
    exact (CoIH m').
Qed.

(* Minc is also associative. This follows by co-induction. *)

Lemma Minc_is_associative :
  specification_of_associativity Natc eq_Natc Minc.
Proof.
  unfold specification_of_associativity.
  cofix CoIH.
  intros a b c.
  destruct a as [ | a'].
    rewrite -> (unfold_Minc_Oc b).
    rewrite -> (unfold_Minc_Oc c).
    rewrite -> (unfold_Minc_Oc (Minc b c)).
    exact eq_Oc.

    destruct b as [ | b'].
      rewrite -> (unfold_Minc_Sc_Oc a').
      rewrite -> (unfold_Minc_Oc c).
      rewrite -> (unfold_Minc_Sc_Oc a').
      exact eq_Oc.

      rewrite -> (unfold_Minc_Sc_Sc a' b').
      destruct c as [ | c'].
        rewrite -> (unfold_Minc_Sc_Oc (Minc a' b')).
        rewrite -> (unfold_Minc_Sc_Oc b').
        rewrite -> (unfold_Minc_Sc_Oc a').
        exact eq_Oc.

        rewrite -> (unfold_Minc_Sc_Sc (Minc a' b') c').
        rewrite -> (unfold_Minc_Sc_Sc b' c').
        rewrite -> (unfold_Minc_Sc_Sc a' (Minc b' c')).
        apply eq_Sc.
        exact (CoIH a' b' c').
Qed.

(* Therefore it can be shown that the co-inductive natural numbers, which 
   contains the infinite element, form a monoid with minimum under eq_Natc. *)

Theorem CoInductive_natural_numbers_and_minimum_form_a_Monoid :
  T_and_Dot_form_a_Monoid_under_eqT Natc eq_Natc Minc.
Proof.
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  split.
    exact (eq_Natc_is_an_equivalence_relation).
    split.
      exact (Minc_preserves_eq_Natc).
      split.
        exact (Minc_is_associative).
        
        exists infinite.
        unfold specification_of_neutrality.
        split.
          exact (infinite_is_right_neutral_for_Minc).
          exact (infinite_is_left_neutral_for_Minc).
Qed.

(* Polymorphic 2x2 matrices *)

Inductive PM22 (T : Type) : Type :=
  | pm22 : T -> T -> T -> T -> PM22 T.

(* Given some equality relation between the elements in a polymorphic matrix,
   two polymorphic matrices are equal if their elements are equal at the 
   right locations. *)

Definition eq_PM22 (T : Type) (eqT : T -> T -> Prop) (A B : PM22 T) :=
  match A with
      | pm22 a11 a12 a21 a22 => match B with
                                  | pm22 b11 b12 b21 b22 =>
                                    eqT a11 b11 /\
                                    eqT a12 b12 /\
                                    eqT a21 b21 /\
                                    eqT a22 b22
                                end
  end.

(* If the underlying equality relation is an equivalence relation, then
   the equality relation between polymorphic matrices will be too. *)

Lemma eq_PM22_is_reflexive :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_a_reflexive_relation (PM22 T) (eq_PM22 T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_reflexive_relation.
  intros [ a11 a12 a21 a22 ].
  unfold eq_PM22.
  unfold specification_of_an_equivalence_relation in H_eqT.
  destruct H_eqT as [H_refl _].
  unfold specification_of_a_reflexive_relation in H_refl.
  
  split.
  exact (H_refl a11).

  split.
  exact (H_refl a12).

  split.
  exact (H_refl a21).

  exact (H_refl a22).
Qed.

Lemma eq_PM22_is_symmetric :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_a_symmetric_relation (PM22 T) (eq_PM22 T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_symmetric_relation.
  intros [ a11 a12 a21 a22 ] [ b11 b12 b21 b22 ] H_ab.
  unfold eq_PM22.
  unfold eq_PM22 in H_ab.
  unfold specification_of_an_equivalence_relation in H_eqT.
  destruct H_eqT as [_ [H_symm _]].
  unfold specification_of_a_symmetric_relation in H_symm.
  destruct H_ab as [ H_1 [ H_2 [ H_3 H_4 ]]].
  
  split.
  exact (H_symm a11 b11 H_1).

  split.
  exact (H_symm a12 b12 H_2).

  split.
  exact (H_symm a21 b21 H_3).

  exact (H_symm a22 b22 H_4).
Qed.

Lemma eq_PM22_is_transitive :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_a_transitive_relation (PM22 T) (eq_PM22 T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_a_transitive_relation.
  intros [ x11 x12 x21 x22 ] [ y11 y12 y21 y22 ] [ z11 z12 z21 z22 ] H_xy H_yz.
  unfold specification_of_an_equivalence_relation in H_eqT.
  destruct H_eqT as [_ [_ H_trans]].
  unfold specification_of_a_transitive_relation in H_trans.

  unfold eq_PM22.
  unfold eq_PM22 in H_xy, H_yz.
  destruct H_xy as [H_xy1 [H_xy2 [H_xy3 H_xy4]]].
  destruct H_yz as [H_yz1 [H_yz2 [H_yz3 H_yz4]]].
  
  split.
  exact (H_trans x11 y11 z11 H_xy1 H_yz1).

  split.
  exact (H_trans x12 y12 z12 H_xy2 H_yz2).

  split.
  exact (H_trans x21 y21 z21 H_xy3 H_yz3).
 
  exact (H_trans x22 y22 z22 H_xy4 H_yz4).
Qed.

Lemma eq_PM22_is_an_equivalence_relation :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      specification_of_an_equivalence_relation (PM22 T) (eq_PM22 T eqT).
Proof.
  intros T eqT H_eqT.
  unfold specification_of_an_equivalence_relation.
  
  split.
  exact (eq_PM22_is_reflexive T eqT H_eqT).

  split.
  exact (eq_PM22_is_symmetric T eqT H_eqT).

  exact (eq_PM22_is_transitive T eqT H_eqT).
Qed.

(* Addition between polymorphic matrices yields a new matrix where
   some binary operation has been applied to every two elements in the right
   order. *)

Definition specification_of_polymorphic_matrix_addition 
           (T : Type)
           (eqT : T -> T -> Prop)
           (Dot : T -> T -> T)
           (PAdd : PM22 T -> PM22 T -> PM22 T) :=
  forall a11 a12 a21 a22 b11 b12 b21 b22 : T,
    eq_PM22 T eqT
            (PAdd (pm22 T a11 a12 a21 a22) (pm22 T b11 b12 b21 b22))
            (pm22 T (Dot a11 b11) (Dot a12 b12) (Dot a21 b21) (Dot a22 b22)).

(* If the binary operation preserves the equivalent relation, polymorphic
   matrix addition will preserve polymorphic matrix equality. *)
                                        
Lemma polymorphic_matrix_addition_preserves_eq_PM22 :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall Dot : T -> T -> T,
        specification_of_preservation T eqT Dot ->
        forall PAdd : PM22 T -> PM22 T -> PM22 T,
          specification_of_polymorphic_matrix_addition T eqT Dot PAdd ->
          specification_of_preservation (PM22 T) (eq_PM22 T eqT) PAdd.
Proof.
  intros T eqT H_eqT Dot H_Dot PAdd H_SPA.
  unfold specification_of_polymorphic_matrix_addition in H_SPA.
  unfold specification_of_preservation.
  intros [ a11 a12 a21 a22 ] 
         [ b11 b12 b21 b22 ]
         [ c11 c12 c21 c22 ]
         [ d11 d12 d21 d22 ] H_ab H_cd.
  
  apply (eq_PM22_is_transitive T eqT H_eqT
           (PAdd (pm22 T a11 a12 a21 a22) (pm22 T c11 c12 c21 c22))
           (pm22 T (Dot a11 c11) (Dot a12 c12) (Dot a21 c21) (Dot a22 c22))).
    apply H_SPA.

  apply (eq_PM22_is_symmetric T eqT H_eqT).
  apply (eq_PM22_is_transitive T eqT H_eqT
           (PAdd (pm22 T b11 b12 b21 b22) (pm22 T d11 d12 d21 d22))
           (pm22 T (Dot b11 d11) (Dot b12 d12) (Dot b21 d21) (Dot b22 d22))).
    apply H_SPA.

  apply (eq_PM22_is_symmetric T eqT H_eqT).
  unfold eq_PM22.
  unfold eq_PM22 in H_ab, H_cd.
  destruct H_ab as [H_ab1 [H_ab2 [H_ab3 H_ab4]]].
  destruct H_cd as [H_cd1 [H_cd2 [H_cd3 H_cd4]]].

  clear H_SPA.
  unfold specification_of_preservation in H_Dot.
  
  split.
  exact (H_Dot a11 b11 c11 d11 H_ab1 H_cd1).

  split.
  exact (H_Dot a12 b12 c12 d12 H_ab2 H_cd2).

  split.
  exact (H_Dot a21 b21 c21 d21 H_ab3 H_cd3).

  exact (H_Dot a22 b22 c22 d22 H_ab4 H_cd4).
Qed.

(* Polymorphic matrix addition has a neutral element if there exists a
   neutral element for the underlying binary operation. This neutral element
   will consist only of elements which are neutral for that operation - I
   will refer to it as the neutral matrix. *)

Lemma neutral_matrix_is_left_neutral_for_polymorphic_matrix_addition :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall Dot : T -> T -> T,
        forall PAdd : PM22 T -> PM22 T -> PM22 T,
          specification_of_polymorphic_matrix_addition T eqT Dot PAdd ->
          forall e : T,
            specification_of_neutrality T eqT Dot e ->
            forall A : PM22 T,
              eq_PM22 T eqT 
                      (PAdd (pm22 T e e e e) A) A.
Proof.
  intros T eqT H_eqT Dot PAdd H_PA e H_e.
  intros [ a11 a12 a21 a22 ].
  unfold specification_of_polymorphic_matrix_addition in H_PA.
  apply (eq_PM22_is_transitive T eqT H_eqT
            (PAdd (pm22 T e e e e) (pm22 T a11 a12 a21 a22))
            (pm22 T (Dot e a11) (Dot e a12) (Dot e a21) (Dot e a22))).
    apply H_PA.

  unfold specification_of_neutrality in H_e.
  destruct H_e as [_ H_e_left].
  unfold eq_PM22.
  
  split.
  exact (H_e_left a11).

  split.
  exact (H_e_left a12).

  split.
  exact (H_e_left a21).

  exact (H_e_left a22).
Qed.

Lemma neutral_matrix_is_right_neutral_for_polymorphic_matrix_addition :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall Dot : T -> T -> T,
        forall PAdd : PM22 T -> PM22 T -> PM22 T,
          specification_of_polymorphic_matrix_addition T eqT Dot PAdd ->
          forall e : T,
            specification_of_neutrality T eqT Dot e ->
            forall A : PM22 T,
              eq_PM22 T eqT 
                      (PAdd A (pm22 T e e e e)) A.
Proof.
  intros T eqT H_eqT Dot PAdd H_PA e H_e.
  intros [ a11 a12 a21 a22 ].
  unfold specification_of_polymorphic_matrix_addition in H_PA.
  apply (eq_PM22_is_transitive T eqT H_eqT
            (PAdd (pm22 T a11 a12 a21 a22) (pm22 T e e e e))
            (pm22 T (Dot a11 e) (Dot a12 e) (Dot a21 e) (Dot a22 e))).
    apply H_PA.

  unfold specification_of_neutrality in H_e.
  destruct H_e as [H_e_right _].
  unfold eq_PM22.
  
  split.
  exact (H_e_right a11).

  split.
  exact (H_e_right a12).

  split.
  exact (H_e_right a21).

  exact (H_e_right a22).
Qed.

(* Furthermore, if the underlying binary operation is associative under the
   equality relation, polymorphic matrix addition will also be associative. 
   Also, the binary operation should preserve the equality relation. *)

Lemma polymorphic_matrix_addition_is_associative :
  forall T : Type,
    forall eqT : T -> T -> Prop,
      specification_of_an_equivalence_relation T eqT ->
      forall Dot : T -> T -> T,
        specification_of_preservation T eqT Dot ->
        specification_of_associativity T eqT Dot ->
        forall PAdd : PM22 T -> PM22 T -> PM22 T,
          specification_of_polymorphic_matrix_addition T eqT Dot PAdd ->
          specification_of_associativity (PM22 T) (eq_PM22 T eqT) PAdd.
Proof.
  intros T eqT H_eqT Dot H_PDot H_ADot PAdd H_SP.
  unfold specification_of_associativity.
  intros [ a11 a12 a21 a22 ] [ b11 b12 b21 b22 ] [ c11 c12 c21 c22 ].
  unfold specification_of_polymorphic_matrix_addition in H_SP.
  unfold specification_of_associativity in H_ADot.
  
  apply (eq_PM22_is_transitive T eqT H_eqT (PAdd (PAdd (pm22 T a11 a12 a21 a22)
                                                       (pm22 T b11 b12 b21 b22))
                                                 (pm22 T c11 c12 c21 c22))
                                           (PAdd (pm22 T (Dot a11 b11)
                                                         (Dot a12 b12)
                                                         (Dot a21 b21)
                                                         (Dot a22 b22))
                                                 (pm22 T c11 c12 c21 c22))).
    apply (polymorphic_matrix_addition_preserves_eq_PM22 
             T eqT H_eqT Dot H_PDot PAdd H_SP).
      apply H_SP.
      apply (eq_PM22_is_reflexive T eqT H_eqT).

  apply (eq_PM22_is_transitive T eqT H_eqT (PAdd (pm22 T (Dot a11 b11)
                                                         (Dot a12 b12)
                                                         (Dot a21 b21)
                                                         (Dot a22 b22))
                                                 (pm22 T c11 c12 c21 c22))
                                           (pm22 T(Dot (Dot a11 b11) c11)
                                                  (Dot (Dot a12 b12) c12)
                                                  (Dot (Dot a21 b21) c21)
                                                  (Dot (Dot a22 b22) c22))).
    apply H_SP.

  apply (eq_PM22_is_symmetric T eqT H_eqT).
                               
  apply (eq_PM22_is_transitive T eqT H_eqT (PAdd (pm22 T a11 a12 a21 a22)
                                                 (PAdd (pm22 T b11 b12 b21 b22)
                                                       (pm22 T c11 c12 c21 c22)))
                                           (PAdd (pm22 T a11 a12 a21 a22)
                                                 (pm22 T (Dot b11 c11)
                                                         (Dot b12 c12)
                                                         (Dot b21 c21)
                                                         (Dot b22 c22)))).
    apply (polymorphic_matrix_addition_preserves_eq_PM22 
             T eqT H_eqT Dot H_PDot PAdd H_SP).
      apply (eq_PM22_is_reflexive T eqT H_eqT).
      apply H_SP.

  apply (eq_PM22_is_transitive T eqT H_eqT (PAdd (pm22 T a11 a12 a21 a22)
                                                 (pm22 T (Dot b11 c11)
                                                         (Dot b12 c12)
                                                         (Dot b21 c21)
                                                         (Dot b22 c22)))
                                           (pm22 T(Dot a11 (Dot b11 c11))
                                                  (Dot a12 (Dot b12 c12))
                                                  (Dot a21 (Dot b21 c21))
                                                  (Dot a22 (Dot b22 c22)))).
    apply H_SP.

  apply (eq_PM22_is_symmetric T eqT H_eqT).
  unfold eq_PM22.

  split.
  exact (H_ADot a11 b11 c11).

  split.
  exact (H_ADot a12 b12 c12).

  split.
  exact (H_ADot a21 b21 c21).

  exact (H_ADot a22 b22 c22).
Qed.

(* The reader may have noticed now that polymorphic matrix addition preserves
   eq_PM22 if Dot preserves eqT; that eq_PM22 is an equivalence relation if
   eqT is; that polymorphic matrix addition has a neutral element if Dot has;
   and that polymorphic matrix addition is associative if Dot is. It can be
   concluded that if some type T and a binary operation Dot form a monoid under
   eqT, then matrices containing elements of type T and polymorphic matrix
   addition with dot form a monoid under eq_PM22. *)

Theorem polymorphic_matrices_and_polymorphic_matrix_addition_form_a_monoid :
  forall (T : Type)
         (eqT : T -> T -> Prop)
         (Dot : T -> T -> T),
    T_and_Dot_form_a_Monoid_under_eqT T eqT Dot ->
    forall PAdd : PM22 T -> PM22 T -> PM22 T,
      specification_of_polymorphic_matrix_addition T eqT Dot PAdd ->
      T_and_Dot_form_a_Monoid_under_eqT (PM22 T) (eq_PM22 T eqT) PAdd.
Proof.
  intros T eqT Dot H_Monoid.
  intros PAdd H_PA.
  unfold T_and_Dot_form_a_Monoid_under_eqT in H_Monoid.
  destruct H_Monoid as [H_eqT [H_PDot [H_ADot H_e]]].
  destruct H_e as [e H_e].
  unfold T_and_Dot_form_a_Monoid_under_eqT.
  
  split.
  exact (eq_PM22_is_an_equivalence_relation T eqT H_eqT).

  split.
  exact (polymorphic_matrix_addition_preserves_eq_PM22
           T eqT H_eqT Dot H_PDot PAdd H_PA).

  split.
  exact (polymorphic_matrix_addition_is_associative
           T eqT H_eqT Dot H_PDot H_ADot PAdd H_PA).

  exists (pm22 T e e e e).
  unfold specification_of_neutrality.
  split.
    exact (neutral_matrix_is_right_neutral_for_polymorphic_matrix_addition
             T eqT H_eqT Dot PAdd H_PA e H_e).
    exact (neutral_matrix_is_left_neutral_for_polymorphic_matrix_addition
             T eqT H_eqT Dot PAdd H_PA e H_e).
Qed.
