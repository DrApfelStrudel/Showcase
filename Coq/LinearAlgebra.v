Require Import Arith unfold_tactic.

(* In the notes I will let an addition function be denoted infix with + and
   multiplication be denoted infix with *. This is not the case in the proofs. *)

(* An element O is Zero for an addition function, if
   O + a = a for all a of the same Type as O. 

   That is, if an element is Zero, it is neutral for addition. *)

Definition Zero (F : Type)
                (FPlus : F -> F -> F)
                (O : F) :=
  forall a : F,
    FPlus O a = a.

(* An element E is One for an multiplication function, if
   it is not Zero for the addition function, and if 
   E * a = a for all a of the same Type as E. 

   That is, if an element is One, it is not neutral for addition 
   but neutral for multiplication. *)

Definition One (F : Type)
           (FPlus : F -> F -> F)
           (FMult : F -> F -> F)
           (E : F) :=
  ~ (Zero F FPlus E)
  /\
  forall a : F,
    FMult E a = a.

(* Two elements are inverse with respect to the addition function
   if the two elements added together yields an element that is Zero. 

   That is, if x and ix are inverse in addition, (x + ix) is neutral
   for addition. *)

Definition plus_inv (F : Type)
           (FPlus : F -> F -> F)
           (x ix : F) :=
  Zero F FPlus (FPlus x ix).

(* Two elements are inverse with respect to the multiplication function
   if the two elements multiplied yields an element that is One.
  
   That is, if x and ix are inverse in multiplication, (x * ix) is not 
   neutral for addition but neutral for multiplication. *)

Definition mult_inv (F : Type)
           (FPlus : F -> F -> F)
           (FMult : F -> F -> F)
           (x ix : F) :=
  One F FPlus FMult (FMult x ix).

(* A Field contains a Type F of elements, an addition function ( + ) over F and
   a multiplication function ( * ) over F. It must be the case that

   - For all a b in F, a + b = b + a  
     (Addition is commutative) 

   - For all a b y in F, (a + b) + y = a + (b + y)  
     (Addition is associative) 

   - There exists a element in F, which is neutral for addition i.e. there
     exists an element which is Zero.
     (Existance of neutral addition element)  

   - For all a in F, there exists an element ia in F such that (a + ia) is 
     neutral for addition. That is, forall x in F, x + (a + ia) = x and
     a + ia is Zero. 
     (Existance of inverse for addition) 

   - For all a b in F, a * b = b * a
     (Multiplication is commutative)
  
   - For all a b y in F, (a * b) * y = a * (b * y)
     (Multiplication is associative)
 
   - There exists a element in F, which is not neutral for addition but
     neutral for multiplication i.e. there exists an element which is One.
     (Existance of neutral multiplication element) 

   - For all a in F, which is not neutral for addition i.e. not Zero, there
     exists an element ia in F such that (a * ia) is neutral for multiplication.
     That is, forall x in F, x * (a * ia) = x and a * ia is One.
     (Existance of inverse for multiplication) 

   - For all a b y in F, y * (a + b) = (y * a) + (y * b)
     (Multiplication can be distributed over addition) *)
 
Definition field_spec (F : Type)
                      (FPlus : F -> F -> F)
                      (FMult : F -> F -> F) :=
  (forall a b : F,
     FPlus a b = FPlus b a)
  /\
  (forall a b y : F,
     FPlus (FPlus a b) y =
     FPlus a (FPlus b y))
  /\
  (exists O : F, Zero F FPlus O)
  /\
  (forall a : F,
   exists na : F,
     plus_inv F FPlus a na)
  /\
  (forall a b : F,
     FMult a b = FMult b a)
  /\
  (forall a b y : F,
     FMult (FMult a b) y =
     FMult a (FMult b y))
  /\
  (exists E : F, One F FPlus FMult E)
  /\
  (forall a : F,
     ~ (Zero F FPlus a) ->
     exists ia : F,
       mult_inv F FPlus FMult a ia)
  /\
  (forall a b y : F,
     FMult y (FPlus a b) =
     FPlus (FMult y a) (FMult y b)).

(* Just a trivial lemma. If an element is one, it isn't zero. But this
   follows from the definition of One. *)

Lemma one_is_not_zero :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
  forall f : F,
    One F FPlus FMult f ->
    ~ (Zero F FPlus f).
Proof.
  intros F FPlus FMult.
  intros f H_of.
  intro H_zf.
  unfold One in H_of.
  destruct H_of as [H_nzf _].
  apply H_nzf.
  exact H_zf.
Qed.

(* An interesting lemma. In a field there exists only one Zero element.
   This follows from the commutativity of addition in the field. *)

Lemma unique_zero :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall O1 O2 : F,
      Zero F FPlus O1 ->
      Zero F FPlus O2 ->
      O1 = O2.
Proof.
-  intros F FPlus FMult H_Sf.
  intros O1 O2 H_zO1 H_zO2.
  unfold Zero in H_zO1.
  unfold Zero in H_zO2.
  unfold field_spec in H_Sf.
  destruct H_Sf as [H_Sf_comm _].
  rewrite <- (H_zO2 O1).
  rewrite -> (H_Sf_comm O2 O1).
  exact (H_zO1 O2).
Qed.

(* Another interesting lemma. There exists only one One element in a field.
   This follows from commutativity of multiplication. *)

Lemma unique_one :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall E1 E2 : F,
      One F FPlus FMult E1 ->
      One F FPlus FMult E2 ->
      E1 = E2.
Proof.
  intros F FPlus FMult H_Sf.
  intros E1 E2 H_OE1 H_OE2.
  unfold One in H_OE1; destruct H_OE1 as [_ H_E1_a].
  unfold One in H_OE2; destruct H_OE2 as [_ H_E2_a].
  unfold field_spec in H_Sf.
  destruct H_Sf as [_ [_ [_ [_ [H_mult_comm _]]]]].
  rewrite <- (H_E2_a E1).
  rewrite -> (H_mult_comm E2 E1).
  exact (H_E1_a E2).
Qed.

(* For all a b y in a field, a + y = b + y implies that a = b. This follows
   from commutativity, associativity and the existance of inverse elements in
   addition. *)

Lemma plus_equal_r_down :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b y : F,
      FPlus a y = FPlus b y ->
      a = b.
Proof.
  intros F FPlus FMult H_Sf.
  intros a b y H_ay_by.
  unfold field_spec in H_Sf.
  destruct H_Sf as [FPlus_comm [FPlus_assoc [_ [FPlus_I _]]]].
  destruct (FPlus_I y) as [ny H_ny].
  unfold plus_inv in H_ny.
  unfold Zero in H_ny.

  rewrite <- (H_ny a).
  rewrite -> (FPlus_comm (FPlus y ny) a).
  rewrite <- (FPlus_assoc a y ny).
  rewrite -> H_ay_by.
  rewrite -> (FPlus_assoc b y ny).
  rewrite -> (FPlus_comm b (FPlus y ny)).
  exact (H_ny b).
Qed.

(* For all a b in a field, a = b implies that for all y in the field,
   a + y = b + y. This is pretty trivial. The variables does not even
   need to be in a field. *)

Lemma plus_equal_r_up :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b : F,
      a = b ->
      forall y : F,
        FPlus a y = FPlus b y.
Proof.
  intros F FPlus FMult H_FS a b H_ab y.
  rewrite -> H_ab.
  reflexivity.
Qed.

(* Because of commutativity of addition and the earlier lemma, it is also
   the case that for all a b y in a field, y + a = y + b implies that a = b. *)

Corollary plus_equal_l_down :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b y : F,
      FPlus y a = FPlus y b ->
      a = b.
Proof.
  intros F FPlus FMult H_FS a b y H_aby.
  assert (H_FS' := H_FS).
  unfold field_spec in H_FS'.
  destruct H_FS' as [FPlus_comm _].
  rewrite -> (FPlus_comm y a) in H_aby.
  rewrite -> (FPlus_comm y b) in H_aby.
  exact (plus_equal_r_down F FPlus FMult H_FS a b y H_aby).
Qed.

(* For all a b in a field, a = b implies that for all y in the field,
   y + a = y + b. Trivial. *)

Lemma plus_equal_l_up :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b : F,
      a = b ->
      forall y : F,
        FPlus y a = FPlus y b.
Proof.
  intros F FPlus FMult H_FS a b H_ab y.
  rewrite -> H_ab.
  reflexivity.
Qed.

(* Any inverse element in addition is unique in the field. That is, if
   a + x = 0 and a + y = 0, then x must be y. This follows from the uniqueness
   of the Zero element and plus_equal  . *)

Lemma plus_inv_is_unique :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a x y : F,
      plus_inv F FPlus a x ->
      plus_inv F FPlus a y ->
      x = y.
Proof.
  intros F FPlus FMult H_Sf.
  intros a x y H_Iax H_Iay.
  unfold plus_inv in H_Iax.
  unfold plus_inv in H_Iay.
  assert (H_ax_ay :=
            unique_zero F FPlus FMult H_Sf (FPlus a x) (FPlus a y) H_Iax H_Iay).
  exact (plus_equal_l_down F FPlus FMult H_Sf x y a H_ax_ay).
Qed.

(* For all a b y in a Field, y not being Zero implies that a * y = b * y implies
   that a = b. This follows from the commutativity, associativity and existance
   of inverse elements for multiplication. *)

Lemma mult_equal_r_down:
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b y : F,
      ~ (Zero F FPlus y) ->
      FMult a y = FMult b y ->
      a = b.
Proof.
  intros F FPlus FMult H_Sf.
  intros a b y H_nzy H_ay_by.
  assert (H_Sf' := H_Sf).
  unfold field_spec in H_Sf'.
  destruct H_Sf' as [_ [_ [_ [_ [mult_comm [mult_assoc [_ [mult_I _]]]]]]]].
  destruct (mult_I y H_nzy) as [ny H_ny].
  unfold mult_inv in H_ny.
  unfold One in H_ny.
  destruct H_ny as [H_nynoZ H_nyN].
  rewrite <- (H_nyN a).
  rewrite -> (mult_comm (FMult y ny) a).
  rewrite <- (mult_assoc a y ny).
  rewrite -> H_ay_by.
  rewrite -> (mult_assoc b y ny).
  rewrite -> (mult_comm b (FMult y ny)).
  exact (H_nyN b).
Qed.

(* For all a b in a Field, a = b implies that for all y in that Field,
   a * y = b * y. Trivial. *)

Lemma mult_equal_r_up:
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b : F,
      a = b ->
      forall y : F,
        FMult a y = FMult b y.
Proof.
  intros F FPlus FMult H_FS a b H_ab y.
  rewrite -> H_ab.
  reflexivity.
Qed.

(* It is also the case that for all a b y in a Field, y not being Zero implies
   y * a = y * b implies a = b. This follows from the earlier lemma and the
   commutativity of multiplication. *)
 
Lemma mult_equal_l_down :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b y : F,
      ~ (Zero F FPlus y) ->
      FMult y a = FMult y b ->
      a = b.
Proof.
  intros F FPlus FMult H_FS.
  intros a b y H_nzy H_ya_yb.
  assert (H_FS' := H_FS).
  unfold field_spec in H_FS'.
  destruct H_FS' as [_ [_ [_ [_ [FMult_comm _]]]]].
  rewrite -> (FMult_comm y a) in H_ya_yb.
  rewrite -> (FMult_comm y b) in H_ya_yb.
  exact (mult_equal_r_down F FPlus FMult H_FS a b y H_nzy H_ya_yb).
Qed.

(* For all a b in a Field, a = b implies that for all y in that Field,
   y * a = y * b. Trivial. *)

Lemma mult_equal_l_up:
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a b : F,
      a = b ->
      forall y : F,
        FMult y a = FMult y b.
Proof.
  intros F FPlus FMult H_FS a b H_ab y.
  rewrite -> H_ab.
  reflexivity.
Qed.

(* For all a in a field, a not being Zero implies that the inverse of a
   is uniquely determined. That is, if a =/= 0, then a * x = 1 and a * y = 1 
   implies that x = y. This follows from the uniqueness of the One element
   and mult_equal. *)

Lemma mult_inv_is_unique_for_not_zero :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a x y : F,
      ~ (Zero F FPlus a) ->
      mult_inv F FPlus FMult a x ->
      mult_inv F FPlus FMult a y ->
      x = y.
Proof.
  intros F FPlus FMult H_Sf.
  intros a x y H_NZa H_Iax H_Iay.
  unfold mult_inv in H_Iax.
  unfold mult_inv in H_Iay.
  assert (H_ax_ay :=
            unique_one F FPlus FMult H_Sf (FMult a x) (FMult a y) H_Iax H_Iay).
  exact (mult_equal_l_down F FPlus FMult H_Sf x y a H_NZa H_ax_ay).
Qed.

(* The neutral element for addition is absorbant for multiplication. That is,
   forall a in a field, a * 0 = 0, where 0 is the neutral element for addition. 
   It follows from the definition of Zero and distributivity of multiplication 
   that (0 + (a * 0)) = (a * 0) + (a * 0), and from that it follows from 
   plus_equal that 0 = (a * 0). *)

Lemma mult_zero_is_abs_r :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a O : F,
      Zero F FPlus O ->
      Zero F FPlus (FMult a O).
Proof.
  intros F FPlus FMult H_FS.
  intros a O H_ZO.
  assert (H_FS' := H_FS).
  unfold field_spec in H_FS'.
  destruct H_FS' as [_ [_ [_ [_ [_ [_ [_ [_ FMult_distr]]]]]]]].

  (* 0 + (a * 0) = (a * 0) + (a * 0) *)
  assert (H_about_aO : FPlus O (FMult a O) = FPlus (FMult a O) (FMult a O)).
    unfold Zero in H_ZO.
    rewrite -> (H_ZO (FMult a O)).
    rewrite <- (H_ZO O) at 1.
    exact (FMult_distr O O a).

  apply (plus_equal_r_down F FPlus FMult H_FS O (FMult a O) (FMult a O)) 
      in H_about_aO.
  rewrite -> H_about_aO in H_ZO.
  exact H_ZO.
Qed.

(* Zero is also absorbant from the other side. This follows from the earlier
   lemma and that multiplication is commutative. *)

Lemma mult_zero_is_abs_l :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall a O : F,
      Zero F FPlus O ->
      Zero F FPlus (FMult O a).
Proof.
  intros F FPlus FMult H_FS.
  intros a O H_ZO.
  assert (H_FS' := H_FS).
  unfold field_spec in H_FS'.
  destruct H_FS' as [_ [_ [_ [_ [FMult_comm _]]]]].
  rewrite -> (FMult_comm O a).
  exact (mult_zero_is_abs_r F FPlus FMult H_FS a O H_ZO).
Qed.

(* The definition of the addition inverse element to the element which is neutral
   for addition. Some would call this -1. It turns out that it has some
   interesting properties. *) 

Definition inv_One (F : Type)
           (FPlus : F -> F -> F)
           (FMult : F -> F -> F)
           (io : F) :=
  forall i : F,
    One F FPlus FMult i ->
    plus_inv F FPlus i io.

(* A lemma that follows from the existance of inverses for addition, the 
   existance of a neutral element in multiplication and the uniqueness of One. 
   The lemma shows that inv_One exists. *)

Lemma inv_One_exists :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    exists inv1 : F,
      inv_One F FPlus FMult inv1.
Proof.
  intros F FPlus FMult H_FS.
  assert (H_FS' := H_FS).
  unfold field_spec in H_FS'.
  destruct H_FS' as [_ [_ [_ [FPlus_I [_ [_ [FMult_E _]]]]]]].
  destruct FMult_E as [E H_E].
  assert (H_IE := FPlus_I E).
  destruct H_IE as [invE H_invE].
  exists invE.
  unfold inv_One.
  intros i H_i.
  rewrite -> (unique_one F FPlus FMult H_FS i E H_i H_E).
  exact H_invE.
Qed.

(* For all a in a Field, a multiplied by the addition inverse of one is the
   inverse of a. Said in another way, a + ((-1) * a) = 0. This follows from the
   commutativity, distributivity, neutral existant and zero absorbant properties
   of multiplication. *) 

Lemma negative_is_plus_inverse :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall inv1 : F,
      inv_One F FPlus FMult inv1 ->
      forall a : F,
        plus_inv F FPlus a (FMult inv1 a).
Proof.
  intros F FPlus FMult H_FS inv1 H_inv1 a.
  unfold plus_inv.
  assert (H_FS' := H_FS).
  unfold field_spec in H_FS'.
  destruct H_FS' as [_ [_ [_ [_ [FMult_comm [_ [FMult_E [_ FMult_D]]]]]]]].
  destruct (FMult_E) as [E H_E].
  assert (H_E' := H_E).
  unfold One in H_E'.
  destruct H_E' as [_ H_Ea].
  rewrite <- (H_Ea a) at 1.
  rewrite -> (FMult_comm E a).
  rewrite -> (FMult_comm inv1 a).
  rewrite <- (FMult_D E inv1 a).
  unfold inv_One in H_inv1.
  assert (H := H_inv1 E H_E).
  unfold plus_inv in H.
  exact (mult_zero_is_abs_r F FPlus FMult H_FS a (FPlus E inv1) H).
Qed.

(* Because of the uniqueness of plus inverses, the inverse of a for addition
   is always the plus inverse of 1 multiplied by a. That is, for all a b
   in the field, a + b = 0 implies that b = (-1) * a. *)

Lemma negative_is_always_plus_inverse :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall inv1 : F,
      inv_One F FPlus FMult inv1 ->
      forall a ainv : F,
        plus_inv F FPlus a ainv ->
        ainv = FMult inv1 a.
Proof.
  intros F FPlus FMult H_FS inv1 H_inv1 a ainv H_I.
  assert (H_I2 := negative_is_plus_inverse F FPlus FMult H_FS inv1 H_inv1 a).
  exact (plus_inv_is_unique F FPlus FMult H_FS a ainv (FMult inv1 a) H_I H_I2).
Qed.

(* There does not exist an multiplication inverse of the neutral element
   for addition. That is, 'division by zero' is not possible. This follows
   from the definition of inverses, One, Zero and that Zero is absorbant
   for multiplication. *)

Lemma zero_has_no_inverse :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall O : F,
      Zero F FPlus O ->
    ~ (exists invO : F,
         mult_inv F FPlus FMult O invO). 
Proof.
  intros F FPlus FMult H_FS O H_ZO.
  intro H_exInvO.
  destruct H_exInvO as [InvO H_InvO].
  unfold mult_inv in H_InvO.
  unfold One in H_InvO.
  destruct H_InvO as [H_NZM _].
  apply H_NZM.
  exact (mult_zero_is_abs_l F FPlus FMult H_FS InvO O H_ZO).
Qed.

(* More to come about elements in the field, perhaps a proof that
   (a * c) * (inva * b) = c * b. *) 

Require Import List.

(* I will define a vector as being a list of some type of element. *)

Definition FVector (F : Type) := list F.

Lemma unfold_length_nil :
  forall F : Type,
    length (nil : FVector F) = 0.
Proof.
  unfold_tactic length.
Qed.
 
Lemma unfold_length_cons :
  forall F : Type,
  forall v1 : F,
  forall v' : FVector F,
    length (v1 :: v') = S (length v').
Proof.
  unfold_tactic length.
Qed.

(* If the length of a vector is 0, the vector must be nil. This 
   follows from the fact that it does not make sense to assume that 
   a vector containing something has a length of 0. *)

Lemma lengthZ_NoE :
  forall F : Type,
  forall v : FVector F,
    length v = 0 ->
    v = nil.
Proof.
  intros F v H_l0.
  destruct v as [ | v1 v'].
    reflexivity.

    rewrite -> (unfold_length_cons F v1 v') in H_l0.
    discriminate H_l0.
Qed.

(* If the length of a vector is more than 0, the vector must contain at least
   one element. This follows from the fact that it does not make sense to 
   assume that nil has a length different from 0. *)

Lemma lengthS_E :
  forall F : Type,
  forall v : FVector F,
  forall n' : nat,
    length v = S n' ->
    exists v1 : F,
      exists v' : FVector F,
        v = v1 :: v'.
Proof.
  intros F v n' H_ls.
  destruct v as [ | v1 v'].
    rewrite -> unfold_length_nil in H_ls.
    discriminate H_ls.

    exists v1.
    exists v'.
    reflexivity.
Qed.

(* Definition of two vectors having the same length. *)

Definition same_length (F : Type) (v w : FVector F) :=
  length v = length w.

(* If two vectors have the same length, stripping of the top element
   of both vectors will yield two vectors which have the same length. 
   This follows from injection on the length of the vectors. *)

Lemma same_length_conserved_down :
  forall F : Type,
  forall v1 w1 : F,
  forall v' w' : FVector F,
    same_length F (v1 :: v') (w1 :: w') ->
    same_length F v' w'.
Proof.
  intros F v1 w1 v' w' H_sl_v_w.
  unfold same_length in H_sl_v_w.
  rewrite ->2 unfold_length_cons in H_sl_v_w.
  injection H_sl_v_w as H_sl_v'_w'.
  unfold same_length.
  exact H_sl_v'_w'.
Qed.

(* If two vectors have the same length, putting two elements on top of both
   of them will yield two vectors which have the same length. This follows
   from f_equal on the length of the vectors. *)

Lemma same_length_conserved_up :
  forall F : Type,
    forall v1 w1 : F,
    forall v' w' : FVector F,
      same_length F v' w' ->
      same_length F (v1 :: v') (w1 :: w').
Proof.
  intros F v1 w1 v' w' H_sl_v'_w'.
  unfold same_length.
  rewrite ->2 (unfold_length_cons).
  unfold same_length in H_sl_v'_w'.
  apply f_equal.
  exact H_sl_v'_w'.
Qed.

(* If a vector has the same length as nil, it must be nil. This
   follows from an earlier lemma about the length being 0. *)

Lemma same_length_nil :
  forall F : Type,
  forall v : FVector F,
    same_length F v nil ->
    v = nil.
Proof.
  intros F v H_sl_v_nil.
  unfold same_length in H_sl_v_nil.
  rewrite -> (unfold_length_nil) in H_sl_v_nil.
  exact (lengthZ_NoE F v H_sl_v_nil).
Qed.

(* If a vector has the same length as a vector containing at least one element,
   it must itself contain at least one element. This follows from an earlier 
   lemma about the length being more than 0. *)

Lemma same_length_cons :
  forall F : Type,
  forall v w' : FVector F,
  forall w1 : F,
    same_length F v (w1 :: w') ->
    exists v1 : F,
      exists v' : FVector F,
        v = v1 :: v'.
Proof.
  intros F v w' w1 H_sl_v_w.
  unfold same_length in H_sl_v_w.
  rewrite -> (unfold_length_cons) in H_sl_v_w.
  destruct (lengthS_E F v (length w') H_sl_v_w) as [v1 [v' H_v]].
  exists v1.
  exists v'.
  exact H_v.
Qed.

(* The property of same length is reflexive. That is, any vector has the
   same length as itself. This follows from standard reflexivity. *)

Lemma same_length_refl :
  forall F : Type,
    forall v : FVector F,
      same_length F v v.
Proof.
  intros F v.
  unfold same_length.
  reflexivity.
Qed.

(* The property of same length is symmetric. If v and w has the same length,
   then w and v has the same length. This follows from standard symmetry. *)

Lemma same_length_symm :
  forall F : Type,
  forall v w : FVector F,
    same_length F v w ->
    same_length F w v.
Proof.
  intros F v w H_sl_v_w.
  unfold same_length in H_sl_v_w.
  unfold same_length.
  symmetry.
  exact H_sl_v_w.
Qed.

(* The property of same length is transitive. If u and v has the same length
   and v and w has the same length, then u and w has the same length. *)

Lemma same_length_trans :
  forall F : Type,
  forall u v w : FVector F,
    same_length F u v ->
    same_length F v w ->
    same_length F u w.
Proof.
  intros F u v w H_sl_u_v H_sl_v_w.
  unfold same_length in H_sl_u_v, H_sl_v_w.
  unfold same_length.
  rewrite -> H_sl_u_v.
  exact H_sl_v_w.
Qed.

(* The three lemmas above proves that the property of same length is
   an equivalence relation. It is reflexive, symmetric and transitive. *)

(* This is the specification of adding two vectors together. Actually it is
   just the specification of using a function when merging two vectors, but
   I will not use it as such, since I in my proofs will make sure that
   the FPlus function is addition in a field. Nevertheless it works 
   by merging two vectors into a vector where a function has been applied
   on each two respective elements of the two vectors. *)

Definition FVPlus_spec (F : Type)
           (FPlus : F -> F -> F)
           (FVPlus : FVector F -> FVector F -> FVector F) :=
  (FVPlus nil nil = nil)
  /\
  (forall x y : F,
   forall xs' ys' : FVector F,
     FVPlus (x :: xs') (y :: ys') = FPlus x y :: FVPlus xs' ys').

(* FVPlus is unique if the input vectors have the same length. In all
   my other proofs I will make sure that input vectors have the same length,
   since I have not defined the result of adding two vectors of different
   lengths with FVPlus. *)

Lemma FVPlus_is_unique_for_same_length :
  forall F : Type,
  forall FPlus : F -> F -> F,
  forall f g : FVector F -> FVector F -> FVector F,
    FVPlus_spec F FPlus f ->
    FVPlus_spec F FPlus g ->
    forall v w : FVector F,
      same_length F v w ->
      f v w = g v w.
Proof.
  intros F FAdd f g H_Sf H_Sg.

  unfold FVPlus_spec in H_Sf.
  destruct H_Sf as [H_Sf_nil H_Sf_cons].
  unfold FVPlus_spec in H_Sg.
  destruct H_Sg as [H_Sg_nil H_Sg_cons].

  intros v w; revert v.
  induction w as [ | w1 w' IHw'].
    intros v H_sl_v_w.
    rewrite -> (same_length_nil F v H_sl_v_w).
    rewrite -> H_Sg_nil.
    exact H_Sf_nil.

    intros v H_sl_v_w.
    destruct (same_length_cons F v w' w1 H_sl_v_w) as [v1 [v' H_v]].
    rewrite -> H_v in H_sl_v_w.
    assert (IH' := IHw' v' (same_length_conserved_down F v1 w1 v' w' H_sl_v_w)).
    rewrite -> H_v.
    rewrite -> (H_Sf_cons v1 w1 v' w').
    rewrite -> IH'.
    rewrite <- (H_Sg_cons v1 w1 v' w').
    reflexivity.
Qed.

(* The first interesting lemma. If two vectors of same length contains
   elements from the same field, adding them together with the addition of the 
   field is commutative. This follows from the fact that addition of each two 
   elements in the vector is commutative because of the properties of the 
   Field and induction. *)

Lemma FVPlus_comm_for_fields :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall v w : FVector F,
        same_length F v w ->
        FVPlus v w = FVPlus w v.
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP v w; revert v.
  induction w as [ | w1 w' IHw'].
    intros v H_sl_v_w.
    rewrite -> (same_length_nil F v H_sl_v_w).
    reflexivity.

    intros v H_sl_v_w.
    destruct (same_length_cons F v w' w1 H_sl_v_w) as [v1 [v' H_v]].
    rewrite -> H_v in H_sl_v_w.
    assert (IH' := IHw' v' (same_length_conserved_down F v1 w1 v' w' H_sl_v_w)).
    rewrite -> H_v.
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [_ H_FVP_cons].
    rewrite -> (H_FVP_cons v1 w1 v' w').
    rewrite -> IH'.
    unfold field_spec in H_FS.
    destruct H_FS as [FPlus_comm _].
    rewrite -> (FPlus_comm v1 w1).
    rewrite <- (H_FVP_cons w1 v1 w' v').
    reflexivity.
Qed.

(* If three vectors of the same length contains elements from the same field,
   adding them together with the addition of the field is associative. This
   follows from the associative property of the field addition and induction. *)

Lemma FVAdd_assoc_for_fields :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall u v w : FVector F,
        same_length F u v ->
        same_length F v w ->
        FVPlus u (FVPlus v w) = FVPlus (FVPlus u v) w.
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP u v; revert u.
  induction v as [ | v1 v' IHv'].
    intros u w H_sl_u_v H_sl_v_w.
    rewrite -> (same_length_nil F u H_sl_u_v).
    rewrite -> (same_length_nil F w (same_length_symm F nil w H_sl_v_w)).
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [H_FVS_nil _].
    rewrite ->2 (H_FVS_nil).
    reflexivity.

    intros u w H_sl_u_v H_sl_v_w.
    destruct (same_length_cons F u v' v1 H_sl_u_v) as [u1 [u' H_u]].
    destruct (same_length_cons F w v' v1
              (same_length_symm F (v1 :: v') w H_sl_v_w)) as [w1 [w' H_w]].
    rewrite -> H_u in H_sl_u_v.
    rewrite -> H_w in H_sl_v_w.
    assert (IH' := IHv' u' w' 
                  (same_length_conserved_down F u1 v1 u' v' H_sl_u_v)      
                  (same_length_conserved_down F v1 w1 v' w' H_sl_v_w)).
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [_ H_FVP_cons].
    rewrite -> H_u, H_w.
    rewrite -> (H_FVP_cons v1 w1 v' w').
    rewrite -> (H_FVP_cons u1 (FPlus v1 w1) u' (FVPlus v' w')).
    rewrite -> IH'.
    unfold field_spec in H_FS.
    destruct H_FS as [_ [FPlus_assoc _]].
    rewrite <- (FPlus_assoc u1 v1 w1).
    rewrite <- (H_FVP_cons (FPlus u1 v1) w1 (FVPlus u' v') w').
    rewrite <- (H_FVP_cons u1 v1 u' v').
    reflexivity.
Qed.

(* For vector addition the zero vector of length n is defined as the vector
   with length n that added with all vectors of the same length yields the
   second vector. That is, the zero vector of length n is neutral for vector
   addition with vectors of length n. *)

Definition VZero_n (F : Type)
                   (FVPlus : FVector F -> FVector F -> FVector F)
                   (VO : FVector F)
                   (n : nat) :=
  (length VO = n)
  /\
  (forall v : FVector F,
     same_length F v VO ->
     FVPlus v VO = v).

(* Very exciting lemma! If vector addition is specified with the addition of
   a field, a zero vector of length (S n') must have the Zero element as
   the first element and the rest of the vector must be a zero vector of
   length n'. *)

Lemma about_VZero_n :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall n' : nat,
      forall VO1 : F,
      forall VO' : FVector F,
          VZero_n F FVPlus (VO1 :: VO') (S n') ->
          (Zero F FPlus VO1) /\
          (VZero_n F FVPlus VO' n').
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP n' VO1 VO' H_VZSn'_VO.
  unfold VZero_n in H_VZSn'_VO.
  destruct H_VZSn'_VO as [H_VZSn'_VO_l H_VZSn'_VO_neutral].
  split.
    unfold Zero.
    intro a.
    assert (H_VO'_refl := same_length_refl F VO').
    apply (same_length_conserved_up F a VO1 VO') in H_VO'_refl.
    assert (H_VO'_a_VO1 := H_VZSn'_VO_neutral (a :: VO') H_VO'_refl).
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [_ H_FVP_cons].
    rewrite -> (H_FVP_cons a VO1 VO' VO') in H_VO'_a_VO1.
    injection H_VO'_a_VO1 as _ H_a_VO1.
    unfold field_spec in H_FS.
    destruct H_FS as [FPlus_comm _].
    rewrite -> (FPlus_comm VO1 a).
    exact H_a_VO1.

    unfold VZero_n.
    split.
      rewrite -> (unfold_length_cons F VO1 VO') in H_VZSn'_VO_l.
      injection H_VZSn'_VO_l as H_VZn'_VO'_l; clear H_VZSn'_VO_l.
      exact H_VZn'_VO'_l.

      intros v H_sl_v_VO'.
      apply (same_length_conserved_up F VO1 VO1 v VO') in H_sl_v_VO'.
      apply (H_VZSn'_VO_neutral (VO1 :: v)) in H_sl_v_VO'.
      unfold FVPlus_spec in H_FVP.
      destruct H_FVP as [_ H_FVP_cons].
      rewrite -> H_FVP_cons in H_sl_v_VO'.
      injection H_sl_v_VO' as H_v_VO' _.
      exact H_v_VO'.
Qed.

(* For any length there exists a vector which is neutral for addition. *)

Lemma VZero_n_exists :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall n : nat,
      exists VO : FVector F,
        VZero_n F FVPlus VO n.
Proof.  
  intros F FPlus FMult H_FS H_FVPlus H_FVP n.
  induction n as [ | n' IHn'].
    exists nil.
    unfold VZero_n.
    split.
      exact (unfold_length_nil F).

      intros v H_sl_v_nil.
      rewrite -> (same_length_nil F v H_sl_v_nil).
      unfold FVPlus_spec in H_FVP.
      destruct H_FVP as [H_FVP_nil _].
      exact H_FVP_nil.

    destruct IHn' as [VO' H_VO'].
    unfold field_spec in H_FS.
    destruct H_FS as [FPlus_comm [_ [FPlus_0 _]]].
    destruct FPlus_0 as [O H_O].
    exists (O :: VO').
    unfold VZero_n.
    unfold VZero_n in H_VO'.
    destruct H_VO' as [H_VO'_l H_VO'_Neu].
    split.
      rewrite -> (unfold_length_cons F O VO').
      rewrite -> H_VO'_l.
      reflexivity.

      intros v H_sl_v_VO.
      destruct (same_length_cons F v VO' O H_sl_v_VO) as [v1 [v' H_v]].
      rewrite -> H_v.
      unfold FVPlus_spec in H_FVP.
      destruct H_FVP as [_ H_FVP_cons].
      rewrite -> (H_FVP_cons v1 O v' VO').
      unfold Zero in H_O.
      rewrite -> (FPlus_comm v1 O).
      rewrite -> H_O.
      rewrite -> H_v in H_sl_v_VO.
      rewrite -> (H_VO'_Neu v' 
                  (same_length_conserved_down F v1 O v' VO' H_sl_v_VO)).
      reflexivity.
Qed.

(* This definition satifies is satified by vectors which only contains elements
   which is neutral for addition. nil will always be neutral for addition
   if both inputs are of the same length since FVPlus nil nil is nil. *)

Fixpoint VZero (F : Type)
         (FPlus : F -> F -> F)
         (VO : FVector F) : Prop :=
  match VO with
    | nil => True
    | VO1 :: VO' => Zero F FPlus VO1 /\ VZero F FPlus VO'
  end.

(* Important unfold lemmas since this is a fixpoint Prop *)

Lemma unfold_VZero_nil :
  forall F : Type,
  forall FPlus : F -> F -> F,
    VZero F FPlus nil = True.
Proof.
  unfold_tactic VZero.
Qed.

Lemma unfold_VZero_cons :
  forall F : Type,
  forall FPlus : F -> F -> F,
  forall VO1 : F,
  forall VO' : FVector F,
    VZero F FPlus (VO1 :: VO') =
    (Zero F FPlus VO1 /\ VZero F FPlus VO').
Proof.
  unfold_tactic VZero.
Qed.  

(* If a vector satifies the VZero property, this is what it implies.
   All the elements in the vector are neutral for the addition function
   provided. *)

Lemma VZero_imp_nil :
  forall F : Type,
  forall FPlus : F -> F -> F,
    VZero F FPlus nil.
Proof.
  intros F FPlus.
  rewrite -> (unfold_VZero_nil F FPlus).
  exact I.
Qed.

Lemma VZero_imp_cons :
  forall F : Type,
  forall FPlus : F -> F -> F,
  forall VO1 : F,
  forall VO' : FVector F,
    VZero F FPlus (VO1 :: VO') ->
    Zero F FPlus VO1 /\ VZero F FPlus VO'.
Proof.
  intros F FPlus VO1 VO' H_VZCons.
  rewrite -> (unfold_VZero_cons F FPlus VO1 VO') in H_VZCons.
  exact H_VZCons.
Qed.

(* It can be shown that if two vectors have the same length and satifies
   the VZero property, they must be the same if the addition of the elements 
   are in a field. This follows from the fact that the Zero element is unique. *)

Lemma the_zero_vector_of_a_specific_length_is_unique :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall VO1 VO2 : FVector F,
        same_length F VO1 VO2 ->
        VZero F FPlus VO1 ->
        VZero F FPlus VO2 ->
        VO1 = VO2.
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP VO1 VO2; revert VO1.
  induction VO2 as [ | VO21 VO2' IHVO2'].
    intros VO1 H_sl_VO1_VO2 _ _.
    exact (same_length_nil F VO1 H_sl_VO1_VO2).

    intros VO1 H_sl_VO1_VO2 H_VZ_VO1 H_VZ_VO2.
    destruct (same_length_cons F VO1 VO2' VO21 H_sl_VO1_VO2) 
      as [VO11 [VO1' H_VO1]].
    rewrite -> H_VO1 in H_VZ_VO1.
    rewrite -> H_VO1.
    apply (VZero_imp_cons F FPlus VO11 VO1') in H_VZ_VO1.
    destruct H_VZ_VO1 as [H_ZVO11 H_VZ_VO1'].
    apply (VZero_imp_cons F FPlus VO21 VO2') in H_VZ_VO2.
    destruct H_VZ_VO2 as [H_ZVO12 H_VZ_VO2'].
    rewrite -> H_VO1 in H_sl_VO1_VO2.
    rewrite -> (IHVO2' VO1' 
                (same_length_conserved_down F VO11 VO21 VO1' VO2' H_sl_VO1_VO2)
                H_VZ_VO1' H_VZ_VO2').
    rewrite -> (unique_zero F FPlus FMult H_FS VO11 VO21 H_ZVO11 H_ZVO12).
    reflexivity.
Qed.

(* Also for any length, any vector being the natural for addition must 
   satisfy the VZero property. That is, the only neutral element for vector
   addition - when element addition are in a field - is the vector containing
   only addition neutral elements. *)

Lemma the_zero_vector_is_the_only_neutral :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall n : nat,
      forall VO : FVector F,
        VZero_n F FVPlus VO n ->
        VZero F FPlus VO.
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP n.
  induction n as [ | n' IHn'].
    intros VO H_VZn.
    unfold VZero_n in H_VZn.
    destruct H_VZn as [H_VZn_l _].
    rewrite -> (lengthZ_NoE F VO H_VZn_l).
    exact (VZero_imp_nil F FPlus).

    intros VO H_VZn.
    assert (H_VZn' := H_VZn).
    unfold VZero_n in H_VZn'.
    destruct H_VZn' as [H_VZn_l _].
    destruct (lengthS_E F VO n' H_VZn_l) as [vO [VO' H_VO]]; clear H_VZn_l.
    rewrite -> H_VO in H_VZn.
    rewrite -> H_VO.
    apply (about_VZero_n F FPlus FMult H_FS FVPlus H_FVP n' vO VO') in H_VZn.
    destruct H_VZn as [H_vOZ H_VO'Z].
    rewrite -> (unfold_VZero_cons F FPlus vO VO').
    split.
      exact H_vOZ.

      exact (IHn' VO' H_VO'Z).
Qed.      

(* The lemmas above has shown, that if addition is defined for a field
   and vector addition is defined for that addition, then the only neutral
   addition vector for any length is the Zero vector of that length. That is,
   it must contain only elements which is neutral for field addition.
   
   Furthermore, this vector always exists regardless of the length and it is
   always unique. *)

(* I can now defined the plus inverse of a vector. A vector is inverse of 
   another vector, if the sum of the two yields a zero vector. Also the
   two vectors have to be of the same length, since I have not uniquely
   defined vector addition for vectors of different lengths. *)

Definition VInv (F : Type)
                (FVPlus : FVector F -> FVector F -> FVector F)
                (v : FVector F)
                (vinv : FVector F) :=
  (same_length F v vinv)
  /\
  (VZero_n F FVPlus (FVPlus v vinv) (length v)).

(* It can be shown that the vector addition inverse exists for any vector. 
   This follows from the properties of the zero vector, properties of a field
   and induction. *)

Lemma VInv_exists :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall v : FVector F,
        exists vinv : FVector F,
          VInv F FVPlus v vinv.
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP v.
  induction v as [ | v1 v' IHv'].
    exists nil.
    unfold VInv.
    split.
      exact (same_length_refl F nil).

      unfold FVPlus_spec in H_FVP.
      destruct H_FVP as [H_FVP_nil _].
      rewrite -> H_FVP_nil.
      unfold VZero_n.
      split.
        reflexivity.
        
        intros v H_sl_v_nil.
        rewrite -> (same_length_nil F v H_sl_v_nil).
        exact H_FVP_nil.

    destruct IHv' as [vinv' H_vinv'].
    unfold field_spec in H_FS.
    destruct H_FS as [FPlus_comm [_ [_ [FPlus_inv _]]]].
    destruct (FPlus_inv v1) as [vinv1 H_vinv1].
    exists (vinv1 :: vinv').
    unfold VInv.
    split.
      unfold VInv in H_vinv'.
      destruct H_vinv' as [H_sl_v'_vinv' _].
      exact (same_length_conserved_up F v1 vinv1 v' vinv' H_sl_v'_vinv').

      unfold VZero_n.
      unfold VInv in H_vinv'.
      destruct H_vinv' as [H_vinv'sl H_vinv'Z].
      unfold FVPlus_spec in H_FVP.
      destruct H_FVP as [_ H_FVP_cons].
      rewrite -> (H_FVP_cons v1 vinv1 v' vinv').
      unfold VZero_n in H_vinv'Z.
      destruct H_vinv'Z as [H_vvl H_vvZ].
      split.
        rewrite ->2 (unfold_length_cons).
        rewrite -> H_vvl.
        reflexivity.

        intros w H_sl.
        destruct (same_length_cons F w (FVPlus v' vinv') (FPlus v1 vinv1) H_sl)
          as [w1 [w' H_w]].
        rewrite -> H_w.
        rewrite -> (H_FVP_cons w1 (FPlus v1 vinv1) w' (FVPlus v' vinv')).
        rewrite -> H_w in H_sl.
        apply (same_length_conserved_down F) in H_sl.
        rewrite -> (H_vvZ w' H_sl).
        unfold plus_inv in H_vinv1.
        unfold Zero in H_vinv1.
        rewrite -> (FPlus_comm w1 (FPlus v1 vinv1)).
        rewrite -> (H_vinv1 w1).
        reflexivity.
Qed.

(* If two vectors are inverse, then the top elements of both vectors must
   be each others inverses in the field, and the rest of the two vectors
   must also be inverse. This follows from the property of zero vectors
   of the same length. *)

Lemma about_VInv :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall v1 vi1 : F,
      forall v' vinv' : FVector F,
        VInv F FVPlus (v1 :: v') (vi1 :: vinv') ->
        (plus_inv F FPlus v1 vi1) /\
        (VInv F FVPlus v' vinv').
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP.
  intros v1 vi1 v' vinv' H_I.
  unfold VInv in H_I.
  destruct H_I as [H_Il H_Iz].  
  assert (H_FVP' := H_FVP).
  unfold FVPlus_spec in H_FVP'.
  destruct H_FVP' as [_ H_FVP_cons].
  rewrite -> (H_FVP_cons v1 vi1 v' vinv') in H_Iz.
  rewrite -> (unfold_length_cons F v1 v') in H_Iz.
  apply (about_VZero_n F FPlus FMult H_FS FVPlus H_FVP (length v') 
           (FPlus v1 vi1) (FVPlus v' vinv')) in H_Iz.
  destruct H_Iz as [H_invZ H_Iz'].
  split.
    unfold plus_inv.
    exact H_invZ.

    unfold VInv.
    split.
      exact (same_length_conserved_down F v1 vi1 v' vinv' H_Il).

      exact H_Iz'.
Qed.

(* I now define multiplication of a constant in a field and a vector.
   The function should yield a vector where every element has been field
   multiplied by the constant. Of course this specification is not restricted
   to fields, but I will only prove things revolving fields, since this spe-
   cification could have different properties if the multiplication is not
   a field multiplication. *)

Definition FVMult_spec (F : Type)
           (FMult : F -> F -> F)
           (FVMult : F -> FVector F -> FVector F) :=
  (forall k : F,
     FVMult k nil = nil)
  /\
  (forall v1 : F,
   forall v' : FVector F,
   forall k : F,
     FVMult k (v1 :: v') = FMult k v1 ::  FVMult k v').

(* This specification is unique regardless of the length of the input
   vector and the multiplication being in a field. *)

Lemma FVMult_is_unique :
  forall F : Type,
    forall FMult : F -> F -> F,
      forall f g : F -> FVector F -> FVector F,
        FVMult_spec F FMult f ->
        FVMult_spec F FMult g ->
        forall v : FVector F,
          forall k : F,
            f k v = g k v.
Proof.
  intros F FMult f g H_Sf H_Sg.

  unfold FVMult_spec in H_Sf.
  destruct H_Sf as [H_Sf_nil H_Sf_cons].
  unfold FVMult_spec in H_Sg.
  destruct H_Sg as [H_Sg_nil H_Sg_cons].

  intro v.
  induction v as [ | v1 v' IHv'].
    intro k.
    rewrite -> (H_Sg_nil k).
    exact (H_Sf_nil k).

    intro k.
    rewrite -> (H_Sg_cons v1 v' k).
    rewrite <- (IHv' k).
    rewrite <- (H_Sf_cons v1 v' k).
    reflexivity.
Qed.

(* Now for another interesting property of the vector addition inverse of 
   a vector. If we have an element which is the inverse of One in a field, then
   the addition inverse of a vector is the inverse of One multiplied by the
   the vector. This follows from the inverse properties of field addition, the
   property of inverse vectors and induction. *)

Lemma the_inverse_of_a_vector_is_the_negative_vector :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall FVMult : F -> FVector F -> FVector F,
        FVMult_spec F FMult FVMult ->
        forall inv1 : F,
          inv_One F FPlus FMult inv1 ->
          forall v vinv : FVector F,
            VInv F FVPlus v vinv ->
            vinv = FVMult inv1 v.
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP FVMult H_FVM inv1 H_inv1.
  intros v vinv; revert v.
  induction vinv as [ | vi1 vinv' IHvinv'].
    intros v H_v.
    unfold VInv in H_v.
    destruct H_v as [H_v_l H_v_z].
    rewrite -> (same_length_nil F v H_v_l).
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [H_FVM_nil _].
    rewrite -> (H_FVM_nil inv1).
    reflexivity.

    intros v H_vI.
    assert (H_vI' := H_vI).
    unfold VInv in H_vI'.
    destruct H_vI' as [H_v'_l _].
    destruct (same_length_cons F v vinv' vi1 H_v'_l) as [v1 [v' H_V]].
    rewrite -> H_V in H_vI.
    apply (about_VInv F FPlus FMult H_FS FVPlus H_FVP v1 vi1 v' vinv') in H_vI.
    destruct H_vI as [H_iv1vi1 H_v'I].
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [_ H_FVM_cons].
    rewrite -> H_V.
    rewrite -> (H_FVM_cons v1 v' inv1).
    rewrite -> (IHvinv' v' H_v'I).
    rewrite -> (negative_is_always_plus_inverse F FPlus FMult H_FS 
                                                inv1 H_inv1 v1 vi1 H_iv1vi1).
    reflexivity.    
Qed.

Lemma field_multiplication_is_distributive_over_vector_addition :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall FVMult : F -> FVector F -> FVector F,
        FVMult_spec F FMult FVMult ->
        forall v w : FVector F,
          same_length F v w ->
          forall k : F,
            FVMult k (FVPlus v w) =
            FVPlus (FVMult k v) (FVMult k w).
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP FVMult H_FVM v w; revert v.
  induction w as [ | w1 w' IHw'].
    intros v H_sl_v_w k.
    rewrite -> (same_length_nil F v H_sl_v_w).
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [H_FVP_nil _].
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [H_FVM_nil _].
    rewrite -> (H_FVP_nil).
    rewrite -> (H_FVM_nil) at 1.
    rewrite <- (H_FVP_nil) at 1.
    rewrite <- (H_FVM_nil k) at 1 2.
    reflexivity.

    intros v H_sl_v_w k.
    destruct (same_length_cons F v w' w1 H_sl_v_w) as [v1 [v' H_v]].
    rewrite -> H_v in H_sl_v_w.
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [_ H_FVP_cons].
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [_ H_FVM_cons].
    rewrite -> H_v.
    rewrite -> (H_FVP_cons v1 w1 v' w').
    rewrite -> (H_FVM_cons (FPlus v1 w1) (FVPlus v' w') k).
    rewrite -> (IHw' v' (same_length_conserved_down F v1 w1 v' w' H_sl_v_w) k).
    unfold field_spec in H_FS.
    destruct H_FS as [_ [_ [_ [_ [_ [_ [_ [_ FMult_distr]]]]]]]].
    rewrite -> (FMult_distr v1 w1 k).
    rewrite <- (H_FVP_cons (FMult k v1) (FMult k w1) (FVMult k v') (FVMult k w')).
    rewrite <- (H_FVM_cons v1 v' k).
    rewrite <- (H_FVM_cons w1 w' k).
    reflexivity.
Qed.

Lemma vector_multiplication_is_distributive_over_field_addition :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->
    forall FVPlus : FVector F -> FVector F -> FVector F,
      FVPlus_spec F FPlus FVPlus ->
      forall FVMult : F -> FVector F -> FVector F,
        FVMult_spec F FMult FVMult ->
        forall v : FVector F,
          forall a b : F,
            FVMult (FPlus a b) v =
            FVPlus (FVMult a v) (FVMult b v).
Proof.
  intros F FPlus FMult H_FS FVPlus H_FVP FVMult H_FVM v.
  induction v as [ | v1 v' IHv'].
    intros a b.
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [H_FVM_nil _].
    rewrite ->3 H_FVM_nil.
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [H_FVP_nil _].
    rewrite -> (H_FVP_nil).
    reflexivity.

    intros a b.
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [_ H_FVM_cons].
    rewrite -> (H_FVM_cons v1 v' (FPlus a b)).
    rewrite -> (IHv' a b).
    unfold field_spec in H_FS.
    destruct H_FS as [_ [_ [_ [_ [FMult_comm [_ [_ [_ FMult_distr]]]]]]]].
    rewrite -> (FMult_comm (FPlus a b) v1).
    rewrite -> (FMult_distr a b v1).
    rewrite -> (FMult_comm v1 a).
    rewrite -> (FMult_comm v1 b).
    unfold FVPlus_spec in H_FVP.
    destruct H_FVP as [_ H_FVP_cons].
    rewrite <- (H_FVP_cons (FMult a v1) (FMult b v1) (FVMult a v') (FVMult b v')).
    rewrite <- (H_FVM_cons v1 v' a).
    rewrite <- (H_FVM_cons v1 v' b).
    reflexivity.
Qed.

Lemma field_multiplication_is_associative_with_respect_to_vector_multiplication :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->      
    forall FVMult : F -> FVector F -> FVector F,
      FVMult_spec F FMult FVMult ->
      forall v : FVector F,
      forall a b : F,
        FVMult a (FVMult b v) =
        FVMult (FMult a b) v. 
Proof.
  intros F FPlus FMult H_FS FVMult H_FVM v.
  induction v as [ | v1 v' IHv'].
    intros a b.
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [H_FVM_nil _].
    rewrite ->3 H_FVM_nil.
    reflexivity.

    intros a b.
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [_ H_FVM_cons].
    rewrite -> (H_FVM_cons v1 v' b).
    rewrite -> (H_FVM_cons (FMult b v1) (FVMult b v') a).
    rewrite -> (IHv' a b).
    unfold field_spec in H_FS.
    destruct H_FS as [_ [_ [_ [_ [_ [FMult_assoc _]]]]]].
    rewrite <- (FMult_assoc a b v1).
    rewrite -> (H_FVM_cons v1 v' (FMult a b)).
    reflexivity.
Qed.

Lemma One_is_neutral_for_vector_multiplication :
  forall (F : Type)
         (FPlus : F -> F -> F)
         (FMult : F -> F -> F),
    field_spec F FPlus FMult ->      
    forall FVMult : F -> FVector F -> FVector F,
      FVMult_spec F FMult FVMult ->
      forall E : F,
        One F FPlus FMult E ->
        forall v : FVector F,
          FVMult E v = v.
Proof.
  intros F FPlus FMult H_FS FVMult H_FVM E H_E v.
  induction v as [ | v1 v' IHv'].
    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [H_FVM_nil _].
    exact (H_FVM_nil E).

    unfold FVMult_spec in H_FVM.
    destruct H_FVM as [_ H_FVM_cons].
    rewrite -> (H_FVM_cons v1 v' E).
    rewrite -> IHv'.
    unfold One in H_E.
    destruct H_E as [_ H_E_Neu].
    rewrite -> (H_E_Neu v1).
    reflexivity.
Qed.
