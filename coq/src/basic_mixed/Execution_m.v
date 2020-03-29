(******************************************************************************)
(** * Definition of mixed-size executions * **)
(******************************************************************************)

Require Import Omega.
Require Import Classical Peano_dec.
Require Import List.
Require Import Bool.
Require Import Datatypes.
From hahn Require Import Hahn.

From imm Require Import Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

(** Definition of a mixed-size execution *)
Record execution_m :=
  { acts : list actid;
    lab : actid -> label;
    range_value : actid -> list (nat*value);

    rmw : actid -> actid -> Prop ;
    data : actid -> actid -> Prop ;   (** data dependency *)
    addr : actid -> actid -> Prop ;   (** address dependency *)
    ctrl : actid -> actid -> Prop ;   (** control dependency *)

    (** Representation of a data dependency to failed RMW.
        It goes from a read to an exclusive read.
        Consider the example:

        a := [x];
        CAS(y, a, 1);
        
        There is an execution w/ failing CAS. In the execution,
        there is an rmw_dep edge between a read event representing `a := [x]'
        and a read event representing failed `CAS(y, a, 1)'.
     *)
    rmw_dep : actid -> actid -> Prop ;

(*     ctrli : relation actid ;  (** control+isync on Power *) *)

    (* note that these relations are byte-wise *)
    rfb : actid -> actid -> list nat;
    cob : actid -> actid -> list nat;
  }.

Definition list_intersect_r (l1 l2 : list nat) : list nat :=
  List.filter (fun n => List.existsb (Nat.eqb n) l2) l1.

Definition list_intersect_r_v (l1 l2 : list (nat*value)) : list (nat*value) :=
  List.filter (fun x => List.existsb (fun x' => Nat.eqb (fst x) (fst x') && Nat.eqb (snd x) (snd x')) l2) l1.

Lemma rel_extensionality (A : Type) (a : relation A) (b : relation A) :
  a ≡ b -> a = b.
Proof.
  intros H.
  apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  intros y.
  apply PropExtensionality.propositional_extensionality.
  apply same_relation_exp.
  assumption.
Qed.

Lemma rel_extensionality_inv (A : Type) (a : relation A) (b : relation A) :
  a = b -> a ≡ b.
Proof.
  intros H. rewrite H. reflexivity.
Qed.

Lemma list_intersect_rP l1 l2 n : In n (list_intersect_r l1 l2) <-> In n l1 /\ In n l2.
Proof.
unfold list_intersect_r.
rewrite filter_In, existsb_exists; split.
- intros [H1 [m [H2 e]]]; split; trivial.
  rewrite Nat.eqb_eq in e; congruence.
- intros [H1 H2]; split; trivial.
  now exists n; split; trivial; rewrite Nat.eqb_refl.
Qed.

Lemma filter_eq_nil:
  forall (A : Type) (f : A -> bool) (l : list A),
  filter f l = nil <-> (forall x : A, In x l -> f x -> False).
Proof.
  intros A f l.
  induction l.
  - intuition.
  - split.
    + intros H.
      simpl in H.
      case (f a) eqn:a_is.
      * discriminate.
      * rewrite IHl in H.
        intros x Hin f_is.
        simpl in Hin.
        destruct Hin as [Hin | Hin]. {
          rewrite Hin in a_is.
          rewrite a_is in f_is.
          intuition.
        } {
          eapply H.
          apply Hin.
          apply f_is.
        }
    + intros H.
      assert (f a = false) as Hf. {
        specialize H with a.
        case (f a) eqn:a_is.
        - intuition.
        - intuition.
      }
      simpl.
      rewrite Hf.
      rewrite IHl.
      intros x Hin f_is.
      apply H with x.
      * simpl. right. assumption.
      * assumption.
Qed.

Lemma list_intersect_r_nil_idem x y :
  list_intersect_r x y = nil ->
    list_intersect_r y x = nil.
Proof.
  unfold list_intersect_r.
  intros H.
  rewrite (PropExtensionality.propositional_extensionality _ _ (filter_eq_nil _ _)).
  rewrite (PropExtensionality.propositional_extensionality _ _ (filter_eq_nil _ _)) in H.
  intros a Hin Hex.
  specialize H with a.
  apply H.
  - apply existsb_exists in Hex.
    destruct Hex as [a_ [Hex1 Hex2]].
    apply Nat.eqb_eq in Hex2.
    rewrite Hex2.
    apply Hex1.
  - apply existsb_exists.
    exists a.
    split.
    + assumption.
    + apply Nat.eqb_eq. reflexivity.
Qed.

Lemma list_intersect_r_vP l1 l2 n : In n (list_intersect_r_v l1 l2) <-> In n l1 /\ In n l2.
Proof.
unfold list_intersect_r_v.
rewrite filter_In, existsb_exists. split.
- intros [H1 [m [H2 e]]]; split; trivial.
  rewrite andb_true_iff in e; destruct e as [e1 e2].
  rewrite Nat.eqb_eq in e1, e2.
  assert (n = m). { destruct n. destruct m. auto. }
  rewrite H. apply H2.
- intros [H1 H2]; split; trivial.
  exists n; split; trivial; rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
  auto.
Qed.

Lemma split_fst_map A B l :
  fst (split l) = (map (fun x : A * B => fst x) l).
Proof.
  induction l.
  - reflexivity.
  - destruct a as [a b].
    assert (fst (split ((a, b) :: l)) = a :: (fst (split l))). {
      simpl. destruct (split l). reflexivity.
    }
    rewrite H.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma seq_eq n m n' m' :
  (forall v, In v (List.seq n m) <-> In v (List.seq n' m')) ->
    (List.seq n m) = (List.seq n' m').
Proof.
  intros H.
  case (List.seq n m) eqn:Hnil_. {
    case (List.seq n' m') eqn:Hnil__; try reflexivity.
    specialize H with n0.
    exfalso.
    eapply in_nil.
    apply H.
    intuition.
  }
  assert (List.seq n m <> nil) as Hnil. {
    intros H_.
    rewrite H_ in Hnil_.
    discriminate.
  }
  rewrite <- Hnil_.
  rewrite <- Hnil_ in H.
  assert (m <> 0) as H0. {
    intros H0.
    rewrite H0 in Hnil.
    apply Hnil.
    reflexivity.
  }
  setoid_rewrite (PropExtensionality.propositional_extensionality _ _ (in_seq_iff _ _ _)) in H.
  assert (m' <> 0) as H0'. {
    intros H0'.
    rewrite H0' in H.
    specialize H with n.
    omega.
  }
  assert ((n+m  = n'+m')) as Hnm. {
    clear H0'.
    specialize H with (n+m) as H_.
    specialize H with (n) as H__.
    specialize H with (n'+m') as H___.
    omega.
  }
  rewrite <- Hnm in H.
  assert (n=n' /\ m=m'). {
    specialize H with (n) as H_.
    specialize H with (n') as H__.
    omega.
  }
  intuition.
Qed.

Lemma seq_succ n m a l :
  List.seq n m = a :: l ->
    exists m', List.seq (S n) (m') = l /\ m = S m' /\ a = n.
Proof.
  intros H.
  destruct m.
  - exfalso.
    discriminate.
  - simpl in H.
    Transparent List.seq.
    unfold List.seq in H.
    fold List.seq in H.
    Opaque List.seq.
    inversion H as [].
    exists m.
    intuition.
Qed.

Lemma NoDup_in_cons A a a' (l : list A) :
  NoDup (a :: l) ->
  In a' l ->
  a <> a'.
Proof.
  intros H1 H2.
  apply nodup_cons in H1.
  intros H.
  apply H1.
  rewrite <- H in H2.
  apply H2.
Qed.

Lemma combine_eq_seq A x y l (r1 : list A) r2 n m :
  x = combine l r1 ->
    y = combine l r2 ->
      l = List.seq n m ->
        (forall a, In a l -> exists b, In (a,b) x /\ In (a,b) y) ->
          x = y.
Proof.
  generalize x y r1 r2 n m.
  induction l.
  - unfold combine.
    intros a b c d e f g h.
    rewrite g. rewrite h.
    reflexivity.
  - clear x y r1 r2 n m.
    intros x y r1 r2 n m Hx Hy Hl Hfa.
    destruct r1 as [| r1 r1s]; destruct r2 as [| r2 r2s].
    + unfold combine in Hx, Hy.
      rewrite Hx in Hfa.
      rewrite Hy in Hfa.
      specialize Hfa with a.
      simpl in Hfa.
      destruct Hfa.
      * left. reflexivity.
      * exfalso. intuition.
    + unfold combine in Hx.
      rewrite Hx in Hfa.
      specialize Hfa with a.
      simpl in Hfa.
      destruct Hfa.
      * left. reflexivity.
      * exfalso. intuition.
    + unfold combine in Hy.
      rewrite Hy in Hfa.
      specialize Hfa with a.
      simpl in Hfa.
      destruct Hfa.
      * left. reflexivity.
      * exfalso. intuition.
    + simpl in Hx, Hy.
      assert (exists m' : nat, List.seq (S n) m' = l /\ m = S m' /\ a = n) as He. {
        apply seq_succ.
        - rewrite Hl. reflexivity.
      }
      destruct He as [m' [He1 [He2 He3]]].
      specialize IHl with (combine l r1s) (combine l r2s) r1s r2s (S n) (m').
      assert (combine l r1s = combine l r2s). {
        apply IHl; try reflexivity.
        - rewrite He1. reflexivity.
        - intros a' He_.
          specialize Hfa with a'.
          rewrite Hx in Hfa.
          rewrite Hy in Hfa.
          assert (a <> a') as Haa'. {
            eapply NoDup_in_cons.
            - rewrite Hl.
              apply nodup_seq.
            - assumption.
          }
          assert (In a' (a :: l)) as He__. {
            simpl. right. apply He_.
          }
          destruct Hfa as [b [Hfa1 Hfa2]]. { assumption. }
          simpl in Hfa1, Hfa2.
          destruct Hfa1 as [ Hfa1 | Hfa1 ].
          + exfalso. inversion Hfa1. auto.
          + destruct Hfa2 as [ Hfa2 | Hfa2 ].
            * exfalso. inversion Hfa2. auto.
            * exists b. auto.
      }
      specialize Hfa with a.
      assert (NoDup (a :: l)) as Hnd. {
        rewrite Hl. apply nodup_seq.
      }
      assert (~In a l) as Hnd_in. {
        apply nodup_cons. apply Hnd.
      }
      destruct Hfa as [b [Hfa1 Hfa2]]. { intuition. }
      rewrite H in Hx.
      rewrite Hx in Hfa1.
      rewrite Hy in Hfa2.
      destruct Hfa1 as [ Hfa1 | Hfa1 ].
      * destruct Hfa2 as [ Hfa2 | Hfa2 ]. {
          rewrite Hfa1 in Hx.
          rewrite Hfa2 in Hy.
          rewrite Hx. rewrite Hy. reflexivity.
        } {
          apply in_combine_l in Hfa2. intuition.
        }
      * apply in_combine_l in Hfa1. intuition.
Qed.

Section Execution_m.

Variable G : execution_m.

Definition acts_set := fun x => In x G.(acts).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'E'" := acts_set.
Notation "'lab'" := G.(lab).
Notation "'range_value'" := G.(range_value).
Notation "'rfb'" := G.(rfb).
Notation "'cob'" := G.(cob).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Definition range :=
  (fun x => fst (split (range_value x))).

Definition value :=
  (fun x => snd (split (range_value x))).

Definition same_range :=
  (fun x y => range x = range y).

Definition overlap :=
  (fun x y => list_intersect_r (range x) (range y)).

Definition overlap_on n :=
  (fun x y => In n (overlap x y)).

Definition is_overlap :=
  (fun x y => nil <> overlap x y).

Definition no_overlap :=
  (fun x y => nil = overlap x y).

Definition wf_values :=
  (fun x y => (list_intersect_r_v (range_value x) (range_value y))).

Definition is_wf_values :=
  (fun x y => incl (rfb x y) (fst (split (wf_values x y)))).

Definition sb := ⦗E⦘ ⨾ ext_sb ⨾  ⦗E⦘.

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* reads-before, aka from-read *)
Definition rf x y := nil <> rfb x y.

(* reads-before, aka from-read *)
Definition rf_on n x y := In n (rfb x y).

(* coherence *)
Definition co := (fun x y => nil <> cob x y)⁺.

(* reads-before, aka from-read *)
Definition cob_on n x y := In n (cob x y).

Definition W_ex := codom_rel rmw.

Definition deps := data ∪ addr ∪ ctrl.

Record Wf_m :=
  { wf_index : forall a b, 
    E a /\ E b /\ a <> b /\ tid a = tid b /\ ~ is_init a -> index a <> index b ;
    wf_values_all : forall a b, E a /\ E b -> is_wf_values a b ;
    rfb_R_total : forall a, (E a /\ R a) -> forall n, In n (range a) -> exists b, In n (rfb b a) ;
    wf_values_W_R_some : forall a, ((R a \/ W a)) -> nil <> range_value a ;
    wf_values_F_none : forall a, F a -> nil = range_value a ;
    range_seq : forall a, exists n m, range a = List.seq n m ;
    rfb_seq : forall a b, exists n m, rfb a b = List.seq n m ;
    data_in_sb : data ⊆ sb ;
    wf_dataD : data ≡ ⦗R⦘ ⨾ data ⨾ ⦗W⦘ ;
    addr_in_sb : addr ⊆ sb ;
    wf_addrD : addr ≡ ⦗R⦘ ⨾ addr ⨾ ⦗RW⦘ ;
    ctrl_in_sb : ctrl ⊆ sb ;
    wf_ctrlD : ctrl ≡ ⦗R⦘ ⨾ ctrl ;
    ctrl_sb : ctrl ⨾ sb ⊆ ctrl ;
    wf_rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    wf_rmwl : rmw ⊆ same_range ;
    wf_rmwi : rmw ⊆ immediate sb ;
    wf_rfE : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ;
    wf_rfD : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ;
    wf_rfl : rf ⊆ same_loc ; (*
    wf_rfv : funeq val rf ;
    wf_rff : functional rf⁻¹ ; *)
    wf_coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    wf_coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    (* wf_col : co ⊆ same_range ; *)
    co_trans : transitive co ;
    wf_cob_total : forall n, is_total (E ∩₁ W ∩₁ (fun x => In n (range x))) (cob_on n) ;
    wf_cob_loc : forall n, (cob_on n) ⊆ (overlap_on n);
    co_irr : irreflexive co ;
    wf_init : forall b l, (E b /\ loc b = Some l) -> (E (InitEvent l) /\ incl (range b) (range (InitEvent l))) ;
    wf_init_lab : forall l, lab (InitEvent l) = Astore Xpln Opln l 0 ;
    rmw_dep_in_sb : rmw_dep ⊆ sb ;
    wf_rmw_depD : rmw_dep ≡ ⦗R⦘ ⨾ rmw_dep ⨾ ⦗R_ex⦘ ;
(*     failed_rmw_fail : rmw_dep ⨾ rmw ⊆ ∅₂ ; *)
  }.
(*   ⟪  wf_rmw_deps : rmw ⊆ data ∪ addr ∪ ctrl ⟫ /\
  ⟪  wf_rmw_ctrl : rmw ⨾ sb ⊆ ctrl ⟫. *)

Implicit Type WF_m : Wf_m.


(******************************************************************************)
(** ** sb properties *)
(******************************************************************************)

Lemma sb_irr : irreflexive sb.
Proof.
unfold sb; unfolder; ins; desf.
eby eapply ext_sb_irr.
Qed.

Lemma sb_trans : transitive sb.
Proof.
unfold sb; unfolder; ins; desf; splits; auto.
eby eapply ext_sb_trans.
Qed.

Lemma sb_sb : sb ⨾ sb ⊆ sb.
Proof.
generalize sb_trans; basic_solver 21.
Qed.

Lemma sb_acyclic : acyclic sb.
Proof.
apply trans_irr_acyclic; [apply sb_irr| apply sb_trans]. 
Qed.

Lemma sb_rt_of_trans : sb＊ = sb^?.
Proof.
  apply rel_extensionality.
  apply rt_of_trans.
  apply sb_trans.
Qed.

Lemma sb_ct_of_trans : sb⁺ = sb.
Proof.
  apply rel_extensionality.
  apply ct_of_trans.
  apply sb_trans.
Qed.

(******************************************************************************)
(** ** Consistency definitions  *)
(******************************************************************************)

Definition complete := E ∩₁ R  ⊆₁ codom_rel rf.
(*Definition rmw_atomicity := rmw ∩ ((fr \ sb) ⨾ (co \ sb)) ⊆ ∅₂.*)

Lemma range_F x :
  Wf_m -> F x -> nil = range x.
Proof.
  intros H H1.
  unfold range.
  pose (wf_values_F_none H) as Hwf.
  destruct Hwf with x.
  - assumption.
  - reflexivity.
Qed.

Lemma same_range_F x y :
  Wf_m -> F x -> F y -> same_range x y.
Proof.
  intros H H1 H2.
  unfold same_range.
  rewrite <- (range_F H H1).
  rewrite <- (range_F H H2).
  reflexivity.
Qed.

Lemma range_value_split_combine x :
  range_value x = combine (range x) (value x).
Proof.
  unfold range.
  unfold value.
  destruct ((split (range_value x))) eqn:H.
  pose (split_combine (range_value x)) as Hp.
  rewrite H in Hp.
  simpl.
  rewrite Hp.
  reflexivity.
Qed.

Lemma overlap_sym x y :
  is_overlap x y -> is_overlap y x.
Proof.
  unfold is_overlap.
  unfold overlap.
  intros H H1.
  apply H.
  apply eq_sym.
  apply list_intersect_r_nil_idem.
  apply eq_sym.
  apply H1.
Qed.

Lemma sb_E x y :
  sb x y -> (E x /\ E y).
Proof.
  intros H.
  unfold sb in H.
  destruct H as [x_ [[H11 H12] [y_ [H2 [H31 H32]]]]].
  rewrite H31 in H32.
  split; assumption.
Qed.

Lemma rf_E x y :
  Wf_m -> rf x y -> (E x /\ E y).
Proof.
  intros H1 H2.
  pose (wf_rfE H1) as Hp.
  apply Hp in H2.
  destruct H2 as [x_ [H21 [y_ [H221 H222]]]].
  destruct H21.
  destruct H222.
  rewrite H2 in H3.
  split; assumption.
Qed.

Lemma rf_w_r x y :
  Wf_m -> rf x y -> (W x /\ R y).
Proof.
  intros H1 H2.
  pose (wf_rfD H1) as Hp.
  apply Hp in H2.
  destruct H2 as [x_ [H21 [y_ [H221 H222]]]].
  destruct H21.
  destruct H222.
  rewrite H2 in H3.
  split; assumption.
Qed.

Lemma rf_on_rf n x y :
  rf_on n x y -> rf x y.
Proof.
  intros H.
  unfold rf_on in H.
  unfold rf.
  case (rfb x y) eqn:Hc.
  - auto.
  - discriminate.
Qed.

Lemma rf_rf_on x y :
  rf x y -> exists n, rf_on n x y.
Proof.
  intros H.
  unfold rf in H.
  unfold rf_on.
  case (rfb x y) eqn:Hc.
  - easy.
  - exists n. intuition.
Qed.

Lemma rf_on_overlap_on n x y :
  Wf_m -> rf_on n x y -> overlap_on n x y.
Proof.
  intros H1 H2.
  unfold rf_on in H2.
  unfold overlap_on.
  unfold overlap.
  apply list_intersect_rP.
  assert (is_wf_values x y) as He. {
    apply wf_values_all.
    apply H1.
    apply rf_E.
    apply H1.
    eapply rf_on_rf.
    apply H2.
  }
  apply He in H2.
  rewrite split_fst_map in H2.
  apply Basic.in_prod_inv in H2.
  destruct H2 as [b H2].
  unfold wf_values in H2.
  apply list_intersect_r_vP in H2.
  repeat rewrite range_value_split_combine in H2.
  destruct H2 as [H21 H22].
  apply in_combine_l in H21.
  apply in_combine_l in H22.
  auto.
Qed.

Lemma overlap_on_is_overlap n x y :
  overlap_on n x y -> is_overlap x y.
Proof.
  intros H.
  unfold overlap_on in H.
  unfold is_overlap.
  case (overlap x y) eqn:Hc.
  - intuition.
  - discriminate.
Qed.

Lemma rf_overlap x y :
  Wf_m -> rf x y -> is_overlap x y.
Proof.
  intros H1 H2.
  unfold rf in H2.
  assert (exists b, In b (rfb x y)) as Ha. {
    case ((rfb x y)) eqn:H.
    - exfalso. intuition.
    - exists n. intuition.
  }
  destruct Ha as [b Ha].
  apply overlap_on_is_overlap with b.
  apply rf_on_overlap_on.
  apply H1.
  unfold rf_on.
  assumption.
Qed.

Lemma rf_overlap_set :
  Wf_m -> rf ⊆ is_overlap.
Proof.
  unfold inclusion.
  intros H1 x y H2.
  apply rf_overlap; assumption.
Qed.

Lemma overlap_on_sym n x y :
  overlap_on n x y -> overlap_on n y x.
Proof.
  unfold overlap_on.
  unfold overlap.
  intros H.
  apply list_intersect_rP.
  apply list_intersect_rP in H.
  intuition.
Qed.

Lemma overlap_on_trans n x y z :
  overlap_on n x y -> overlap_on n y z -> overlap_on n x z.
Proof.
  unfold overlap_on.
  unfold overlap.
  intros H1 H2.
  apply list_intersect_rP.
  apply list_intersect_rP in H1.
  apply list_intersect_rP in H2.
  intuition.
Qed.

Lemma same_range_overlap_on n x y z :
  overlap_on n x y -> same_range x z -> overlap_on n x z.
Proof.
  unfold overlap_on.
  unfold overlap.
  unfold same_range.
  intros H1 H2.
  apply list_intersect_rP.
  apply list_intersect_rP in H1.
  rewrite <- H2.
  intuition.
Qed.

Lemma is_overlap_sym x y :
  is_overlap x y -> is_overlap y x.
Proof.
  unfold is_overlap.
  unfold overlap.
  intros H H1.
  apply H.
  apply eq_sym.
  apply list_intersect_r_nil_idem.
  apply eq_sym.
  apply H1.
Qed.

Lemma same_range_sym x y :
  same_range x y -> same_range y x.
Proof.
  unfold same_range. intuition.
Qed.

Lemma same_range_trans x y z :
  same_range x y -> same_range y z -> same_range x z.
  unfold same_range.
  intros H1 H2.
  rewrite H1.
  apply H2.
Qed.

Lemma is_overlap_F_left x y :
  Wf_m -> (F x) -> (W y \/ R y) -> is_overlap x y -> False.
Proof.
  intros H1 H2 H3 H4.
  unfold is_overlap in H4.
  unfold overlap in H4.
  pose (wf_values_F_none H1 H2) as H.
  unfold range in H4.
  rewrite <- H in H4.
  simpl in H4.
  apply H4.
  reflexivity.
Qed.

Lemma is_overlap_F_right x y :
  Wf_m -> (W x \/ R x) -> (F y) -> is_overlap x y -> False.
Proof.
  intros H1 H2 H3 H4.
  apply is_overlap_sym in H4.
  apply (is_overlap_F_left H1 H3 H2 H4).
Qed.

Lemma rf_wf_values_in_x x y : 
  Wf_m -> rf x y -> incl (wf_values x y) (range_value x).
Proof.
  intros H1 H2.
  unfold incl.
  intros [a b].
  intros H3.
  unfold wf_values in H3.
  apply list_intersect_r_vP in H3.
  easy.
Qed.

Lemma rf_wf_values_in_y x y : 
  Wf_m -> rf x y -> incl (wf_values x y) (range_value y).
Proof.
  intros H1 H2.
  unfold incl.
  intros [a b].
  intros H3.
  unfold wf_values in H3.
  apply list_intersect_r_vP in H3.
  easy.
Qed.

Lemma rfb_wf_values_in n x y :
  Wf_m -> In n (rfb x y) ->
    (exists v, In (n,v) (range_value x) /\ In (n,v) (range_value y)).
Proof.
  intros H1 H2.
  assert (rf x y) as Hrf. {
    unfold rf.
    intros H.
    rewrite <- H in H2.
    eapply in_nil.
    apply H2.
  }
  pose (wf_values_all H1 _ _ (rf_E H1 Hrf)) as Hwf.
  unfold is_wf_values in Hwf.
  unfold incl in Hwf.
  specialize Hwf with n.
  apply Hwf in H2 as H2_.
  unfold wf_values in H2_.
  rewrite split_fst_map in H2_.
  apply Basic.in_prod_inv in H2_.
  destruct H2_ as [b H2_].
  apply list_intersect_r_vP in H2_.
  exists b.
  assumption.
Qed.


Lemma cob_on_co n x y :
  cob_on n x y -> co x y.
Proof.
  intros H.
  unfold cob_on in H.
  unfold co.
  econstructor 1.
  case (cob x y) eqn:Hc.
  - auto.
  - discriminate.
Qed.

Lemma ri_dom_m r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r ∩ sb ⊆ ⦗d1⦘ ⨾ r ∩ sb ⨾ ⦗d2⦘.
Proof. rewrite DOM at 1; basic_solver. Qed.
Lemma re_dom_m r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r \ sb ⊆ ⦗d1⦘ ⨾ (r \ sb) ⨾ ⦗d2⦘.
Proof. rewrite DOM at 1; basic_solver. Qed.

End Execution_m.
