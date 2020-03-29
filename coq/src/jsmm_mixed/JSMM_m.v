(******************************************************************************)
(** * Definition of the JSMM memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
From imm Require Import Events.
Require Import Execution_m.
(*Require Import Execution_eco.*)

Set Implicit Arguments.
Remove Hints plus_n_O.

Section JSMM_m.

Variable G : execution_m.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'range_value'" := G.(range_value).
Notation "'rf_on'" := G.(rf_on).
Notation "'overlap_on'" := G.(overlap_on).
Notation "'no_overlap'" := G.(no_overlap).
Notation "'rfb'" := G.(rfb).
Notation "'cob'" := G.(cob).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
(* Notation "'fr'" := G.(fr). *)
(* Notation "'eco'" := G.(eco). *)
Notation "'same_range'" := G.(same_range).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Definition sw := ⦗ Sc ⦘ ⨾ (rf ∩ same_range) ⨾ ⦗ Sc ⦘.
Definition hb := (sb ∪ sw)⁺.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition jsmm_m_consistent (tot : relation actid) (tearfree : actid -> Prop) :=
  ⟪ Ctot   : strict_total_order E tot ⟫ /\
  ⟪ Chbtot : hb ⊆ tot ⟫ /\
  ⟪ Chbrf : irreflexive (hb ⨾ rf) ⟫ /\
  ⟪ Chbrfhb : forall n,
      irreflexive (hb ⨾ (rf_on n)⁻¹ ⨾ (hb ∩ overlap_on n) ⨾ ⦗ W ⦘) ⟫ /\
  ⟪ Cirr1 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ tot ⨾ sw⁻¹ ⨾ (tot ∩ same_range)) ⟫ /\
  ⟪ Cirr2 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ hb ⨾
                   (hb ∩ rf)⁻¹ ⨾ ⦗W∩₁Sc⦘ ⨾ (tot ∩ same_range)) ⟫ /\
  ⟪ Cirr3 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ (tot ∩ same_range) ⨾ ⦗R∩₁Sc⦘ ⨾
                   (hb ∩ rf)⁻¹ ⨾ hb) ⟫ /\
  ⟪ Ctf :
      functional (⦗tearfree⦘ ⨾ (rf⁻¹ ∩ same_range) ⨾ ⦗tearfree⦘) ⟫.

Lemma sw_E x y :
  Wf_m G -> sw x y -> (E x /\ E y).
Proof.
  intros WF H.
  unfold sw in H.
  destruct H as [x_ [[H11 H12] [y_ [[H21 H22] [H31 H32]]]]].
  rewrite <- H11 in H21,H22.
  rewrite H31 in H21, H22, H32.
  pose (wf_rfE WF) as Hp.
  apply Hp in H21.
  destruct H21 as [x__ [H21_ [y__ [H221_ H222_]]]].
  destruct H21_.
  destruct H222_.
  rewrite H1 in H2.
  split; assumption.
Qed.

Lemma hb_E x y :
  Wf_m G -> hb x y -> (E x /\ E y).
Proof.
  intros WF H.
  unfold hb in H.
  split.
  - eapply ct_doma.
    + assert (doma (sb ∪ sw) E) as Ha. {
        unfold doma. intros a b Ha. destruct Ha as [Ha | Ha].
        - apply sb_E in Ha. apply Ha.
        - apply sw_E in Ha. apply Ha. apply WF.
      }
      apply Ha.
    + apply H.
  - eapply ct_domb.
    + assert (domb (sb ∪ sw) E) as Ha. {
        unfold domb. intros a b Ha. destruct Ha as [Ha | Ha].
        - apply sb_E in Ha. apply Ha.
        - apply sw_E in Ha. apply Ha. apply WF.
      }
      apply Ha.
    + apply H.
Qed.

(******************************************************************************)
(** ** SC-DRF  *)
(******************************************************************************)

Definition data_race_free :=
  forall x y,
    hb x y \/ hb y x \/
    (~(W x) /\ ~(W y)) \/
    no_overlap x y \/
   (same_range x y /\ Sc x /\ Sc y).

Definition seqcst tot :=
  irreflexive (rf ⨾ tot) /\
  (forall n, 
     irreflexive (⦗W⦘ ⨾ (tot ∩ overlap_on n) ⨾ (rf_on n)⁻¹ ⨾ tot)).

Lemma hb_tot_inconsist tot x y :
  strict_total_order E tot ->
  hb ⊆ tot->
  tot x y ->
  hb y x ->
  False.
Proof.
  intros H1 H2 H3 H4.
  destruct H1 as [[H111 H112] H12].
  apply H111 with x.
  pose (H2 _ _ H4) as H.
  apply (H112 x y x H3 H).
Qed.

Lemma spo_hb tot :
  strict_total_order E tot ->
  hb ⊆ tot->
  strict_partial_order hb.
Proof.
  intros H1 H2.
  split.
  - unfold strict_total_order in H1.
    apply irreflexive_inclusion with tot.
    + assumption.
    + apply H1.
  - unfold hb. intuition.
Qed.

Lemma rf_sw x y :
  rf x y ->
  same_range x y ->
  Sc x ->
  Sc y ->
  sw x y.
Proof.
  unfold sw.
  exists x.
  split. { intuition. }
  unfold inter_rel.
  exists y.
  intuition.
Qed.

Lemma sw_hb x y :
  sw x y ->
  hb x y.
Proof.
  unfold hb.
  intuition.
Qed.

Lemma sw_sc :
  Wf_m G ->
  sw = ⦗W∩₁Sc⦘ ⨾ sw ⨾ ⦗R∩₁Sc⦘.
Proof.
  intros Hwf.
  apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  intros y.
  apply PropExtensionality.propositional_extensionality.
  split.
  - intros H.
    unfold sw.
    unfold sw in H.
    destruct H as [x_ [H1 [y_ [H21 H22]]]].
    destruct H1 as [H11 H12].
    rewrite <- H11 in H21.
    destruct H22 as [H221 H222].
    rewrite H221 in H21, H222.
    assert (W x /\ R y) as Wx_Ry. { apply rf_w_r. apply Hwf. apply H21. }
    econstructor.
    split. { econstructor. reflexivity. econstructor. apply Wx_Ry. apply H12. }
    econstructor.
    split. {
      econstructor.
      split. { econstructor. reflexivity. assumption. }
      econstructor.
      split. { apply H21. }
      econstructor. reflexivity. assumption.
    }
    econstructor. { reflexivity. }
    econstructor; easy.
  - intros H.
    unfold sw.
    unfold sw in H.
    destruct H as [x_ [H1 [y_ [[x__ [H21 [y__ [H221 H222]]]] H3]]]].
    destruct H1 as [H1a H1b].
    rewrite <- H1a in H21.
    destruct H21 as [H21a H21b].
    rewrite <- H21a in H221.
    destruct H3 as [H3a H3b].
    rewrite H3a in H3b, H222.
    destruct H222 as [H222a H222b].
    rewrite H222a in H222b, H221.
    econstructor.
    split. { econstructor. reflexivity. assumption. }
    econstructor.
    split. { apply H221. }
    econstructor. { reflexivity. }
    assumption.
Qed.

Lemma sw_sc_inv :
  Wf_m G ->
  sw⁻¹ = ⦗R∩₁Sc⦘ ⨾ sw⁻¹ ⨾ ⦗W∩₁Sc⦘.
Proof.
  intros Hwf.
  apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  intros y.
  apply PropExtensionality.propositional_extensionality.
  split.
  - intros H.
    rewrite sw_sc in H.
    apply transp_seq in H.
    rewrite (rel_extensionality ((transp_seq sw (⦗R ∩₁ Sc⦘)))) in H.
    apply seqA in H.
    rewrite (rel_extensionality (transp_eqv_rel (R ∩₁ Sc))) in H.
    rewrite (rel_extensionality (transp_eqv_rel (W ∩₁ Sc))) in H.
    assumption.
    apply Hwf.
  - intros H.
    rewrite sw_sc.
    apply transp_seq.
    rewrite (rel_extensionality ((transp_seq sw (⦗R ∩₁ Sc⦘)))).
    apply seqA in H.
    rewrite (rel_extensionality (transp_eqv_rel (R ∩₁ Sc))).
    rewrite (rel_extensionality (transp_eqv_rel (W ∩₁ Sc))).
    assumption.
    apply Hwf.
Qed.

Lemma sw_rf_Cirr1_left x y :
  Wf_m G ->
  (sw⁻¹) x y -> (⦗R∩₁Sc⦘ ⨾ (rf ∩ same_range)⁻¹ ⨾ ⦗W∩₁Sc⦘) x y.
Proof.
  intros Hwf H.
  rewrite sw_sc_inv in H.
  unfold sw in H.
  destruct H as [x_ [H1 H2]].
  destruct H1 as [x_is H11].
  rewrite <- x_is in H2.
  econstructor.
  split. { econstructor. reflexivity. assumption. }
  destruct H2 as [y_ [[y__ [[H21211 H21212] [x__ [H212221 [H2122221 H2122222]]]]] [H221 H222]]].
  econstructor.
  split. { econstructor; rewrite <- H2122221; apply H212221. }
  econstructor. { rewrite <- H21211. rewrite H221. reflexivity. }
  rewrite <- H21211. apply H222.
  apply Hwf.
Qed.

Lemma sw_rf_Cirr1_right x y :
  Wf_m G ->
  (⦗R∩₁Sc⦘ ⨾ (rf ∩ same_range)⁻¹ ⨾ ⦗W∩₁Sc⦘) x y -> (sw⁻¹) x y.
Proof.
  intros Hwf H.
  rewrite sw_sc_inv.
  unfold sw.
  destruct H as [x_ [H1 H2]].
  destruct H1 as [x_is H11].
  rewrite <- x_is in H2.
  econstructor.
  split. { econstructor. reflexivity. assumption. }
  destruct H2 as [y_ [H21 [H221 H222]]].
  rewrite H221 in H222, H21.
  econstructor.
  split. {
    econstructor.
    split. { econstructor. apply H221. rewrite H221. apply H222. }
    econstructor.
    split. { apply H21. }
    econstructor. reflexivity. apply H11.
  }
  rewrite H221.
  econstructor. reflexivity. apply H222.
  apply Hwf.
Qed.

Lemma sw_rf_Cirr1 :
  Wf_m G ->
  (sw⁻¹) = (⦗R∩₁Sc⦘ ⨾ (rf ∩ same_range)⁻¹ ⨾ ⦗W∩₁Sc⦘).
Proof.
  intros Hwf.
  apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  intros y.
  apply PropExtensionality.propositional_extensionality.
  split.
  apply sw_rf_Cirr1_left.
  apply Hwf.
  apply sw_rf_Cirr1_right.
  apply Hwf.
Qed.

Lemma Cirr1_alt tot :
  Wf_m G ->
  irreflexive (⦗W∩₁Sc⦘ ⨾ tot ⨾ sw⁻¹ ⨾ (tot ∩ same_range)) = irreflexive (⦗W∩₁Sc⦘ ⨾ tot ⨾ ⦗R∩₁Sc⦘ ⨾ (rf ∩ same_range)⁻¹ ⨾ ⦗W∩₁Sc⦘ ⨾ (tot ∩ same_range)).
Proof.
  intros Hwf.
  rewrite sw_rf_Cirr1.
  repeat rewrite (rel_extensionality (seqA _ _ _)).
  reflexivity.
  apply Hwf.
Qed.

Lemma drf_tot__hb_sc x y tot :
  data_race_free ->
  strict_total_order E tot ->
  hb ⊆ tot ->
  tot x y ->
  is_overlap G x y ->
  W x \/ W y ->
  hb x y \/ (same_range x y /\ Sc x /\ Sc y).
Proof.
  intros DRF tot_wf hb_in_tot H1 H2 H3.
  unfold data_race_free in DRF.
  destruct DRF with x y as [hbXY | [hbYX | [[nWX nWY] | [novrlpXY | [slXY [scX scY]]]]]]; auto.
  - exfalso.
    assert (tot y x). { apply hb_in_tot. apply hbYX. }
    unfold strict_total_order in tot_wf.
    destruct tot_wf as [[tot_wf11 tot_wf12] tot_wf2].
    apply tot_wf11 with x.
    unfold transitive in tot_wf12.
    apply (tot_wf12 x y x H1 H).
  - exfalso.
    destruct H3; contradiction.
  - exfalso.
    destruct H2.
    apply novrlpXY.
Qed.

End JSMM_m.
