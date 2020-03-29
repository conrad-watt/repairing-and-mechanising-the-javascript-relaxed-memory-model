(******************************************************************************)
(** * Definition of the JSMM memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Arith.
Require Import List.
Require Import Bool.
From imm Require Import Events Execution JSMM.
Require Import Execution_m.
Require Import JSMM_m.

Set Implicit Arguments.

Section JSMM_m_deadness.

Variable G : execution_m.

Variable tfree : (actid -> Prop).

Hypothesis WF_m : Wf_m G.

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
Notation "'fr'" := G.(fr).
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

Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).

Definition jsmm_m_consistent_wrong tot :=
  ⟪ Ctot   : strict_total_order E tot ⟫ /\
  ⟪ Chbtot : hb ⊆ tot ⟫ /\
  ⟪ Chbrf : irreflexive (hb ⨾ rf) ⟫ /\
  ⟪ Chbrfhb : forall n,
      irreflexive (hb ⨾ (rf_on n)⁻¹ ⨾ (hb ∩ overlap_on n) ⨾ ⦗ W ⦘) ⟫ /\
  ⟪ Cirr :
      irreflexive (⦗W⦘ ⨾ tot ⨾ sw⁻¹ ⨾ (tot ∩ same_range)) ⟫ /\
  ⟪ Ctf :
      functional (⦗tfree⦘ ⨾ (rf⁻¹ ∩ same_range) ⨾ ⦗tfree⦘) ⟫.

Record syn_dead_wrt Gtot Htot := {
  deadwrt_WRsc :
    ⦗W⦘ ⨾ Gtot ⨾ ⦗R∩₁Sc⦘ ⊆ Htot;
  deadwrt_WscW :
    ⦗W ∩₁Sc⦘ ⨾ Gtot ⨾ ⦗W⦘ ⊆ Htot;
}.

Record syn_dead Gtot := {
  deadg_hb_tot : hb ⊆ Gtot;
  deadg_tot' : forall Htot, jsmm_m_consistent_wrong Htot -> syn_dead_wrt Gtot Htot;
}.

Lemma syn_deadness_cst Gtot Htot :
  hb ⊆ Gtot ->
    strict_total_order E Gtot ->
      strict_total_order E Htot ->
        syn_dead_wrt Gtot Htot ->
          jsmm_m_consistent_wrong Htot ->
            jsmm_m_consistent_wrong Gtot.
Proof.
  intros Ha Hb Hc [Hd1 Hd2] He.
  econstructor. { assumption. }
  econstructor. { assumption. }
  econstructor. { apply He. }
  econstructor. { apply He. }
  econstructor. {
    unfold irreflexive.
    intros x H.
    destruct H as [x_ [H1 [y [H2 [z [H3 [H4 H5]]]]]]].
    destruct H1 as [H11 H12].
    rewrite <- H11 in H2.
    destruct He as [Ctot [Chbtot [Chbrf [Chbrfhb [Cirr Ctf]]]]].
    unfold irreflexive in Cirr.
    destruct Cirr with x.
    constructor 1 with x.
    split. { constructor. reflexivity. assumption. }
    constructor 1 with y.
    split. {
      apply Hd1.
      constructor 1 with x.
      split. { constructor. reflexivity. assumption. }
      constructor 1 with y.
      split. { assumption. }
      constructor. { reflexivity. }
      destruct H3 as [z_ [[H311 H312] [y_ [H32 [H33 H34]]]]].
      rewrite H33 in H32, H34.
      rewrite <- H311 in H32.
      constructor. {
      eapply rf_w_r.
      - assumption.
      - apply H32.
      }
      assumption.
    }
    constructor 1 with z.
    split. { assumption. }
    constructor. {
      apply Hd2.
      constructor 1 with z.
      destruct H3 as [z_ [[H311 H312] [y_ [H32 [H33 H34]]]]].
      rewrite H33 in H32, H34.
      rewrite <- H311 in H32.
      split. {
        constructor. { reflexivity. }
        constructor. { eapply rf_w_r. assumption. apply H32. }
        assumption.
      }
      constructor 1 with x.
      split. { assumption. }
      constructor. reflexivity. assumption.
    }
    assumption.
  }
  apply He.
Qed.

Lemma syn_deadness_sc Gtot Htot :
  hb ⊆ Gtot ->
    hb ⊆ Htot ->
      strict_total_order E Gtot ->
        strict_total_order E Htot ->
          data_race_free G ->
            syn_dead_wrt Gtot Htot ->
              seqcst G Htot ->
                seqcst G Gtot.
Proof.
  intros Ha Hb Hc Hd He [Hf1 Hf2] Hg.
  unfold seqcst.
  split.
  - unfold irreflexive.
    intros x H.
    destruct H as [y [H1 H2]].
    destruct (drf_tot__hb_sc He Hc Ha H2).
    + apply is_overlap_sym. apply rf_overlap. apply WF_m. apply H1.
    + right. eapply rf_w_r. apply WF_m. apply H1.
    + destruct Hg as [Hg1 Hg2]. apply Hg1 with x.
      constructor 1 with y.
      split. { assumption. }
      apply Hb. apply H.
    + destruct Hc as [[Hc11 Hc12] Hc2].
      apply Hc11 with x.
      apply Hc12 with y. {
        apply Ha.
        constructor. right.
        apply rf_sw.
        - apply H1.
        - apply same_range_sym. apply H.
        - apply H.
        - apply H.
      }
      apply H2.
  - intros n z H.
    destruct H as [z_ [[H11 H12] [x [[H21 H22] [y [H3 H4]]]]]].
    rewrite <- H11 in H21, H22.
    unfold transp in H3.
    assert (Htot z x) as Htot1. {
      destruct (drf_tot__hb_sc He Hc Ha H21) as [Hl | Hr].
      - eapply overlap_on_is_overlap. apply H22.
      - left. apply H12.
      - apply Hb. apply Hl.
      - apply Hf1.
        econstructor.
        split. { econstructor. reflexivity. apply H12. }
        econstructor.
        split. { apply H21. }
        econstructor. { reflexivity. }
        econstructor.
        + eapply rf_w_r. apply WF_m. eapply rf_on_rf. apply H3.
        + apply Hr.
    }
    assert (Htot y z) as Htot2. {
      destruct (drf_tot__hb_sc He Hc Ha H4) as [Hl | Hr].
      - eapply overlap_on_is_overlap. apply overlap_on_trans with x.
        apply rf_on_overlap_on. apply WF_m. apply H3. apply overlap_on_sym. apply H22.
      - left. eapply rf_w_r. apply WF_m. eapply rf_on_rf. apply H3.
      - apply Hb. apply Hl.
      - apply Hf2.
        econstructor.
        split. { econstructor. reflexivity. econstructor. eapply rf_w_r.
                 apply WF_m. eapply rf_on_rf. apply H3. apply Hr. }
        econstructor.
        split. { apply H4. }
        econstructor. { reflexivity. }
        assumption.
    }
    destruct Hg as [Hg1 Hg2].
    apply (Hg2 n z).
    econstructor.
    split. { econstructor. reflexivity. assumption. }
    econstructor.
    split. { econstructor. apply Htot1. apply H22. }
    econstructor.
    split. { apply H3. }
    apply Htot2.
Qed.

End JSMM_m_deadness.
