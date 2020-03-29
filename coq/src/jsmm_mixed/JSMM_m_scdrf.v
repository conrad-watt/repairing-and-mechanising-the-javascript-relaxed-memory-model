(******************************************************************************)
(** * Definition of the JSMM memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Arith.
Require Import List.
Require Import Bool.
From imm Require Import Events.
Require Import Execution_m.
Require Import JSMM_m.

Set Implicit Arguments.

Section JSMM_m_scdrf.

Variable G : execution_m.
Variable tot : relation actid.
Variable tearfree : actid -> Prop.
Hypothesis WF : Wf_m G.
Hypothesis CNST : jsmm_m_consistent G tot tearfree.
Hypothesis DRF : data_race_free G.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'range_value'" := G.(range_value).
Notation "'rf_on'" := G.(rf_on).
Notation "'overlap_on'" := G.(overlap_on).
Notation "'no_overlap'" := G.(no_overlap).
Notation "'is_overlap'" := G.(is_overlap).
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

Notation sw := G.(sw).
Notation hb := G.(hb).

Theorem sc_drf :
  seqcst G tot.
Proof.
  unfold seqcst.
  split.
  - intro x.
    intro H.
    destruct H as [y [Hrf Htot]].
    assert (hb y x \/ (same_range y x /\ Sc y /\ Sc x)). {
      eapply (drf_tot__hb_sc DRF).
      - apply CNST.
      - apply CNST.
      - assumption.
      - apply overlap_sym; apply (rf_overlap WF Hrf).
      - pose (rf_w_r WF Hrf). intuition.
    }
    destruct CNST as [CNST1 [CNST2 [CNST3 _]]].
    apply (CNST3 y).
    exists x.
    split; try assumption.
    destruct H.
    + assumption.
    + assert (sw x y). { unfold sw. exists x. split. { intuition. } unfold inter_rel. exists y. intuition. }
      assert (hb x y). { unfold hb. intuition. }
      exfalso. eapply (hb_tot_inconsist CNST1 CNST2 Htot H1).
  - intros n x.
    unfolder.
    intros [x_ [[H11 H12] [y [[H211 H212] [z [H221 H222]]]]]].
    destruct CNST as [CNST1 [CNST2 [CNST3 [CNST4 [CNST5 [CNST6 CNST7]]]]]].
    rewrite <- H11 in H211, H212.
    assert (tot z y). { eapply CNST1. apply H222. apply H211. }
    assert (hb z y \/ (same_range z y /\ Sc z /\ Sc y)) as Hzy. {
      eapply (drf_tot__hb_sc DRF).
      - apply CNST.
      - apply CNST.
      - apply H.
      - apply (rf_overlap WF).
        unfold Execution_m.rf_on in H221.
        unfold Execution_m.rf.
        intros is_nil.
        eapply in_nil.
        rewrite <- is_nil in H221.
        apply H221.
      - pose (rf_w_r WF (rf_on_rf _ _ _ _ H221)). left. intuition.
    }
    assert (hb z y) as Hzy_. {
      destruct Hzy as [Hzy1 | Hzy2].
      assumption.
      apply sw_hb.
      apply rf_sw.
      apply (rf_on_rf _ _ _ _ H221).
      intuition. intuition. intuition.
    }
    assert (hb x y \/ (same_range x y /\ Sc x /\ Sc y)) as Hxy. {
      apply overlap_on_is_overlap in H212.
      eapply (drf_tot__hb_sc DRF); try assumption.
      - apply CNST.
      - apply CNST.
      - assumption.
      - left. assumption.
    }
    assert (hb z x \/ (same_range z x /\ Sc z /\ Sc x)) as Hzx. {
      eapply (drf_tot__hb_sc DRF). apply CNST. apply CNST. assumption. eapply overlap_on_is_overlap.
      eapply overlap_on_trans. apply rf_on_overlap_on. apply WF. apply H221.
      apply overlap_on_sym. apply H212. right. assumption.
    }
    destruct Hxy as [hbxy | [srxy [scx scy]]].
    + destruct Hzx as [hbzx | [srzx [scz scx]]].
      * apply (CNST4 n x).
        econstructor.
        split. apply hbxy.
        econstructor.
        split. apply H221.
        econstructor.
        split. {
          econstructor.
          apply hbzx.
          eapply overlap_on_trans.
          apply (rf_on_overlap_on _ _ _ WF H221).
          apply overlap_on_sym.
          apply H212.
        }
        econstructor. reflexivity. assumption.
      * apply CNST6 with x.
        econstructor.
        split. { econstructor. reflexivity. econstructor; assumption. }
        econstructor.
        split. apply hbxy.
        econstructor.
        split. { econstructor. apply Hzy_. eapply rf_on_rf. apply H221. }
        repeat econstructor; try assumption.
        apply rf_on_rf in H221.
        apply rf_w_r in H221.
        easy. assumption.
    + destruct Hzx as [hbzx | [srzx [scz scx_]]].
      * apply CNST7 with x.
        econstructor.
        split. { repeat econstructor; assumption. }
        econstructor.
        split. { econstructor. apply H211. assumption. }
        econstructor.
        split. { econstructor. reflexivity. repeat econstructor.
                 apply rf_on_rf in H221. apply rf_w_r in H221. easy. assumption. assumption. }
        econstructor.
        split. { econstructor. apply Hzy_. eapply rf_on_rf. apply H221. }
        assumption.
      * apply CNST5 with x.
        econstructor.
        split. { repeat econstructor; assumption. }
        econstructor.
        split. { apply H211. }
        econstructor.
        split. { econstructor. split. repeat econstructor. apply scz.
                 econstructor. split. econstructor. eapply rf_on_rf. apply H221.
                 apply same_range_trans with x; assumption. econstructor. reflexivity.
                 assumption.
        }
        econstructor. easy. easy.
Qed.
End JSMM_m_scdrf.
