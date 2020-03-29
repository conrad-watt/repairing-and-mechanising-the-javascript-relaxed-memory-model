(******************************************************************************)
(** * Definition of the JSMM memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Arith List Bool.
From imm Require Import Events Execution JSMM.
Require Import Execution_m.
Require Import JSMM_m.

Set Implicit Arguments.

Section JSMM_m_JSMM.

Variable G : execution_m.
Variable tot : relation actid.
Variable tearfree : actid -> Prop.

Hypothesis WF_m : Wf_m G.
Hypothesis Uni_m_1 : is_overlap G = same_range G.
Hypothesis Uni_m_2 : functional ((rf G)⁻¹).

Definition loc_default : location := Coq.Numbers.BinNums.xH.

Definition val_default : Events.value := 0.

Definition uni_rng (a : actid) : location :=
  match hd_error (range_value G a) with
  | Some (l,v) => Loc.Loc.of_succ_nat l
  | _ => loc_default
  end.

Definition uni_val (a : actid) : Events.value :=
  match hd_error (range_value G a) with
  | Some (l,v) => v
  | _ => val_default
  end.

Hypothesis WF_E_m : forall (a : actid),
                      match (G.(lab) a) with
                      | Aload ex o l v => l = (uni_rng a) /\ v = (uni_val a)
                      | Astore s o l v => l = (uni_rng a) /\ v = (uni_val a)
                      | Afence o => True
                      end.

Notation "'G.E'" := (acts_set G).
Notation "'G.rf'" := (rf G).
Notation "'G.lab'" := (lab G).

Notation "'G.rmw'" := (Execution_m.rmw G).

Notation "'G.sb'" := (Execution_m.sb G).
Notation "'G.sw'" := (JSMM_m.sw G).
Notation "'G.hb'" := (JSMM_m.hb G).

Notation "'G.same_range'" := (same_range G).

Notation "'G.R'" := (fun a => is_true (is_r (lab G) a)).
Notation "'G.W'" := (fun a => is_true (is_w (lab G) a)).
Notation "'G.F'" := (fun a => is_true (is_f (lab G) a)).
Notation "'G.R_ex'" := (fun a => is_true (R_ex (lab G) a)).

Notation "'G.Pln'" := (fun a => is_true (is_only_pln (lab G) a)).
Notation "'G.Rlx'" := (fun a => is_true (is_rlx (lab G) a)).
Notation "'G.Rel'" := (fun a => is_true (is_rel (lab G) a)).
Notation "'G.Acq'" := (fun a => is_true (is_acq (lab G) a)).
Notation "'G.Acqrel'" := (fun a => is_true (is_acqrel (lab G) a)).
Notation "'G.Acq/Rel'" := (fun a => is_true (is_ra (lab G) a)).
Notation "'G.Sc'" := (fun a => is_true (is_sc (lab G) a)).

(*

Definition lab_m_lab : (actid -> label) :=
  (fun a => match (G.(lab) a) with
            | Aload ex o l v => Aload ex o (uni_rng a) (uni_val a)
            | Astore s o l v => Astore s o (uni_rng a) (uni_val a)
            | Afence o => Afence o
            end).
*)

Variable H_co : relation actid.

Record H_co_is_wf :=
  {
  H_wf_coE : H_co ≡ ⦗G.E⦘ ⨾ H_co ⨾ ⦗G.E⦘ ;
  H_wf_coD : H_co ≡ ⦗G.W⦘ ⨾ H_co ⨾ ⦗G.W⦘ ;
  H_wf_col : H_co ⊆ (same_loc G.lab) ;
  H_co_trans : transitive H_co ;
  H_wf_co_total : forall ol, is_total (G.E ∩₁ G.W ∩₁ (fun x => (loc G.lab) x = ol)) H_co ;
  H_co_irr : irreflexive H_co
  }.

Hypothesis H_co_wf : H_co_is_wf.

Definition H : execution :=
  {| Execution.acts := G.(acts);
     Execution.lab := G.(lab);
     Execution.rmw := G.(rmw);
     Execution.data := G.(data);
     Execution.addr := G.(addr);
     Execution.ctrl := G.(ctrl);
     Execution.rmw_dep := G.(rmw_dep);
     Execution.rf := G.(rf);
     Execution.co := H_co |}.

Notation "'H.E'" := (Execution.acts_set JSMM_m_JSMM.H).
Notation "'H.rf'" := (Execution.rf JSMM_m_JSMM.H).
Notation "'H.lab'" := (Execution.lab JSMM_m_JSMM.H).

Notation "'H.rmw'" := (Execution.rmw JSMM_m_JSMM.H).

Notation "'H.sb'" := (Execution.sb H).
Notation "'H.sw'" := (JSMM.sw JSMM_m_JSMM.H).
Notation "'H.hb'" := (JSMM.hb JSMM_m_JSMM.H).

Notation "'H.same_loc'" := (same_loc H.lab).

Notation "'H.R'" := (fun a => is_true (is_r H.lab a)).
Notation "'H.W'" := (fun a => is_true (is_w H.lab a)).
Notation "'H.F'" := (fun a => is_true (is_f H.lab a)).
Notation "'H.R_ex'" := (fun a => is_true (R_ex H.lab a)).

Notation "'H.Sc'" := (fun a => is_true (is_sc H.lab a)).

Lemma uni_rng_is_overlap x y : 
  nil <> range_value G x ->
    nil <> range_value G y ->
      uni_rng x = uni_rng y ->
        is_overlap G x y.
Proof.
  intros H1 H2 H3.
  unfold uni_rng in H3.
  unfold hd_error in H3.
  destruct (range_value G x) as [| x_x lx] eqn:is_x; destruct (range_value G y) as [| y_y ly] eqn:is_y; try easy.
  destruct x_x as [x_x1 x_x2]; destruct y_y as [y_y1 y_y2].
  apply Pnat.SuccNat2Pos.inj in H3.
  rewrite H3 in is_x, H1.
  apply overlap_on_is_overlap with y_y1.
  unfold overlap_on.
  unfold overlap.
  apply list_intersect_rP.
  unfold range.
  rewrite is_x.
  rewrite is_y.
  split.
  - apply (in_split_l ((y_y1, x_x2) :: lx) ((y_y1, x_x2))). simpl. left. reflexivity.
  - apply (in_split_l ((y_y1, y_y2) :: ly) ((y_y1, y_y2))). simpl. left. reflexivity.
Qed.

Lemma rf_m_overlap : G.rf ∩ G.same_range = G.rf.
Proof.
  apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  intros y.
  apply PropExtensionality.propositional_extensionality.
  apply same_relation_exp.
  apply inter_absorb_r.
  rewrite <- Uni_m_1.
  apply rf_overlap_set.
  apply WF_m.
Qed.

Lemma E_m_E : H.E = G.E.
Proof.
  auto.
Qed.

Lemma lab_m_lab : H.lab = G.lab.
Proof.
  auto.
Qed.

Lemma sb_m_sb : H.sb = G.sb.
Proof.
  auto.
Qed.

Lemma rmw_m_rmw : H.rmw = G.rmw.
Proof.
  auto.
Qed.

Lemma rf_m_rf : H.rf = G.rf.
Proof.
  auto.
Qed.

Lemma mod_m_mod : Events.mod H.lab = Events.mod G.lab.
Proof.
  apply functional_extensionality.
  intros x.
  unfold Events.mod.
  simpl.
  destruct (G.lab x) eqn:H; reflexivity.
Qed.

Lemma W_m_W : H.W = G.W.
Proof.
  apply functional_extensionality.
  intros x.
  unfold is_w.
  simpl.
  destruct (G.lab x) eqn:H; reflexivity.
Qed.

Lemma R_m_R : H.R = G.R.
Proof.
  apply functional_extensionality.
  intros x.
  unfold is_r.
  simpl.
  destruct (G.lab x) eqn:H; reflexivity.
Qed.

Lemma Sc_m_Sc : H.Sc = G.Sc.
Proof.
  apply functional_extensionality.
  intros x.
  unfold is_sc.
  rewrite mod_m_mod.
  destruct (Events.mod G.lab x) eqn:H; reflexivity.
Qed.

Lemma R_ex_m_R_ex : H.R_ex = G.R_ex.
Proof.
  apply functional_extensionality.
  intros x.
  unfold R_ex.
  simpl.
  destruct (G.lab x); reflexivity.
Qed.

Lemma sw_m_sw : H.sw = G.sw.
Proof.
  unfold JSMM.sw.
  unfold JSMM_m.sw.
  repeat rewrite Sc_m_Sc.
  rewrite rf_m_rf.
  rewrite rf_m_overlap.
  reflexivity.
Qed.

Lemma hb_m_hb : H.hb = G.hb.
Proof.
  unfold JSMM.hb.
  unfold JSMM_m.hb.
  rewrite sb_m_sb.
  rewrite sw_m_sw.
  reflexivity.
Qed.

Lemma same_range_uni_rng x y:
  G.same_range x y -> uni_rng x = uni_rng y.
Proof.
  intros H.
  unfold uni_rng.
  unfold same_range in H.
  unfold range in H.
  destruct (range_value G x) eqn:r_v.
  - simpl in H.
    unfold hd_error.
    assert (range_value G y = nil) as H1. {
      apply -> length_zero_iff_nil.
      rewrite <- split_length_l.
      rewrite <- H.
      apply length_nil.
    }
    rewrite H1.
    reflexivity.
  - simpl.
    destruct p as [n v].
    destruct (range_value G y) eqn:r_v2.
    + assert ((length ((n, v) :: l)) = 0) as F. {
      rewrite <- split_length_l.
      apply <- length_zero_iff_nil.
      auto.
      }
      exfalso.
      simpl in F.
      discriminate.
    + destruct p as [n0 v0].
      assert (n = n0). {
        simpl in H.
        unfold fst.
        destruct (split l).
        destruct (split l0).
        simpl in H.
        injection H.
        easy.
      }
      simpl.
      rewrite H0.
      reflexivity.
Qed.

Lemma same_range_same_loc: H.same_loc = G.same_range.
Proof.
  apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  intros y.
  apply PropExtensionality.propositional_extensionality.
  split.
  - intros H.
    unfold same_loc in H.
    unfold loc in H. simpl in H.
    destruct (G.lab x) eqn:is_x; destruct (G.lab y) eqn:is_y; try discriminate.
    + rewrite <- Uni_m_1. apply uni_rng_is_overlap.
      * apply (wf_values_W_R_some WF_m). left. unfold is_r. rewrite is_x. easy.
      * apply (wf_values_W_R_some WF_m). left. unfold is_r. rewrite is_y. easy.
      * inversion H. specialize (WF_E_m x) as WF_E_m1. specialize (WF_E_m y) as WF_E_m2.
        rewrite is_x in WF_E_m1. rewrite is_y in WF_E_m2. rewrite H1 in WF_E_m1.
        destruct WF_E_m1 as [WF_E_m11 WF_E_m12]. destruct WF_E_m2 as [WF_E_m211 WF_E_m22].
        rewrite <- WF_E_m11. rewrite <- WF_E_m211. reflexivity.
    + rewrite <- Uni_m_1. apply uni_rng_is_overlap.
      * apply (wf_values_W_R_some WF_m). left. unfold is_r. rewrite is_x. easy.
      * apply (wf_values_W_R_some WF_m). right. unfold is_w. rewrite is_y. easy.
      * inversion H. specialize (WF_E_m x) as WF_E_m1. specialize (WF_E_m y) as WF_E_m2.
        rewrite is_x in WF_E_m1. rewrite is_y in WF_E_m2. rewrite H1 in WF_E_m1.
        destruct WF_E_m1 as [WF_E_m11 WF_E_m12]. destruct WF_E_m2 as [WF_E_m211 WF_E_m22].
        rewrite <- WF_E_m11. rewrite <- WF_E_m211. reflexivity.
    + rewrite <- Uni_m_1. apply uni_rng_is_overlap.
      * apply (wf_values_W_R_some WF_m). right. unfold is_w. rewrite is_x. easy.
      * apply (wf_values_W_R_some WF_m). left. unfold is_r. rewrite is_y. easy.
      * inversion H. specialize (WF_E_m x) as WF_E_m1. specialize (WF_E_m y) as WF_E_m2.
        rewrite is_x in WF_E_m1. rewrite is_y in WF_E_m2. rewrite H1 in WF_E_m1.
        destruct WF_E_m1 as [WF_E_m11 WF_E_m12]. destruct WF_E_m2 as [WF_E_m211 WF_E_m22].
        rewrite <- WF_E_m11. rewrite <- WF_E_m211. reflexivity.
    + rewrite <- Uni_m_1. apply uni_rng_is_overlap.
      * apply (wf_values_W_R_some WF_m). right. unfold is_w. rewrite is_x. easy.
      * apply (wf_values_W_R_some WF_m). right. unfold is_w. rewrite is_y. easy.
      * inversion H. specialize (WF_E_m x) as WF_E_m1. specialize (WF_E_m y) as WF_E_m2.
        rewrite is_x in WF_E_m1. rewrite is_y in WF_E_m2. rewrite H1 in WF_E_m1.
        destruct WF_E_m1 as [WF_E_m11 WF_E_m12]. destruct WF_E_m2 as [WF_E_m211 WF_E_m22].
        rewrite <- WF_E_m11. rewrite <- WF_E_m211. reflexivity.
    + apply same_range_F; try assumption.
      * unfold is_f. rewrite is_x. easy.
      * unfold is_f. rewrite is_y. easy.
 - intros H.
   unfold same_loc.
   unfold loc.
   simpl.
   specialize WF_E_m with x as WF_E_m_x.
   specialize WF_E_m with y as WF_E_m_y.
   pose (same_range_uni_rng H) as H1.
   destruct (G.lab x) eqn:is_x; destruct (G.lab y) eqn:is_y; auto.
   all: try by desf; rewrite H1.
   all: exfalso.
   1,2: eapply (@is_overlap_F_right _ x y WF_m); eauto; [| | by rewrite Uni_m_1; apply H];
     type_solver.
   all: eapply (@is_overlap_F_left _ x y WF_m); eauto; [| | by rewrite Uni_m_1; apply H];
     type_solver.
Qed.

Hint Rewrite E_m_E lab_m_lab sb_m_sb rmw_m_rmw rf_m_rf mod_m_mod W_m_W R_m_R Sc_m_Sc R_ex_m_R_ex sw_m_sw hb_m_hb same_range_same_loc:
  H_G_rewriteDb.

Hint Rewrite <- E_m_E lab_m_lab sb_m_sb rmw_m_rmw rf_m_rf mod_m_mod W_m_W R_m_R Sc_m_Sc R_ex_m_R_ex sw_m_sw hb_m_hb same_range_same_loc:
  H_G_rewriteDb_r.

Tactic Notation "H_G_rewrite" :=
  autorewrite with H_G_rewriteDb.

Tactic Notation "H_G_rewrite_r" :=
  autorewrite with H_G_rewriteDb_r.

Lemma rf_rfb x y:
  G.rf x y -> rfb G x y = range G y.
Proof.
  intros H.
  pose (rf_E WF_m H) as G_E_x_G_E_y.
  pose (rf_w_r WF_m H) as G_W_x_G_R_y.
  assert (G.same_range x y) as Hsr. {
    rewrite <- Uni_m_1.
    apply rf_overlap.
    apply WF_m.
    apply H.
  }
  unfold functional in Uni_m_2.
  unfold rf in Uni_m_2.
  unfold transp in Uni_m_2.
  assert (forall n, In n (range G y) -> In n (rfb G x y)) as He. {
    intros n Hin.
    assert (exists b : actid, In n (rfb G b y)) as He. {
      apply rfb_R_total.
      - apply WF_m.
      - easy.
      - assumption.
    }
    destruct He as [x_ He].
    assert (x_ = x) as x_x_. {
      apply Uni_m_2 with y.
      - intros Hloc.
        eapply in_nil.
        rewrite Hloc.
        apply He.
      - apply H.
    }
    rewrite <- x_x_.
    apply He.
  }
  assert (forall n, In n (rfb G x y) -> In n (range G y)) as He_r. {
    intros n Hin.
    pose (wf_values_all WF_m _ _ G_E_x_G_E_y) as Hwfv_.
    unfold is_wf_values in Hwfv_.
    unfold incl in Hwfv_.
    pose (Hwfv_ _ Hin) as Hwfv.
    unfold wf_values in Hwfv.
    rewrite split_fst_map in Hwfv.
    apply Basic.in_prod_inv in Hwfv.
    destruct Hwfv as [b Hwfv].
    assert (n=fst(n,b)) as n_pair. { easy. }
    rewrite list_intersect_r_vP in Hwfv.
    destruct Hwfv as  [_ Hwfv].
    unfold range.
    rewrite n_pair.
    apply in_split_l.
    apply Hwfv.
  }
  pose (rfb_seq WF_m x y) as Hee.
  pose (range_seq WF_m y) as Hee_r.
  destruct Hee as [n [m Hee]].
  destruct Hee_r as [n' [m' Hee_r]].
  rewrite Hee.
  rewrite Hee in He, He_r.
  rewrite Hee_r.
  rewrite Hee_r in He, He_r.
  apply seq_eq.
  intuition.
Qed.

Lemma rf_range_value x y :
  G.rf x y -> range_value G x = range_value G y.
Proof.
  intros H.
  pose (wf_values_all WF_m _ _ (rf_E WF_m H)) as Hwf.
  unfold is_wf_values in Hwf.
  rewrite (rf_rfb H) in Hwf.
  unfold wf_values in Hwf.
  unfold incl in Hwf.
  rewrite split_fst_map in Hwf.
  pose (rf_overlap WF_m H) as Hsr.
  rewrite Uni_m_1 in Hsr.
  pose (range_seq WF_m x) as Hseq.
  destruct Hseq as [n [m Hseq]].
  eapply combine_eq_seq.
  - apply range_value_split_combine.
  - rewrite Hsr. apply range_value_split_combine.
  - apply Hseq.
  - intros a Ina.
    specialize Hwf with a.
    apply Basic.in_prod_inv in Hwf.
    destruct Hwf as [b Hwf].
    exists b.
    rewrite <- (PropExtensionality.propositional_extensionality _ _ (list_intersect_r_vP _ _ _)).
    apply Hwf.
    rewrite <- Hsr.
    apply Ina.
Qed.

Lemma rf_wf_values_in_r x y :
  G.rf x y -> incl (range_value G y) (wf_values G x y).
Proof.
  intros H1.
  unfold incl.
  intros [a b].
  intros H2.
  apply list_intersect_r_vP.
  split.
  - rewrite (rf_range_value H1).
    assumption.
  - assumption.
Qed.

Lemma wf_H : Wf H.
Proof.
  constructor; H_G_rewrite; try (apply WF_m); try (apply H_co_wf).
  - rewrite <- Uni_m_1. apply rf_overlap_set. apply WF_m.
  - unfold funeq.
    intros x y H.
    pose (rf_rfb H) as Hrfb.
    pose (rf_w_r WF_m H) as Ha.
    destruct Ha as [Hw Hr].
    unfold is_w in Hw.
    unfold is_r in Hr.
    specialize WF_E_m with x as WF_E_mw.
    specialize WF_E_m with y as WF_E_mr.
    destruct (G.lab x) eqn: G_lab_x; destruct (G.lab y) eqn: G_lab_y; try discriminate.
    + unfold val. rewrite G_lab_x. rewrite G_lab_y.
      destruct WF_E_mw as [WF_E_mw1 WF_E_mw2].
      destruct WF_E_mr as [WF_E_mr1 WF_E_mr2].
      rewrite WF_E_mw2.
      rewrite WF_E_mr2.
      cut (uni_val x = uni_val y).
      auto.
      unfold uni_val.
      rewrite (rf_range_value H).
      destruct (range_value G y); reflexivity.
  - apply Uni_m_2.
  - rewrite <- same_range_same_loc. apply H_co_wf.
  - pose (wf_init WF_m) as WF_m_init.
    intros l H.
    destruct H as [b H].
    specialize (WF_m_init b l).
    apply (WF_m_init H).
Qed.

Lemma Chbrfhb_alt_left :
  (forall n, irreflexive (G.hb ⨾ (G.(rf_on) n)⁻¹ ⨾ (G.hb ∩ G.(overlap_on) n) ⨾ ⦗ G.W ⦘)) ->
    irreflexive (G.hb ⨾ G.rf⁻¹ ⨾ G.hb ∩ G.same_range ⨾ ⦗G.W⦘).
Proof.
  intros H.
  unfold irreflexive.
  intros x H2.
  destruct H2 as [y [H1 [z [H2 [x_ [[H31 H32] [H41 H42]]]]]]].
  rewrite H41 in H42, H32, H31.
  assert (exists n, rf_on G n z y) as Hn. { apply rf_rf_on. apply H2. }
  destruct Hn as [n Hn].
  destruct H with n x.
  econstructor.
  split. {apply H1. }
  econstructor.
  split. { apply Hn. }
  econstructor.
  split. { econstructor. apply H31. eapply same_range_overlap_on.
           apply rf_on_overlap_on. apply WF_m. apply Hn. apply H32. }
  econstructor; easy.
Qed.

Lemma Chbrfhb_alt_right :
  irreflexive (G.hb ⨾ G.rf⁻¹ ⨾ G.hb ∩ G.same_range ⨾ ⦗G.W⦘) ->
    (forall n, irreflexive (G.hb ⨾ (G.(rf_on) n)⁻¹ ⨾ (G.hb ∩ G.(overlap_on) n) ⨾ ⦗ G.W ⦘)).
Proof.
  intros H n.
  unfold irreflexive.
  unfold irreflexive in H.
  intros x H2.
  apply H with x.
  destruct H2 as [y [H21 [z [H221 [x_ [[H22211 H22212] H2222]]]]]].
  destruct H2222 as [H2222a H2222b].
  rewrite H2222a in H2222b, H22211, H22212.
  econstructor.
  split. { apply H21. }
  econstructor.
  split. { eapply rf_on_rf. apply H221. }
  econstructor.
  split. { econstructor. apply H22211. rewrite <- Uni_m_1.
           eapply overlap_on_is_overlap. apply H22212. }
  econstructor.
  reflexivity.
  assumption.
Qed.

Lemma Chbrfhb_alt :
  (forall n, irreflexive (G.hb ⨾ (G.(rf_on) n)⁻¹ ⨾ (G.hb ∩ G.(overlap_on) n) ⨾ ⦗ G.W ⦘)) =
    irreflexive (G.hb ⨾ G.rf⁻¹ ⨾ G.hb ∩ G.same_range ⨾ ⦗G.W⦘).
Proof.
  apply PropExtensionality.propositional_extensionality.
  split.
  apply Chbrfhb_alt_left.
  apply Chbrfhb_alt_right.
Qed.

Lemma Cirr3_alt_left :
  irreflexive (⦗H.W∩₁H.Sc⦘ ⨾ tot ⨾ ⦗H.R∩₁H.Sc⦘ ⨾ (H.hb ∩ H.rf)⁻¹ ⨾ (H.hb ∩ H.same_loc)) ->
    irreflexive (⦗H.W∩₁H.Sc⦘ ⨾ (tot ∩ H.same_loc) ⨾ ⦗H.R∩₁H.Sc⦘ ⨾ (H.hb ∩ H.rf)⁻¹ ⨾ H.hb).
Proof.
  intros H1.
  unfold irreflexive.
  unfold irreflexive in H1.
  intros x H2.
  apply H1 with x.
  destruct H2 as [x_ [H21 H22]].
  assert (x = x_) as x_x_. { destruct H21. assumption. }
  rewrite <- x_x_ in H21, H22.
  econstructor.
  split. apply H21.
  destruct H22 as [y [H221 H222]].
  econstructor.
  split. apply H221.
  destruct H222 as [y_ [H2221 H2222]].
  assert (y = y_) as y_y_. { destruct H2221. assumption. }
  rewrite <- y_y_ in H2221, H2222.
  econstructor.
  split. apply H2221.
  destruct H2222 as [z [H22221 H22222]].
  econstructor.
  split. apply H22221.
  econstructor. { assumption. }
  apply (same_loc_trans) with y.
  - eapply (Execution.wf_rfl wf_H).
    destruct H22221. assumption.
  - destruct H221. apply same_loc_sym. assumption.
Qed.

Lemma Cirr3_alt_right :
  irreflexive (⦗H.W∩₁H.Sc⦘ ⨾ (tot ∩ H.same_loc) ⨾ ⦗H.R∩₁H.Sc⦘ ⨾ (H.hb ∩ H.rf)⁻¹ ⨾ H.hb) ->
    irreflexive (⦗H.W∩₁H.Sc⦘ ⨾ tot ⨾ ⦗H.R∩₁H.Sc⦘ ⨾ (H.hb ∩ H.rf)⁻¹ ⨾ (H.hb ∩ H.same_loc)).
Proof.
  intros H1.
  unfold irreflexive.
  unfold irreflexive in H1.
  intros x H2.
  apply H1 with x.
  destruct H2 as [x_ [H21 H22]].
  assert (x = x_) as x_x_. { destruct H21. assumption. }
  rewrite <- x_x_ in H21, H22.
  econstructor.
  split. apply H21.
  destruct H22 as [y [H221 [y_ [H2221 [z [H22221 H22222]]]]]].
  assert (y = y_) as y_y_. { destruct H2221. assumption. }
  rewrite <- y_y_ in H2221, H22221.
  econstructor.
  assert ((tot ∩ H.same_loc) x y) as H221_1. {
    destruct H22222 as [Hhb Hsl].
    destruct H22221 as [Ha Hb].
    econstructor.
    - assumption.
    - apply (same_loc_trans) with z.
      + apply same_loc_sym. assumption.
      + eapply (Execution.wf_rfl wf_H). assumption.
  }
  split. { apply H221_1. }
  econstructor.
  split. apply H2221.
  econstructor.
  split. apply H22221.
  apply H22222.
Qed.

Lemma Cirr3_alt :
  irreflexive (⦗H.W∩₁H.Sc⦘ ⨾ (tot ∩ H.same_loc) ⨾ ⦗H.R∩₁H.Sc⦘ ⨾ (H.hb ∩ H.rf)⁻¹ ⨾ H.hb) =
    irreflexive (⦗H.W∩₁H.Sc⦘ ⨾ tot ⨾ ⦗H.R∩₁H.Sc⦘ ⨾ (H.hb ∩ H.rf)⁻¹ ⨾ (H.hb ∩ H.same_loc)).
Proof.
  apply PropExtensionality.propositional_extensionality.
  split.
  apply Cirr3_alt_right.
  apply Cirr3_alt_left.
Qed.

Lemma tearfree_trivial :
  functional (⦗tearfree⦘ ⨾ (G.rf⁻¹ ∩ G.same_range) ⨾ ⦗tearfree⦘).
Proof.
  apply functional_seq. { apply functional_eqv_rel. }
  apply functional_seq.
  - apply functional_inter_l. assumption.
  - apply functional_eqv_rel.
Qed.

Lemma consist_m_consist_left :
  jsmm_m_consistent G tot tearfree -> jsmm_consistent H tot.
Proof.
  intros H.
  constructor.
  - apply H.
  - repeat constructor.
    + H_G_rewrite. apply H.
    + H_G_rewrite. apply H.
    + H_G_rewrite. rewrite <- Chbrfhb_alt. apply H.
    + H_G_rewrite. rewrite <- rf_m_overlap. rewrite <- Cirr1_alt. apply H. apply WF_m.
    + H_G_rewrite. apply H.
    + rewrite <- Cirr3_alt. H_G_rewrite. apply H.
Qed.

Lemma consist_m_consist_right :
  jsmm_consistent H tot -> jsmm_m_consistent G tot tearfree.
Proof.
  intros H.
  constructor.
  - apply H.
  - repeat constructor.
    + H_G_rewrite_r. apply H.
    + H_G_rewrite_r. apply H.
    + rewrite Chbrfhb_alt. H_G_rewrite_r. apply H.
    + rewrite Cirr1_alt. rewrite rf_m_overlap. H_G_rewrite_r. apply H. apply WF_m.
    + H_G_rewrite_r. apply H.
    + H_G_rewrite_r. rewrite Cirr3_alt. apply H.
    + apply tearfree_trivial.
Qed.

Theorem consist_m_consist :
  jsmm_m_consistent G tot tearfree <-> jsmm_consistent H tot.
Proof.
  split.
  apply consist_m_consist_left.
  apply consist_m_consist_right.
Qed.

End JSMM_m_JSMM.
