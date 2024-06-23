Require Import Autosubst2.syntax ssreflect ssrbool.
From Hammer Require Import Tactics.
From stdpp Require Import relations (rtc(..), rtc_transitive).

Reserved Infix "⤳h" (at level 60, no associativity).
Reserved Infix "⇒" (at level 60, no associativity).
Reserved Infix "⇒n" (at level 60, no associativity).

Definition isAbs a :=
  match a with
  | tAbs _ => true
  | _ => false
  end.

Inductive ERed : tm -> tm -> Prop :=
| ER_App a0 a1 b :
  a0 ⤳h a1 ->
  tApp a0 b ⤳h tApp a1 b

| ER_AppAbs a b :
  tApp (tAbs a) b ⤳h subst_tm (b..) a

where "a ⤳h b" := (ERed a b).

Derive Inversion ered_inv with (forall a b, ERed a b).

(* Parallel reduction *)
Inductive Par : tm -> tm -> Prop :=
| P_Var i :
  var_tm i ⇒ var_tm i
| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp a0 b0 ⇒ tApp a1 b1
| P_AppAbs a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp (tAbs a0) b0 ⇒ subst_tm (b1..) a1
| P_Abs a0 a1 :
  a0 ⇒ a1 ->
  tAbs a0 ⇒ tAbs a1
where "a ⇒ b" := (Par a b).

Lemma P_AppAbs' a0 a1 b0 b1 t :
  t = subst_tm (b1..) a1 ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp (tAbs a0) b0 ⇒ t.
Proof. move => > ->. by apply P_AppAbs. Qed.

Lemma Par_renaming a b :
  a ⇒ b ->
  forall ξ, ren_tm ξ a ⇒ ren_tm ξ b.
Proof.
  move => h.
  elim:a b/h.
  - sfirstorder.
  - hauto lq:on ctrs:Par.
  - move => * /=.
    apply : P_AppAbs'; eauto.
    by asimpl.
  - hauto lq:on ctrs:Par.
Qed.

Lemma morphing_suc ρ0 ρ1 :
  (forall i, ρ0 i ⇒ ρ1 i) ->
  (forall i, (up_tm_tm ρ0) i ⇒ (up_tm_tm ρ1) i).
Proof.
  move => > ? []//=.
  - sfirstorder.
  - move => n. asimpl.
    sfirstorder use:Par_renaming.
Qed.

Lemma Par_morphing a b (h : a ⇒ b):
  forall ρ0 ρ1, (forall i, ρ0 i ⇒ ρ1 i) ->
             subst_tm ρ0 a ⇒ subst_tm ρ1 b.
Proof.
  elim : a b / h.
  - sfirstorder.
  - hauto lq:on ctrs:Par.
  - move => */=.
    apply : P_AppAbs'; cycle 1.
    sfirstorder use:morphing_suc.
    sfirstorder.
    by asimpl.
  - hauto lq:on ctrs:Par use:morphing_suc.
Qed.

(* Parallel, non-essential reduction *)
Inductive NPar : tm -> tm -> Prop :=
| PN_Var i :
  var_tm i ⇒n var_tm i

| PN_Abs a0 a1 :
  a0 ⇒ a1 ->
  tAbs a0 ⇒n tAbs a1

| PN_App a0 a1 b0 b1 :
  a0 ⇒n a1 ->
  b0 ⇒ b1 ->
  tApp a0 b0 ⇒n tApp a1 b1

where "a ⇒n b":= (NPar a b).

Lemma NPar_Par a b : a ⇒n b -> a ⇒ b.
Proof. induction 1; hauto lq:on ctrs:Par. Qed.

Lemma NPar_renaming a b :
  a ⇒n b ->
  forall ξ, ren_tm ξ a ⇒n ren_tm ξ b.
Proof.
  move => h.
  elim:a b/h.
  - sfirstorder.
  - hauto lq:on ctrs:NPar use:Par_renaming.
  - hauto lq:on ctrs:NPar use:Par_renaming.
  (* - hauto lq:on ctrs:NPar use:Par_renaming. *)
Qed.

(* Lemma isAbs_renaming a ξ : isAbs a = isAbs (ren_tm ξ a). *)
(* Proof. elim : a ξ => //=. Qed. *)

Lemma ER_AppAbs' a b u :
  u = subst_tm (b..) a ->
  tApp (tAbs a) b ⤳h u.
Proof. move => ->. by apply ER_AppAbs. Qed.

Lemma ERed_renaming a b :
  a ⤳h b ->
  forall ξ, ren_tm ξ a ⤳h ren_tm ξ b.
Proof.
  move => h.
  elim : a b /h.
  - hauto lq:on ctrs:ERed.
  - move => a b ξ /=.
    apply : ER_AppAbs'. by asimpl.
Qed.

Notation "s ⤳*h t" := (rtc ERed s t) (at level 60, no associativity).

Lemma hms_merge t a u  :
  t ⇒n a ->
  a ⤳h u ->
  t ⇒ u.
Proof.
  move => h.
  move : u.
  elim : t a / h.
  - hauto lq:on ctrs:Par inv:ERed.
  - hauto q:on ctrs:Par inv:ERed.
  (* - hauto lq:on ctrs:Par inv:ERed. *)
  - hauto lq:on inv:NPar, ERed ctrs:Par use:NPar_Par.
Qed.

(* Takahashi's *-sequence *)
Inductive starseq : tm -> tm -> Prop :=
| S_Refl M N :
  M ⇒n N ->
  (* ------- *)
  starseq M N
| S_Step M P N :
  M ⤳h P ->
  M ⇒ N ->
  starseq P N ->
  starseq M N.

Lemma starseq_renaming ξ a b :
  starseq a b ->
  starseq (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move => h.
  elim : a b /h;
    hauto lq:on ctrs:starseq use:NPar_renaming, Par_renaming, ERed_renaming.
Qed.

Lemma starseq_app_cong M N P Q :
  starseq M N ->
  P ⇒ Q ->
  starseq (tApp M P) (tApp N Q).
Proof.
  move => h. move : P Q. elim : M N / h.
  - sfirstorder use:S_Refl, PN_App.
  - move => M P N hMP hMN hPN ih R Q hRQ.
    case E : (isAbs M).
    + apply S_Refl.
      case : M hMP hMN E=>//.
      move => M.
      elim/ered_inv=>//_ a0 b0 hab0 [?] ? h _. (* subst. *)
      (* hauto lq:on inv:Par ctrs:NPar. *)
    + hauto lq:on ctrs:starseq, NPar, Par, ERed.
Qed.

Lemma starseq_par a b :
  starseq a b ->
  a ⇒ b.
Proof. induction 1; sfirstorder use:NPar_Par. Qed.

Lemma starseq_abs_cong M N
  (h : starseq M N) :
  starseq (tAbs M) (tAbs N).
Proof.
  apply S_Refl.
  hauto lq:on ctrs:NPar use:starseq_par.
Qed.

Lemma starseq_ρ_par ρ0 ρ1 :
  (forall i : fin, starseq (ρ0 i) (ρ1 i)) ->
  (forall i : fin, Par (ρ0 i) (ρ1 i)).
Proof. firstorder using starseq_par. Qed.

Lemma ipar_starseq_morphing :
  forall M N : tm,
  M ⇒ N ->
  forall ρ0 ρ1 : fin -> tm,
    (forall i : fin, starseq (ρ0 i) (ρ1 i)) -> starseq (subst_tm ρ0 M) (subst_tm ρ1 N).
Proof.
  move => M N h. elim : M N / h.
  - sfirstorder.
  - move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 hρ /=.
    apply starseq_app_cong.
    sfirstorder.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par.
  - move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 h.
    simpl.
    apply : S_Step.
    by apply ER_AppAbs.
    apply P_AppAbs' with (a1 := subst_tm (up_tm_tm ρ1) a1) (b1 := subst_tm ρ1 b1).
    by asimpl.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par, morphing_suc.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par.
    asimpl.
    apply iha.
    case => //=.
    by apply ihb.
  - move => a0 a1 ha iha ρ0 ρ1 hρ /=.
    apply starseq_abs_cong.
    apply iha.
    case => //=; asimpl.
    hauto l:on.
    move => n. asimpl.
    sfirstorder use:starseq_renaming.
    (* renaming *)
Qed.

Lemma hms_split t s (h : t ⇒ s) :
  starseq t s.
Proof.
  elim : t s /h .
  - hauto lq:on ctrs:NPar, starseq.
  - eauto using starseq_app_cong.
  - move => a0 a1 b0 b1 ha iha hb ihb.
    apply : S_Step.
    by apply ER_AppAbs.
    by apply P_AppAbs.
    hauto lq:on ctrs:starseq inv:nat use:ipar_starseq_morphing.
  - eauto using starseq_abs_cong.
Qed.

(* Erase the information about one step par from starseq *)
Lemma starseq_erase a b (h : starseq a b) :
  exists u, a ⤳*h u /\ u ⇒n b.
Proof.
  elim : a b /h; hauto lq:on ctrs:rtc.
Qed.

Lemma local_postponement t a u  :
  t ⇒n a ->
  a ⤳h u ->
  exists q, t ⤳*h q /\ q ⇒n u.
Proof. sfirstorder use:hms_split, hms_merge, starseq_erase. Qed.

Lemma local_postponement_star t a u :
  t ⇒n a ->
  a ⤳*h u ->
  exists q, t ⤳*h q /\ q ⇒n u.
  move => + h. move : t. elim : a u / h.
  sfirstorder.
  qauto l:on ctrs:rtc use:local_postponement, rtc_transitive.
Qed.

Lemma factorization t u :
  rtc Par t u ->
  exists v, rtc ERed t v /\ rtc NPar v u.
Proof.
  move => h. elim:t u/h=>//=.
  - hauto lq:on ctrs:rtc.
  - move => a b c ha hb [v][ihb0]ihb1.
    move /hms_split /starseq_erase : ha.
    move => [u][hu0]hu1.
    move : local_postponement_star ihb0 hu1; repeat move/[apply].
    move => [q][hq0]hq1.
    exists q. hauto lq:on ctrs:rtc use:rtc_transitive.
Qed.

Fixpoint ne a :=
  match a with
  | var_tm _ => true
  | tAbs _ => false
  | tApp a b => ne a && nf b
  end
with nf a :=
  match a with
  | var_tm _ => true
  | tAbs a => nf a
  | tApp a b => ne a && nf b
  end.

Lemma ne_is_nfb a : ne a ==> nf a.
Proof. elim : a; hauto lqb:on. Qed.

Lemma ne_is_nf a : ne a -> nf a.
Proof. sfirstorder use:ne_is_nfb b:on. Qed.


Inductive LoRed : tm -> tm -> Prop :=
| LoR_App0 a0 a1 b :
  ~~ isAbs a0 ->
  LoRed a0 a1 ->
  LoRed (tApp a0 b) (tApp a1 b)

| LoR_App1 a b0 b1 :
  ne a ->
  LoRed b0 b1 ->
  LoRed (tApp a b0) (tApp a b1)

| LoR_AppAbs a b :
  LoRed (tApp (tAbs a) b) (subst_tm (b..) a)

| LoR_Abs a b :
  LoRed a b ->
  LoRed (tAbs a) (tAbs b).

Lemma NPar_Var_inv a i :
  rtc NPar a (var_tm i) ->
  a = var_tm i.
Proof.
  move E : (var_tm i) => T h. move : i E.
  elim: a T/h; hauto lq:on rew:off inv:NPar ctrs:NPar, rtc.
Qed.

Lemma NPar_Abs_inv a b :
  rtc NPar a (tAbs b) ->
  exists a0, a = tAbs a0 /\ rtc Par a0 b.
Proof.
  move E : (tAbs b) => T h.
  move : b E.
  elim : a T/h; hauto lq:on ctrs:rtc inv:NPar.
Qed.

Lemma ERed_LoRed a b :
  ERed a b -> LoRed a b.
Proof.
  induction 1; hauto lq:on inv:ERed ctrs:LoRed.
Qed.

Lemma EReds_LoReds a b :
  rtc ERed a b -> rtc LoRed a b.
Proof. sfirstorder use:relations.rtc_subrel, ERed_LoRed unfold:subrel. Qed.

Lemma NPars_Pars a b :
  rtc NPar a b -> rtc Par a b.
Proof. sfirstorder use:relations.rtc_subrel, NPar_Par unfold:subrel. Qed.

Lemma LoRed_Abs_Cong a b :
  rtc LoRed a b ->
  rtc LoRed (tAbs a) (tAbs b).
Proof. move => h. elim:a b/h; hauto lq:on ctrs:LoRed, rtc. Qed.

Lemma LoRed_Abs_inv a b :
  rtc LoRed a b ->
  isAbs a -> isAbs b.
Proof. induction 1; hauto lq:on inv:LoRed. Qed.

Lemma LoRed_App_Cong a0 a1 b0 b1 :
  rtc LoRed a0 a1 ->
  ne a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tApp a0 b0) (tApp a1 b1).
Proof.
  move => h. move : b0 b1.
  elim : a0 a1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - move => a0 a1 a2 h0 h1 ih b0 b1 ha2 h.
    move : ih h (ha2) => /[apply]/[apply] h.
    apply : rtc_l; eauto.
    apply LoR_App0=>//.
    apply /negP.
    move => ?.
    have : isAbs a2 by hauto q:on ctrs:rtc use:LoRed_Abs_inv.
    move : ha2; clear. elim : a2 => //=.
Qed.

Lemma NPar_App_inv u a b :
  rtc NPar u (tApp a b) ->
  exists a0 b0, u = tApp a0 b0 /\ rtc NPar a0 a /\ rtc Par b0 b.
Proof.
  move E : (tApp a b) => T h.
  move : a b E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - move => a0 b0 c ha hb ihb a b ?. subst.
    specialize ihb with (1 := eq_refl).
    move : ihb => [a1][b1][?][ih0]ih1. subst.
    inversion ha; subst.
    hauto lq:on ctrs:Par, rtc.
Qed.

Definition whnf (a : tm) :=
  match a with
  | tAbs _ => true
  | _ => false
  end.

Lemma standardization a b :
  rtc Par a b -> nf b ->
  rtc LoRed a b.
Proof.
  elim : b a =>//=.
  - move => n a /factorization.
    hauto lq:on rew:off use:NPar_Var_inv, EReds_LoReds.
  - move => b ihb a /factorization.
    move => [a0][h0].
    move /NPar_Abs_inv => [a1][?]ha1. subst.
    move : ihb ha1; repeat move/[apply].
    hauto lq:on use:LoRed_Abs_Cong, EReds_LoReds, rtc_transitive.
  - move => a iha b ihb u /factorization.
    move => [u0][hu]hu0 /andP.
    move => [].
    move /NPar_App_inv : hu0.
    move => [a0][b0][?][h0]h1. subst.
    move /[dup] /ne_is_nf => *.
    have {}iha:rtc LoRed a0 a by sfirstorder use:NPars_Pars.
    have {}ihb:rtc LoRed b0 b by sfirstorder.
    hauto lq:on ctrs:rtc use:LoRed_App_Cong, rtc_transitive, EReds_LoReds.
Qed.
