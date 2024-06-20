Require Import Autosubst2.syntax ssreflect ssrbool.
From Hammer Require Import Tactics.
From stdpp Require Import relations (rtc(..)).

Reserved Infix "⤳h" (at level 60, no associativity).
Reserved Infix "⤳n" (at level 60, no associativity).
Reserved Infix "⇒" (at level 60, no associativity).
Reserved Infix "⇒n" (at level 60, no associativity).

Fixpoint count_var n (a : tm) :=
  match a with
  | var_tm i => if Nat.eqb n i then 1 else 0
  | tAbs a => count_var (S n) a
  | tApp a b => count_var n a + count_var n b
  end.

Definition isAbs a :=
  match a with
  | tAbs _ => true
  | _ => false
  end.

Inductive ERed : tm -> tm -> Prop :=
| ER_App a0 a1 b :
  ~~ isAbs a0 ->
  a0 ⤳h a1 ->
  tApp a0 b ⤳h tApp a1 b

| ER_AppAbs a b :
  tApp (tAbs a) b ⤳h subst_tm (b..) a

| ER_Abs a b :
  a ⤳h b ->
  tAbs a ⤳h tAbs b

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

Lemma Par_morphing a b :
  forall ρ0 ρ1, (forall i, ρ0 i ⇒ ρ1 i) ->
             subst_tm ρ0 a ⇒ subst_tm ρ1 b.

(* Parallel reduction *)
Inductive IPar : nat -> tm -> tm -> Prop :=
| IP_Var i :
  IPar 0 (var_tm i) (var_tm i)
| IP_App k0 a0 a1 k1 b0 b1 :
  IPar k0 a0 a1 ->
  IPar k1 b0 b1 ->
  IPar (k0 + k1) (tApp a0 b0) (tApp a1 b1)
| IP_AppAbs k0 a0 a1 k1 b0 b1 :
  IPar k0 a0 a1 ->
  IPar k1 b0 b1 ->
  IPar (k0 + count_var 0 a1 * k1 + 1) (tApp (tAbs a0) b0) (subst_tm (b1..) a1)
| IP_Abs k a0 a1 :
  IPar k a0 a1 ->
  IPar k (tAbs a0) (tAbs a1).

(* Parallel, non-essential reduction *)
Inductive NPar : tm -> tm -> Prop :=
| PN_Var i :
  var_tm i ⇒n var_tm i

| PN_AppAbs a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  tApp (tAbs a0) b0 ⇒n tApp (tAbs a1) b1

| PN_Abs a0 a1 :
  a0 ⇒n a1 ->
  tAbs a0 ⇒n tAbs a1

| PN_App a0 a1 b0 b1 :
  a0 ⇒n a1 ->
  b0 ⇒ b1 ->
  tApp a0 b0 ⇒n tApp a1 b1

where "a ⇒n b":= (NPar a b).

Lemma NPar_Par a b : a ⇒n b -> a ⇒ b.
Proof. induction 1; hauto lq:on ctrs:Par. Qed.

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
  - hauto lq:on ctrs:Par inv:ERed.
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
      elim/ered_inv=>//_ a0 b0 hab0 [?] ? h _. subst.
      hauto lq:on inv:Par ctrs:NPar.
    + hauto lq:on ctrs:starseq, NPar, Par, ERed.
Qed.

Lemma starseq_abs_cong M N
  (h : starseq M N) :
  starseq (tAbs M) (tAbs N).
Proof. elim:M N/h; hauto lq:on ctrs:starseq, NPar, Par, ERed. Qed.

Lemma starseq_par a b :
  starseq a b ->
  a ⇒ b.
Proof. induction 1; sfirstorder use:NPar_Par. Qed.

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
    admit.
  - move => a0 a1 b0 b1 ha iha hb ihb ρ0 ρ1 h.
    simpl.
    apply : S_Step.
    by apply ER_AppAbs.
    apply P_AppAbs' with (a1 := subst_tm (up_tm_tm ρ1) a1) (b1 := subst_tm ρ1 b1).
    by asimpl.
    (* par cong *)
    admit.
    (* par cong *)
    admit.
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
    (* renaming *)
    admit.
Admitted.

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
    best use:ipar_starseq_morphing.
  - eauto using starseq_abs_cong.
Admitted.
