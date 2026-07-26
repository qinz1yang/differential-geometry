import DifferentialGeometry.Analysis.Calculus.MovingInverse
import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1MetricLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageInjectivity

set_option autoImplicit false

/-!
# Exact inverse chart tails for Step B1

The reverse finite-stage comparison map is used only to prove injectivity.  This
file instead studies the exact inverse `Function.invFunOn` of the forward map.
The analysis input is `OpenPartialHomeomorph.exists_symm_cInf`; a bad-pair
argument later turns its one-sequence conclusion into the rectangular
source/target-stage tail needed by Step B1.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem exists_inv_seq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {A G : Nat → E → E} {Q W K : Set E}
    (hQ : IsOpen Q) (hW : IsOpen W) (hK : IsCompact K)
    (hKQ : K ⊆ Q) (hQW : closure Q ⊆ W)
    (hconv : MapCInfConvOnCompacts Q A id)
    (hgood : ∀ᶠ n in atTop,
      IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E)
          (∞ : WithTop ℕ∞) (A n) W ∧
        Set.InjOn (A n) W ∧ LeftInvOn (G n) (A n) W) :
    ∃ V : Set E,
      IsOpen V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
        MapCInfConvOnCompacts V G id ∧
        ∀ᶠ n in atTop, ContDiffOn Real (∞ : WithTop ℕ∞) (G n) V := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  have hex : ∀ n, N ≤ n →
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
          E E (∞ : WithTop ℕ∞),
        Φ.source = W ∧ Φ.target = A n '' W ∧
          Set.EqOn Φ (A n) W := by
    intro n hn
    exact exists_diffeo_of_injOn (hN n hn).1 hW (hN n hn).2.1
  let Φ : (n : Nat) → N ≤ n →
      PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
        E E (∞ : WithTop ℕ∞) := fun n hn ↦ Classical.choose (hex n hn)
  let e : Nat → OpenPartialHomeomorph E E := fun n ↦
    if hn : N ≤ n then (Φ n hn).toOpenPartialHomeomorph
    else OpenPartialHomeomorph.refl E
  let eInf : OpenPartialHomeomorph E E := OpenPartialHomeomorph.refl E
  have heq : ∀ n, N ≤ n → Set.EqOn (e n) (A n) W := by
    intro n hn
    simpa only [e, dif_pos hn] using (Classical.choose_spec (hex n hn)).2.2
  have hsource : ∀ n, closure Q ⊆ (e n).source := by
    intro n
    by_cases hn : N ≤ n
    · have hsrc : (Φ n hn).source = W :=
        (Classical.choose_spec (hex n hn)).1
      simp only [e, dif_pos hn]
      change closure Q ⊆ (Φ n hn).source
      rw [hsrc]
      exact hQW
    · simp only [e, dif_neg hn, OpenPartialHomeomorph.refl_source,
        subset_univ]
  have hstage_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (e n : E → E) Q := by
    intro n
    by_cases hn : N ≤ n
    · have hcd : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E)
          (∞ : WithTop ℕ∞) (Φ n hn : E → E) W := by
        have hsrc : (Φ n hn).source = W :=
          (Classical.choose_spec (hex n hn)).1
        rw [← hsrc]
        exact (Φ n hn).contMDiffOn_toFun
      have hcd' : ContDiffOn Real (∞ : WithTop ℕ∞)
          (Φ n hn : E → E) W := by
        simpa only [contMDiffOn_iff_contDiffOn] using hcd
      simpa only [e, dif_pos hn] using hcd'.mono (subset_closure.trans hQW)
    · simpa only [e, dif_neg hn, OpenPartialHomeomorph.refl_apply,
        id_eq] using
        (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
  have he_conv : MapCInfConvOnCompacts Q (fun n ↦ (e n : E → E)) id := by
    apply hconv.congr_eventually hQ
    · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
      intro z hz
      exact heq n hn (subset_closure.trans hQW hz)
    · exact Set.eqOn_refl id Q
  have heInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (eInf : E → E) Q := by
    simpa only [eInf, OpenPartialHomeomorph.refl_apply, id_eq] using
      (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
  have heInf_symm_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (eInf.symm : E → E) eInf.target := by
    simpa only [eInf, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq] using
      (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
  have hKt : K ⊆ eInf.target := by
    simp only [eInf, OpenPartialHomeomorph.refl_target, subset_univ]
  have hKpre : eInf.symm '' K ⊆ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKQ hx
  obtain ⟨V, hV, hVcompact, hKV, _hVtarget, _hVpre, hstage, hinv⟩ :=
    OpenPartialHomeomorph.exists_symm_cInf hQ hK he_conv
      (Filter.Eventually.of_forall hsource) hstage_cd heInf_cd
      heInf_symm_cd hKt hKpre
  have heq_inv : ∀ᶠ n in atTop,
      Set.EqOn (G n) (e n).symm V := by
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩, hstage] with n hn hstageN
    intro w hw
    have hwTarget : w ∈ (e n).target := hstageN.1 (subset_closure hw)
    have hpreQ : (e n).symm w ∈ Q := hstageN.2 (subset_closure hw)
    have hpreW : (e n).symm w ∈ W := hQW (subset_closure hpreQ)
    have hew : e n ((e n).symm w) = w := (e n).right_inv hwTarget
    have hAw : A n ((e n).symm w) = w := by
      exact (heq n hn hpreW).symm.trans hew
    calc
      G n w = G n (A n ((e n).symm w)) := congrArg (G n) hAw.symm
      _ = (e n).symm w := (hN n hn).2.2 hpreW
  have hGconv : MapCInfConvOnCompacts V G id := by
    apply hinv.congr_eventually hV
    · exact heq_inv
    · exact Set.eqOn_refl id V
  have hGcd : ∀ᶠ n in atTop,
      ContDiffOn Real (∞ : WithTop ℕ∞) (G n) V := by
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩,
      hstage, heq_inv] with n hn hstageN heqN
    have hsymm : ContDiffOn Real (∞ : WithTop ℕ∞)
        ((e n).symm : E → E) V := by
      have hraw : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E)
          (∞ : WithTop ℕ∞) ((Φ n hn).symm : E → E)
          (Φ n hn).target :=
        (Φ n hn).symm.contMDiffOn_toFun
      have hraw' : ContDiffOn Real (∞ : WithTop ℕ∞)
          ((Φ n hn).symm : E → E) (Φ n hn).target := by
        simpa only [contMDiffOn_iff_contDiffOn] using hraw
      have hsub : V ⊆ (Φ n hn).target := by
        intro w hw
        have hw' : w ∈ (e n).target := hstageN.1 (subset_closure hw)
        simpa only [e, dif_pos hn] using hw'
      simpa only [e, dif_pos hn] using hraw'.mono hsub
    exact hsymm.congr fun _w hw ↦ heqN hw
  exact ⟨V, hV, hVcompact, hKV, hGconv, hGcd⟩

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- Along any cofinal pair of stages, the exact coordinate inverse of the
forward comparison map converges smoothly to the identity on a neighborhood
of every compact target core.  The reverse comparison map is not used here. -/
theorem HasStageJetData.inv_chart_conv
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (S T Vrad : Real) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < r)
    (alpha : LiveSlot L inp.pack r)
    (Q W K : Set E) (hQ : IsOpen Q) (hW : IsOpen W)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (hQW : closure Q ⊆ W)
    (hWint : W ⊆ interior (C0 alpha))
    (kn ln : Nat → Nat)
    (hkn : Tendsto kn atTop atTop) (hln : Tendsto ln atTop atTop)
    (hsource : ∀ᶠ n in atTop,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      Set.MapsTo
        (NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P S (kn n))) :
    let Lphi := L.subseq hphi
    let G : Nat → E → E := fun n w ↦
      let Yk := X.obj (Lphi.φ (kn n))
      let Yl := X.obj (Lphi.φ (ln n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
      let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
      let F := stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
      chiK (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.symm w))
    ∃ Vout : Set E,
      IsOpen Vout ∧ IsCompact (closure Vout) ∧ K ⊆ Vout ∧
        MapCInfConvOnCompacts Vout G id ∧
        ∀ᶠ n in atTop,
          ContDiffOn Real (∞ : WithTop ℕ∞) (G n) Vout := by
  classical
  dsimp only
  let Lphi := L.subseq hphi
  let A : Nat → E → E := fun n z ↦
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
    let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    chiL (stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
      (chiK.symm z))
  let G : Nat → E → E := fun n w ↦
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
    let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    let F := stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
    chiK (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.symm w))
  change ∃ Vout : Set E,
    IsOpen Vout ∧ IsCompact (closure Vout) ∧ K ⊆ Vout ∧
      MapCInfConvOnCompacts Vout G id ∧
      ∀ᶠ n in atTop,
        ContDiffOn Real (∞ : WithTop ℕ∞) (G n) Vout
  rcases hstage with ⟨hdata, hmetric, hjets, hbase⟩
  have hgap : 0 ≤
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 :=
    mul_nonneg (by positivity) (inp.decay.lambda_pos inp.hD 0).le
  have hTr : T < r := by linarith
  have hSr : S < r := hST.trans hTr
  have hQint : Q ⊆ interior (C0 alpha) :=
    subset_closure.trans (hQW.trans hWint)
  have hsourceQ : ∀ᶠ n in atTop,
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      Set.MapsTo
        (NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        Q (Lphi.hatSourceBall inp.decay P S (kn n)) := by
    filter_upwards [hsource] with n hn
    simpa only [Lphi] using
      hn.mono_left (subset_closure.trans hQW)
  have hAconv : MapCInfConvOnCompacts Q A id := by
    simpa only [A, Lphi] using
      HasStageJetData.chart_conv (I := I) inp P L hr phi hphi hconn
        U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha Q hQint
        kn ln hkn hln hsourceQ
  obtain ⟨Njet, hNjet⟩ := hjets S hSr 1 (1 / 2 : Real) (by norm_num)
  obtain ⟨Ninj, hNinj⟩ :=
    HasStageJetData.inj_tail (I := I) inp P L hr phi hphi hcomplete hconn
      U C0 C1 aInf Jinf Jbarinf gInf
      ⟨hdata, hmetric, hjets, hbase⟩ T Vrad hroom hVr
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
  have hgood : ∀ᶠ n in atTop,
      IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E)
          (∞ : WithTop ℕ∞) (A n) W ∧
        Set.InjOn (A n) W ∧ LeftInvOn (G n) (A n) W := by
    filter_upwards [hkn.eventually_ge_atTop (max Njet Ninj),
      hln.eventually_ge_atTop (max Njet Ninj), hsource] with n hnk hnl hsrc
    have hnkJet : Njet ≤ kn n := (le_max_left _ _).trans hnk
    have hnlJet : Njet ≤ ln n := (le_max_left _ _).trans hnl
    have hnkInj : Ninj ≤ kn n := (le_max_right _ _).trans hnk
    have hnlInj : Ninj ≤ ln n := (le_max_right _ _).trans hnl
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    letI : MetricSpace Yl.M := (P (Lphi.φ (ln n))).ms
    letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
    let F := stageComparisonMap inp P Lphi r hr hconn (kn n) (ln n)
    let ck := seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)
    let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric ck
    let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric cl
    have hjet (z : E) (hz : z ∈ W) :
        F (chiK.symm z) ∈ (normalExpPD (I := I) Yl cl).target ∧
          ContDiffAt Real ∞ (A n) z ∧
          ∀ j ≤ 1, mapDerivNorm j (A n) id z ≤ (1 / 2 : Real) := by
      have hzInt : z ∈ interior (C0 alpha) := hWint hz
      have hzSrc := hsrc hz
      simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
        hNjet (kn n) hnkJet (ln n) hnlJet alpha z
          (interior_subset hzInt) hzInt hzSrc
    have hAcd : ContDiffOn Real ∞ (A n) W := fun z hz ↦
      (hjet z hz).2.1.contDiffWithinAt
    have hAinv : ∀ z ∈ W,
        (fderiv Real (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E)
          z (A n)) (extChartAt 𝓘(ℝ, E) z z)).IsInvertible := by
      intro z hz
      have hdiff : DifferentiableAt Real (A n) z :=
        (hjet z hz).2.1.differentiableAt (by simp)
      have hraw : mapDerivNorm 1 (A n) id z ≤ (1 / 2 : Real) :=
        (hjet z hz).2.2 1 le_rfl
      have hneu := neumannOfDerivNorm hdiff hraw
      apply Coordinates.isInvertible_of_norm_id_sub_lt
      simpa only [writtenInExtChartAt_model_space, ext_chart_model_space_apply] using
        hneu.trans_lt (by norm_num)
    have hAloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (A n) W := by
      apply Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hW
      · simpa only [contMDiffOn_iff_contDiffOn] using hAcd
      · exact hAinv
    have hFInj := hNinj (kn n) hnkInj (ln n) hnlInj
    have hgeomK := hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf
      (kn n) alpha
    have hUtgt : U alpha ⊆ chiK.target := by
      intro z hz
      have hzBall := hgeomK.2.1 hz
      rw [Metric.mem_ball, dist_zero_right] at hzBall
      change z ∈ (NormalCoordinates.framedExpDiffeo
        (I := I) Yk.metric ck).source
      rw [NormalCoordinates.framedExp_source]
      apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yk.metric ck
      simpa only [NormalCoordinates.normalFrame_sqrt] using hzBall
    have hsmallTarget : ∀ q : Yl.M,
        q ∈ (normalExpPD (I := I) Yl cl).target → q ∈ chiL.source := by
      intro q hq
      rcases hq with ⟨v, hv, rfl⟩
      have hvNorm : ‖v‖ < expRadiusGp (I := I) Yl.metric cl := by
        change v ∈ Metric.ball (0 : E)
          (expRadiusGp (I := I) Yl.metric cl) at hv
        simpa only [Metric.mem_ball, dist_zero_right] using hv
      have hvSource : v ∈ (NormalCoordinates.framedExpDiffeo
          (I := I) Yl.metric cl).source := by
        rw [NormalCoordinates.framedExp_source]
        apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yl.metric cl
        apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yl.metric cl
        simpa only [NormalCoordinates.normalFrame_sqrt] using hvNorm
      have hmap := (NormalCoordinates.framedExpDiffeo
        (I := I) Yl.metric cl).map_source hvSource
      simpa only [normalExpPD, chiL] using hmap
    have hAinj : Set.InjOn (A n) W := by
      intro z hz w hw hzw
      have hzU : z ∈ U alpha := hIntU (hWint hz)
      have hwU : w ∈ U alpha := hIntU (hWint hw)
      have hzT : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P T (kn n) :=
        cball_subset_of_le hST.le (hsrc hz)
      have hwT : chiK.symm w ∈ Lphi.hatSourceBall inp.decay P T (kn n) :=
        cball_subset_of_le hST.le (hsrc hw)
      have hFzSrc : F (chiK.symm z) ∈ chiL.source := by
        exact hsmallTarget _ (hjet z hz).1
      have hFwSrc : F (chiK.symm w) ∈ chiL.source := by
        exact hsmallTarget _ (hjet w hw).1
      have hFzw : F (chiK.symm z) = F (chiK.symm w) := by
        apply chiL.toPartialEquiv.injOn hFzSrc hFwSrc
        simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using hzw
      have hxy : chiK.symm z = chiK.symm w := by
        exact hFInj hzT hwT hFzw
      calc
        z = chiK (chiK.symm z) := (chiK.right_inv (hUtgt hzU)).symm
        _ = chiK (chiK.symm w) := congrArg chiK hxy
        _ = w := chiK.right_inv (hUtgt hwU)
    have hleft : LeftInvOn (G n) (A n) W := by
      intro z hz
      have hzU : z ∈ U alpha := hIntU (hWint hz)
      have hzClosed : chiK.symm z ∈
          Lphi.hatSourceBall inp.decay P S (kn n) := hsrc hz
      have hzBall : chiK.symm z ∈ Metric.ball Yk.basepoint T := by
        rw [Metric.mem_ball]
        have hzLe : dist (chiK.symm z) Yk.basepoint ≤ S := by
          simpa only [NetLimitData.hatSourceBall, Yk] using hzClosed
        exact hzLe.trans_lt hST
      have hFzSrc : F (chiK.symm z) ∈ chiL.source := by
        exact hsmallTarget _ (hjet z hz).1
      have hdecode : chiL.symm (A n z) = F (chiK.symm z) := by
        simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
          chiL.left_inv hFzSrc
      have hFInjBall : Set.InjOn F (Metric.ball Yk.basepoint T) := by
        exact hFInj.mono Metric.ball_subset_closedBall
      have hinv : Function.invFunOn F (Metric.ball Yk.basepoint T)
          (chiL.symm (A n z)) = chiK.symm z := by
        rw [hdecode]
        exact hFInjBall.leftInvOn_invFunOn hzBall
      change chiK (Function.invFunOn F (Metric.ball Yk.basepoint T)
        (chiL.symm (A n z))) = z
      rw [hinv]
      exact chiK.right_inv (hUtgt hzU)
    exact ⟨hAloc, hAinj, hleft⟩
  exact exists_inv_seq hQ hW hK hKQ hQW hAconv hgood

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- On a fixed compact target core, the exact coordinate inverses of all
sufficiently late forward comparison maps have one common two-stage jet tail.
The inverse is `Function.invFunOn` on the prescribed source ball. -/
theorem HasStageJetData.inv_chart_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (S T Vrad : Real) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < r)
    (alpha : LiveSlot L inp.pack r)
    (Q W K : Set E) (hQ : IsOpen Q) (hW : IsOpen W)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (hQW : closure Q ⊆ W)
    (hWint : W ⊆ interior (C0 alpha))
    (hsource : ∃ Nsrc : Nat, ∀ k ≥ Nsrc,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      Set.MapsTo
        (NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P S k))
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    let Lphi := L.subseq hphi
    let G : Nat → Nat → E → E := fun k l w ↦
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      let F := stageComparisonMap inp P Lphi r hr hconn k l
      chiK (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.symm w))
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ w ∈ K,
      mapDerivNorm j (G k l) id w ≤ eps := by
  classical
  dsimp only
  let Lphi := L.subseq hphi
  let G : Nat → Nat → E → E := fun k l w ↦
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    let F := stageComparisonMap inp P Lphi r hr hconn k l
    chiK (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.symm w))
  change ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ w ∈ K,
    mapDerivNorm j (G k l) id w ≤ eps
  apply mapCInf_pair_tail (U := K) (Φ := G) (Φinf := id)
    ?_ hK Subset.rfl p eps heps
  intro kn ln hkn hln
  obtain ⟨Nsrc, hNsrc⟩ := hsource
  have hsourceSeq : ∀ᶠ n in atTop,
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      Set.MapsTo
        (NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
    filter_upwards [hkn.eventually_ge_atTop Nsrc] with n hn
    simpa only [Lphi] using hNsrc (kn n) hn
  obtain ⟨Vout, _hVopen, _hVcompact, hKVout, hconv, _hGcd⟩ :=
    HasStageJetData.inv_chart_conv (I := I) inp P L hr phi hphi
      hcomplete hconn U C0 C1 aInf Jinf Jbarinf gInf hstage
      S T Vrad hST hroom hVr alpha Q W K hQ hW hK hKQ hQW hWint
      kn ln hkn hln hsourceSeq
  intro K' hK' hK'K j
  simpa only [G, Lphi] using
    hconv K' hK' (hK'K.trans hKVout) j

end HCGCompactness
end DifferentialGeometry
