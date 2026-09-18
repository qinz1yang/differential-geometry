import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem WindowedModelWitness.comparison_jet_zero_contDiffWithinAt
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    {s : ℝ} (hs : s ∈ Ioc (-modelDepth delta) 0) (y : W.model.M)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)) (v : Fin 2 → TangentSpace I3 y) :
    ContDiffWithinAt ℝ ∞ (fun r => W.comparison.jet 0 r y v)
      (Icc (-modelDepth delta) 0) s := by
  let a : ℝ := -modelDepth delta
  let c : ℝ := (a + s) / 2
  let Q : ℝ := S.scalar t x
  have hQ : 0 < Q := W.scalar_pos
  have hac : a < c := by dsimp [a, c]; linarith [hs.1]
  have hcs : c < s := by dsimp [a, c]; linarith [hs.1]
  have hc : c < 0 := lt_of_lt_of_le hcs hs.2
  have htac : parabolicTime t Q a < parabolicTime t Q c := by
    dsimp only [parabolicTime]
    linarith [div_lt_div_of_pos_right hac hQ]
  have hct : parabolicTime t Q c < t := by
    dsimp only [parabolicTime]
    have hh := div_neg_of_neg_of_pos hc hQ
    linarith
  have hstart : parabolicTime t Q a = t - (delta * S.scalar t x)⁻¹ := by
    simp only [parabolicTime, a, Q, modelDepth, mul_inv, div_eq_mul_inv, neg_mul,
      sub_eq_add_neg]
  have hslab : Icc (parabolicTime t Q a) t ⊆ D.carrier := by
    rw [hstart]
    exact W.window_mem
  have hreg' : Ioo (parabolicTime t Q a) t ⊆ D.regular := by
    intro r hr
    have hleft : a < (r - t) * Q := by
      apply (div_lt_iff₀ hQ).mp
      have hr1 : t + a / Q < r := hr.1
      linarith
    have hright : (r - t) * Q < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hr.2) hQ
    have hh := hreg ((r - t) * Q) ⟨hleft, hright⟩
    have heq : parabolicTime t (S.scalar t x) ((r - t) * Q) = r := by
      change t + ((r - t) * Q) / Q = r
      rw [mul_div_cancel_right₀ _ hQ.ne']
      ring
    rwa [heq] at hh
  let w : Fin 2 → TangentSpace I3 (W.embedding y) :=
    fun j => mfderiv I3 I3 W.embedding y (v j)
  have hsource0 := (tensor0SEvalCLM (I := I3) (x := W.embedding y) w).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time S hS htac hct hslab hreg' (W.embedding y))
  have htime : ContDiff ℝ ∞ (parabolicTime t Q) :=
    contDiff_const.add (contDiff_id.div_const Q)
  have hmap : MapsTo (parabolicTime t Q) (Icc c 0) (Icc (parabolicTime t Q c) t) := by
    intro r hr
    constructor
    · dsimp only [parabolicTime]
      linarith [div_le_div_of_nonneg_right hr.1 hQ.le]
    · change t + r / Q ≤ t
      exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hr.2 hQ.le)
  have hsource : ContDiffOn ℝ ∞
      (fun r => (S.base.metric (parabolicTime t Q r)).inner (W.embedding y) (w 0) (w 1))
      (Icc c 0) := by
    have hh := hsource0.comp htime.contDiffOn hmap
    change ContDiffOn ℝ ∞
      (fun r => metricTensorField (S.base.metric (parabolicTime t Q r)) (W.embedding y) w)
      (Icc c 0) at hh
    simpa only [metricTensorField_apply] using hh
  have hscaled : ContDiffOn ℝ ∞
      (fun r => (rescaledMetric S t (S.scalar t x) W.scalar_pos r).inner
        (W.embedding y) (w 0) (w 1)) (Icc c 0) := by
    simpa only [rescaledMetric, scaleMetric_inner, SolutionOn.family,
      Function.comp_def, smul_eq_mul, Q] using hsource.const_smul Q
  have hpull : ContDiffOn ℝ ∞ (fun r => W.comparison.pullback r y v) (Icc c 0) :=
    hscaled.congr (fun r _ => W.comparison.pullback_eq r y hy v)
  have hmodel0 := (tensor0SEvalCLM (I := I3) (x := y) v).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time W.model.S W.model.isSolution hac hc
      (fun _ hr => hr.2) (fun _ hr => hr.2) y)
  have hmodel : ContDiffOn ℝ ∞
      (fun r => (W.model.S.base.metric r).inner y (v 0) (v 1)) (Icc c 0) := by
    change ContDiffOn ℝ ∞
      (fun r => metricTensorField (W.model.S.base.metric r) y v) (Icc c 0) at hmodel0
    simpa only [metricTensorField_apply] using hmodel0
  have hzero : ContDiffOn ℝ ∞ (fun r => W.comparison.jet 0 r y v) (Icc c 0) :=
    (hpull.sub hmodel).congr (fun r _ => W.comparison.jet_zero r y v)
  apply (hzero s ⟨hcs.le, hs.2⟩).congr_set
  filter_upwards [Ioi_mem_nhds hcs] with r hr
  apply propext
  change (c ≤ r ∧ r ≤ 0) ↔ (-modelDepth delta ≤ r ∧ r ≤ 0)
  have hcr : c < r := hr
  have har : -modelDepth delta < r := hac.trans hcr
  simp only [hcr.le, har.le, true_and]

theorem WindowedModelWitness.comparison_jet_contDiffWithinAt
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (q : ℕ) {s : ℝ} (hs : s ∈ Ioc (-modelDepth delta) 0) (y : W.model.M)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)) (v : Fin 2 → TangentSpace I3 y) :
    ContDiffWithinAt ℝ ∞ (fun r => W.comparison.jet q r y v)
      (Icc (-modelDepth delta) 0) s := by
  have hdepth : -modelDepth delta < 0 := neg_lt_zero.mpr (inv_pos.mpr W.eps_pos)
  exact DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
    (f := fun b r => W.comparison.jet b r y v)
    (uniqueDiffOn_Icc hdepth) ⟨hs.1.le, hs.2⟩
    (W.comparison_jet_zero_contDiffWithinAt hS hreg hs y hy v)
    (fun b r hr => W.comparison.jet_succ b r hr y hy v) q

theorem WindowedModelWitness.hasDerivWithinAt_comparison_jet
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (q : ℕ) {s : ℝ} (hs : s ∈ Ioc (-modelDepth delta) 0) (y : W.model.M)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)) (v : Fin 2 → TangentSpace I3 y) :
    HasDerivWithinAt (fun r => W.comparison.jet q r y v)
      (W.comparison.jet (q + 1) s y v) (Icc (-modelDepth delta) 0) s := by
  rw [W.comparison.jet_succ q s ⟨hs.1.le, hs.2⟩ y hy v]
  exact ((W.comparison_jet_contDiffWithinAt hS hreg q hs y hy v).differentiableWithinAt
    (by simp)).hasDerivWithinAt

theorem WindowedModelWitness.hasDerivWithinAt_comparison_jet_unit
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (q : ℕ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0) (y : W.model.M)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)) (v : Fin 2 → TangentSpace I3 y) :
    HasDerivWithinAt (fun r => W.comparison.jet q r y v)
      (W.comparison.jet (q + 1) s y v) (Icc (-1 : ℝ) 0) s := by
  have hdepth : 1 < modelDepth delta := (one_lt_inv₀ W.eps_pos).mpr W.eps_lt_one
  have hs' : s ∈ Ioc (-modelDepth delta) 0 := ⟨by linarith [hs.1], hs.2⟩
  apply (W.hasDerivWithinAt_comparison_jet hS hreg q hs' y hy v).mono
  intro r hr
  exact ⟨by linarith [hr.1], hr.2⟩

private theorem StrongNeck.comparison_jet_zero_contDiffOn_of_ancient
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t)
    (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)
    (v : Fin 2 → TangentSpace IC y) :
    ContDiffOn ℝ ∞ (fun s => nk.comparison.jet 0 s y v) (Icc (-1 : ℝ) 0) := by
  let Q : ℝ := S.scalar t x
  have hQ : 0 < Q := nk.Q_pos
  have ht : t ≤ 0 := nk.time_domain
    ⟨sub_le_self _ (inv_nonneg.mpr hQ.le), le_rfl⟩
  have hac : parabolicTime t Q (-2) < parabolicTime t Q (-1) := by
    dsimp only [parabolicTime]
    have hh := div_lt_div_of_pos_right (by norm_num : (-2 : ℝ) < -1) hQ
    linarith
  have hct : parabolicTime t Q (-1) < t := by
    dsimp only [parabolicTime]
    have hh := div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hQ
    linarith
  let w : Fin 2 → TangentSpace I3 (nk.map y) := fun j => mfderiv IC I3 nk.map y (v j)
  have hsource0 := (tensor0SEvalCLM (I := I3) (x := nk.map y) w).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time S hS hac hct
      (fun _ hr => hr.2.trans ht) (fun _ hr => hr.2.trans_le ht) (nk.map y))
  have htime : ContDiff ℝ ∞ (parabolicTime t Q) :=
    contDiff_const.add (contDiff_id.div_const Q)
  have hmap : MapsTo (parabolicTime t Q) (Icc (-1 : ℝ) 0)
      (Icc (parabolicTime t Q (-1)) t) := by
    intro r hr
    constructor
    · dsimp only [parabolicTime]
      linarith [div_le_div_of_nonneg_right hr.1 hQ.le]
    · change t + r / Q ≤ t
      exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hr.2 hQ.le)
  have hsource : ContDiffOn ℝ ∞
      (fun r => (S.base.metric (parabolicTime t Q r)).inner (nk.map y) (w 0) (w 1))
      (Icc (-1 : ℝ) 0) := by
    have hh := hsource0.comp htime.contDiffOn hmap
    change ContDiffOn ℝ ∞
      (fun r => metricTensorField (S.base.metric (parabolicTime t Q r)) (nk.map y) w)
      (Icc (-1 : ℝ) 0) at hh
    simpa only [metricTensorField_apply] using hh
  have hscaled : ContDiffOn ℝ ∞
      (fun r => (rescaledMetric S t (S.scalar t x) nk.Q_pos r).inner
        (nk.map y) (w 0) (w 1)) (Icc (-1 : ℝ) 0) := by
    simpa only [rescaledMetric, scaleMetric_inner, SolutionOn.family,
      Function.comp_def, smul_eq_mul, Q] using hsource.const_smul Q
  have hpull : ContDiffOn ℝ ∞ (fun r => nk.comparison.pullback r y v) (Icc (-1 : ℝ) 0) :=
    hscaled.congr (fun r _ => nk.comparison.pullback_eq r y hy v)
  have hcylinder : ContDiffOn ℝ ∞
      (fun r => (nk.cylinder.metric r).inner y (v 0) (v 1)) (Icc (-1 : ℝ) 0) := by
    have hh : ContDiff ℝ ∞ (fun r : ℝ =>
        2 * (1 - r) * inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 (v 0).1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 (v 1).1) +
            (v 0).2 * (v 1).2) := by fun_prop
    exact hh.contDiffOn.congr (fun r hr => nk.cylinder.inner_eq r hr.2 y (v 0) (v 1))
  exact (hpull.sub hcylinder).congr (fun r _ => nk.comparison.jet_zero r y v)

theorem StrongNeck.comparison_jet_contDiffOn_of_ancient
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t)
    (q : ℕ) (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)
    (v : Fin 2 → TangentSpace IC y) :
    ContDiffOn ℝ ∞ (fun s => nk.comparison.jet q s y v) (Icc (-1 : ℝ) 0) := by
  intro s hs
  exact DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
    (f := fun b r => nk.comparison.jet b r y v)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hs
    (nk.comparison_jet_zero_contDiffOn_of_ancient hS y hy v s hs)
    (fun b r hr => nk.comparison.jet_succ b r hr y hy v) q

theorem StrongNeck.hasDerivWithinAt_comparison_jet_of_ancient
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t)
    (q : ℕ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0)
    (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)
    (v : Fin 2 → TangentSpace IC y) :
    HasDerivWithinAt (fun r => nk.comparison.jet q r y v)
      (nk.comparison.jet (q + 1) s y v) (Icc (-1 : ℝ) 0) s := by
  rw [nk.comparison.jet_succ q s hs y hy v]
  exact ((nk.comparison_jet_contDiffOn_of_ancient hS q y hy v s hs).differentiableWithinAt
    (by simp)).hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
