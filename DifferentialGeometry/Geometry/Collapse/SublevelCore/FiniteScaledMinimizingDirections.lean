import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature

/-!
# Minimizing directions of a rescaled finite-order metric (LC55 at scale `R`, finite case)

Finite-order analogue of LC5X's `mem_inwardMinimizingDirections_radialScaled_iff`
(SublevelCore/ScaledMinimizingDirections.lean), the GAP B lemma of sheet-LC5X.md for a limit metric
`G` of finite order. Lane F8-NEW2, task 6.

* `finiteScaleMetric c hc G`: the metric `c • G` of the same order (the finite-order twin of
  `scaleMetric`; for a smooth metric the two agree, `finiteScaleMetric_eq_scaleMetric`).
* `metricSpray_const_smul_of_isCoercive`: a constant positive factor does not change the metric
  spray of chart coefficients (the Christoffel symbols are scale invariant).
* `geodesicSpray_finiteScaleMetric`, `geodesicFlow_finiteScaleMetric`,
  `expMap_finiteScaleMetric`: hence `c • G` and `G` have the same geodesic spray, flow and
  exponential map.
* `finiteMinimizingDirectionsTo_scaleMetric`: `R⁻¹ • v` is a minimizing unit direction of `G`
  from `q` to `{n}` iff `v` is one of `R⁻² • G` in the rescaled metric space `(M, R⁻¹ d)`, the
  shape of LC5X's smooth lemma (only the rescaled metric space is needed: the finite direction
  set uses no bundle instances).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The metric `c • G` of the same (finite) order. -/
def finiteScaleMetric {n : ℕ∞ω} (c : ℝ) (hc : 0 < c)
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) where
  inner x := c • G.inner x
  symm x v w := by
    simp [smul_apply, smul_eq_mul, G.symm x v w]
  pos x v hv := by
    simpa [smul_apply, smul_eq_mul] using mul_pos hc (G.pos x v hv)
  isVonNBounded x := by
    by_cases hlarge : 1 ≤ c
    · refine (G.isVonNBounded x).subset ?_
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv ⊢
      by_cases hv0 : v = 0
      · simp [hv0]
      · have hpos := G.pos x v hv0
        simp only [smul_apply, smul_eq_mul] at hv
        nlinarith
    · have hsmall : c < 1 := lt_of_not_ge hlarge
      let L : TangentSpace I x →L[ℝ] TangentSpace I x :=
        c⁻¹ • (1 : TangentSpace I x →L[ℝ] TangentSpace I x)
      refine ((G.isVonNBounded x).image L).subset ?_
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      refine ⟨c • v, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        simp only [smul_apply, smul_eq_mul] at hv
        have hscale : G.inner x (c • v) (c • v) = c * (c * G.inner x v v) := by
          simp [smul_eq_mul]
        rw [hscale]
        nlinarith
      · calc
          L (c • v) = c⁻¹ • (c • v) := by
            simp [L, smul_smul, mul_comm]
          _ = v := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  contMDiff := by
    let _ : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := fun _ => inferInstance
    simpa only [Pi.smul_apply] using
      (G.contMDiff.const_smul_section (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (a := c))

@[simp] theorem finiteScaleMetric_inner {n : ℕ∞ω} (c : ℝ) (hc : 0 < c)
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    (finiteScaleMetric c hc G).inner x v w = c * G.inner x v w :=
  rfl

/-- For a smooth metric the finite-order scaling is `scaleMetric`. -/
theorem finiteScaleMetric_eq_scaleMetric (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    finiteScaleMetric c hc g = scaleMetric c hc g :=
  rfl

end DifferentialGeometry

namespace DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ContinuousDualEquiv E]
  [CompleteSpace E] [CoerciveBilinInverse E]

private local instance scaledSprayDualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance scaledSprayDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance scaledSprayBilinNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance scaledSprayBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance scaledSprayTriNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance scaledSprayTriNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **The metric spray is scale invariant.** -/
theorem metricSpray_const_smul_of_isCoercive {c : ℝ} (hc : 0 < c)
    (φ : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E × E) (hφ : IsCoercive (φ z.1)) :
    metricSpray (fun x => c • φ x) z = metricSpray φ z := by
  have hcφ : IsCoercive (c • φ z.1) := by
    obtain ⟨κ, hκ, hκu⟩ := hφ
    refine ⟨c * κ, mul_pos hc hκ, fun u => ?_⟩
    have h := hκu u
    simp only [smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h hc.le]
  have hD : fderiv ℝ (fun x => c • φ x) z.1 = c • fderiv ℝ φ z.1 :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := φ) c) z.1
  rw [metricSpray_eq φ z hφ, metricSpray_eq (fun x => c • φ x) z hcφ]
  congr 2
  rw [hD]
  apply hcφ.bilin_injective
  rw [apply_koszul_vec]
  ext w
  simp only [smul_apply, apply_koszul_vec, koszul_cov_apply, smul_eq_mul]
  ring

end DifferentialGeometry.MetricKoszul

section Spray

namespace Bundle.ContMDiffRiemannianMetric

open DifferentialGeometry.MetricKoszul (metricSpray metricSpray_const_smul_of_isCoercive)
open private pullbackCoefficients from DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance scaledSprayDualEquiv : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- `c • G` and `G` have the same geodesic spray. -/
theorem geodesicSpray_finiteScaleMetric {n : ℕ∞ω} (c : ℝ) (hc : 0 < c)
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    (DifferentialGeometry.finiteScaleMetric c hc G).geodesicSpray = G.geodesicSpray := by
  funext p
  have hco : IsCoercive
      (pullbackCoefficients G (extChartAt I p.proj).symm (extChartAt I p.proj p.proj)) :=
    DifferentialGeometry.Geometry.MetricSmoothing.isCoercive_chartCoeff G p.proj
      (mem_extChartAt_target p.proj)
  have hcoef : pullbackCoefficients (DifferentialGeometry.finiteScaleMetric c hc G)
      (extChartAt I p.proj).symm =
      fun x => c • pullbackCoefficients G (extChartAt I p.proj).symm x := by
    funext x
    rfl
  change metricSpray (pullbackCoefficients (DifferentialGeometry.finiteScaleMetric c hc G)
      (extChartAt I p.proj).symm) (extChartAt I p.proj p.proj, p.snd) =
    metricSpray (pullbackCoefficients G (extChartAt I p.proj).symm)
      (extChartAt I p.proj p.proj, p.snd)
  rw [hcoef]
  exact metricSpray_const_smul_of_isCoercive hc _ _ hco

/-- `c • G` and `G` have the same geodesic flow. -/
theorem geodesicFlow_finiteScaleMetric {n : ℕ∞ω} (c : ℝ) (hc : 0 < c)
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    (DifferentialGeometry.finiteScaleMetric c hc G).geodesicFlow = G.geodesicFlow := by
  funext p t
  unfold geodesicFlow
  rw [geodesicSpray_finiteScaleMetric]

/-- `c • G` and `G` have the same exponential map. -/
theorem expMap_finiteScaleMetric {n : ℕ∞ω} (c : ℝ) (hc : 0 < c)
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    (DifferentialGeometry.finiteScaleMetric c hc G).expMap = G.expMap := by
  funext p
  unfold expMap
  rw [geodesicFlow_finiteScaleMetric]

end Bundle.ContMDiffRiemannianMetric

end Spray

namespace DifferentialGeometry.Geometry.Collapse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Minimizing directions of the rescaled finite metric** (finite analogue of
`mem_inwardMinimizingDirections_radialScaled_iff`): `R⁻¹ • v` is a minimizing unit direction of
`G` from `q` to `{o}` iff `v` is one of `R⁻² • G` in the rescaled metric space `(M, R⁻¹ d)`. -/
theorem finiteMinimizingDirectionsTo_scaleMetric {n : ℕ∞ω}
    {G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)} {R : ℝ} (hR : 0 < R)
    {o q : M} {v : TangentSpace I q} :
    R⁻¹ • v ∈ G.finiteMinimizingDirectionsTo {o} q ↔
      (letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      let GR := finiteScaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) G
      v ∈ GR.finiteMinimizingDirectionsTo {o} q) := by
  have hinf : @Metric.infDist M (m.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace q {o} =
      R⁻¹ * Metric.infDist q {o} := by
    rw [@Metric.infDist_singleton M (m.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace,
      Metric.infDist_singleton]
    rfl
  have hinner : G.inner q (R⁻¹ • v) (R⁻¹ • v) = R⁻¹ ^ 2 * G.inner q v v := by
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hexp : (finiteScaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) G).expMap = G.expMap :=
    Bundle.ContMDiffRiemannianMetric.expMap_finiteScaleMetric _ _ G
  change (G.inner q (R⁻¹ • v) (R⁻¹ • v) = 1 ∧
      G.expMap (⟨q, Metric.infDist q {o} • R⁻¹ • v⟩ : TangentBundle I M) ∈ ({o} : Set M)) ↔
    (R⁻¹ ^ 2 * G.inner q v v = 1 ∧
      (finiteScaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) G).expMap
        (⟨q, @Metric.infDist M (m.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace q {o} • v⟩ :
          TangentBundle I M) ∈ ({o} : Set M))
  rw [hexp, hinf, hinner, smul_smul, mul_comm (Metric.infDist q {o}) R⁻¹]

end DifferentialGeometry.Geometry.Collapse
