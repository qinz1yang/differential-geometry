import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeScaling
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Collapse.AnnularAdaptedCoordinates

/-!
# Inward minimizing directions at a rescaled metric (LC54/LC55 at scale `R`)

Master207A, A:22905 (LC55) and its use in LC57 at a fixed scale `R`: the normalized model is
`(N, R⁻¹ d, R⁻² g)`, realized by the instances `m.rescale R⁻¹`, `radialScaledBundle g R⁻¹`,
`radialScaledContinuous`, `radialScaledManifold` (`AnnularAdaptedCoordinates.lean`). Constant
scaling does not change the Christoffel symbols, hence not the geodesics; with `d_R = R⁻¹ d` and the
reparametrization `γ_{c v}(s) = γ_v(c s)` (`intrinsicGeo_smul_apply`), the inward unit minimizing
directions of the rescaled metric are `R` times those of `g`:
`v ∈ 𝒰_R(n, q) ↔ R⁻¹ v ∈ 𝒰(n, q)`.

* `chartChristoffel_scaleMetric`, `chartChristoffelContraction_scaleMetric`,
  `isGeodesic_scaleMetric_iff`: the geodesic equation is scale invariant.
* `intrinsicGeodesic_radialScaled_eq`: the intrinsic geodesics of `R⁻² g` (rescaled instances)
  are those of `g`.
* `mem_inwardMinimizingDirections_radialScaled_iff`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

section Christoffel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartGram_scale' (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ x : M) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (scaleMetric (I := I) c hc g)
        x₀ x =
      c • DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x := by
  ext i j
  simp [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]

private theorem chartInvGram_scale' (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ x : M) :
    chartInvGramMatrix (I := I) (scaleMetric (I := I) c hc g) x₀ x =
      c⁻¹ • chartInvGramMatrix (I := I) g x₀ x := by
  let A := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x
  have hc₀ : c ≠ 0 := ne_of_gt hc
  change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
    (scaleMetric (I := I) c hc g) x₀ x)⁻¹ = c⁻¹ • A⁻¹
  rw [chartGram_scale' (I := I) c hc g x₀ x]
  by_cases hA : IsUnit A.det
  · let : Invertible c := invertibleOfNonzero hc₀
    simpa only [invOf_eq_inv] using Matrix.inv_smul A c hA
  · have hscaled : ¬IsUnit (c • A).det := by
      simpa [Matrix.det_smul, isUnit_iff_ne_zero, hc₀] using hA
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ hA, smul_zero]

private theorem partialDeriv_const_mul_ne' (c : ℝ) (hc : c ≠ 0) (u : E → ℝ)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun z => c * u z) y =
      c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u y := by
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  by_cases hu : DifferentiableAt ℝ u y
  · rw [fderiv_const_mul hu c]
    simp
  · have hcu : ¬DifferentiableAt ℝ (fun z => c * u z) y := by
      intro h
      have hinv : DifferentiableAt ℝ (fun z => c⁻¹ * (c * u z)) y := h.const_mul c⁻¹
      have heq : (fun z => c⁻¹ * (c * u z)) = u := by
        funext z
        field_simp [hc]
      exact hu (by simpa only [heq] using hinv)
    rw [fderiv_zero_of_not_differentiableAt hu, fderiv_zero_of_not_differentiableAt hcu]
    simp

private theorem chartGramOnE_scale' (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) (scaleMetric (I := I) c hc g) x₀ i j =
      fun y => c * chartGramOnE (I := I) g x₀ i j y := by
  funext y
  simp [chartGramOnE, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
    scaleMetric_inner]

/-- Constant scaling does not change the chart Christoffel symbols. -/
theorem chartChristoffel_scaleMetric (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x₀ : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) (scaleMetric (I := I) c hc g) x₀ i j k y =
      chartChristoffel (I := I) g x₀ i j k y := by
  classical
  have hc₀ : c ≠ 0 := ne_of_gt hc
  rw [chartChristoffel_def, chartChristoffel_def]
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro l _
  rw [chartInvGram_scale' (I := I) c hc g, chartGramOnE_scale' (I := I) c hc g x₀ l j,
    chartGramOnE_scale' (I := I) c hc g x₀ l i, chartGramOnE_scale' (I := I) c hc g x₀ i j,
    partialDeriv_const_mul_ne' c hc₀, partialDeriv_const_mul_ne' c hc₀,
    partialDeriv_const_mul_ne' c hc₀]
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp [hc₀]

/-- Constant scaling does not change the Christoffel contraction of the geodesic equation. -/
theorem chartChristoffelContraction_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w y : E) :
    chartChristoffelContraction (I := I) (scaleMetric (I := I) c hc g) x₀ v w y =
      chartChristoffelContraction (I := I) g x₀ v w y := by
  classical
  unfold chartChristoffelContraction
  simp_rw [chartChristoffel_scaleMetric (I := I) c hc g]

/-- The geodesic equation is invariant under constant scaling of the metric. -/
theorem isGeodesic_scaleMetric_iff (c : ℝ) (hc : 0 < c) {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} :
    IsGeodesic (I := I) (scaleMetric (I := I) c hc g) γ ↔ IsGeodesic (I := I) g γ := by
  unfold IsGeodesic HasGeodesicEquationAt
  simp only [chartChristoffelContraction_scaleMetric (I := I) c hc g]

end Christoffel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] hM in
/-- On a Riemannian manifold whose bundle metric is `g`, the metric-space distance realizes the
`g`-length distance. -/
theorem riemannianEDistOf_eq_ofReal_dist (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (a b : M) :
    riemannianEDistOf g a b = ENNReal.ofReal (dist a b) := by
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm, ← IsRiemannianManifold.out (I := I),
    edist_dist]

/-- A continuous geodesic of a constant multiple of `g` with initial data `(p, v)` is the
intrinsic geodesic of `g` with that initial data. -/
theorem eq_intrinsicGeodesic_of_isGeodesic_scaleMetric
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {c : ℝ}
    (hc : 0 < c) {p : M} {v : TangentSpace I p} {Γ : ℝ → M}
    (hΓ : IsGeodesic (I := I) (scaleMetric c hc g) Γ) (hcont : Continuous Γ) (h0 : Γ 0 = p)
    (hv : (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) = (v : E)) :
    Γ = intrinsicGeodesic (I := I) g hEnorm p v :=
  isGeodesic_eq_of_initial (I := I) g ((isGeodesic_scaleMetric_iff c hc).mp hΓ)
    (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v) hcont
    (intrinsicGeodesic_continuous (I := I) g hEnorm p v)
    (h0.trans (intrinsicGeodesic_zero (I := I) g hEnorm p v).symm)
    (hv.trans (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v).symm)

/-- The rescaled intrinsic geodesic is a geodesic of the scaled tensor (stated for the original
smooth structure). -/
theorem isGeodesic_radialScaled_intrinsicGeodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) (p : M)
    (v : TangentSpace I p) :
    IsGeodesic (I := I) (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g)
      (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic (I := I) gR hnR p v) := by
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  let := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
  let : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
  let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  exact intrinsicGeodesic_isGeodesic (I := I) gR hnR p v

/-- The rescaled intrinsic geodesic is continuous. -/
theorem continuous_radialScaled_intrinsicGeodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) (p : M)
    (v : TangentSpace I p) :
    Continuous (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic (I := I) gR hnR p v) := by
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  let := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
  let : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
  let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  exact intrinsicGeodesic_continuous (I := I) gR hnR p v

/-- The rescaled intrinsic geodesic starts at `p`. -/
theorem radialScaled_intrinsicGeodesic_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) (p : M)
    (v : TangentSpace I p) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic (I := I) gR hnR p v) 0 = p := by
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  let := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
  let : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
  let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  exact intrinsicGeodesic_zero (I := I) gR hnR p v

/-- The rescaled intrinsic geodesic has initial velocity `v`. -/
theorem radialScaled_intrinsicGeodesic_mfderiv_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) (p : M)
    (v : TangentSpace I p) :
    (mfderiv 𝓘(ℝ, ℝ) I (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic (I := I) gR hnR p v) 0 (1 : ℝ) : E) = (v : E) := by
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  let := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
  let : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
  let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  exact intrinsicGeodesic_mfderiv_zero (I := I) gR hnR p v

/-- **The intrinsic geodesics of `R⁻² g` are those of `g`.** With the rescaled instances
(`m.rescale R⁻¹`, `radialScaledBundle g R⁻¹`, …) the intrinsic geodesic of the scaled tensor with
initial velocity `v` is the intrinsic geodesic of `g` with the same initial velocity. -/
theorem intrinsicGeodesic_radialScaled_eq (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) (p : M)
    (v : TangentSpace I p) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic (I := I) gR hnR p v) =
      intrinsicGeodesic (I := I) g hEnorm p v :=
  eq_intrinsicGeodesic_of_isGeodesic_scaleMetric g hEnorm _
    (isGeodesic_radialScaled_intrinsicGeodesic g hEnorm hR p v)
    (continuous_radialScaled_intrinsicGeodesic g hEnorm hR p v)
    (radialScaled_intrinsicGeodesic_zero g hEnorm hR p v)
    (radialScaled_intrinsicGeodesic_mfderiv_zero g hEnorm hR p v)

/-- **Inward minimizing directions at the rescaled metric.** With the rescaled instances, `v` is
an inward unit minimizing direction of `R⁻² g` at `q` toward `n` iff `R⁻¹ v` is one of `g`. -/
theorem mem_inwardMinimizingDirections_radialScaled_iff {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g} {R : ℝ} (hR : 0 < R) {n q : M}
    {v : TangentSpace I q} :
    R⁻¹ • v ∈ inwardMinimizingDirections (I := I) g hEnorm n q ↔
      (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
      letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold I M :=
        radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
      let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
      v ∈ inwardMinimizingDirections (I := I) gR hnR n q) := by
  have hgeo := intrinsicGeodesic_radialScaled_eq g hEnorm hR q v
  have hinner : g.inner q (R⁻¹ • v) (R⁻¹ • v) =
      (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner q v v := by
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  have hsmul := intrinsicGeo_smul_apply (I := I) g hEnorm q v R⁻¹ (dist n q)
  calc R⁻¹ • v ∈ inwardMinimizingDirections (I := I) g hEnorm n q
      ↔ g.inner q (R⁻¹ • v) (R⁻¹ • v) = 1 ∧
          intrinsicGeodesic (I := I) g hEnorm q (R⁻¹ • v) (dist n q) = n := Iff.rfl
    _ ↔ (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner q v v = 1 ∧
          intrinsicGeodesic (I := I) g hEnorm q v (R⁻¹ * dist n q) = n := by
        rw [hinner, hsmul]
    _ ↔ _ := by
        rw [← hgeo]
        exact Iff.rfl

end DifferentialGeometry.Geometry.Collapse
