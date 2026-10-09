import DifferentialGeometry.Geometry.Collapse.AnnularDirections
import DifferentialGeometry.Geometry.Collapse.DistancePerturbationGradient

/-!
# LC30: the radial function at a supplied cone scale (unconditional tiers)

Blueprint 207A, LC30 (`thm:collapse-radial-function`, A:21214–21268), with
`U = {1/20 < d_p < 20}` and `C = {1/10 ≤ d_p ≤ 10}`. The blueprint's proof is LC27 (verifying the
hypothesis of the smoothing input LC28 on `U`), then LC28 (producing `F`), then LC29. LC28 is a
separate foundation (lane W3-LC28). This file proves the two unconditional tiers, against the
exact LC28 output form recorded in `build-logs/resume/sheet-W3-F4.md` (Addendum 1):

* tier 1, `minimizingDirectionsTo_pairwise_lt_of_kleinerLottApprox`: for every `θ > 0` and every
  error below the explicit `radialSmoothingConeError θ`, the minimizing directions to `p` at
  every point of `U` are pairwise `θ`-close (LC28's hypothesis with `Y = {p}`);
* tier 2, `radialFunction_of_smoothing`: every `F` with LC28's four output clauses for
  `Y = {p}`, `U`, `C`, `e < 1/40`, `ε < 1` is an LC30 radial function: nonnegative, zero at `p`,
  `1 - ε ≤ ‖∇F‖ ≤ 1 + ε` on `C`, its level band `F⁻¹[1/5, 2]` lies in `{1/5 - e < d_p < 2 + e} ⊆ C`
  and has an open neighbourhood on which `F` is smooth without critical points.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

/-- The explicit LC30 cone-error threshold attached to a direction-diameter budget `θ`: LC27's
bound with `a = 1/20`, `b = 20` and `τ = min (π/4) (θ/4)`. -/
def radialSmoothingConeError (θ : ℝ) : ℝ :=
  min (1 / 600) ((1 - Real.cos (min (π / 4) (θ / 4))) / 1800)

theorem radialSmoothingConeError_pos {θ : ℝ} (hθ : 0 < θ) : 0 < radialSmoothingConeError θ := by
  have hτ : 0 < min (π / 4) (θ / 4) := lt_min (by positivity) (by positivity)
  have hτπ : min (π / 4) (θ / 4) < 2 * π := by
    linarith [min_le_left (π / 4) (θ / 4), Real.pi_pos]
  have hcos : Real.cos (min (π / 4) (θ / 4)) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
      (by linarith [min_le_left (π / 4) (θ / 4), Real.pi_pos]) hτ
  unfold radialSmoothingConeError
  exact lt_min (by norm_num) (by linarith [hcos])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC30, tier 1 (LC28's hypothesis on `U`): with `sec ≥ -(1/60)²` on `B(p, 400)` and an actual
pointed Kleiner–Lott map to an AC82 cone with error below `radialSmoothingConeError θ`, the
initial unit velocities of minimizing segments to `p` are pairwise `θ`-close at every point of
`U = {1/20 < d_p < 20}`. -/
theorem minimizingDirectionsTo_pairwise_lt_of_kleinerLottApprox (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ θ : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2))
    (hθ : 0 < θ) (hδ : δ < radialSmoothingConeError θ) :
    ∀ q ∈ {x : M | 1 / 20 < dist x p ∧ dist x p < 20},
      ∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, ∀ v' ∈ minimizingDirectionsTo g hEnorm {p} q,
        Real.sqrt (g.inner q (v - v') (v - v')) < θ := by
  intro q hq v hv v' hv'
  set τ := min (π / 4) (θ / 4) with hτ_def
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτπ : τ < π / 2 := by linarith [min_le_left (π / 4) (θ / 4), Real.pi_pos]
  have hδ1 : δ < 1 / 600 := hδ.trans_le (min_le_left _ _)
  have hδ2 : δ < (1 - Real.cos τ) / 1800 := hδ.trans_le (min_le_right _ _)
  obtain ⟨w, -, -, -, hdiam, hsin⟩ := exists_outward_unit_direction_of_kleinerLottApprox g hEnorm
    φ H (a := 1 / 20) (b := 20) (κ := 1 / 60) (τ := τ) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (20 : ℝ) * 20 = 400 by norm_num] using hsec) hτ hτπ
    (by linarith) (by linarith) (by linarith)
    ⟨by rw [dist_comm]; exact hq.1.le, by rw [dist_comm]; exact hq.2.le⟩
  have h := hdiam v hv v' hv'
  have hτθ : τ ≤ θ / 4 := min_le_right _ _
  linarith

/-- LC30, tier 2 (post-smoothing): any `F` satisfying LC28's four output clauses for `Y = {p}`,
`U = {1/20 < d_p < 20}`, `C = {1/10 ≤ d_p ≤ 10}`, value error `e < 1/40` and difference
Lipschitz constant `0 ≤ ε < 1` is an LC30 radial function. -/
theorem radialFunction_of_smoothing (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) {ε e : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (he : e < 1 / 40) {F : M → ℝ} {O : Set M}
    (hO : IsOpen O) (hCO : {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O)
    (hFO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O)
    (hclose : ∀ x, |F x - Metric.infDist x {p}| < e)
    (hout : ∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p})
    (hlip : ∀ x y,
      |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) :
    (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
    (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
      1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
        Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε) ∧
    (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
    F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
    ∃ O' : Set M, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun g F q ≠ 0 := by
  simp only [Metric.infDist_singleton] at hclose hout hlip
  have hgrad : ∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
      1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
        Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε := by
    intro q hq
    have hqp : q ≠ p := by
      rintro rfl
      have h1 := hq.1
      rw [dist_self] at h1
      norm_num at h1
    exact one_sub_le_norm_gradFun_and_le_one_add g hEnorm p hε hlip hqp
      ((hFO.contMDiffAt (hO.mem_nhds (hCO hq))).mdifferentiableAt (by simp))
  have hband : ∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e := by
    intro x hx
    have h := abs_lt.mp (hclose x)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hepos : 0 < e := (abs_nonneg _).trans_lt (hclose p)
  refine ⟨fun x => ?_, ?_, hgrad, hband, fun x hx => ?_, ?_⟩
  · by_cases hx : x ∈ {x : M | 1 / 20 < dist x p ∧ dist x p < 20}
    · have h := abs_lt.mp (hclose x)
      linarith [hx.1]
    · rw [hout x hx]
      exact dist_nonneg
  · have hp : p ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} := by
      intro hp
      have h1 := hp.1
      rw [dist_self] at h1
      norm_num at h1
    rw [hout p hp, dist_self]
  · obtain ⟨h1, h2⟩ := hband x hx
    exact ⟨by linarith, by linarith⟩
  · refine ⟨{x : M | 1 / 10 < dist x p ∧ dist x p < 10}, ?_, fun x hx => ?_, ?_, ?_⟩
    · exact (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
        (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
    · obtain ⟨h1, h2⟩ := hband x hx
      exact ⟨by linarith, by linarith⟩
    · exact hFO.mono fun x hx => hCO ⟨hx.1.le, hx.2.le⟩
    · intro q hq hzero
      have h := (hgrad q ⟨hq.1.le, hq.2.le⟩).1
      rw [hzero] at h
      simp only [map_zero, Real.sqrt_zero] at h
      linarith

end DifferentialGeometry.Geometry.Collapse
