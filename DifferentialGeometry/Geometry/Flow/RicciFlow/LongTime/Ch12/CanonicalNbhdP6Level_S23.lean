import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Seed_S23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerRicci_S21
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm

/-!
# CH12-S23 / K3, group L: static lemmas

* `scalar_neg_of_defect_S23`: normalised Ricci defect `< 1` forces negative scalar curvature.
* `exists_level_point_S23`: intermediate value along the (path-connected) ball.
* `seed_of_witness_S23`: a (non-round) canonical witness at `z` gives a normalised seed of constants
  depending only on `(ε, C₁, C₂, t R(z))`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

section Static

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem scalar_neg_of_defect_S23 (g : SmoothRiemannianMetric ThreeModel M) (p : M)
    (hdef : sSup (defectSet_O5 g p) < 1) : metricScalarAt g p < 0 := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel p) = 3 := finrank_euclideanSpace_fin
  obtain ⟨basis, -, -, -, horth, -⟩ := exists_orthonormal_curvature_eigenframe g p hdim
  have hON : ∀ i j, g.inner p (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [horth i j]
    fin_cases i <;> fin_cases j <;> simp [delta3]
  have hneg : ∀ i, ricciTensor g p (basis i) (basis i) < 0 := by
    intro i
    have h1 := defect_quad_le_O5 g p (basis i)
    simp only [hON i i, ite_true, mul_one] at h1
    have := (abs_le.mp h1).2
    linarith
  rw [metricScalarAt_eq_orthonormal_trace g p basis hON, Fin.sum_univ_three]
  linarith [hneg 0, hneg 1, hneg 2]

end Static

/-- Intermediate value along a Riemannian ball. -/
theorem exists_level_point_S23 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p y : M) {r c : ℝ} (hr : 0 < r)
    (hy : y ∈ riemannianBallOf g p r) (hp : metricScalarAt g p < c)
    (hyc : c ≤ metricScalarAt g y) :
    ∃ z ∈ riemannianBallOf g p r, metricScalarAt g z = c ∧ z ∈ connectedComponent p := by
  have hpc := isPathConnected_riemannianBallOf (I := ThreeModel) g p hr
  have hpm : p ∈ riemannianBallOf g p r := by
    change riemannianEDistOf g p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr hr
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  have := hpc.isConnected.isPreconnected.intermediate_value hpm hy hcont.continuousOn
    ⟨hp.le, hyc⟩
  obtain ⟨z, hz, hzc⟩ := this
  exact ⟨z, hz, hzc, hpc.isConnected.isPreconnected.subset_connectedComponent hpm hz⟩

/-- A canonical witness at `z` gives a normalised seed of radius `b`, provided
`b² C₂ (t R(z)) ≤ 1` and the ball-volume constant `κ` of the witness is available. -/
theorem seed_of_witness_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} (s : RegularSlice F.observation)
    (z : s.stage.Carrier) (W : SpatialCanonicalWitness s.metric ε C1 C2 z) {κ b : ℝ}
    (hκ : ∀ r : ℝ, 0 < r → r ^ 4 * normSq0S s.metric z 4 (metricRm04At s.metric z) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤ ballVolume s.metric z r)
    (hb : 0 < b) (hbQ : b ^ 2 * C2 * (s.time * metricScalarAt s.metric z) ≤ 1) :
    HasNormalizedSeed_S13 s z b κ := by
  have ht := s.positive
  have hQ := W.Q_pos
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hsQ : 0 < Real.sqrt (metricScalarAt s.metric z) := Real.sqrt_pos.mpr hQ
  have hsQsq := Real.sq_sqrt hQ.le
  set Q := metricScalarAt s.metric z with hQdef
  set ρ : ℝ := b * Real.sqrt s.time with hρ
  have hρpos : 0 < ρ := by positivity
  have hρsq : ρ ^ 2 = b ^ 2 * s.time := by rw [hρ, mul_pow, Real.sq_sqrt ht.le]
  have hρQ : ρ ^ 2 * C2 * Q ≤ 1 := by rw [hρsq]; nlinarith
  have hρ1 : ρ * Real.sqrt Q ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < (ρ * Real.sqrt Q) ^ 2 := by nlinarith
    rw [mul_pow, hsQsq] at this
    nlinarith [mul_pos hρpos hρpos]
  have hρrad : ρ ≤ W.radius := by
    refine le_trans ?_ W.radius_lower
    rw [← one_div, le_div_iff₀ hsQ]; exact hρ1
  have hsub : riemannianBallOf s.metric z ρ ⊆ W.domain.carrier :=
    (riemannianBallOf_mono s.metric z hρrad).trans W.ball_inside
  have hCQ : C2 * Q ≤ (ρ ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]; nlinarith
  refine normSeed_of_phys_S23 s z (b := b) (w := κ) (fun q hq => ?_) ?_
  · have hrm := W.rm_bound q (hsub hq)
    have := sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le s.metric q hrm
    exact this.mono (by linarith)
  · refine hκ ρ hρpos ?_
    have hrm := W.rm_bound z (interior_subset W.center_inside)
    have hC2Q : 0 ≤ C2 * Q := by positivity
    have hN := (Real.sqrt_le_iff.mp hrm).2
    calc ρ ^ 4 * normSq0S s.metric z 4 (metricRm04At s.metric z)
        ≤ ρ ^ 4 * (C2 * Q) ^ 2 := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = (ρ ^ 2 * C2 * Q) ^ 2 := by ring
      _ ≤ 1 := by
        have h0 : 0 ≤ ρ ^ 2 * C2 * Q := by positivity
        nlinarith

end GC.LongTime.Ch12
