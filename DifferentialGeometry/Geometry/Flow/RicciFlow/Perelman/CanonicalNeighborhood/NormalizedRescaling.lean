import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredSourceInputs

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

namespace NormalizedSequence
variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}

private theorem terminal_mem (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) :
    (0 : ℝ) ∈ (X.interval i).carrier := by
  rw [X.carrier_eq]
  exact ⟨by linarith [X.depth_pos i], le_rfl⟩

def terminalCurvatureRescale (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 1 ≤ (X.term i).S.scalar 0 (x i)) :
    NormalizedSequence.{u} eps kappa sigma Phi where
  interval i := parabolicInterval (X.interval i) 0 ((X.term i).S.scalar 0 (x i))
    (terminal_mem X i)
  term i := {
    M := (X.term i).M
    topology := (X.term i).topology
    charted := (X.term i).charted
    smooth := (X.term i).smooth
    sigmaCompact := (X.term i).sigmaCompact
    t2 := (X.term i).t2
    t2TangentBundle := (X.term i).t2TangentBundle
    basepoint := x i
    S := parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
      (lt_of_lt_of_le zero_lt_one (hQ i)) (terminal_mem X i)
    isSolution := parabolicSolution_isSolutionOn (X.term i).S (X.term i).isSolution _ _ _ _ }
  depth i := (X.term i).S.scalar 0 (x i) * X.depth i
  scale i := (X.term i).S.scalar 0 (x i) * X.scale i
  depth_pos i := mul_pos (lt_of_lt_of_le zero_lt_one (hQ i)) (X.depth_pos i)
  depth_buffer i := (X.depth_buffer i).trans (le_mul_of_one_le_left (X.depth_pos i).le (hQ i))
  scale_pos i := mul_pos (lt_of_lt_of_le zero_lt_one (hQ i)) (X.scale_pos i)
  depth_tendsto := tendsto_atTop_mono
    (fun i => le_mul_of_one_le_left (X.depth_pos i).le (hQ i)) X.depth_tendsto
  scale_tendsto := tendsto_atTop_mono
    (fun i => le_mul_of_one_le_left (X.scale_pos i).le (hQ i)) X.scale_tendsto
  carrier_eq i := by
    ext s
    simp only [parabolicInterval_carrier, mem_ofPred_eq, X.carrier_eq, mem_Icc,
      parabolicTime, zero_add]
    have hp := lt_of_lt_of_le zero_lt_one (hQ i)
    rw [le_div_iff₀ hp, div_le_iff₀ hp]
    ring_nf
  regular_eq i := by
    ext s
    simp only [parabolicInterval_regular, mem_ofPred_eq, X.regular_eq, mem_Ioo,
      parabolicTime, zero_add]
    have hp := lt_of_lt_of_le zero_lt_one (hQ i)
    rw [lt_div_iff₀ hp, div_lt_iff₀ hp]
    ring_nf
  connected i := X.connected i
  orientation i := X.orientation i
  complete i s hs := by
    have hc : RiemannianMetricComplete ((X.term i).S.base.metric
        (parabolicTime 0 ((X.term i).S.scalar 0 (x i)) s)) := ⟨X.complete i _ hs⟩
    exact (hc.of_lower (lt_of_lt_of_le zero_lt_one (hQ i)) (fun _ _ => le_rfl)).complete
  source_bound i := by
    obtain ⟨C, hC⟩ := X.source_bound i
    refine ⟨((X.term i).S.scalar 0 (x i))⁻¹ ^ 2 * C, fun s hs y => ?_⟩
    exact (parabolicRmNormSq (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
      (lt_of_lt_of_le zero_lt_one (hQ i)) (terminal_mem X i) s y).le.trans
      (mul_le_mul_of_nonneg_left (hC _ hs y) (sq_nonneg _))
  base_one i := by
    change (parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
      (lt_of_lt_of_le zero_lt_one (hQ i)) (terminal_mem X i)).scalar 0 (x i) = 1
    simp only [parabolicSolution_scalar, parabolicTime_zero,
      inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one (hQ i)))]
  noncollapse i := by
    rw [← recentered_noncollapse_scale (lt_of_lt_of_le zero_lt_one (hQ i)).le]
    exact parabolic_spatial_noncollapse (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
      (lt_of_lt_of_le zero_lt_one (hQ i)) (terminal_mem X i) kappa
      (Real.sqrt (X.scale i) * sigma) (X.noncollapse i)
  pinching i := by
    rw [← rescalePinchingFunction_rescale]
    exact phiAlmostNonnegative_paraSolution (X.term i).S
      (lt_of_lt_of_le zero_lt_one (hQ i)) (terminal_mem X i) (X.pinching i)
  higher_good i s hs y hy := by
    have hp := lt_of_lt_of_le zero_lt_one (hQ i)
    apply (orientedWitness_paraSolution_iff (X.term i).S (X.orientation i)
      hp (terminal_mem X i) s y eps kappa).mpr
    apply X.higher_good i
    · change -X.depth i ≤ 0 + s / _ ∧ 0 + s / _ ≤ 0
      simp only [zero_add]
      rw [le_div_iff₀ hp, div_le_iff₀ hp]
      constructor <;> nlinarith [hs.1, hs.2]
    · change 2 ≤ (parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
        hp (terminal_mem X i)).scalar s y at hy
      simp only [parabolicSolution_scalar] at hy
      rw [← div_eq_inv_mul, le_div_iff₀ hp] at hy
      exact (by linarith [hQ i] : 2 ≤ 2 * (X.term i).S.scalar 0 (x i)).trans hy

end NormalizedSequence
end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
