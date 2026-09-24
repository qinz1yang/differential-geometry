import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionBufferedCanonical

noncomputable section
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_bufferedCanonical_of_shrinkingSphericalSpaceFormFlow
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) P)
    (hbase : PointedFlowScalarAtBase (I := I3) P 1)
    {alpha : ℝ} (ha : 0 < alpha) (H : ℝ) :
    Nonempty (BufferedCanonical P.S alpha
      (max (2 * (Real.pi / Real.sqrt (1 / 6)) + 1) 2 + 1) H P.basepoint 0) := by
  let eps := min alpha 1 / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps < 1 := by
    dsimp [eps]
    linarith [min_le_right alpha 1]
  have htol : eps < alpha := by
    dsimp [eps]
    linarith [min_le_left alpha 1]
  obtain ⟨W⟩ := exists_canonicalWitness_of_shrinkingSphericalSpaceFormFlow
    P hround hbase heps heps1
  apply CanonicalWitness.exists_bufferedCanonical W htol
  intro cap hc
  obtain ⟨hdepth, _⟩ := hc
  let i : Fin cap.chain.count := ⟨0, cap.chain.count_pos⟩
  let p := (cap.chain.necks i).center
  have hv : cap.tube_map (p, 0) ∈ cap.tube := by
    rw [← cap.tube_eq]
    exact ⟨(p, 0), ⟨Set.mem_univ _, by norm_num⟩, rfl⟩
  have hcontra := localCap_tube_depth_lt_two_mul_comparisonConstant W cap hdepth hv
  have hsqrt : (1 / 10 : ℝ) < Real.sqrt (1 / 6) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1 / 6 : ℝ))
    have hn := Real.sqrt_nonneg (1 / 6 : ℝ)
    nlinarith
  have hratio : Real.pi / Real.sqrt (1 / 6) < 40 := by
    apply (div_lt_iff₀ (by positivity : 0 < Real.sqrt (1 / 6))).2
    nlinarith [Real.pi_lt_four]
  exfalso
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
