import DifferentialGeometry.Geometry.HarmonicMap.CompactTargetCriticalValues
import Mathlib.Topology.Compactness.SigmaCompact

set_option autoImplicit false
noncomputable section

open Set Metric Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

/-- The actual interior critical values of a Morrey disk are countable. This
allows boundary accumulation and asserts no global finiteness or boundary rank. -/
theorem IsMorreyDisk.countable_interior_critical_values
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    (diskInteriorCriticalValues (E := E) q).Countable := by
  let D : Set ℂ := ball (0 : ℂ) 1
  let : LocallyCompactSpace D := isOpen_ball.locallyCompactSpace
  have hσ : IsSigmaCompact D := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hσ
  have hKD (n : ℕ) : K n ⊆ ball (0 : ℂ) 1 := by
    rw [show ball (0 : ℂ) 1 = ⋃ n, K n from hcover.symm]
    exact subset_iUnion K n
  let B : Set ℂ := {z | z ∈ ball (0 : ℂ) 1 ∧ ¬ Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)}
  have hB : B.Countable := by
    apply (countable_iUnion fun n =>
      (hq.finite_not_injective_mfderiv_of_isCompact hγ (hK n) (hKD n)).countable).mono
    intro z hz
    have hzU : z ∈ ⋃ n, K n := hcover.symm ▸ hz.1
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hzU
    exact mem_iUnion.mpr ⟨n, hzn, hz.2⟩
  apply ((hB.preimage Subtype.val_injective).mono ?_).image q
  intro z hz
  exact ⟨mem_ball_zero_iff.mpr hz.1, hz.2⟩

end DifferentialGeometry.Geometry
