import DifferentialGeometry.Geometry.HarmonicMap.ConformalRank
import DifferentialGeometry.Analysis.Calculus.DiskTraceApproximation

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Values of the actual disk at its interior noninjective differentials. -/
def diskInteriorCriticalValues (q : C(closedDisk, M)) : Set M :=
  q '' {z : closedDisk | ‖(z : ℂ)‖ < 1 ∧ ¬ Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)}

/-- A compact target set avoiding the prescribed trace has its FULL inverse
image in a compact interior source set. The actual Morrey critical points and
values over that target set are finite. No boundary rank or boundary singleton
law, global finiteness, or changed metric is required. -/
theorem IsMorreyDisk.compact_preimage_and_finite_critical_values_away_trace
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {K : Set M} (hK : IsCompact K) (haway : Disjoint K (Set.range γ)) :
    IsCompact ((Subtype.val : closedDisk → ℂ) '' (q ⁻¹' K)) ∧
      ((Subtype.val : closedDisk → ℂ) '' (q ⁻¹' K)) ⊆ ball (0 : ℂ) 1 ∧
      {z : closedDisk | q z ∈ K ∧ ¬ Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)}.Finite ∧
      (diskInteriorCriticalValues (E := E) q ∩ K).Finite := by
  classical
  let A : Set ℂ := (Subtype.val : closedDisk → ℂ) '' (q ⁻¹' K)
  have hA : IsCompact A :=
    (hK.isClosed.preimage q.continuous).isCompact.image continuous_subtype_val
  have hAD : A ⊆ ball (0 : ℂ) 1 := by
    rintro z ⟨x, hx, rfl⟩
    apply mem_ball_zero_iff.mpr
    have hle : ‖(x : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    by_contra hnot
    have hnorm : ‖(x : ℂ)‖ = 1 := le_antisymm hle (le_of_not_gt hnot)
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hnorm
    have hxθ : diskBoundary θ = x := Subtype.ext hθ
    obtain ⟨σ, _, htrace⟩ := hq.trace
    have hvalue : q (diskBoundary θ) = γ (σ θ) :=
      congrArg (fun Γ : freeLoop M => Γ θ) htrace
    rw [hxθ] at hvalue
    exact Set.disjoint_left.mp haway hx ⟨σ θ, hvalue.symm⟩
  have hcrit := hq.finite_not_injective_mfderiv_of_isCompact hγ hA hAD
  have hfinite : {z : closedDisk | q z ∈ K ∧ ¬ Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)}.Finite := by
    apply Set.Finite.of_injOn (f := (Subtype.val : closedDisk → ℂ)) ?_
      Subtype.val_injective.injOn hcrit
    intro z hz
    exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  refine ⟨hA, hAD, hfinite, ?_⟩
  apply (hfinite.image q).subset
  rintro y ⟨⟨z, hz, rfl⟩, hy⟩
  exact ⟨z, ⟨hy, hz.2⟩, rfl⟩

/-- The actual interior critical values are locally finite off the prescribed
trace image, even when critical points could accumulate at the source boundary. -/
theorem IsMorreyDisk.locally_finite_critical_values_away_trace
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {y : M} (hy : y ∉ Set.range γ) :
    ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ V ⊆ (Set.range γ)ᶜ ∧
      (diskInteriorCriticalValues (E := E) q ∩ V).Finite := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have hΓ : IsClosed (Set.range γ) := (isCompact_range γ.continuous).isClosed
  obtain ⟨K, hK, hyK, hKaway⟩ := exists_compact_subset hΓ.isOpen_compl hy
  have hdisj : Disjoint K (Set.range γ) := Set.disjoint_left.mpr fun _ hK hΓ => hKaway hK hΓ
  have hfinite := (hq.compact_preimage_and_finite_critical_values_away_trace hγ hK hdisj).2.2.2
  exact ⟨interior K, isOpen_interior, hyK, interior_subset.trans hKaway,
    hfinite.subset (inter_subset_inter_right _ interior_subset)⟩

end DifferentialGeometry.Geometry
