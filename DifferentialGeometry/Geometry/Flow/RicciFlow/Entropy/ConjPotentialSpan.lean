import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotential

/-!
# Compact-interval conjugate potential

This file packages the lower-order conjugate-heat operator on an already
chosen reflected regular-time interval.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-- On any prescribed compact reflected regular-time interval, the
conjugate-heat potential operator is continuous and has one finite norm bound. -/
theorem conjA1_on
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {h : Real}
    (hreg : ∀ s ∈ Set.Icc (0 : Real) h, (T : Real) - s ∈ D.regular) :
    ∃ C1 : NNReal,
      ContinuousOn (fun s : Real ↦ conjA1 (I := I) (M := M) S T s)
        (Set.Icc (0 : Real) h) ∧
      ∀ s ∈ Set.Icc (0 : Real) h,
        ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
        tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hcont : ContinuousOn
      (fun s : Real ↦ conjA1 (I := I) (M := M) S T s)
      (Set.Icc (0 : Real) h) :=
    conjA1_cont (I := I) (M := M) S hS T hreg
  have hnorm : ContinuousOn
      (fun s : Real ↦ ‖conjA1 (I := I) (M := M) S T s‖)
      (Set.Icc (0 : Real) h) :=
    continuous_norm.comp_continuousOn hcont
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  let C1 : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨C1, hcont, ?_⟩
  intro s hs
  change ‖conjA1 (I := I) (M := M) S T s‖ ≤ max C 0
  exact (hC ⟨s, hs, rfl⟩).trans (le_max_left _ _)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
/-- On a compact regular-time slab, the conjugate-heat scalar coefficient has
one pointwise bound uniform in time and space. -/
theorem conjCoeff_span
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Icc a b, ∀ x : M,
        |(conjCoeff (I := I) (M := M) S t : M → Real) x| ≤ C := by
  let K : Set (Real × M) := Set.Icc a b ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod (isCompact_univ (X := M))
  have hcont : ContinuousOn
      (fun p : Real × M =>
        |(conjCoeff (I := I) (M := M) S p.1 : M → Real) p.2|) K := by
    exact ((conjCoeff_joint (I := I) S hS).continuousOn.mono
      (Set.prod_mono hab Set.Subset.rfl)).abs
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x
  exact (hC ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩).trans
    (le_max_left _ _)

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
