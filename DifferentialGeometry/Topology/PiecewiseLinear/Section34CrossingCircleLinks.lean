import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_two_poles_on_derived_cell_base
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite Γ.faces]
    (hΓ : IsCombinatorialManifold 1 Γ) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces) :
    ∃ y₀ y₁ : E, y₀ ≠ y₁ ∧
      Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁} := by
  have hS : IsPLSphere 0 (derivedNeighborhoodCellBase Γ s).space :=
    hΓ.barycentricSubdivision.isPLSphere_upperLink _
      (singleton_centroid_mem_barycentricSubdivision Γ hs) (k := 0)
      (Finset.card_singleton _) le_rfl
  obtain ⟨y₀, y₁, hne, hpair⟩ := isPLSphere_zero_iff.mp hS
  refine ⟨y₀, y₁, hne, ?_⟩
  rw [inter_comm, derivedNeighborhoodCellBase_inter_subcomplex R Γ hΓR hs, hpair]

open Classical in
theorem exists_four_arc_trace_of_circle_disks
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite Γ.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hΓ : IsCombinatorialManifold 1 Γ) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces) (hsB : s ∉ (boundaryComplex 3 R).faces)
    {ψ : (ℝ × ℝ) × ℝ → E} {V : Set ((ℝ × ℝ) × ℝ)} {Ω W : Set E}
    (hψ : IsPLHomeomorphOn ψ V (R.space ∩ Ω)) (hWΩ : W ⊆ Ω)
    (haxis : ∀ p ∈ V, ψ p ∈ Γ.space ↔ p.1 = 0)
    {P : Fin 4 → Set E} {q : Fin 4 → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i))
    (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    (hread : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i)
    (hbd : ∀ x ∈ R.space ∩ W, ∀ i, x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hcell : (derivedNeighborhoodCell R s).space ⊆ W) :
    ∃ (y₀ y₁ : E) (γ : Fin 4 → ℝ → E), y₀ ≠ y₁ ∧
      IsPLSphere 2 (derivedNeighborhoodCellBase R s).space ∧
      Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁} ∧
      (∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1)
        ((derivedNeighborhoodCellBase R s).space ∩ P i)) ∧
      (∀ i, γ i 0 = y₀) ∧ (∀ i, γ i 1 = y₁) ∧
      (∀ i j, i ≠ j →
        ((derivedNeighborhoodCellBase R s).space ∩ P i) ∩
          ((derivedNeighborhoodCellBase R s).space ∩ P j) = {y₀, y₁}) ∧
      ∀ i : Fin 4, ∀ U ⊆ (derivedNeighborhoodCellBase R s).space \
        (((derivedNeighborhoodCellBase R s).space ∩ P i) ∪
          ((derivedNeighborhoodCellBase R s).space ∩ P (i + 2))),
        IsPreconnected U →
        (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 1))).Nonempty →
        (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 3))).Nonempty → False := by
  obtain ⟨y₀, y₁, hne, hpoles⟩ := hΓ.exists_two_poles_on_derived_cell_base R Γ hΓR hs
  obtain ⟨γ, hγ, hzero, hone, hpair, hsep⟩ :=
    exists_fourArcTrace_of_crossHalfPlane_disks R Γ hΓR hs hψ hWΩ haxis hq hPR
      hread hbd hcell hpoles
  exact ⟨y₀, y₁, γ, hne,
    hR.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex (hΓR hs) hsB,
    hpoles, hγ, hzero, hone, hpair, hsep⟩

end DifferentialGeometry.Topology.PiecewiseLinear
