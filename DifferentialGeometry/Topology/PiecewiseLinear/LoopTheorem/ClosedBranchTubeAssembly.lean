/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeRealisation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isSourceTrackedBranchTube_of_markedCells {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M] {D : SingularTwoCell M}
    {BdM B : Set M} (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 3 L)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ)
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    {R Lc : Geometry.SimplicialComplex ℝ E} (hRfin : R.faces.Finite) (hRL : IsSubdivision R L)
    {m : ℕ} (hm : 2 ≤ m) {cc : ℕ → E}
    {K : ℕ → Geometry.SimplicialComplex ℝ E} (hKfin : ∀ k, (K k).faces.Finite)
    (hK : ∀ k, IsConeBase (cc k) (K k)) (hS : ∀ k, IsPLSphere 2 (K k).space)
    {y₀ y₁ : ℕ → E} {T : ℕ → Fin 4 → Set E} {γ : ℕ → Fin 4 → ℝ → E}
    {q₀ q₁ : ℕ → (Fin 3 → ℝ) → E} {D₀ D₁ : ℕ → Set E}
    (hγ : ∀ k i, IsPLHomeomorphOn (γ k i) (Icc 0 1) (T k i)) (hγzero : ∀ k i, γ k i 0 = y₀ k)
    (hγone : ∀ k i, γ k i 1 = y₁ k) (hTS : ∀ k i, T k i ⊆ (K k).space)
    (hTT : ∀ k i j, i ≠ j → T k i ∩ T k j = {y₀ k, y₁ k})
    (hsep : ∀ k, ∀ i : Fin 4, ∀ U ⊆ (K k).space \ (T k i ∪ T k (i + 2)), IsPreconnected U →
      (U ∩ T k (i + 1)).Nonempty → (U ∩ T k (i + 3)).Nonempty → False)
    (hq₀ : ∀ k, IsPLHomeomorphOn (q₀ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₀ k))
    (hq₁ : ∀ k, IsPLHomeomorphOn (q₁ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₁ k))
    (hD₀S : ∀ k, D₀ k ⊆ (K k).space) (hD₁S : ∀ k, D₁ k ⊆ (K k).space)
    (hdis : ∀ k, Disjoint (D₀ k) (D₁ k))
    (hb₀ : ∀ k i, q₀ k '' stdSimplexBoundary 2 ∩ T k i = {γ k i (1 / 4)})
    (hb₁ : ∀ k i, q₁ k '' stdSimplexBoundary 2 ∩ T k i = {γ k i (3 / 4)})
    (hy₀ : ∀ k, y₀ k ∈ D₀ k) (hy₁ : ∀ k, y₁ k ∈ D₁ k)
    (hcap : ∀ k < m, D₁ k = D₀ (k + 1)) (hcapc : D₁ m = D₀ 0)
    (harm : ∀ k < m, ∀ i, T k i ∩ D₁ k = T (k + 1) i ∩ D₀ (k + 1))
    (harmc : ∀ i, T m i ∩ D₁ m = T 0 (fourSpokeFlipPerm i) ∩ D₀ 0)
    (hpt : ∀ k < m, ∀ i, γ k i (3 / 4) = γ (k + 1) i (1 / 4))
    (hptc : ∀ i, γ m i (3 / 4) = γ 0 (fourSpokeFlipPerm i) (1 / 4))
    (hadj : ∀ k < m,
      coneSet (cc k) (K k).space ∩ coneSet (cc (k + 1)) (K (k + 1)).space = D₁ k)
    (hadjc : coneSet (cc m) (K m).space ∩ coneSet (cc 0) (K 0).space = D₀ 0)
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) →
      Disjoint (coneSet (cc j) (K j).space) (coneSet (cc k) (K k).space))
    (hN : ⋃ k ≤ m, coneSet (cc k) (K k).space = (derivedNeighborhood R Lc).space)
    (hcore : ⋃ k ≤ m, coneSet (cc k) {y₀ k, y₁ k} = ι '' hD.singularSet.branchCarrier c)
    {α : Fin 4 → EuclideanSpace ℝ (Fin 2)} {v : Fin 4 → ℝ} (hαJ : ∀ i, α i ∈ J)
    (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1) (hray : ∀ i, γ 0 i (1 / 2) = ι (D (ρ (α i, v i))))
    (hbase : cc 0 = ι (D (α 0))) (hα2 : α 2 = α 0) (hα1 : α 1 = τ (α 0))
    (hα3 : α 3 = α 1) (hv0 : 0 < v 0) (hv1 : 0 < v 1) (hv2 : v 2 < 0) (hv3 : v 3 < 0) :
    ∃ (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (_ : Finite Pc.faces) (φ : (ℝ × ℝ) × ℝ → E)
      (u : ℝ × ℝ → ℝ × ℝ),
      IsSourceTrackedBranchTube hD c ι L J ρ (derivedNeighborhood R Lc) Pc φ u
        fourSpokeModelLeaf := by
  obtain ⟨φ, u, hφcyl, hu, hseam, hu0, huσ, hφcore, hφray, hφ0⟩ :=
    exists_cylinder_of_markedCells hm hKfin hK hS hγ hγzero hγone hTS hTT hsep hq₀ hq₁ hD₀S
      hD₁S hdis hb₀ hb₁ hy₀ hy₁ hcap hcapc harm harmc hpt hptc hadj hadjc hfar
  rw [hN] at hφcyl
  obtain ⟨Pc, hPcfin, hPc⟩ := isHPolytope_spliceSquare.isPolyhedron.exists_simplicialComplex
  have : Finite Pc.faces := hPcfin.to_subtype
  have hττ : τ (τ (α 0)) = α 0 := hτ.2.2.2.2.2.2.1 _ (hαJ 0)
  refine ⟨Pc, this, φ, u, isSourceTrackedBranchTube_of_cylinder hD hιc hι hL hJ hτ hRfin hRL
    hPc hφcyl hu hseam hu0 huσ (hφcore.trans hcore) hαJ hv
    (fun i => (hφray i).trans (hray i)) (hφ0.trans hbase) hα2 hα1 hα3 hv0 hv1 hv2 hv3
    fun j => ?_⟩
  rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl
  · rw [fourSpokeFlipPerm_zero, hα1, hττ]
    exact ⟨rfl, iff_of_true hv0 hv1⟩
  · rw [fourSpokeFlipPerm_one, hα1]
    exact ⟨rfl, iff_of_true hv1 hv0⟩
  · rw [fourSpokeFlipPerm_two, hα3, hα1, hττ, hα2]
    exact ⟨rfl, iff_of_false (not_lt.mpr hv2.le) (not_lt.mpr hv3.le)⟩
  · rw [fourSpokeFlipPerm_three, hα2, hα3, hα1]
    exact ⟨rfl, iff_of_false (not_lt.mpr hv3.le) (not_lt.mpr hv2.le)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
