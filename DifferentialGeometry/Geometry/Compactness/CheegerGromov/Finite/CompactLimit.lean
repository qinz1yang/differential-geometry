import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# LFR14, clause T3: compact limits

Blueprint LFR14 (master207A.tex:25869): the comparison maps `jᵢ` are partial diffeomorphisms whose
sources exhaust the limit `N`. If `N` is compact, eventually every `jᵢ` is defined on all of `N`
and is onto the connected `Xᵢ`, hence a global `C^K` diffeomorphism.

* `eventually_source_eq_univ_of_compactSpace`: the frozen statement T3 of
  `build-logs/scratch/D-LFR14/Target.lean`, verbatim.
* Consumer `eventually_nonempty_diffeomorph_of_compactSpace`: eventually there is a `C^K`
  diffeomorphism `N ≃ Xᵢ` that agrees with `jᵢ`
  (`KappaSolutions.globalDiffeomorphOfUniv`, Topology/Manifold/PartialDiffeomorph/Globalization.lean).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u

/-- **T3 — compact limit.** If `N` is compact, eventually every `j i` is defined on all of `N`
and onto the connected `X i` (so `globalDiffeomorphOfUniv` turns it into a `C^K` diffeomorphism). -/
theorem eventually_source_eq_univ_of_compactSpace
    {n K : ℕ} {X : ℕ → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)] [∀ i, T2Space (X i)]
    [∀ i, ConnectedSpace (X i)]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [CompactSpace N]
    [Nonempty N]
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) :
    ∀ᶠ i in atTop, (j i).source = univ ∧ (j i).target = univ := by
  filter_upwards [hexh univ isCompact_univ] with i hi
  have hsrc : (j i).source = univ := univ_subset_iff.mp hi
  refine ⟨hsrc, ?_⟩
  apply DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorph_target_eq_univ_of_compact_source
  · rw [hsrc]
    exact isCompact_univ
  · rw [hsrc]
    exact univ_nonempty

/-- Consumer: for a compact limit, eventually every comparison map `j i` is (the underlying map
of) a global `C^K` diffeomorphism `N ≃ X i`. -/
theorem eventually_nonempty_diffeomorph_of_compactSpace
    {n K : ℕ} {X : ℕ → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)] [∀ i, T2Space (X i)]
    [∀ i, ConnectedSpace (X i)]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [CompactSpace N]
    [Nonempty N]
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) :
    ∀ᶠ i in atTop, ∃ Φ : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X i) K, (Φ : N → X i) = j i := by
  filter_upwards [eventually_source_eq_univ_of_compactSpace j hexh] with i hi
  exact ⟨DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalDiffeomorphOfUniv
    (j i) hi.1 hi.2, rfl⟩

end DifferentialGeometry.CheegerGromovCompactness
