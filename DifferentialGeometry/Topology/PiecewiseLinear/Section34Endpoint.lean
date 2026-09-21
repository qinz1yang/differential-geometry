/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.OpenSourceReduction

/-!
# The Section 34 endpoint: from a labelled cell diagram to Moise 35.2 on an open source

A *cell diagram* for an approximation problem `(U, h, η)` is a labelled family of piecewise
linear cells in the source manifold whose union is `U`, a labelled family of cells in the
target manifold over the same grading and the same face relation, and a family of carriers
`H l` in the target manifold, indexed by the same labels, each containing both `h '' sourceCell l`
and `targetCell l` and of diameter less than `η x` at every `x` of `sourceCell l`.

Given such a diagram the labelled cell assembly produces a piecewise linear embedding `f` of
`U` carrying `sourceCell l` onto `targetCell l`; for `x ∈ sourceCell l` both `f x` and `h x`
lie in `H l`, so `dist (f x) (h x) < η x`; this is the estimate
`exists_isPLHomeomorphInto_dist_lt_of_cellDiagram`.  Then `moise352Open_of_section34CellDiagram`
deduces `Moise352Open 3` from the existence of a diagram for every problem, with no assembly
hypothesis of any kind.

Carriers are indexed by the cell labels, not by the stages of a tower and not by the simplices
of a triangulation of `U` in one Euclidean chart: a stage-indexed family cannot be locally
finite in `h '' U`, and there is no locally finite triangulation theorem for an arbitrary open
subset of a three-dimensional piecewise linear manifold.  Local finiteness of the two cell
families is required in their own unions, that is in the subspaces `U` and `⋃ l, targetCell l`,
and never in the ambient manifolds.

`Section34CellDiagram` is an **open obligation**: no producer of it is proved here, and the
only evidence for its inhabitability at present is the assembly theorem it feeds, whose
hypotheses are simultaneously satisfiable.  A genuine inhabitant requires a locally finite
labelled cell subdivision of an arbitrary open set of a three-dimensional piecewise linear
manifold together with the whole target-side construction of Section 34, and is deferred.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Estimate

variable {Λ M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [Nonempty M₂]

theorem exists_isPLHomeomorphInto_dist_lt_of_cellDiagram (dim : Λ → ℕ) (face : Λ → Set Λ)
    (P Q : Λ → Set (EuclideanSpace ℝ (Fin 3)))
    (r : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (s : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (u : Λ → EuclideanSpace ℝ (Fin 3) → M₁) (v : Λ → EuclideanSpace ℝ (Fin 3) → M₂)
    (sourceCell : Λ → Set M₁) (targetCell : Λ → Set M₂) (carrier : Λ → Set M₂) (U : Set M₁)
    (h : M₁ → M₂) (η : M₁ → ℝ) (hdim : ∀ l, dim l ≤ 3)
    (hr : ∀ l, IsPLHomeomorphOn (r l) (stdSimplex ℝ (Fin (dim l + 1))) (P l))
    (hs : ∀ l, IsPLHomeomorphOn (s l) (stdSimplex ℝ (Fin (dim l + 1))) (Q l))
    (hu : ∀ l, IsPLHomeomorphInto 3 (u l) (P l))
    (hv : ∀ l, IsPLHomeomorphInto 3 (v l) (Q l))
    (hsourceCell : ∀ l, sourceCell l = u l '' P l)
    (htargetCell : ∀ l, targetCell l = v l '' Q l)
    (hfaceDim : ∀ l m, m ∈ face l → m = l ∨ dim m < dim l)
    (hsourceBoundary : ∀ l, u l '' (r l '' stdSimplexBoundary (dim l)) =
      ⋃ m ∈ face l \ {l}, sourceCell m)
    (htargetBoundary : ∀ l, v l '' (s l '' stdSimplexBoundary (dim l)) =
      ⋃ m ∈ face l \ {l}, targetCell m)
    (hsourceInter : ∀ l m, sourceCell l ∩ sourceCell m = ⋃ k ∈ face l ∩ face m, sourceCell k)
    (htargetInter : ∀ l m, targetCell l ∩ targetCell m = ⋃ k ∈ face l ∩ face m, targetCell k)
    (hLFs : ∀ x ∈ ⋃ l, sourceCell l, ∃ W ∈ 𝓝 x, {l | (sourceCell l ∩ W).Nonempty}.Finite)
    (hLFt : ∀ y ∈ ⋃ l, targetCell l, ∃ W ∈ 𝓝 y, {l | (targetCell l ∩ W).Nonempty}.Finite)
    (hcover : (⋃ l, sourceCell l) = U)
    (hcarrier : ∀ l, h '' sourceCell l ∪ targetCell l ⊆ carrier l)
    (hsmall : ∀ l, ∀ x ∈ sourceCell l, ∀ y ∈ carrier l, ∀ z ∈ carrier l, dist y z < η x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f U ∧ ∀ x ∈ U, dist (f x) (h x) < η x := by
  obtain ⟨f, hf, hfim⟩ := exists_isPLHomeomorphInto_of_labelledCells dim face P Q r s u v
    sourceCell targetCell hdim hr hs hu hv hsourceCell htargetCell hfaceDim hsourceBoundary
    htargetBoundary hsourceInter htargetInter hLFs hLFt
  refine ⟨f, hcover ▸ hf, fun x hx => ?_⟩
  rw [← hcover] at hx
  obtain ⟨l, hl⟩ := mem_iUnion.mp hx
  refine hsmall l x hl (f x) (hcarrier l (Or.inr ?_)) (h x) (hcarrier l (Or.inl ⟨x, hl, rfl⟩))
  rw [← hfim l]
  exact mem_image_of_mem f hl

end Estimate

def Section34CellDiagram : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ η : M₁ → ℝ, ContinuousOn η U → (∀ x ∈ U, 0 < η x) →
    ∃ (Λ : Type u) (dim : Λ → ℕ) (face : Λ → Set Λ)
      (P Q : Λ → Set (EuclideanSpace ℝ (Fin 3)))
      (r : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
      (s : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
      (u : Λ → EuclideanSpace ℝ (Fin 3) → M₁) (v : Λ → EuclideanSpace ℝ (Fin 3) → M₂)
      (sourceCell : Λ → Set M₁) (targetCell : Λ → Set M₂) (carrier : Λ → Set M₂),
      (∀ l, dim l ≤ 3) ∧
      (∀ l, IsPLHomeomorphOn (r l) (stdSimplex ℝ (Fin (dim l + 1))) (P l)) ∧
      (∀ l, IsPLHomeomorphOn (s l) (stdSimplex ℝ (Fin (dim l + 1))) (Q l)) ∧
      (∀ l, IsPLHomeomorphInto 3 (u l) (P l)) ∧ (∀ l, IsPLHomeomorphInto 3 (v l) (Q l)) ∧
      (∀ l, sourceCell l = u l '' P l) ∧ (∀ l, targetCell l = v l '' Q l) ∧
      (∀ l m, m ∈ face l → m = l ∨ dim m < dim l) ∧
      (∀ l, u l '' (r l '' stdSimplexBoundary (dim l)) = ⋃ m ∈ face l \ {l}, sourceCell m) ∧
      (∀ l, v l '' (s l '' stdSimplexBoundary (dim l)) = ⋃ m ∈ face l \ {l}, targetCell m) ∧
      (∀ l m, sourceCell l ∩ sourceCell m = ⋃ k ∈ face l ∩ face m, sourceCell k) ∧
      (∀ l m, targetCell l ∩ targetCell m = ⋃ k ∈ face l ∩ face m, targetCell k) ∧
      (∀ x ∈ ⋃ l, sourceCell l, ∃ W ∈ 𝓝 x, {l | (sourceCell l ∩ W).Nonempty}.Finite) ∧
      (∀ y ∈ ⋃ l, targetCell l, ∃ W ∈ 𝓝 y, {l | (targetCell l ∩ W).Nonempty}.Finite) ∧
      (⋃ l, sourceCell l) = U ∧
      (∀ l, h '' sourceCell l ∪ targetCell l ⊆ carrier l) ∧
      ∀ l, ∀ x ∈ sourceCell l, ∀ y ∈ carrier l, ∀ z ∈ carrier l, dist y z < η x

theorem moise352Open_of_section34CellDiagram (hdiagram : Section34CellDiagram.{u}) :
    Moise352Open.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  rcases isEmpty_or_nonempty M₁ with hM | hM
  · have hUe : U = ∅ := eq_empty_iff_forall_notMem.mpr fun x _ => (hM.false x).elim
    exact ⟨h, by rw [hUe]; exact isPLHomeomorphInto_empty h, fun x _ => (hM.false x).elim⟩
  · have : Nonempty M₂ := ⟨h (Classical.arbitrary M₁)⟩
    obtain ⟨Λ, dim, face, P, Q, r, s, u, v, sourceCell, targetCell, carrier, hdim, hr, hs, hu,
      hv, hsourceCell, htargetCell, hfaceDim, hsourceBoundary, htargetBoundary, hsourceInter,
      htargetInter, hLFs, hLFt, hcover, hcarrier, hsmall⟩ := hdiagram hU hh η hηc hηpos
    exact exists_isPLHomeomorphInto_dist_lt_of_cellDiagram dim face P Q r s u v sourceCell
      targetCell carrier U h η hdim hr hs hu hv hsourceCell htargetCell hfaceDim
      hsourceBoundary htargetBoundary hsourceInter htargetInter hLFs hLFt hcover hcarrier hsmall

end DifferentialGeometry.Topology.PiecewiseLinear
