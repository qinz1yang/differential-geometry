import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.Basic

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
    (hr : ∀ l, IsPLHomeomorphOn (r l) (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim l + 1))) (P l))
    (hs : ∀ l, IsPLHomeomorphOn (s l) (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim l + 1))) (Q l))
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

end DifferentialGeometry.Topology.PiecewiseLinear
