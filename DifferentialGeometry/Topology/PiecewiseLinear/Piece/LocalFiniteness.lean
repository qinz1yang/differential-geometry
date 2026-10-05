import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Topology.Compactness.LocallyFinite

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

structure LocallyFinitePLPieceIn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (Y : Set X) where
  complex : Geometry.SimplicialComplex ℝ E
  locallyFinite : LocallyFinite (fun s : complex.faces =>
    (Subtype.val : complex.space → E) ⁻¹'
      convexHull ℝ ((s : Finset E) : Set E))
  map : E → X
  bijOn : BijOn map complex.space Y
  continuousOn : ContinuousOn map complex.space
  isEmbedding : IsEmbedding (fun x : complex.space => map x)
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' Y)

end

section

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

omit [FiniteDimensional ℝ Ea] in
theorem LocallyFinitePLPieceIn.finite_faces_inter_of_isCompact
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) {C : Set Ea} (hC : IsCompact C)
    (hC𝒦 : C ⊆ 𝒦.complex.space) :
    {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ (convexHull ℝ (t : Set Ea) ∩ C).Nonempty}.Finite := by
  have hCsub : IsCompact ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹' C) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_iff.mpr]
    · exact hC
    · intro x hx
      exact ⟨⟨x, hC𝒦 hx⟩, rfl⟩
  have hfin := 𝒦.locallyFinite.finite_nonempty_inter_compact hCsub
  refine (hfin.image fun i : 𝒦.complex.faces => (i : Finset Ea)).subset ?_
  rintro t ⟨ht, x, hxt, hxC⟩
  exact ⟨⟨t, ht⟩, ⟨⟨x, hC𝒦 hxC⟩, hxt, hxC⟩, rfl⟩

end

end DifferentialGeometry.Topology.PiecewiseLinear
