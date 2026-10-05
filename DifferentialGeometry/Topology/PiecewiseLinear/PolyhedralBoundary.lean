import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifold

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem boundaryComplex_zero_space [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) : (boundaryComplex 0 K).space = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨s, hs, -⟩ := (boundaryComplex 0 K).mem_space_iff.mp hx
  obtain ⟨-, t, ht, -, hcard, -⟩ := hs
  have := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
  omega

open Classical in
private theorem PLPieceIn.image_boundaryComplex_eq {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {m : ℕ} {P : Set X}
    (T₁ : PLPieceIn E n X P) (T₂ : PLPieceIn F n X P)
    (hT₁ : IsCombinatorialManifoldWithBoundary (m + 1) T₁.complex) :
    T₁.map '' (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₁.complex).space =
      T₂.map '' (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₂.complex).space := by
  classical
  have : Finite T₁.complex.faces := T₁.finite_faces.to_subtype
  have : Finite T₂.complex.faces := T₂.finite_faces.to_subtype
  have htrans := T₁.isPLHomeomorphOn_transition T₂
  have hT₂ : IsCombinatorialManifoldWithBoundary (m + 1) T₂.complex :=
    hT₁.of_isPLHomeomorphOn htrans
  apply Subset.antisymm
  · rintro y ⟨x, hxB, rfl⟩
    have hxK := boundaryComplex_space_subset (m + 1) T₁.complex hxB
    let z := Function.invFunOn T₂.map T₂.complex.space (T₁.map x)
    have hzK : z ∈ T₂.complex.space :=
      T₂.bijOn.surjOn.mapsTo_invFunOn (T₁.bijOn.mapsTo hxK)
    have hzB : z ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₂.complex).space :=
      (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn T₁.complex T₂.complex hT₁
        htrans hxK).mpr hxB
    exact ⟨z, hzB, T₂.bijOn.invOn_invFunOn.2 (T₁.bijOn.mapsTo hxK)⟩
  · rintro y ⟨z, hzB, rfl⟩
    have hzK := boundaryComplex_space_subset (m + 1) T₂.complex hzB
    let x := Function.invFunOn T₁.map T₁.complex.space (T₂.map z)
    have hxK : x ∈ T₁.complex.space :=
      T₁.bijOn.surjOn.mapsTo_invFunOn (T₂.bijOn.mapsTo hzK)
    have hxB : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₁.complex).space :=
      (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn T₂.complex T₁.complex hT₂
        (T₂.isPLHomeomorphOn_transition T₁) hzK).mpr hzB
    exact ⟨x, hxB, T₁.bijOn.invOn_invFunOn.2 (T₂.bijOn.mapsTo hzK)⟩

open Classical in
noncomputable def polyhedralBoundary {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (m : ℕ) (P : Set X)
    (h : IsPolyhedralManifoldWithBoundary (n := n) m P) : Set X :=
  let T := Classical.choose h
  T.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T.piece.complex).space

open Classical in
theorem polyhedralBoundary_eq_of_piece {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {m : ℕ} {P : Set X}
    (h : IsPolyhedralManifoldWithBoundary (n := n) m P) (T : PLPiece n X P) :
    polyhedralBoundary m P h =
      T.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T.piece.complex).space := by
  classical
  let T₀ := Classical.choose h
  have hT₀ : IsCombinatorialManifoldWithBoundary m T₀.piece.complex :=
    Classical.choose_spec h
  change T₀.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T₀.piece.complex).space =
    T.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T.piece.complex).space
  cases m with
  | zero =>
    have hzero₀ := @boundaryComplex_zero_space _ _ _ (Classical.decEq _)
      T₀.piece.complex
    have hzero := @boundaryComplex_zero_space _ _ _ (Classical.decEq _)
      T.piece.complex
    rw [hzero₀, hzero, image_empty, image_empty]
  | succ m => exact T₀.piece.image_boundaryComplex_eq T.piece hT₀

end DifferentialGeometry.Topology.PiecewiseLinear
