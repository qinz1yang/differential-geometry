import DifferentialGeometry.Topology.SimplicialComplex.MaximalFaceChart
import DifferentialGeometry.Topology.Homology.Local.Graded
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set DifferentialGeometry.Homology
open scoped Manifold

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]


theorem exists_maximalFace_above (s : Finset E) (hs : s ∈ K.faces) :
    ∃ (t : Finset E) (ht : t ∈ K.faces), s ⊆ t ∧ IsMax (⟨t, ht⟩ : K.faces) := by
  obtain ⟨t, hst, ht⟩ := (Set.toFinite K.faces).exists_le_maximal hs
  exact ⟨t, ht.prop, hst, fun u hu ↦ ht.2 u.prop hu⟩

theorem not_isZero_localHomology_maximalFace (s : Finset E) (hs : s ∈ K.faces)
    (hmax : IsMax (⟨s, hs⟩ : K.faces)) (d : ℕ) (hcard : s.card = (d + 1) + 1) :
    ¬IsZero (relativeHomology (TopCat.of K.space)
      ({geometricFaceBarycenter K s hs}ᶜ : Set K.space) (ModuleCat.of ℤ ℤ) (d + 1)) := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s
  let x : K.space := geometricFaceBarycenter K s hs
  have hx : x ∈ U := geometricFaceBarycenter_mem_faceOpenStar K s hs
  let y : U := ⟨x, hx⟩
  let e := maximalFaceEuclideanChart K s hs hmax hcard
  have hy : y ∈ e.source := mem_univ y
  have he := chartLocalHomologyIso (X := TopCat.of U)
    (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1)))) e y hy (ModuleCat.of ℤ ℤ) (d + 1)
  have hu := puncturedNeighborhoodHomologyIso (TopCat.of K.space) U x hx
    (ModuleCat.of ℤ ℤ) (isOpen_faceOpenStar K s) (d + 1)
  intro hz
  exact not_isZero_localEuclidean_at_top d (e y) ((hz.of_iso hu).of_iso he.symm)

private theorem face_card_le_of_local_vanishing (n : ℕ)
    (hv : ∀ (x : K.space) (q : ℕ), n < q →
      IsZero (relativeHomology (TopCat.of K.space) ({x}ᶜ : Set K.space)
        (ModuleCat.of ℤ ℤ) q)) (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ n + 1 := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_maximalFace_above K s hs
  apply (Finset.card_le_card hst).trans
  by_contra h
  have hbig : n + 1 < t.card := Nat.lt_of_not_ge h
  let d := t.card - 2
  have hcard : t.card = (d + 1) + 1 := by dsimp [d]; omega
  exact not_isZero_localHomology_maximalFace K t ht hmax d hcard
    (hv (geometricFaceBarycenter K t ht) (d + 1) (by dsimp [d]; omega))

section Manifold
variable {M : Type} [TopologicalSpace M] [T1Space M] (e : K.space ≃ₜ M)

include e in
theorem face_card_le_of_manifold_homeomorph {n : ℕ} [NeZero n]
    [ChartedSpace (EuclideanHalfSpace n) M] (s : Finset E) (hs : s ∈ K.faces) :
    s.card ≤ n + 1 := by
  apply face_card_le_of_local_vanishing K n ?_ s hs
  intro x q hq
  exact (isZero_localManifold_of_gt (n := n) (ModuleCat.of ℤ ℤ) (e x) q hq).of_iso
    (chartLocalHomologyIso (X := TopCat.of K.space) (Y := TopCat.of M)
      e.toOpenPartialHomeomorph x (mem_univ x) (ModuleCat.of ℤ ℤ) q)

include e in
theorem face_card_le_of_boundaryless_homeomorph {n : ℕ} {H : Type}
    [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H) [BoundarylessManifold I M]
    (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ n + 1 := by
  apply face_card_le_of_local_vanishing K n ?_ s hs
  intro x q hq
  exact (isZero_localManifold_interior_of_gt (ModuleCat.of ℤ ℤ) I (e x)
    BoundarylessManifold.isInteriorPoint q hq).of_iso
      (chartLocalHomologyIso (X := TopCat.of K.space) (Y := TopCat.of M)
        e.toOpenPartialHomeomorph x (mem_univ x) (ModuleCat.of ℤ ℤ) q)

end Manifold

end DifferentialGeometry.Topology.SimplicialComplex
