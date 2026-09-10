import DifferentialGeometry.Topology.LocalDegree.AffineCoordinate
import DifferentialGeometry.Topology.LocalDegree.CoordinateChangeHomotopy

set_option autoImplicit false
open Metric Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.LocalDegree

theorem isolatedZero_mpullback_partialDiffeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) {V : F → F} (hV : isolatedZero V (φ x)) :
    isolatedZero (_root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) φ V) x := by
  obtain ⟨S, hS⟩ := hV
  obtain ⟨A, _, R, hR, hP, hPz, _⟩ :=
    exists_sphereMap_coordinateChange_homotopy φ hn hx hS.pos hS.continuousOn hS.nonzero
  have h0 : _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) φ V x = 0 := by
    erw [_root_.VectorField.mpullback_apply, hS.zero, map_zero]
  refine ⟨R, hR, hP, fun z hz => ⟨?_, ?_⟩⟩
  · intro he
    by_contra hne
    exact hPz z hz hne he
  · intro he
    exact he ▸ h0

variable {d : ℕ}

theorem euclideanLocalDegree_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin (d + 1))) n)
    (hn : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ φ.source)
    {V : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hV : isolatedZero V (φ x)) :
    euclideanLocalDegree (_root_.VectorField.mpullback
        𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) φ V) x
      (isolatedZero_mpullback_partialDiffeomorph φ hn hx hV) =
        euclideanLocalDegree V (φ x) hV := by
  obtain ⟨S, hS⟩ := hV
  obtain ⟨A, _, R, hR, hP, hPz, hG, hGz, hH⟩ :=
    exists_sphereMap_coordinateChange_homotopy φ hn hx hS.pos hS.continuousOn hS.nonzero
  let P := _root_.VectorField.mpullback
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) φ V
  let G := _root_.VectorField.mpullback
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
    (fun z => φ x + A (z - x)) V
  have hGeq (z : EuclideanSpace ℝ (Fin (d + 1))) :
      G z = A.symm (V (φ x + A (z - x))) :=
    mpullback_affineCoordinate_eq A x z (φ x) V
  have hP0 : P x = 0 := by
    dsimp only [P]
    erw [_root_.VectorField.mpullback_apply, hS.zero, map_zero]
  have hG0 : G x = 0 := by
    rw [hGeq]
    simp only [sub_self, map_zero, add_zero, hS.zero]
    rfl
  have hiP : IsolatingRadius P x R := ⟨hR, hP, fun z hz =>
    ⟨fun he => by by_contra hne; exact hPz z hz hne he, fun he => he ▸ hP0⟩⟩
  have hiG : IsolatingRadius G x R := ⟨hR, hG, fun z hz =>
    ⟨fun he => by by_contra hne; exact hGz z hz hne he, fun he => he ▸ hG0⟩⟩
  have he : euclideanLocalDegree P x ⟨R, hiP⟩ = euclideanLocalDegree G x ⟨R, hiG⟩ := by
    erw [euclideanLocalDegree_eq_sphereDegree _ hiP ⟨R, hR, le_rfl⟩,
      euclideanLocalDegree_eq_sphereDegree _ hiG ⟨R, hR, le_rfl⟩]
    exact euclideanSphereDegree_eq_of_homotopy (hH ⟨R, hR, le_rfl⟩).some
  calc
    _ = euclideanLocalDegree G x ⟨R, hiG⟩ := he
    _ = euclideanLocalDegree (fun z => A.symm (V (φ x + A (z - x)))) x
        (isolatedZero_affineCoordinate A x (φ x) ⟨S, hS⟩) :=
      euclideanLocalDegree_congr ⟨R, hiG⟩ _ (Filter.Eventually.of_forall hGeq)
    _ = _ := euclideanLocalDegree_affineCoordinate A x (φ x) ⟨S, hS⟩

end Poincare.LocalDegree
