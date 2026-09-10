import DifferentialGeometry.Topology.SimplicialSet.RealizationEulerCharacteristic
import DifferentialGeometry.Topology.SimplicialSet.BoundaryHomeomorphism
import DifferentialGeometry.Topology.SimplicialComplex.Simplex

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Simplicial
namespace Poincare.Simplex
open Poincare.Topology.SimplicialComplex

private def boundaryRealizationCoordinates (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet) ≃ₜ boundary (Fin (n + 1)) :=
  (Poincare.SSet.boundaryRealizationHomeomorph n).trans (Homeomorph.ulift.sets rfl)


theorem finiteHomologyType_boundary (k : Type) [Field k] (n : ℕ) :
    Poincare.Homology.finiteHomologyType k (TopCat.of (boundary (Fin (n + 1)))) :=
  (Poincare.Homology.finiteHomologyType_iff_of_homeomorph k (boundaryRealizationCoordinates n)).mp
    (Poincare.SSet.finiteHomologyType_realization k (_root_.SSet.boundary n : _root_.SSet))

private def boundaryNondegenerateEquiv {n d : ℕ} (hd : d < n) :
    (_root_.SSet.boundary n : _root_.SSet).nonDegenerate d ≃
      (Δ[n] : _root_.SSet).nonDegenerate d where
  toFun x := ⟨x.val.val, ((_root_.SSet.boundary n).mem_nonDegenerate_iff x.val).mp x.prop⟩
  invFun x := ⟨⟨x.val, by rw [_root_.SSet.boundary_obj_eq_univ d n hd]; trivial⟩,
    ((_root_.SSet.boundary n).mem_nonDegenerate_iff _).mpr x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem boundary_count {n d : ℕ} (hd : d < n) :
    Nat.card ((_root_.SSet.boundary n : _root_.SSet).nonDegenerate d) =
      (facesOfCard (boundarySimplex (Finset.univ : Finset (Fin (n + 1)))) (d + 1)).card := by
  rw [Nat.card_congr (boundaryNondegenerateEquiv hd),
    Nat.card_congr _root_.SSet.stdSimplex.nonDegenerateEquiv', Nat.card_eq_fintype_card]
  rw [card_facesOfCard_boundarySimplex_of_lt _ (d + 1) (by omega) (by simpa)]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp


theorem eulerChar_boundary (k : Type) [Field k] (n : ℕ) :
    Poincare.Homology.eulerChar k (TopCat.of (boundary (Fin (n + 1)))) = 1 - (-1 : ℤ)^n := by
  rw [← Poincare.Homology.eulerChar_eq_of_homeomorph k (boundaryRealizationCoordinates n),
    Poincare.SSet.eulerChar_realization_eq_sum_card_nonDegenerate k _ n]
  have hd : ∀ s ∈ boundarySimplex (Finset.univ : Finset (Fin (n + 1))), s.card ≤ n := by
    intro s hs
    have := Finset.card_lt_card hs.2
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have he := faceEulerChar_eq_sum (boundarySimplex (Finset.univ : Finset (Fin (n + 1)))) n hd
  have hχ := faceEulerChar_boundarySimplex (Finset.univ_nonempty (α := Fin (n + 1)))
  rw [he] at hχ
  simp only [Finset.card_univ, Fintype.card_fin, pow_succ] at hχ
  rw [Finset.sum_range_succ', facesOfCard_zero, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hχ
  convert hχ using 1
  · apply Finset.sum_congr rfl
    intro d hd
    rw [boundary_count (Finset.mem_range.mp hd), pow_succ]
    ring
  · ring

end Poincare.Simplex
