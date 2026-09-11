import DifferentialGeometry.Topology.SimplicialComplex.GeometricBoundaryEuler
import DifferentialGeometry.Topology.SimplicialComplex.LinkEulerSum

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Homology
open scoped Manifold
namespace DifferentialGeometry.Topology.SimplicialComplex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
  (hLK : L ≤ K) {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ n).boundary M)
include hLK e hboundary


theorem faceEulerChar_boundary_of_geometric_pair :
    faceEulerChar L.toPreAbstractSimplicialComplex =
      (1 - (-1 : ℤ) ^ n) * faceEulerChar K.toPreAbstractSimplicialComplex := by
  classical
  let F := (Set.toFinite K.faces).toFinset
  let B := (Set.toFinite L.faces).toFinset
  let w : Finset E → ℤ := fun s => -(-1 : ℤ) ^ s.card
  have hfilter : F.filter (fun s => s ∈ L.faces) = B := by
    ext s
    simp only [F, B, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hLK h, h⟩⟩
  have hsumL : (∑ s ∈ F, if s ∈ L.faces then w s else 0) =
      faceEulerChar L.toPreAbstractSimplicialComplex := by
    rw [← Finset.sum_filter, hfilter]
    rfl
  have hpoint (s : Finset E) (hs : s ∈ F) :
      1 - faceEulerChar (link K.toPreAbstractSimplicialComplex s) =
        (-1 : ℤ) ^ n * (w s - if s ∈ L.faces then w s else 0) := by
    have hsK : s ∈ K.faces := (Set.toFinite K.faces).mem_toFinset.mp hs
    rw [faceLink_values_of_geometric_boundary hLK e hboundary hsK]
    by_cases hsL : s ∈ L.faces
    · rw [if_pos hsL, if_pos hsL]
      ring
    · rw [if_neg hsL, if_neg hsL, sub_zero]
      have hc : s.card - 1 + 1 = s.card := Nat.sub_add_cancel
        (Finset.card_pos.mpr (K.nonempty_of_mem_faces hsK))
      have hw : w s = (-1 : ℤ) ^ (s.card - 1) := by
        change -(-1 : ℤ) ^ s.card = _
        conv_lhs => rw [← hc, pow_succ]
        ring
      rw [hw]
      ring
  have hsum : faceEulerChar K.toPreAbstractSimplicialComplex =
      (-1 : ℤ) ^ n * (faceEulerChar K.toPreAbstractSimplicialComplex -
        faceEulerChar L.toPreAbstractSimplicialComplex) := by
    conv_lhs => rw [← sum_one_sub_faceEulerChar_link K.toPreAbstractSimplicialComplex]
    change (∑ s ∈ F, (1 - faceEulerChar (link K.toPreAbstractSimplicialComplex s))) = _
    calc
      _ = ∑ s ∈ F, (-1 : ℤ) ^ n * (w s - if s ∈ L.faces then w s else 0) :=
        Finset.sum_congr rfl hpoint
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsumL]
        rfl
  have hsq : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  have hmul := congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z) hsum
  rw [← mul_assoc, hsq, one_mul] at hmul
  linarith


theorem eulerChar_boundary_of_geometric_pair (k : Type) [Field k] :
    eulerChar k (TopCat.of ((𝓡∂ n).boundary M)) =
      (1 - (-1 : ℤ) ^ n) * eulerChar k (TopCat.of M) := by
  rw [eulerChar_boundary_eq_faceEulerChar hLK e hboundary k,
    eulerChar_eq_faceEulerChar_of_geometric_homeomorphism e k]
  exact faceEulerChar_boundary_of_geometric_pair hLK e hboundary


theorem relativeEulerChar_boundary_of_geometric_pair (k : Type) [Field k] :
    relativeEulerChar (TopCat.of M) ((𝓡∂ n).boundary M) k =
      (-1 : ℤ) ^ n * eulerChar k (TopCat.of M) := by
  rw [relativeEulerChar_eq_sub (TopCat.of M) ((𝓡∂ n).boundary M) k
    (finiteHomologyType_boundary_of_geometric_pair hLK e hboundary k)
    (finiteHomologyType_of_geometric_homeomorphism e k),
    eulerChar_boundary_of_geometric_pair hLK e hboundary k]
  ring

end DifferentialGeometry.Topology.SimplicialComplex
