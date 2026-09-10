import DifferentialGeometry.Topology.SimplicialComplex.GeometricBoundaryPair
import DifferentialGeometry.Topology.SimplicialComplex.GeometricManifoldDimension

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold
namespace Poincare.Topology.SimplicialComplex

private theorem faceEulerChar_link_eq_zero_of_card_bound {ι : Type*} [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) [Finite K.faces] (s : Finset ι)
    (hd : ∀ t ∈ K, t.card ≤ s.card) : faceEulerChar (link K s) = 0 := by
  have he : (Set.toFinite (link K s).faces).toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have ht' := (Set.toFinite (link K s).faces).mem_toFinset.mp ht
    have hle := card_add_card_le_of_mem_link K hd ht'
    have hpos := Finset.card_pos.mpr ht'.1
    omega
  simp only [faceEulerChar, he, Finset.sum_empty]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
  (hLK : L ≤ K) {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ n).boundary M)
include hLK e hboundary


theorem boundaryFace_card_lt_of_geometric_pair {d : ℕ}
    (hd : ∀ t ∈ K.faces, t.card ≤ d) {s : Finset E} (hs : s ∈ L.faces) : s.card < d := by
  classical
  have hle := hd s (hLK hs)
  by_contra hnot
  have hc : s.card = d := by omega
  have hzero := faceEulerChar_link_eq_zero_of_card_bound K.toPreAbstractSimplicialComplex s
    (fun t ht => (hd t ht).trans_eq hc.symm)
  have hone := faceLink_values_of_geometric_boundary hLK e hboundary (hLK hs)
  rw [if_pos hs] at hone
  omega


theorem boundaryFace_card_le_of_geometric_pair {s : Finset E} (hs : s ∈ L.faces) :
    s.card ≤ n := by
  have hlt := boundaryFace_card_lt_of_geometric_pair hLK e hboundary
    (fun t ht => face_card_le_of_manifold_homeomorph (n := n) K e t ht) hs
  omega

end Poincare.Topology.SimplicialComplex

namespace Poincare.Topology.SimplicialComplex
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
  (hLK : L ≤ K) {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanHalfSpace 3) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ 3).boundary M)
include hLK e hboundary

open Classical in
theorem triangle_cofaces_of_geometric_boundary {s : Finset E}
    (hs : s ∈ facesOfCard K.toPreAbstractSimplicialComplex 3) :
    (cofaces K.toPreAbstractSimplicialComplex s 4).card = if s ∈ L.faces then 1 else 2 := by
  classical
  have hd : ∀ t ∈ K.faces, t.card ≤ 4 :=
    fun t ht => face_card_le_of_manifold_homeomorph (n := 3) K e t ht
  obtain ⟨hsK, hcard⟩ := (mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
  have hdlink : ∀ t ∈ link K.toPreAbstractSimplicialComplex s, t.card ≤ 1 := by
    intro t ht
    have hle := card_add_card_le_of_mem_link K.toPreAbstractSimplicialComplex hd ht
    omega
  have hEuler := faceEulerChar_eq_sum (link K.toPreAbstractSimplicialComplex s) 1 hdlink
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, facesOfCard_zero, Finset.card_empty, Nat.cast_zero,
    mul_zero, zero_add, pow_one, neg_neg, one_mul] at hEuler
  rw [card_facesOfCard_link K.toPreAbstractSimplicialComplex s 1 (by decide), hcard] at hEuler
  have hvalue := faceLink_values_of_geometric_boundary hLK e hboundary hsK
  norm_num [hcard] at hvalue
  rw [hEuler] at hvalue
  split_ifs at hvalue ⊢ <;> exact_mod_cast hvalue

open Classical in
theorem edgeLink_values_of_geometric_boundary {s : Finset E}
    (hs : s ∈ facesOfCard K.toPreAbstractSimplicialComplex 2) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) = if s ∈ L.faces then 1 else 0 := by
  classical
  obtain ⟨hsK, hcard⟩ := (mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
  have hvalue := faceLink_values_of_geometric_boundary hLK e hboundary hsK
  simpa only [hcard, Nat.reduceSub, pow_one, pow_succ, pow_zero, one_mul,
    neg_mul_neg, sub_self] using hvalue

end Poincare.Topology.SimplicialComplex
