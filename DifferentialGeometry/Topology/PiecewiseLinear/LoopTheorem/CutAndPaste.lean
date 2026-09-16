import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import Mathlib.Tactic.Group

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace SingularTwoCell

universe u

theorem exists_two_cells_of_isCrosscut
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) {p q : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCrosscut (frontier D.domain) A p q) :
    ∃ D₁ D₂ : SingularTwoCell M,
      D₁.domain ∪ D₂.domain = D.domain ∧
      D₁.domain ∩ D₂.domain = A ∧
      frontier D₁.domain = (D₁.domain ∩ frontier D.domain) ∪ A ∧
      frontier D₂.domain = (D₂.domain ∩ frontier D.domain) ∪ A ∧
      A ⊆ frontier D₁.domain ∧
      A ⊆ frontier D₂.domain ∧
      IsPLBall 1 (D₁.domain ∩ frontier D.domain) ∧
      IsPLBall 1 (D₂.domain ∩ frontier D.domain) ∧
      Set.range D₁.boundary =
        D '' (D₁.domain ∩ frontier D.domain) ∪ D '' A ∧
      Set.range D₂.boundary =
        D '' (D₂.domain ∩ frontier D.domain) ∪ D '' A ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 C → C ⊆ D.domain →
        Disjoint (interior C) A → C ⊆ D₁.domain ∨ C ⊆ D₂.domain := by
  obtain ⟨U, V, hU, hV, hunion, hinter, hfrontU, hfrontV, hAU, hAV,
    htraceU, htraceV, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut D.isPLBall_domain hA hcut
  have hUD : U ⊆ D.domain := hunion ▸ subset_union_left
  have hVD : V ⊆ D.domain := hunion ▸ subset_union_right
  have htraceUSub : U ∩ frontier D.domain ⊆ frontier U := by
    intro x hx
    apply (mem_frontier_iff_notMem_interior hx.1).mpr
    intro hxint
    exact (mem_frontier_iff_notMem_interior (hUD hx.1)).mp hx.2
      (interior_mono hUD hxint)
  have htraceVSub : V ∩ frontier D.domain ⊆ frontier V := by
    intro x hx
    apply (mem_frontier_iff_notMem_interior hx.1).mpr
    intro hxint
    exact (mem_frontier_iff_notMem_interior (hVD hx.1)).mp hx.2
      (interior_mono hVD hxint)
  have hfrontUSub : frontier U ⊆ (U ∩ frontier D.domain) ∪ A := by
    intro x hx
    rcases hfrontU hx with hxD | hxA
    · exact Or.inl ⟨hU.isPolyhedron.isClosed.frontier_subset hx, hxD⟩
    · exact Or.inr hxA
  have hfrontVSub : frontier V ⊆ (V ∩ frontier D.domain) ∪ A := by
    intro x hx
    rcases hfrontV hx with hxD | hxA
    · exact Or.inl ⟨hV.isPolyhedron.isClosed.frontier_subset hx, hxD⟩
    · exact Or.inr hxA
  have hfrontUEq : frontier U = (U ∩ frontier D.domain) ∪ A :=
    Subset.antisymm hfrontUSub (union_subset htraceUSub hAU)
  have hfrontVEq : frontier V = (V ∩ frontier D.domain) ∪ A :=
    Subset.antisymm hfrontVSub (union_subset htraceVSub hAV)
  let D₁ := D.restrict hU hUD
  let D₂ := D.restrict hV hVD
  refine ⟨D₁, D₂, hunion, hinter, hfrontUEq, hfrontVEq, hAU, hAV,
    htraceU, htraceV, ?_, ?_, rfl, rfl, hside⟩
  · change Set.range (D.restrict hU hUD).boundary =
      D '' (U ∩ frontier D.domain) ∪ D '' A
    rw [D.range_boundary_restrict hU hUD, hfrontUEq, image_union]
  · change Set.range (D.restrict hV hVD).boundary =
      D '' (V ∩ frontier D.domain) ∪ D '' A
    rw [D.range_boundary_restrict hV hVD, hfrontVEq, image_union]

end SingularTwoCell

theorem not_mem_or_not_mem_of_eq_mul_conj_mul_conj
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {l a b x y : G}
    (hl : l = a * (x * b * x⁻¹) * (y * a⁻¹ * y⁻¹)) (hlN : l ∉ N) :
    a ∉ N ∨ b ∉ N := by
  by_contra h
  rw [not_or] at h
  have ha : a ∈ N := not_not.mp h.1
  have hb : b ∈ N := not_not.mp h.2
  apply hlN
  rw [hl]
  exact N.mul_mem
    (N.mul_mem ha (‹N.Normal›.conj_mem b hb x))
    (‹N.Normal›.conj_mem a⁻¹ (N.inv_mem ha) y)

theorem not_mem_or_not_mem_of_eq_mul_conj_inv_mul
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {l a b x : G}
    (hl : l = a * (x * (b⁻¹ * a) * x⁻¹)) (hlN : l ∉ N) :
    a ∉ N ∨ b ∉ N := by
  by_contra h
  rw [not_or] at h
  have ha : a ∈ N := not_not.mp h.1
  have hb : b ∈ N := not_not.mp h.2
  apply hlN
  rw [hl]
  exact N.mul_mem ha
    (‹N.Normal›.conj_mem (b⁻¹ * a) (N.mul_mem (N.inv_mem hb) ha) x)

theorem four_path_mul_conj_inv_mul_factorization
    {G : Type*} [Group G] (s t u p : G) :
    s * t * u * p =
      (s * u) * ((u⁻¹ * t * u) * ((s * t⁻¹ * u * p⁻¹)⁻¹ * (s * u)) *
        (u⁻¹ * t * u)⁻¹) := by
  group

theorem not_mem_or_not_mem_of_four_path_factorization
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {s t u p : G} (hN : s * t * u * p ∉ N) :
    s * u ∉ N ∨ s * t⁻¹ * u * p⁻¹ ∉ N := by
  apply not_mem_or_not_mem_of_eq_mul_conj_inv_mul N
    (four_path_mul_conj_inv_mul_factorization s t u p) hN

end DifferentialGeometry.Topology.PiecewiseLinear
