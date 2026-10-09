import DifferentialGeometry.Geometry.Exponential.Flat.FixedAxisCyclic
import Mathlib.GroupTheory.Index

/-!
A finite positive three-dimensional isometry group preserving an unoriented line has an
actual cyclic normal subgroup of index at most two. This is the fixed-vector stabilizer;
its two-point orbit bounds the index and its actual SO3 image proves cyclicity.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_lineHolonomy_cyclicSubgroup (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3))
    [instH : Finite H] (hpos : ∀ g : H, 0 < LinearMap.det g.val.toLinearMap)
    (q : E3) (hq : q ≠ 0) (hline : ∀ g : H, g.val q = q ∨ g.val q = -q) :
    ∃ K : Subgroup H, IsCyclic K ∧ K.Normal ∧ K.index ≤ 2 ∧
      ∀ g : H, g ∈ K ↔ g.val q = q := by
  let instAction : MulAction H E3 :=
    { smul := fun g x => g.val x
      one_smul := by intro x; rfl
      mul_smul := by intro g h x; rfl }
  let K := MulAction.stabilizer H q
  have hK (g : H) : g ∈ K ↔ g.val q = q := Iff.rfl
  let J := K.map H.subtype
  let e : K ≃* J := K.equivMapOfInjective H.subtype Subtype.val_injective
  let instJ : Finite J := Finite.of_equiv K e.toEquiv
  have hjpos (g : J) : 0 < LinearMap.det g.val.toLinearMap := by
    obtain ⟨a, ha, he⟩ := g.property
    rw [← he]
    exact hpos a
  have hjfix (g : J) : g.val q = q := by
    obtain ⟨a, ha, he⟩ := g.property
    rw [← he]
    exact (hK a).mp ha
  let instCyclic : IsCyclic J := finitePositive_fixedAxis_isCyclic J hjpos q hq hjfix
  have hcyclic : IsCyclic K := isCyclic_of_injective e.toMonoidHom e.injective
  have hnormal : K.Normal := by
    constructor
    intro n hn g
    have hnq := (hK n).mp hn
    have hninv : n.val ((g⁻¹).val q) = (g⁻¹).val q := by
      rcases hline g⁻¹ with h | h
      · rw [h, hnq]
      · rw [h, map_neg, hnq]
    change g.val (n.val (g.val.symm q)) = q
    change n.val (g.val.symm q) = g.val.symm q at hninv
    rw [hninv, g.val.apply_symm_apply]
  have hindex : K.index ≤ 2 := by
    change (MulAction.stabilizer H q).index ≤ 2
    rw [MulAction.index_stabilizer]
    have horbit : MulAction.orbit H q ⊆ ({q, -q} : Set E3) := by
      intro x hx
      obtain ⟨g, rfl⟩ := hx
      change g.val q ∈ ({q, -q} : Set E3)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hline g
    have hpair : ({q, -q} : Set E3).ncard ≤ 2 := by
      simpa only [Set.ncard_singleton] using Set.ncard_insert_le q ({-q} : Set E3)
    exact (Set.ncard_le_ncard horbit).trans hpair
  exact ⟨K, hcyclic, hnormal, hindex, hK⟩

end DifferentialGeometry.Geometry.FlatSurface
