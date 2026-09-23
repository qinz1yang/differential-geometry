import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_separation_scales_of_locallyFinite {X ι : Type*} [MetricSpace X]
    {A : ι → Set X} (hA : ∀ i, IsCompact (A i)) (hlf : LocallyFinite A)
    {cap : ι → ℝ} (hcap : ∀ i, 0 < cap i) :
    ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧ (∀ i, ε i < cap i) ∧
      ∀ i j, Disjoint (A i) (A j) → ∀ x ∈ A i, ∀ y ∈ A j,
        ε i + ε j < dist x y := by
  classical
  let F : ι → Set X := fun i => ⋃ j : {j // Disjoint (A i) (A j)}, A j
  have hFc : ∀ i, IsClosed (F i) := fun i =>
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun j => (hA j).isClosed
  have hAF : ∀ i, Disjoint (A i) (F i) := by
    intro i
    refine Set.disjoint_left.mpr ?_
    intro x hx hxF
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxF
    exact Set.disjoint_left.mp j.2 hx hj
  have hsep : ∀ i, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A i, ∀ y ∈ F i, r < dist x y := by
    intro i
    obtain ⟨r, hr, hdist⟩ := Metric.exists_pos_forall_lt_edist (hA i) (hFc i) (hAF i)
    refine ⟨r, by exact_mod_cast hr, fun x hx y hy => ?_⟩
    have hd := hdist x hx y hy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hd
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hd
  choose r hr hdist using hsep
  refine ⟨fun i => min (cap i / 2) (r i / 3), fun i =>
    lt_min (by linarith [hcap i]) (by linarith [hr i]), fun i => ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith [hcap i])
  · intro i j hij x hx y hy
    have hxy := hdist i x hx y (mem_iUnion.mpr ⟨⟨j, hij⟩, hy⟩)
    have hyx := hdist j y hy x (mem_iUnion.mpr ⟨⟨i, hij.symm⟩, hx⟩)
    rw [dist_comm y x] at hyx
    have hi := min_le_right (cap i / 2) (r i / 3)
    have hj := min_le_right (cap j / 2) (r j / 3)
    linarith [hr i]

end DifferentialGeometry.Topology.PiecewiseLinear
