import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# An inhabitant of `Cfs15StageOutput`: the flat cloud

The first consumer of `exists_cfs15StageOutput_C15`: a flat cloud — the unit-ball piece
`S = L ∩ B̄(0, 1)` of a `k`-dimensional subspace `L`, the whole subspace as enlarged cloud `T = L`,
constant radius `1` and constant plane `L` — satisfies CFS15's hypotheses at every quality, so it
carries a `Cfs15StageOutput k K ε c_w S L 1 L` (an actual `k`-dimensional zero set with its nearest
map, from one kernel call), and §2.3's exit puts the zero set inside `L`.

* `exists_cfs15StageOutput_flat_C15`; `flat_zeroSet_subset_C15`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace GC.MetricGeometry

universe u

/-- An affine subspace through a point of the direction is the direction itself. -/
theorem affineSubspace_mk'_coe_of_mem_C15 {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (L : Submodule ℝ H) {x : H} (hx : x ∈ L) :
    (AffineSubspace.mk' x L : Set H) = L := by
  ext y
  change y ∈ AffineSubspace.mk' x L ↔ y ∈ L
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  exact L.sub_mem_iff_left hx

/-- **The flat cloud carries a stage output.** For `0 < ε ≤ 1/10` (radius ratio `B = 1`) there
is `c_w ≥ 0` such that for every `k`-dimensional subspace `L` of a finite-dimensional inner
product space, the cloud `S = L ∩ B̄(0, 1) ⊆ T = L` with radius `1` and plane `L` has a
`Cfs15StageOutput k K ε c_w S L 1 L`. -/
theorem exists_cfs15StageOutput_flat_C15 (k K : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (L : Submodule ℝ H), Module.finrank ℝ L = k →
        Nonempty (Cfs15StageOutput k K ε cw ((L : Set H) ∩ closedBall 0 1) (L : Set H)
          (fun _ => 1) (fun _ => L)) := by
  obtain ⟨cw, hcw, δ₀, hδ₀, h⟩ := exists_cfs15StageOutput_C15.{u} k K 1 ε le_rfl hε hεsmall
  refine ⟨cw, hcw, fun H _ _ _ L hL => ?_⟩
  refine h H _ _ inter_subset_left
    ((isCompact_closedBall (0 : H) 1).totallyBounded.subset inter_subset_right) (fun _ => 1)
    (fun _ => L) (fun _ _ => hL) 1 1 δ₀ one_pos (fun _ _ => le_rfl) (fun _ _ => le_rfl) hδ₀
    le_rfl (fun _ _ _ _ _ => by norm_num) ?_
  intro x hx
  rw [affineSubspace_mk'_coe_of_mem_C15 L hx.1, hausdorffEDist_self]
  exact zero_le

/-- §2.3's exit on the flat cloud: the native zero set of a flat output lies in `L`. -/
theorem flat_zeroSet_subset_C15 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} (L : Submodule ℝ H)
    (O : Cfs15StageOutput k K ε cw ((L : Set H) ∩ closedBall 0 1) (L : Set H) (fun _ => 1)
      (fun _ => L)) : O.Z ⊆ L :=
  O.zeroSet_subset_stageQ L (fun _ hx => hx.1) (fun _ _ => le_rfl)

end GC.MetricGeometry
