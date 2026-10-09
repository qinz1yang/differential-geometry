import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! ZSP04 (master207B, B:6531), base step in a coordinate interval: a compact subset of an open
set of the line is covered by the interiors of finitely many nondegenerate closed intervals inside
the open set whose endpoints avoid a prescribed finite set (the zero-face levels `∂C₃`). -/

set_option autoImplicit false
open Set Metric

namespace DifferentialGeometry.Topology

theorem exists_finite_Icc_cover_avoiding {K U F : Set ℝ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hF : F.Finite) :
    ∃ s : Finset (ℝ × ℝ), (∀ ab ∈ s, ab.1 < ab.2 ∧ Icc ab.1 ab.2 ⊆ U ∧ ab.1 ∉ F ∧ ab.2 ∉ F) ∧
      K ⊆ ⋃ ab ∈ s, Ioo ab.1 ab.2 := by
  have hloc : ∀ x ∈ K, ∃ ab : ℝ × ℝ, (ab.1 < ab.2 ∧ Icc ab.1 ab.2 ⊆ U ∧ ab.1 ∉ F ∧ ab.2 ∉ F) ∧
      x ∈ Ioo ab.1 ab.2 := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x (hKU hx)
    obtain ⟨a, ⟨ha1, ha2⟩, haF⟩ :=
      ((Ioo_infinite (by linarith : x - ε / 2 < x)).sdiff hF).nonempty
    obtain ⟨b, ⟨hb1, hb2⟩, hbF⟩ :=
      ((Ioo_infinite (by linarith : x < x + ε / 2)).sdiff hF).nonempty
    refine ⟨(a, b), ⟨by simp only; linarith, ?_, haF, hbF⟩, ⟨ha2, hb1⟩⟩
    intro y hy
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    simp only at hy
    constructor <;> linarith [hy.1, hy.2]
  choose! p hp using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Ioo (p x).1 (p x).2)
    (fun _ => isOpen_Ioo) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (hp x hx).2⟩)
  classical
  refine ⟨t.image (fun x : K => p x), ?_, ?_⟩
  · intro ab hab
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hab
    exact (hp x x.2).1
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
    exact mem_iUnion₂.mpr ⟨p x, Finset.mem_image_of_mem _ hxt, hyx⟩

end DifferentialGeometry.Topology
