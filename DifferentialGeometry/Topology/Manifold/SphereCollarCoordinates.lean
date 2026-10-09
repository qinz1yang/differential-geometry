import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]
  {e : Metric.sphere (0 : E) 1 → M}
  (d : SmoothTwoSidedCollar (𝓡 n) I e)

private def reverseRadius : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := 1 - r
  invFun r := 1 - r
  left_inv r := by dsimp; ring
  right_inv r := by dsimp; ring
  contMDiff_toFun := contMDiff_const.sub contMDiff_id
  contMDiff_invFun := contMDiff_const.sub contMDiff_id

private def reverseRadiusProd :
    (Metric.sphere (0 : E) 1 × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), (𝓡 n).prod 𝓘(ℝ, ℝ)⟯
      (Metric.sphere (0 : E) 1 × ℝ) :=
  (Diffeomorph.refl (𝓡 n) _ ∞).prodCongr reverseRadius

def radialPartialDiffeomorph (v : Metric.sphere (0 : E) 1) :
    _root_.PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  exact ((Manifold.spherePolarChart (n := n) v).symm.trans
    (reverseRadiusProd (E := E) (n := n)).toPartialDiffeomorph).trans d.toPartialDiffeomorph

theorem radialPartialDiffeomorph_apply (v z : Metric.sphere (0 : E) 1) (r : ℝ)
    (hr : 0 < r) (ht : 1 - r ∈ Ioo (-d.radius) d.radius) :
    d.radialPartialDiffeomorph v (r • (z : E)) =
      d.toFun (z, ⟨1 - r, ht⟩) := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  change d.toPartialDiffeomorph ((reverseRadiusProd (E := E) (n := n))
    ((Manifold.spherePolarChart (n := n) v).symm (r • (z : E)))) = _
  rw [Manifold.spherePolarChart_symm_apply, Manifold.sphereDirection_pos_smul v z hr]
  have hn : ‖r • (z : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  rw [hn]
  exact d.toPartialDiffeomorph_apply (z, ⟨1 - r, ht⟩)

theorem mem_radialPartialDiffeomorph_source (v z : Metric.sphere (0 : E) 1) (r : ℝ)
    (hr : 0 < r) (ht : 1 - r ∈ Ioo (-d.radius) d.radius) :
    r • (z : E) ∈ (d.radialPartialDiffeomorph v).source := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · exact smul_ne_zero (ne_of_gt hr) (ne_zero_of_mem_unit_sphere z)
  · change (reverseRadiusProd (E := E) (n := n))
      ((Manifold.spherePolarChart (n := n) v).symm (r • (z : E))) ∈ d.toPartialDiffeomorph.source
    rw [d.toPartialDiffeomorph_source, Manifold.spherePolarChart_symm_apply,
      Manifold.sphereDirection_pos_smul v z hr]
    have hn : ‖r • (z : E)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
    rw [hn]
    exact ⟨trivial, ht⟩

@[simp] theorem radialPartialDiffeomorph_sphere (v z : Metric.sphere (0 : E) 1) :
    d.radialPartialDiffeomorph v (z : E) = e z := by
  have h := d.radialPartialDiffeomorph_apply v z 1 zero_lt_one
    (by simp only [sub_self]; exact ⟨neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
  simpa only [one_smul, sub_self, d.toFun_zero] using h

theorem sphere_subset_radialPartialDiffeomorph_source (v : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 ⊆ (d.radialPartialDiffeomorph v).source := by
  intro x hx
  have h := d.mem_radialPartialDiffeomorph_source v ⟨x, hx⟩ 1 zero_lt_one
    (by simp only [sub_self]; exact ⟨neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
  simpa only [one_smul] using h

theorem radialPartialDiffeomorph_symm_apply (v : Metric.sphere (0 : E) 1) (p : d.neighborhood) :
    (d.radialPartialDiffeomorph v).symm p.val =
      (1 - (d.toDiffeomorph.symm p).2.val) • ((d.toDiffeomorph.symm p).1 : E) := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  change Manifold.spherePolarChart (n := n) v
    ((reverseRadiusProd (E := E) (n := n)).symm (d.toPartialDiffeomorph.symm p.val)) = _
  rw [d.toPartialDiffeomorph_symm_apply p]
  rfl

theorem mem_radialPartialDiffeomorph_target (v : Metric.sphere (0 : E) 1)
    (hwidth : d.radius ≤ 1) (p : d.neighborhood) :
    p.val ∈ (d.radialPartialDiffeomorph v).target := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  refine ⟨?_, trivial, ?_⟩
  · change p.val ∈ d.toPartialDiffeomorph.target
    rw [d.toPartialDiffeomorph_target]
    exact p.property
  · change 0 < ((reverseRadiusProd (E := E) (n := n)).symm
      (d.toPartialDiffeomorph.symm p.val)).2
    rw [d.toPartialDiffeomorph_symm_apply p]
    change 0 < 1 - (d.toDiffeomorph.symm p).2.val
    linarith [(d.toDiffeomorph.symm p).2.property.2]

theorem norm_radialPartialDiffeomorph_symm (v : Metric.sphere (0 : E) 1)
    (hwidth : d.radius ≤ 1) (p : d.neighborhood) :
    ‖(d.radialPartialDiffeomorph v).symm p.val‖ = 1 - (d.toDiffeomorph.symm p).2.val := by
  rw [d.radialPartialDiffeomorph_symm_apply v p, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith [(d.toDiffeomorph.symm p).2.property.2] :
      0 < 1 - (d.toDiffeomorph.symm p).2.val), norm_eq_of_mem_sphere, mul_one]

theorem mem_radialPartialDiffeomorph_source_iff (v : Metric.sphere (0 : E) 1) (x : E) :
    x ∈ (d.radialPartialDiffeomorph v).source ↔
      x ≠ 0 ∧ 1 - ‖x‖ ∈ Ioo (-d.radius) d.radius := by
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨v⟩
  change ((x ∈ ((Manifold.spherePolarChart (n := n) v).symm.trans
    (reverseRadiusProd (E := E) (n := n)).toPartialDiffeomorph).source) ∧
    (reverseRadiusProd (E := E) (n := n))
      ((Manifold.spherePolarChart (n := n) v).symm x) ∈ d.toPartialDiffeomorph.source) ↔ _
  rw [d.toPartialDiffeomorph_source]
  change ((x ≠ 0 ∧ True) ∧ (True ∧ 1 - ‖x‖ ∈ Ioo (-d.radius) d.radius)) ↔ _
  simp

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
