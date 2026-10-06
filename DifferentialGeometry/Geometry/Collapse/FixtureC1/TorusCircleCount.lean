import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleCentres
import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusEll

/-!
# The support count of the centre net of the flat torus (S-FIXTURE-C1b, F1, G3 file 1)

At most `401²` circle centres of the `R`-spaced net lie within `200 R` of a point. Every such centre
is the image of a node `(R a, R b, 0)` with integer `(a, b)` in a box of side `401` around the
integer part of the planar coordinates of a fixed lift of the point (the lift of the centre within
`200 R` of the lift of the point, then the period shifts of the nodes), so the centre set is
contained in the image of a finite box.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

section Count

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (N : ℕ)
  (hL0 : Λ.L 0 = N * R) (hL1 : Λ.L 1 = N * R)

include hL0 hL1 in
/-- **The centres within `200 R` of a point lie in the image of a box of side `401`.** -/
theorem torCentres_near_subset_image_FXC1 (hR : 0 < R) (x : Tor_FXC1 Λ) :
    ∃ B : Finset (ℤ × ℤ), B.card = 401 * 401 ∧
      torCentres_FXC1 Λ R N ∩ {j | dist x j < 200 * R} ⊆
        (fun z : ℤ × ℤ => torPi_FXC1 Λ (torNode_FXC1 R z.1 z.2)) '' (B : Set (ℤ × ℤ)) := by
  obtain ⟨xt, rfl⟩ := torPi_surjective_FXC1 Λ x
  let c₀ : ℤ := ⌊xt 0 / R⌋
  let c₁ : ℤ := ⌊xt 1 / R⌋
  refine ⟨Finset.Icc (c₀ - 200) (c₀ + 200) ×ˢ Finset.Icc (c₁ - 200) (c₁ + 200), ?_, ?_⟩
  · rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    congr 1 <;> omega
  · rintro j ⟨⟨⟨a, b⟩, -, rfl⟩, hj⟩
    obtain ⟨y, hy, hxy⟩ := exists_lift_of_dist_lt_FXC1 Λ xt _ hj
    obtain ⟨n, hn⟩ := torPi_eq_iff_FXC1.mp hy.symm
    have hy0 : y 0 = R * ((a + N * n.toInts 0 : ℤ) : ℝ) := by
      rw [hn]
      simp only [PiLp.add_apply, torNode_zero_FXC1, latticeVec_apply_FXC1, hL0]
      push_cast
      ring
    have hy1 : y 1 = R * ((b + N * n.toInts 1 : ℤ) : ℝ) := by
      rw [hn]
      simp only [PiLp.add_apply, torNode_one_FXC1, latticeVec_apply_FXC1, hL1]
      push_cast
      ring
    have hbd : ∀ (i : Fin 3) (z : ℤ), y i = R * (z : ℝ) →
        (⌊xt i / R⌋ - 200 : ℤ) ≤ z ∧ z ≤ ⌊xt i / R⌋ + 200 := by
      intro i z hz
      have h1 := PiLp.norm_apply_le (xt - y) i
      rw [PiLp.sub_apply, hz, Real.norm_eq_abs] at h1
      have h2 : |xt i - R * z| < 200 * R := lt_of_le_of_lt h1 hxy
      rw [abs_lt] at h2
      have h3 : xt i / R - 200 < z := by
        rw [sub_lt_iff_lt_add, div_lt_iff₀ hR]; nlinarith [h2.2]
      have h4 : (z : ℝ) < xt i / R + 200 := by
        have e : xt i / R + 200 = (xt i + 200 * R) / R := by field_simp
        rw [e, lt_div_iff₀ hR]; nlinarith [h2.1]
      have h5 := Int.floor_le (xt i / R)
      have h6 := Int.lt_floor_add_one (xt i / R)
      have h7 : (⌊xt i / R⌋ : ℝ) - 200 < z := by linarith
      have h8 : (z : ℝ) < ⌊xt i / R⌋ + 201 := by linarith
      have h9 : (⌊xt i / R⌋ : ℤ) - 200 < z := by exact_mod_cast h7
      have h10 : z < (⌊xt i / R⌋ : ℤ) + 201 := by exact_mod_cast h8
      constructor <;> omega
    refine ⟨(a + N * n.toInts 0, b + N * n.toInts 1), ?_, ?_⟩
    · have e0 := hbd 0 _ hy0
      have e1 := hbd 1 _ hy1
      simp only [Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
      exact ⟨⟨e0.1, e0.2⟩, ⟨e1.1, e1.2⟩⟩
    · exact torPi_node_shift_FXC1 Λ N hL0 hL1 a b _ _

include hL0 hL1 in
/-- **At most `401²` centres within `200 R` of a point.** -/
theorem torCentres_ncard_le_FXC1 (hR : 0 < R) (x : Tor_FXC1 Λ) :
    (torCentres_FXC1 Λ R N ∩ {j | dist x j < 200 * R}).ncard ≤ 401 * 401 := by
  obtain ⟨B, hB, hsub⟩ := torCentres_near_subset_image_FXC1 Λ N hL0 hL1 hR x
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_image_le (f := fun z : ℤ × ℤ => torPi_FXC1 Λ (torNode_FXC1 R z.1 z.2))
    (B.finite_toSet)
  rw [Set.ncard_coe_finset, hB] at h2
  exact h1.trans h2

end Count

end DifferentialGeometry.Geometry.Collapse
