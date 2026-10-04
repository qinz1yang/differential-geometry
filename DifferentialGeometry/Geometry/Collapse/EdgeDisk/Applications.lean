import DifferentialGeometry.Geometry.Collapse.EdgeDisk.AdjustedScale
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.HeightQuotient
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.ProperRestriction
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FibreSaturation
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CompactEdgePiece
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.ReplacementStratum
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FaceIndependence
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.DegreeTwoMultigraph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumers of the EDP/FDC kernels (lane W4-EDP)

* `edgeHeight_value_of_adjustedScale`: EDP01's output form `|s - ρ| ≤ C_ρΛρ` (with (AE) and the
  normalization by `R_i`) feeds EDP03's value estimate directly in physical units:
  `|A/s - P/ρ| < 2c₃ + 10 C_ρΛΔ`.
* `adjustedScale_slow_const`: the global EDP01 kernel on `ℝ` for a constant scale blended with a
  constant cloud value by a constant cutoff.
* `circleHeight_upper_isProperMap`: EDP04's properness for the height `Re` on the compact circle,
  restricted to the open base `(-1, 1)` and the closed half `Im ≥ 0` (a closed vertical condition).
* `circle_surjective_of_injective`: EDP06's kernel gives that every continuous injective self-map
  of the circle is onto.
* `circle_axis_points_isCompact`: FDC02's kernel on the circle.
* `corner_pair_plane_bijective`: EDP06's corner kernel on the plane with identity coordinates.
* `loop_cycle_decomposition`, `parallel_pair_cycle_decomposition`: the degree-two lemma for one
  loop and for two parallel edges.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val

/-- **EDP01 → EDP03 consumer.** In physical units: if the adjusted scale obeys EDP01's value bound
`|s - ρ| ≤ κρ` and the adjusted height vector obeys (AE) `|A - P| < c₃ρ`, then on the band
`0 ≤ P/ρ < 5Δ` the actual height `A/s` is within `2c₃ + 10κΔ` of the original height `P/ρ`. -/
theorem edgeHeight_value_of_adjustedScale {ρ s A P R c₃ κ Δ : ℝ} (hR : 0 < R)
    (hρR : 99 / 100 < ρ / R) (hs : |s - ρ| ≤ κ * ρ) (hA : |A - P| < c₃ * ρ) (ht0 : 0 ≤ P / ρ)
    (ht : P / ρ < 5 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ) (hϑ : κ * Δ < 1 / 1000000) :
    |A / s - P / ρ| < 2 * c₃ + 10 * (κ * Δ) := by
  have hρ : 0 < ρ := by
    have := (lt_div_iff₀ hR).mp hρR
    linarith
  have hS : |s / R - ρ / R| ≤ κ * (ρ / R) := by
    rw [← sub_div, abs_div, abs_of_pos hR, mul_div_assoc']
    exact div_le_div_of_nonneg_right hs hR.le
  have hB : |A / R - P / R| < c₃ * (ρ / R) := by
    rw [← sub_div, abs_div, abs_of_pos hR, mul_div_assoc']
    exact div_lt_div_of_pos_right hA hR
  have hq : P / R / (ρ / R) = P / ρ := by
    field_simp
  have hT : A / R / (s / R) = A / s := by
    rcases eq_or_ne s 0 with h0 | h0
    · simp [h0]
    · field_simp
  have h := edgeHeight_quotient_value_lt (p := P / R) (B := A / R) hρR hS hB (by rwa [hq])
    (by rwa [hq]) hΔ hκ hϑ
  rwa [hq, hT] at h

/-- **EDP01 consumer.** The global kernel for constant data on `ℝ`: the scale `1`, the cloud value
`1 + ε` and the cutoff `1/2` give a blend within `ε` of the scale and with zero derivative bound
`(1 + 0 + 1·0)·1`. -/
theorem adjustedScale_slow_const {ε : ℝ} (hε : |ε| ≤ 1) (x : ℝ) :
    |(1 - 1 / 2) * 1 + 1 / 2 * (1 + ε) - 1| ≤ 1 * 1 * 1 ∧
      ‖fderiv ℝ (fun _ : ℝ => (1 - 1 / 2) * (1 : ℝ) + 1 / 2 * (1 + ε)) x‖ ≤ (1 + 0 + 1 * 0) * 1 := by
  have h := adjustedScale_slow (ρ := fun _ : ℝ => (1 : ℝ)) (z := fun _ => 1 + ε)
    (χ := fun _ => 1 / 2) (Λ := 1) (K₁ := 1) (K₂ := 0) (K₃ := 0) (by norm_num) (by norm_num)
    (fun _ => differentiableAt_const _) (fun _ => one_pos) (fun _ => by simp)
    (fun _ => by norm_num)
    (fun _ _ => ⟨differentiableAt_const _, differentiableAt_const _, by simpa using hε, by simp,
      by simp⟩) x
  exact ⟨h.2.1, h.2.2⟩

/-- **EDP04 consumer.** The height `Re` on the compact circle, restricted to the open base `(-1,1)`
and the closed upper half, is a proper map onto `(-1, 1)`. -/
theorem circleHeight_upper_isProperMap :
    IsProperMap (fun x : ↥((fun z : Circle => (z : ℂ).re) ⁻¹' Ioo (-1 : ℝ) 1 ∩
        {z : Circle | 0 ≤ (z : ℂ).im}) => (⟨(x.1 : ℂ).re, x.2.1⟩ : Ioo (-1 : ℝ) 1)) :=
  isProperMap_restrictPreimage_inter_isClosed (M := Circle)
    (Complex.continuous_re.comp continuous_circle_coe) (Ioo (-1 : ℝ) 1)
    (isClosed_le continuous_const (Complex.continuous_im.comp continuous_circle_coe))

/-- **EDP06 consumer.** Every continuous injective self-map of the circle is surjective. -/
theorem circle_surjective_of_injective {c : Circle → Circle} (hc : Continuous c)
    (hinj : Function.Injective c) : Function.Surjective c := by
  have hrange := range_eq_of_range_subset_of_isEmbedding (F := EuclideanSpace ℝ (Fin 1))
    (d := (id : Circle → Circle)) hc hinj Topology.IsEmbedding.id (by simp)
  rw [range_id] at hrange
  exact range_eq_univ.mp hrange

/-- **FDC02 consumer.** On the circle, the points with `Re = 0` and `|Im| < 2` (strict witness)
form a compact set: the weak condition `|Im| ≤ 2` adds no limit point. -/
theorem circle_axis_points_isCompact :
    IsCompact {z : Circle | (z : ℂ).re = 0 ∧ |(z : ℂ).im| < 2} := by
  apply isCompact_of_weak_limit_replacement (M := Circle) (ι := Unit) isClosed_univ (subset_univ _)
    (fun _ (z : Circle) => (z : ℂ).re) (fun _ (z : Circle) => (z : ℂ).im)
    (fun _ => Complex.continuous_re.comp continuous_circle_coe)
    (fun _ => Complex.continuous_im.comp continuous_circle_coe) (fun _ => 0) (fun _ => 2)
  · rintro z ⟨h1, h2⟩
    exact ⟨(), h1, h2⟩
  · intro z _ _ h1 _
    refine ⟨h1, ?_⟩
    have hz := Complex.abs_im_le_norm (z : ℂ)
    rw [Circle.norm_coe] at hz
    linarith

/-- **EDP06 consumer.** On the plane with base coordinates the identity, the face differentials
`(2 dx, dy)` are an invertible pair. -/
theorem corner_pair_plane_bijective :
    Function.Bijective fun w : ℝ × ℝ => ((2 : ℝ) * w.1, w.2) :=
  corner_base_pair_bijective (V := ℝ × ℝ) (W := ℝ × ℝ) (by simp)
    (LinearMap.id : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) (LinearMap.id : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) (fun y => ⟨y, rfl⟩)
    two_ne_zero

end DifferentialGeometry.Geometry.Collapse.EdgeDisk

namespace GC.GraphManifold

/-- **Degree-two consumer.** One vertex with one loop is a single cycle. -/
theorem loop_cycle_decomposition :
    ∃ (C : Type) (n : C → ℕ), Finite C ∧ (∀ c, 0 < n c) ∧
      ∃ (vtx : (Σ c, Fin (n c)) ≃ Unit) (edg : (Σ c, Fin (n c)) ≃ Unit),
        ∀ c k, s((fun _ : Unit => ()) (edg ⟨c, k⟩), (fun _ : Unit => ()) (edg ⟨c, k⟩)) =
          s(vtx ⟨c, k⟩, vtx ⟨c, finRotate (n c) k⟩) :=
  exists_cycle_decomposition_of_degree_two (fun _ : Unit => ()) (fun _ : Unit => ()) (by decide)

/-- **Degree-two consumer.** Two vertices joined by two parallel edges form one cycle. -/
theorem parallel_pair_cycle_decomposition :
    ∃ (C : Type) (n : C → ℕ), Finite C ∧ (∀ c, 0 < n c) ∧
      ∃ (vtx : (Σ c, Fin (n c)) ≃ Bool) (edg : (Σ c, Fin (n c)) ≃ Bool),
        ∀ c k, s((fun _ : Bool => false) (edg ⟨c, k⟩), (fun _ : Bool => true) (edg ⟨c, k⟩)) =
          s(vtx ⟨c, k⟩, vtx ⟨c, finRotate (n c) k⟩) :=
  exists_cycle_decomposition_of_degree_two (fun _ : Bool => false) (fun _ : Bool => true)
    (by decide)

end GC.GraphManifold
