import DifferentialGeometry.Geometry.Metric.ActualCloudSupportScale
import DifferentialGeometry.Geometry.Metric.ActualCloudPrunedPlanes
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Consumers of CFS26 and CFS27 on explicit data.
* CFS26: a one-chart packet on `ℝ` with the clipped cutoff `min 1 (200 - |p|)` and the 1-Lipschitz marker
  `max 0 (min 1 (200 - |z|))`; every pair of cloud points obeys CFS07 and every selection obeys (MCb).
* CFS27: in `ℝ²` with blocks `span{e₀}` (`R = 1`) and `span{e₁}` (`R = 1/4`), the pruned projection of the reference
  chart `0` fixes the actual image `e₀` and deletes the NONZERO second coordinate of the tilted graph direction
  `e₀ + e₁`; the retained first coordinate keeps the graph identity. -/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry

/-- The clipped marker is 1-Lipschitz. -/
theorem actualCloud_clipped_marker_lipschitz :
    LipschitzWith 1 (fun z : ℝ => max 0 (min 1 (200 - |z|))) := by
  have h : LipschitzWith 1 (fun z : ℝ => 200 - |z|) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
      show 200 - |x| - (200 - |y|) = -(|x| - |y|) by ring, abs_neg]
    exact abs_abs_sub_abs_le_abs_sub x y
  exact (h.const_min 1).const_max 0

/-- CFS26 consumer: the explicit one-chart packet satisfies CFS07 for all cloud pairs and (MCb) at `L = 128`. -/
theorem actualCloud_support_scale_consumer :
    (∀ p ∈ ball (0 : ℝ) 199, ∀ q ∈ ball (0 : ℝ) 199,
      dist p q ≤ 128 * max ((1 / 640 : ℝ) * 1) ((1 / 640 : ℝ) * 1) →
      (3 / 5 : ℝ) * 1 ≤ 1 ∧ (1 : ℝ) ≤ (5 / 3 : ℝ) * 1) ∧
    ∀ select : ℝ → ℝ, (∀ x ∈ (fun p : ℝ => p) '' ball 0 199, select x ∈ ball (0 : ℝ) 199 ∧ select x = x) →
      ∀ x ∈ (fun p : ℝ => p) '' ball 0 199, ∀ y ∈ (fun p : ℝ => p) '' ball 0 199,
        dist y x ≤ 128 * max ((1 / 640 : ℝ) * 1) ((1 / 640 : ℝ) * 1) →
        (1 / 640 : ℝ) * 1 / (5 / 3) ≤ (1 / 640 : ℝ) * 1 ∧
          (1 / 640 : ℝ) * 1 ≤ (5 / 3) * ((1 / 640 : ℝ) * 1) := by
  classical
  let ζ : ∀ _ : Unit, ball (0 : ℝ) (200 * (fun _ : ℝ => (1 : ℝ)) 0) → ℝ :=
    fun _ p => min 1 (200 - |(p : ℝ)|)
  have hmarker : ∀ (i : Unit) (p : ℝ), (fun (_ : Unit) (z : ℝ) => max 0 (min 1 (200 - |z|))) i
      ((fun p : ℝ => p) p) = (fun _ : ℝ => (1 : ℝ)) ((fun _ : Unit => (0 : ℝ)) i) *
      (Subtype.val : ball ((fun _ : Unit => (0 : ℝ)) i)
        ((fun _ : Unit => (200 : ℝ)) i * (fun _ : ℝ => (1 : ℝ)) ((fun _ : Unit => (0 : ℝ)) i)) → ℝ).extend
        (ζ i) 0 p := by
    intro i p
    simp only [one_mul]
    by_cases hp : p ∈ ball (0 : ℝ) (200 * 1)
    · have he := Function.Injective.extend_apply Subtype.val_injective (ζ i) (0 : ℝ → ℝ)
        (⟨p, hp⟩ : ball (0 : ℝ) (200 * 1))
      simp only at he
      rw [he]
      have hlt : |p| < 200 := by simpa [Real.dist_eq] using hp
      simp only [ζ]
      exact max_eq_right (le_min zero_le_one (by linarith))
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hp a.property)]
      have hge : 200 ≤ |p| := by
        by_contra h
        exact hp (by simpa [Real.dist_eq] using lt_of_not_ge h)
      simp only [Pi.zero_apply]
      exact max_eq_left (min_le_of_right_le (by linarith))
  have hcore : ∀ i : Unit, (fun _ : Unit => ball (0 : ℝ) 199) i ⊆
      ball ((fun _ : Unit => (0 : ℝ)) i)
        ((fun _ : Unit => (200 : ℝ)) i * (fun _ : ℝ => (1 : ℝ)) ((fun _ : Unit => (0 : ℝ)) i)) := by
    intro i
    simp only [mul_one]
    exact ball_subset_ball (by norm_num)
  have hres := actualCloud_support_scale_all_preimages (M := ℝ) (H := ℝ) (I := Unit)
    (fun p => p) (fun _ => (1 : ℝ)) (Λ := 0) (LipschitzWith.const 1)
    (fun _ => (0 : ℝ)) (fun _ => (200 : ℝ)) 1 le_rfl (fun _ => Or.inl rfl)
    (by norm_num) (fun _ => one_pos) ζ (fun _ z => max 0 (min 1 (200 - |z|)))
    (fun _ => actualCloud_clipped_marker_lipschitz) hmarker (fun _ => ball (0 : ℝ) 199) hcore
    (by
      intro i p hp
      have hlt : |p| < 199 := by simpa [Real.dist_eq] using hp
      exact min_eq_left (by linarith))
    (ball 0 199) (fun p hp => ⟨(), hp⟩) (σ := 1 / 640) (L := 128) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨hres.1, fun select hsel => hres.2 select hsel⟩

/-- CFS27 consumer: the reference chart `0` deletes the small block `span{e₁}`; the actual image `e₀` is fixed, the
tilted direction `e₀ + e₁` loses its nonzero second coordinate, and the retained first coordinate is unchanged. -/
theorem actualCloud_pruned_plane_consumer :
    let e : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun j => EuclideanSpace.single j 1
    let V : Fin 2 → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun j => ℝ ∙ e j
    let R : Fin 2 → ℝ := ![1, 1 / 4]
    let K := actualCloudPrunedProjection V R 0
    K (e 0) = e 0 ∧ (e 0 + e 1) 1 ≠ 0 ∧ K (e 0 + e 1) 1 = 0 ∧ K (e 0 + e 1) 0 = 1 := by
  intro e V R K
  let coord : Fin 2 → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := fun j =>
    innerSL ℝ (e j)
  have hcoord : ∀ j y, coord j y = y j := by
    intro j y
    simp only [coord, e, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  have hR0 : R 0 = 1 := rfl
  have hR1 : R 1 = 1 / 4 := rfl
  have hdel : ∀ j : Fin 2, R j ≤ R 0 / 2 ↔ j = 1 := by
    intro j
    fin_cases j <;> simp [hR0, hR1] <;> norm_num
  have hproj_zero : ∀ (j : Fin 2) (y : EuclideanSpace ℝ (Fin 2)), y j = 0 →
      (V j).starProjection y = 0 := by
    intro j y hy
    apply ((V j).starProjection_apply_eq_zero_iff).mpr
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← innerSL_apply_apply (𝕜 := ℝ)]
    change coord j y = 0
    rw [hcoord, hy]
  have hres := actualCloud_pruned_model_plane (M := Unit) (E := ℝ) (fun _ => e 0) (fun _ => 1) V
    (fun j y => coord j y) R
    (by intro j q; fin_cases j <;> simp [hcoord, e])
    (by
      intro j q hpos
      fin_cases j
      · simp [hR0]; norm_num
      · simp [hcoord, e] at hpos)
    (by
      intro j q hzero
      exact hproj_zero j (e 0) (by rw [← hcoord]; exact hzero))
    0 (by rw [hR0]; norm_num) () (by rw [hR0]; norm_num)
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (e 0 + e 1))
  obtain ⟨hfix, hplane, -⟩ := hres
  have hmem : K (e 0 + e 1) ∈ (V 1)ᗮ := by
    have h := (hplane 1 ((hdel 1).mpr rfl)).2
    apply h
    refine ⟨(1 : ℝ), ?_⟩
    simp [K]
  have hzero1 : K (e 0 + e 1) 1 = 0 := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← innerSL_apply_apply (𝕜 := ℝ)] at hmem
    change coord 1 (K (e 0 + e 1)) = 0 at hmem
    rwa [hcoord] at hmem
  have hretain : (coord 0).comp K = coord 0 := by
    apply actualCloudPrunedProjection_retained_identity V R 0 (coord 0)
    intro j hj v hv
    have hj1 := (hdel j).mp hj
    subst hj1
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hcoord]
    simp [e]
  refine ⟨hfix, ?_, hzero1, ?_⟩
  · simp [e]
  · have h := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L (e 0 + e 1)) hretain
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hcoord, hcoord] at h
    rw [h]
    simp [e]

end GC.MetricGeometry
