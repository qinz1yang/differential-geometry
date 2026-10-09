import DifferentialGeometry.Analysis.InnerProductSpace.AffineProjectionDistance
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry

theorem zero_set_subset_variable_ball_union_of_affine_test
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I T : Set H) (r : H → ℝ) (P : I → Submodule ℝ H)
    [∀ i : I, (P i).HasOrthogonalProjection] (η : H → H)
    (A E δ B ε : ℝ) (hE : 0 ≤ E) (hδ : 0 < δ) (hB : 0 < B)
    (hr : ∀ i : I, 0 < r i) (hinterior : A * δ < 1)
    (haccuracy : B * (E + 2) * δ < ε)
    (hcloud : ∀ i : I, hausdorffEDist (T ∩ ball (i : H) (r i / δ))
      ((AffineSubspace.mk' (i : H) (P i) : Set H) ∩ ball (i : H) (r i / δ)) ≤
        ENNReal.ofReal (δ * r i))
    (herror : ∀ i : I, ∀ w ∈ ball (i : H) (A * r i),
      ‖η w - (P i)ᗮ.starProjection (w - i)‖ ≤ E * δ * r i)
    (hscale : ∀ i : I, ∀ q ∈ T,
      dist q i < (A + 2 * δ) * r i → r i ≤ B * r q) :
    {w | w ∈ ⋃ i : I, ball (i : H) (A * r i) ∧ η w = 0} ⊆
      ⋃ q ∈ T, ball q (ε * r q) := by
  intro w hw
  obtain ⟨i, hwi⟩ := mem_iUnion.mp hw.1
  have hri := hr i
  let p : H := (i : H) + (P i).starProjection (w - i)
  have hpcenter : dist p i ≤ dist w i := by
    simpa only [p, dist_eq_norm, add_sub_cancel_left] using
      (P i).norm_starProjection_apply_le (w - i)
  have htestRadius : A * r i < r i / δ := by
    apply (lt_div_iff₀ hδ).mpr
    nlinarith [mul_lt_mul_of_pos_right hinterior hri]
  have hpplane : p ∈ (AffineSubspace.mk' (i : H) (P i) : Set H) := by
    change p - i ∈ P i
    simpa only [p, add_sub_cancel_left] using (P i).starProjection_apply_mem (w - i)
  have hptest : p ∈ (AffineSubspace.mk' (i : H) (P i) : Set H) ∩ ball (i : H) (r i / δ) :=
    ⟨hpplane, (hpcenter.trans_lt hwi).trans htestRadius⟩
  have hstrict : ENNReal.ofReal (δ * r i) < ENNReal.ofReal (2 * δ * r i) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_pos hδ hri]
  have hswap : hausdorffEDist
      ((AffineSubspace.mk' (i : H) (P i) : Set H) ∩ ball (i : H) (r i / δ))
      (T ∩ ball (i : H) (r i / δ)) < ENNReal.ofReal (2 * δ * r i) := by
    rw [hausdorffEDist_comm]
    exact (hcloud i).trans_lt hstrict
  obtain ⟨q, hq, hpq⟩ := exists_edist_lt_of_hausdorffEDist_lt hptest hswap
  have hpqdist : dist p q < 2 * δ * r i := edist_lt_ofReal.mp hpq
  have hlocal : dist q i < (A + 2 * δ) * r i := by
    have ht := dist_triangle q p i
    rw [dist_comm q p] at ht
    have hwcenter : dist w i < A * r i := hwi
    nlinarith
  have hcompare := hscale i q hq.1 hlocal
  have hrq : 0 < r q := by nlinarith
  have hnormal : ‖(P i)ᗮ.starProjection (w - i)‖ ≤ E * δ * r i := by
    simpa only [hw.2, zero_sub, norm_neg] using herror i w hwi
  have hwp : dist w p ≤ E * δ * r i := by
    simpa only [p, dist_eq_norm, sub_add_eq_sub_sub,
      Submodule.starProjection_orthogonal_val] using hnormal
  have hclose : dist w q < (E + 2) * δ * r i := by
    have ht := dist_triangle w p q
    nlinarith
  have hfinal : (E + 2) * δ * r i < ε * r q := by
    calc
      _ ≤ (E + 2) * δ * (B * r q) :=
        mul_le_mul_of_nonneg_left hcompare (by positivity)
      _ = (B * (E + 2) * δ) * r q := by ring
      _ < _ := mul_lt_mul_of_pos_right haccuracy hrq
  exact mem_iUnion₂.mpr ⟨q, hq.1, hclose.trans hfinal⟩

theorem zero_set_subset_variable_ball_union_of_scale_control
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I T : Set H) (hIT : I ⊆ T) (r : H → ℝ) (P : I → Submodule ℝ H)
    [∀ i : I, (P i).HasOrthogonalProjection] (η : H → H)
    (A D E δ B ε : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hδ : 0 < δ) (hB : 0 < B)
    (hr : ∀ i : I, 0 < r i) (hinterior : A * δ < 1)
    (hreach : A + 2 * δ ≤ D) (haccuracy : B * (E + 2) * δ < ε)
    (hcloud : ∀ i : I, hausdorffEDist (T ∩ ball (i : H) (r i / δ))
      ((AffineSubspace.mk' (i : H) (P i) : Set H) ∩ ball (i : H) (r i / δ)) ≤
        ENNReal.ofReal (δ * r i))
    (herror : ∀ i : I, ∀ w ∈ ball (i : H) (A * r i),
      ‖η w - (P i)ᗮ.starProjection (w - i)‖ ≤ E * δ * r i)
    (hcontrol : ∀ x ∈ T, ∀ y ∈ T,
      dist y x ≤ D * max (r y) (r x) → r x / B ≤ r y) :
    {w | w ∈ ⋃ i : I, ball (i : H) (A * r i) ∧ η w = 0} ⊆
      ⋃ q ∈ T, ball q (ε * r q) := by
  apply zero_set_subset_variable_ball_union_of_affine_test
    I T r P η A E δ B ε hE hδ hB hr hinterior haccuracy hcloud herror
  intro i q hq hlocal
  have hnear : dist q i ≤ D * max (r q) (r i) := by
    calc
      _ ≤ (A + 2 * δ) * r i := hlocal.le
      _ ≤ D * r i := mul_le_mul_of_nonneg_right hreach (hr i).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hD
  have h := hcontrol i (hIT i.property) q hq hnear
  have hm := (div_le_iff₀ hB).mp h
  simpa only [mul_comm] using hm

end GC.MetricGeometry
