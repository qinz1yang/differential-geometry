import DifferentialGeometry.Analysis.Calculus.FirstPositiveLevel
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# First crossings of monotone left-continuous functions

A positive first crossing of a continuous barrier is attained without right continuity.
For cubic barriers this crossing agrees with the existing first positive ratio level.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace Real

def firstPositiveCrossing (V F : ℝ → ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ V r ≤ F r}

theorem firstPositiveCrossing_constant_eq_firstPositiveLevel {f : ℝ → ℝ} {c w : ℝ}
    (hf : ContinuousOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hinfty : Tendsto f atTop (𝓝 0)) (hw : 0 < w) (hwc : w < c) :
    firstPositiveCrossing f (Function.const ℝ w) = firstPositiveLevel f w := by
  obtain ⟨hpos, heq, hbefore⟩ := firstPositiveLevel_spec hf hzero hinfty hw hwc
  have hleast : IsLeast {r : ℝ | 0 < r ∧ f r ≤ w} (firstPositiveLevel f w) := by
    refine ⟨⟨hpos, heq.le⟩, ?_⟩
    intro r hr
    by_contra! hrs
    exact (hbefore r hr.1 hrs).not_ge hr.2
  exact hleast.csInf_eq

theorem firstPositiveCrossing_spec {V F : ℝ → ℝ}
    (hmono : MonotoneOn V (Ioi 0))
    (hleft : ∀ r, 0 < r → ContinuousWithinAt V (Iio r) r)
    (hF : ContinuousOn F (Ioi 0))
    (hsmall : ∃ a > 0, ∀ r, 0 < r → r ≤ a → F r < V r)
    (hex : ∃ r > 0, V r ≤ F r) :
    0 < firstPositiveCrossing V F ∧
      V (firstPositiveCrossing V F) = F (firstPositiveCrossing V F) ∧
      ∀ r, 0 < r → r < firstPositiveCrossing V F → F r < V r := by
  let S : Set ℝ := {r | 0 < r ∧ V r ≤ F r}
  have hS : S.Nonempty := hex
  obtain ⟨a, ha, hnear⟩ := hsmall
  have hlow : a ∈ lowerBounds S := by
    intro r hr
    by_contra! hra
    exact (hnear r hr.1 hra.le).not_ge hr.2
  have hB : BddBelow S := ⟨a, hlow⟩
  have hpos : 0 < sInf S := ha.trans_le (le_csInf hS hlow)
  have hbefore : ∀ r, 0 < r → r < sInf S → F r < V r := by
    intro r hr hrs
    by_contra! hbad
    exact (not_le_of_gt hrs) (csInf_le hB ⟨hr, hbad⟩)
  have hFc : ContinuousAt F (sInf S) := hF.continuousAt (Ioi_mem_nhds hpos)
  have hle : F (sInf S) ≤ V (sInf S) := by
    apply le_of_tendsto_of_tendsto hFc.continuousWithinAt (hleft (sInf S) hpos)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos)] with r hrs hr
    exact (hbefore r hr hrs).le
  have hge : V (sInf S) ≤ F (sInf S) := by
    have : NeBot (𝓝[S] (sInf S)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (csInf_mem_closure hS hB)
    have hFcS : ContinuousWithinAt F S (sInf S) := hFc.continuousWithinAt
    apply ge_of_tendsto hFcS
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hmono hpos hr.1 (csInf_le hB hr)).trans hr.2
  exact ⟨hpos, hge.antisymm hle, hbefore⟩

theorem firstPositiveCrossing_cube_spec_of_bounded {V : ℝ → ℝ} {w : ℝ}
    (hmono : MonotoneOn V (Ioi 0))
    (hleft : ∀ r, 0 < r → ContinuousWithinAt V (Iio r) r)
    (hw : 0 < w)
    (hsmall : ∃ a > 0, ∀ r, 0 < r → r ≤ a → w * r ^ 3 < V r)
    (hbounded : ∃ C, ∀ r, 0 < r → V r ≤ C) :
    0 < firstPositiveCrossing V (fun r => w * r ^ 3) ∧
      V (firstPositiveCrossing V (fun r => w * r ^ 3)) =
        w * firstPositiveCrossing V (fun r => w * r ^ 3) ^ 3 ∧
      ∀ r, 0 < r → r < firstPositiveCrossing V (fun s => w * s ^ 3) →
        w * r ^ 3 < V r := by
  apply firstPositiveCrossing_spec hmono hleft (by fun_prop) hsmall
  obtain ⟨C, hC⟩ := hbounded
  let R := max 1 (C / w + 1)
  have hR1 : 1 ≤ R := le_max_left 1 (C / w + 1)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hCR : C / w < R := by
    have h := le_max_right 1 (C / w + 1)
    dsimp only [R]
    linarith
  have hCw : C < w * R := by
    simpa only [mul_comm] using (div_lt_iff₀ hw).mp hCR
  refine ⟨R, hR, (hC R hR).trans (hCw.le.trans ?_)⟩
  exact mul_le_mul_of_nonneg_left (le_self_pow₀ hR1 (by norm_num)) hw.le

theorem firstPositiveCrossing_cube_eq_firstPositiveLevel {V : ℝ → ℝ} {w : ℝ}
    (hmono : MonotoneOn V (Ioi 0))
    (hleft : ∀ r, 0 < r → ContinuousWithinAt V (Iio r) r)
    (hsmall : ∃ a > 0, ∀ r, 0 < r → r ≤ a → w * r ^ 3 < V r)
    (hex : ∃ r > 0, V r ≤ w * r ^ 3) :
    firstPositiveCrossing V (fun r => w * r ^ 3) =
      firstPositiveLevel (fun r => V r / r ^ 3) w := by
  obtain ⟨hpos, heq, hbefore⟩ :=
    firstPositiveCrossing_spec hmono hleft (by fun_prop) hsmall hex
  let R := firstPositiveCrossing V (fun r => w * r ^ 3)
  have hleast : IsLeast {r : ℝ | 0 < r ∧ V r / r ^ 3 = w} R := by
    refine ⟨⟨hpos, (div_eq_iff (pow_ne_zero 3 hpos.ne')).mpr heq⟩, ?_⟩
    intro r hr
    by_contra! hlt
    have hroot : V r = w * r ^ 3 :=
      (div_eq_iff (pow_ne_zero 3 hr.1.ne')).mp hr.2
    exact (hbefore r hr.1 hlt).ne' hroot
  exact hleast.csInf_eq.symm

end Real
