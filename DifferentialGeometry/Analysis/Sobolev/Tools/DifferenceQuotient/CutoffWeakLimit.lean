import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.LocalWeakLimit
import DifferentialGeometry.Analysis.Sobolev.Tools.CutoffDiffQuotLp
import DifferentialGeometry.Analysis.Integration.LpNorm

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private local instance : MeasurableSpace E := WithLp.measurableSpace 2 (Fin d → ℝ)

theorem hasWeakPartialDeriv_of_cutoff_diffQuot_uniform_bound
    {Ω Ω₀ : Set E} (hΩ : IsOpen Ω) (hΩ₀ : IsOpen Ω₀)
    (u : Lp ℝ 2 (volume.restrict Ω))
    {η : E → ℝ} (hη : MemLp η ∞ volume) (hηc : HasCompactSupport η)
    (hηone : ∀ z ∈ Ω₀, η z = 1)
    (k : Fin d) {δ C : ℝ} (hδ : 0 < δ)
    (hroom : cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ h, 0 < |h| → |h| ≤ δ →
      (∫ z, (η z * diffQuot k h u z) ^ 2) ≤ C) :
    ∃ v : E → ℝ, MemLp v 2 (volume.restrict Ω₀) ∧
      DeGiorgi.HasWeakPartialDeriv k v u Ω₀ ∧
      eLpNorm v 2 (volume.restrict Ω₀) ≤ ENNReal.ofReal (Real.sqrt C) := by
  have hsub : closure Ω₀ ⊆ tsupport η := by
    apply closure_minimal _ (isClosed_tsupport η)
    intro z hz
    apply subset_tsupport η
    change η z ≠ 0
    rw [hηone z hz]
    exact one_ne_zero
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hηc.of_isClosed_subset isClosed_closure hsub
  have hroom₀ : cthickening δ (closure Ω₀) ⊆ Ω :=
    (cthickening_subset_of_subset δ hsub).trans hroom
  apply hasWeakPartialDeriv_of_diffQuot_uniform_bound_local hΩ hΩ₀ hΩ₀c hδ
    hroom₀ (Lp.memLp u) k (Real.sqrt_nonneg C)
  intro h hhpos hh
  have hroomh : cthickening |h| (tsupport η) ⊆ Ω :=
    (cthickening_mono hh _).trans hroom
  let U := cutoffDiffQuotLp hΩ.measurableSet hη k h u
  have hU : (U : E → ℝ) =ᵐ[volume] fun z => η z * diffQuot k h u z :=
    cutoffDiffQuotLp_coeFn hΩ.measurableSet hη k h hroomh u
  have hmul : MemLp (fun z => η z * diffQuot k h u z) 2 volume :=
    (Lp.memLp U).ae_eq hU
  have hnorm : eLpNorm (fun z => η z * diffQuot k h u z) 2 volume ≤
      ENNReal.ofReal (Real.sqrt C) := by
    apply Integration.eLpNorm_two_le_of_integral_norm_sq_le hmul
    simpa only [Real.norm_eq_abs, sq_abs] using hbound h hhpos hh
  calc
    eLpNorm (diffQuot k h u) 2 (volume.restrict Ω₀) =
        eLpNorm (fun z => η z * diffQuot k h u z) 2 (volume.restrict Ω₀) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hΩ₀.measurableSet] with z hz
      rw [hηone z hz, one_mul]
    _ ≤ eLpNorm (fun z => η z * diffQuot k h u z) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ ENNReal.ofReal (Real.sqrt C) := hnorm

end DifferentialGeometry.Analysis.Sobolev
