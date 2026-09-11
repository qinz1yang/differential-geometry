import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section

open Filter Set
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  {μ : Measure α} {p : ℝ≥0∞} {s : Set α}

def zeroExtend (hs : MeasurableSet s) (u : Lp E p (μ.restrict s)) : Lp E p μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp u)).toLp _

theorem coeFn_zeroExtend (hs : MeasurableSet s) (u : Lp E p (μ.restrict s)) :
    zeroExtend hs u =ᵐ[μ] s.indicator u := MemLp.coeFn_toLp _

@[simp] theorem norm_zeroExtend (hs : MeasurableSet s) (u : Lp E p (μ.restrict s)) :
    ‖zeroExtend hs u‖ = ‖u‖ := by
  rw [zeroExtend, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  rfl

theorem zeroExtend_add (hs : MeasurableSet s) (u v : Lp E p (μ.restrict s)) :
    zeroExtend hs (u + v) = zeroExtend hs u + zeroExtend hs v := by
  apply Lp.ext
  have hadd : s.indicator (fun x => (u + v) x) =ᵐ[μ] s.indicator (fun x => u x + v x) := by
    have hh := Lp.coeFn_add u v
    rw [EventuallyEq, ae_restrict_iff' hs] at hh
    filter_upwards [hh] with x hx
    by_cases hxs : x ∈ s
    · simp only [indicator_of_mem hxs, hx hxs, Pi.add_apply]
    · simp only [indicator_of_notMem hxs]
  filter_upwards [coeFn_zeroExtend hs (u + v), coeFn_zeroExtend hs u, coeFn_zeroExtend hs v,
    Lp.coeFn_add (zeroExtend hs u) (zeroExtend hs v), hadd] with x ha hu hv hvv haddx
  rw [ha, haddx, hvv, Pi.add_apply, hu, hv]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs]
  · simp only [indicator_of_notMem hxs, add_zero]

theorem zeroExtend_smul (hs : MeasurableSet s) (c : 𝕜) (u : Lp E p (μ.restrict s)) :
    zeroExtend hs (c • u) = c • zeroExtend hs u := by
  apply Lp.ext
  have hsm : s.indicator (fun x => (c • u) x) =ᵐ[μ] s.indicator (fun x => c • u x) := by
    have hh := Lp.coeFn_smul c u
    rw [EventuallyEq, ae_restrict_iff' hs] at hh
    filter_upwards [hh] with x hx
    by_cases hxs : x ∈ s
    · simp only [indicator_of_mem hxs, hx hxs, Pi.smul_apply]
    · simp only [indicator_of_notMem hxs]
  filter_upwards [coeFn_zeroExtend hs (c • u), coeFn_zeroExtend hs u,
    Lp.coeFn_smul c (zeroExtend hs u), hsm] with x ha hu hv hsmx
  rw [ha, hsmx, hv, Pi.smul_apply, hu]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs]
  · simp only [indicator_of_notMem hxs, smul_zero]

variable [Fact (1 ≤ p)]

def zeroExtendₗᵢ (hs : MeasurableSet s) : Lp E p (μ.restrict s) →ₗᵢ[𝕜] Lp E p μ where
  toFun := zeroExtend hs
  map_add' := zeroExtend_add hs
  map_smul' := zeroExtend_smul hs
  norm_map' := norm_zeroExtend hs

end MeasureTheory.Lp
