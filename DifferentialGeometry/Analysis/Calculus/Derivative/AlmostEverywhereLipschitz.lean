import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DifferentialGeometry.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {L C : ℝ≥0} {f : E → F}

private theorem dual_increment_le_on_of_ae_fderiv
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s) (hf : LipschitzOnWith L f s)
    (hD : ∀ᵐ x ∂μ.restrict s, ‖fderiv ℝ f x‖ ≤ C)
    (ell : F →L[ℝ] ℝ) (hell : ‖ell‖ ≤ 1) (v a : E) (ha : a ∈ s) (hav : a + v ∈ s) :
    ‖ell (f (a + v) - f a)‖ ≤ C * ‖v‖ := by
  have hdiff : ∀ᵐ x ∂μ.restrict s, DifferentiableAt ℝ f x := by
    filter_upwards [hf.ae_differentiableWithinAt hs.measurableSet,
      ae_restrict_mem hs.measurableSet] with x hx hxs
    exact hx.differentiableAt (hs.mem_nhds hxs)
  have hgood : ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ C :=
    (ae_restrict_iff' hs.measurableSet).mp (hdiff.and hD)
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null
    (show μ {x | ¬(x ∈ s → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ C)} = 0 from hgood)
  have hNfull : ∀ᵐ x ∂μ, x ∈ Nᶜ := measure_eq_zero_iff_ae_notMem.mp hNzero
  have hNgood {x : E} (hx : x ∈ Nᶜ) :
      x ∈ s → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ C := by
    by_contra hn
    exact hx (hNsub hn)
  let line : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hlines : ∀ᵐ b ∂μ, ∀ᵐ (t : ℝ) ∂volume, b + t • v ∈ Nᶜ := by
    have hraw := (ae_ae_add_linearMap_mem_iff line.toLinearMap volume μ hNm.compl).2 hNfull
    change ∀ᵐ b ∂μ, ∀ᵐ (t : ℝ) ∂volume, b + line t ∈ Nᶜ at hraw
    exact hraw
  let T : Set E := {b | b ∈ s ∧ b + v ∈ s}
  have hT : IsOpen T := hs.inter (hs.preimage (continuous_id.add continuous_const))
  have haT : a ∈ T := ⟨ha, hav⟩
  have hbound : ∀ᵐ b ∂μ, b ∈ T → ‖ell (f (b + v) - f b)‖ ≤ C * ‖v‖ := by
    filter_upwards [hlines] with b hb
    intro hbT
    have hseg : MapsTo (fun t : ℝ => b + t • v) (uIcc 0 1) s := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      simpa only [add_sub_cancel_left] using hconv.add_smul_sub_mem hbT.1 hbT.2 ht'
    let u : ℝ → ℝ := fun t => ell (f (b + t • v))
    have hlineLip : LipschitzWith (0 + ‖line‖₊) (fun t : ℝ => b + t • v) := by
      exact (LipschitzWith.const b).add line.lipschitz
    have huLip : LipschitzOnWith (‖ell‖₊ * (L * (0 + ‖line‖₊))) u (uIcc 0 1) :=
      ell.lipschitz.comp_lipschitzOnWith (hf.comp hlineLip.lipschitzOnWith hseg)
    have huAC : AbsolutelyContinuousOnInterval u 0 1 := huLip.absolutelyContinuousOnInterval
    have huD : ∀ᵐ (t : ℝ) ∂volume, t ∈ uIcc 0 1 → ‖deriv u t‖ ≤ C * ‖v‖ := by
      filter_upwards [hb] with t ht
      intro hts
      have hx := hNgood ht (hseg hts)
      have hcurve : HasDerivAt (fun z : ℝ => b + z • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add b
      have hud : HasDerivAt u (ell (fderiv ℝ f (b + t • v) v)) t :=
        ell.hasFDerivAt.comp_hasDerivAt t (hx.1.hasFDerivAt.comp_hasDerivAt t hcurve)
      rw [hud.deriv]
      calc
        ‖ell (fderiv ℝ f (b + t • v) v)‖ ≤ ‖ell‖ * ‖fderiv ℝ f (b + t • v) v‖ :=
          ell.le_opNorm _
        _ ≤ 1 * (C * ‖v‖) :=
          mul_le_mul hell ((fderiv ℝ f (b + t • v)).le_opNorm v |>.trans
            (mul_le_mul_of_nonneg_right hx.2 (norm_nonneg v))) (norm_nonneg _) zero_le_one
        _ = C * ‖v‖ := one_mul _
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := (0 : ℝ)) (b := 1) (huD.mono fun t ht hts => ht (uIoc_subset_uIcc hts))
    rw [huAC.integral_deriv_eq_sub] at hi
    simpa only [u, one_smul, zero_smul, add_zero, map_sub, sub_zero, abs_one, mul_one] using hi
  have hleft : ContinuousAt (fun b : E => f (b + v)) a :=
    ContinuousAt.comp (f := fun b : E => b + v) (x := a)
      ((hf.continuousOn (a + v) hav).continuousAt (hs.mem_nhds hav))
      (continuous_id.add continuous_const).continuousAt
  have hright : ContinuousAt f a :=
    (hf.continuousOn a ha).continuousAt (hs.mem_nhds ha)
  have hc : ContinuousAt (fun b : E => ‖ell (f (b + v) - f b)‖) a :=
    (ell.continuous.continuousAt.comp (hleft.sub hright)).norm
  have hacl : a ∈ closure {b : E | ‖ell (f (b + v) - f b)‖ ≤ C * ‖v‖} := by
    rw [_root_.mem_closure_iff]
    intro O hO haO
    obtain ⟨b, hbOT, hb⟩ := _root_.mem_closure_iff.mp (μ.dense_of_ae hbound a)
      (O ∩ T) (hO.inter hT) ⟨haO, haT⟩
    exact ⟨b, hbOT.1, hb hbOT.2⟩
  exact hc.continuousWithinAt.closure_le hacl continuous_const.continuousWithinAt (fun _ h => h)

theorem lipschitzOnWith_of_ae_norm_fderiv_le
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s) (hf : LipschitzOnWith L f s)
    (hD : ∀ᵐ x ∂μ.restrict s, ‖fderiv ℝ f x‖ ≤ C) : LipschitzOnWith C f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  obtain ⟨ell, hell, hattain⟩ := exists_dual_vector'' ℝ (f y - f x)
  have h := dual_increment_le_on_of_ae_fderiv hs hconv hf hD ell hell (y - x) x hx
    (by simpa only [add_sub_cancel] using hy)
  rw [add_sub_cancel, hattain] at h
  simp only [norm_algebraMap', norm_norm] at h
  simpa only [dist_eq_norm, norm_sub_rev] using h

theorem lipschitzWith_of_ae_norm_fderiv_le
    (hf : LipschitzWith L f) (hD : ∀ᵐ x ∂μ, ‖fderiv ℝ f x‖ ≤ C) :
    LipschitzWith C f := by
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_ae_norm_fderiv_le isOpen_univ convex_univ hf.lipschitzOnWith
    (by simpa only [Measure.restrict_univ] using hD)

end DifferentialGeometry.Analysis
