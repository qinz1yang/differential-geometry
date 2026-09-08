import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Energy
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {T : ℝ}

private theorem memLp_top_of_continuousOn {ζ : ℝ → ℝ}
    (hζ : ContinuousOn ζ (Icc (0 : ℝ) T)) : MemLp ζ ∞ (timeMeasure T) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hζ
  refine MemLp.of_bound (hζ.aestronglyMeasurable measurableSet_Icc) C ?_
  exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht => hC t ht)

omit [CompleteSpace X] in
private theorem memLp_timeH1_smul_derivative (z : timeH1 ℝ T) (u : timeH1 X T) :
    MemLp (fun t => z.deriv t • u.toFun t + z.toFun t • u.deriv t) 2 (timeMeasure T) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn u.continuousOn_toFun
  have h1 : MemLp (fun t => z.deriv t • u.toFun t) 2 (timeMeasure T) := by
    have hu : MemLp u.toFun ∞ (timeMeasure T) := MemLp.of_bound
      (u.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc) C
      ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hC t ht))
    exact hu.smul (Lp.memLp z.deriv)
  exact h1.add ((Lp.memLp u.deriv).smul (memLp_top_of_continuousOn z.continuousOn_toFun))

private theorem timeH1_apply_dual_primitive (L : X →L[ℝ] ℝ) (u : timeH1 X T) :
    ∃ v : timeH1 ℝ T,
      (∀ t ∈ Icc (0 : ℝ) T, v.toFun t = L (u.toFun t)) ∧
      v.deriv =ᵐ[timeMeasure T] (fun t => L (u.deriv t)) := by
  let v := timeH1.mk (L u.init) (L.compLpL 2 (timeMeasure T) u.deriv)
  have hd : v.deriv =ᵐ[timeMeasure T] (fun t => L (u.deriv t)) := L.coeFn_compLpL u.deriv
  refine ⟨v, ?_, hd⟩
  intro t ht
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hi : (∫ s in (0 : ℝ)..t, v.deriv s) = ∫ s in (0 : ℝ)..t, L (u.deriv s) :=
    intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict
      (hd.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))
  rw [timeH1.toFun_apply, hi, L.intervalIntegral_comp_comm
    (u.intervalIntegrable_deriv ⟨le_rfl, ht.1.trans ht.2⟩ ht), timeH1.toFun_apply, map_add]
  rfl

private theorem integral_timeH1_smul_derivative (z : timeH1 ℝ T) (u : timeH1 X T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, z.deriv s • u.toFun s + z.toFun s • u.deriv s) =
      z.toFun t • u.toFun t - z.init • u.init := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  obtain ⟨v, hv, hvd⟩ := timeH1_apply_dual_primitive L u
  have hzAC := (z.absolutelyContinuousOnInterval_toFun (ht.1.trans ht.2)).mono
    (by simpa only [uIcc_of_le (ht.1.trans ht.2)] using
      uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hvAC := (v.absolutelyContinuousOnInterval_toFun (ht.1.trans ht.2)).mono
    (by simpa only [uIcc_of_le (ht.1.trans ht.2)] using
      uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hid := hzAC.integral_deriv_mul_eq_sub hvAC
  have hsub : uIcc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht
  have hder : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) t →
      _root_.deriv z.toFun s * v.toFun s + z.toFun s * _root_.deriv v.toFun s =
        z.deriv s * L (u.toFun s) + z.toFun s * L (u.deriv s) := by
    have hz := (ae_restrict_iff' measurableSet_Icc).mp z.ae_hasDerivWithinAt_toFun
    have hv' := (ae_restrict_iff' measurableSet_Icc).mp v.ae_hasDerivWithinAt_toFun
    have hvd' := (ae_restrict_iff' measurableSet_Icc).mp hvd
    filter_upwards [hz, hv', hvd', Measure.ae_ne volume 0, Measure.ae_ne volume T]
      with s hs hvds hld hs0 hsT hst
    have hsI := hsub (uIoc_subset_uIcc hst)
    have hsN : Icc (0 : ℝ) T ∈ 𝓝 s := Icc_mem_nhds
      (lt_of_le_of_ne hsI.1 hs0.symm) (lt_of_le_of_ne hsI.2 hsT)
    rw [((hs hsI).hasDerivAt hsN).deriv, ((hvds hsI).hasDerivAt hsN).deriv,
      hv s hsI, hld hsI]
  rw [intervalIntegral.integral_congr_ae hder, hv t ht, hv 0 ⟨le_rfl, ht.1.trans ht.2⟩,
    timeH1.toFun_zero, timeH1.toFun_zero] at hid
  have hqi : IntegrableOn (fun s => z.deriv s • u.toFun s + z.toFun s • u.deriv s)
      (Icc (0 : ℝ) T) volume :=
    (memLp_timeH1_smul_derivative z u).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hq := hqi.mono_set hsub
  rw [← L.intervalIntegral_comp_comm hq.intervalIntegrable]
  simpa only [map_add, map_smul, smul_eq_mul, map_sub] using hid

theorem exists_timeH1_smul (z : timeH1 ℝ T) (u : timeH1 X T) :
    ∃ w : timeH1 X T,
      w.init = z.init • u.init ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = z.toFun t • u.toFun t) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => z.deriv t • u.toFun t + z.toFun t • u.deriv t) := by
  let q := fun t => z.deriv t • u.toFun t + z.toFun t • u.deriv t
  have hq : MemLp q 2 (timeMeasure T) := memLp_timeH1_smul_derivative z u
  let w := timeH1.mk (z.init • u.init) (hq.toLp q)
  have hwd : w.deriv =ᵐ[timeMeasure T] q := hq.coeFn_toLp
  refine ⟨w, rfl, ?_, hwd⟩
  intro t ht
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hi : (∫ s in (0 : ℝ)..t, w.deriv s) = ∫ s in (0 : ℝ)..t, q s :=
    intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict
      (hwd.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))
  rw [timeH1.toFun_apply, hi, integral_timeH1_smul_derivative z u ht]
  change z.init • u.init + (z.toFun t • u.toFun t - z.init • u.init) = _
  abel

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
