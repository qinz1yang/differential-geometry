import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem lineDeriv_extension_ae_fderiv
    {Ω : Set E} (hΩ : IsOpen Ω) {f g : E → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hfg : EqOn f g Ω) (i : Fin d) :
    (fun x => lineDeriv ℝ g x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
        (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  filter_upwards [ae_restrict_mem hΩ.measurableSet,
    ae_mono Measure.restrict_le_self hg.ae_differentiableAt] with x hx hdx
  have hloc : f =ᶠ[𝓝 x] g := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hfg hy
  rw [hdx.lineDeriv_eq_fderiv, hloc.fderiv_eq]

theorem hasWeakPartialDeriv_fderiv_of_lipschitzOnWith
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f Ω) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f Ω := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  refine (hasWeakPart_of_lip (Omega := Ω) hg i).congr_ae ?_
    (lineDeriv_extension_ae_fderiv hΩ hg hfg i)
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  exact (hfg hx).symm

theorem memLp_top_fderiv_of_lipschitzOnWith
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f Ω) (i : Fin d) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) ∞
      (volume.restrict Ω) := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  exact (memLp_congr_ae (lineDeriv_extension_ae_fderiv hΩ hg hfg i)).mp
    (hg.memLp_lineDeriv (μ := volume.restrict Ω) (EuclideanSpace.single i 1))

theorem memLp_fderiv_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f)
    (p : ℝ≥0∞) (i : Fin d) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p
      (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (measure_mono (μ := (volume : Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  exact (memLp_top_fderiv_of_lipschitzOnWith hΩ (hC.mono subset_closure) i).mono_exponent
    le_top

theorem memW1p_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (p : ℝ≥0∞) :
    DeGiorgi.MemW1p p f Ω := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (measure_mono (μ := (volume : Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  refine ⟨(hf.continuousOn.memLp_top_of_subset_isCompact hΩc hΩ.measurableSet
    subset_closure).mono_exponent le_top, ?_⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  intro i
  exact ⟨fun x => fderiv ℝ f x (EuclideanSpace.single i 1),
    memLp_fderiv_of_locallyLipschitzOn hΩ hΩc hf p i,
    hasWeakPartialDeriv_fderiv_of_lipschitzOnWith hΩ (hC.mono subset_closure) i⟩

private theorem locallyLipschitzOn_exp_neg
    {s : Set E} {f : E → ℝ} (hf : LocallyLipschitzOn s f) :
    LocallyLipschitzOn s (fun x => Real.exp (-f x)) := by
  have hcont : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t)) := contDiff_id.neg.exp
  have he : LocallyLipschitz (fun t : ℝ => Real.exp (-t)) := hcont.locallyLipschitz
  apply locallyLipschitzOn_iff_restrict.mpr
  exact he.comp hf.restrict

private theorem fderiv_exp_neg_ae
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f Ω) (i : Fin d) :
    (fun x => fderiv ℝ (fun y => Real.exp (-f y)) x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
        (fun x => -Real.exp (-f x) * fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  filter_upwards [ae_restrict_mem hΩ.measurableSet,
    hf.ae_differentiableWithinAt (μ := volume) hΩ.measurableSet] with x hx hdx
  have hd : DifferentiableAt ℝ f x := hdx.differentiableAt (hΩ.mem_nhds hx)
  simpa only [Pi.neg_apply, smul_apply,
    neg_apply, smul_eq_mul, mul_neg, neg_mul] using
      congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
        hd.hasFDerivAt.neg.exp.fderiv

theorem hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => -Real.exp (-f x) * fderiv ℝ f x (EuclideanSpace.single i 1))
      (fun x => Real.exp (-f x)) Ω := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  have he := locallyLipschitzOn_exp_neg hf
  obtain ⟨D, hD⟩ := he.exists_lipschitzOnWith_of_compact hΩc
  exact (hasWeakPartialDeriv_fderiv_of_lipschitzOnWith hΩ
    (hD.mono subset_closure) i).congr_ae (Filter.EventuallyEq.rfl)
      (fderiv_exp_neg_ae hΩ (hC.mono subset_closure) i)

theorem memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f)
    (p : ℝ≥0∞) (i : Fin d) :
    MemLp
      (fun x => -Real.exp (-f x) * fderiv ℝ f x (EuclideanSpace.single i 1))
      p (volume.restrict Ω) := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  exact (memLp_congr_ae (fderiv_exp_neg_ae hΩ (hC.mono subset_closure) i)).mp
    (memLp_fderiv_of_locallyLipschitzOn hΩ hΩc (locallyLipschitzOn_exp_neg hf) p i)

theorem memW1p_exp_neg_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (p : ℝ≥0∞) :
    DeGiorgi.MemW1p p (fun x => Real.exp (-f x)) Ω :=
  memW1p_of_locallyLipschitzOn hΩ hΩc (locallyLipschitzOn_exp_neg hf) p

end DifferentialGeometry.Analysis.Sobolev.Euclidean
