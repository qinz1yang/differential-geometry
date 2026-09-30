import DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal
import DifferentialGeometry.Analysis.Integration.Lp.Product

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_spatial_diffQuot_le_eLpNorm_weakPartial_local
    {Ω Ω' Ω'' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    (μ : Measure Z) (U V : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (k : Fin d)
    (hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V (t, x)) (fun x => U (t, x)) Ω)
    {h0 : ℝ} (hh0 : 0 < h0) (hthick : cthickening h0 (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : |h| ≤ h0) :
    eLpNorm (fun p : Z × E => diffQuot k h (fun x => U (p.1, x)) p.2)
        2 (μ.prod (volume.restrict Ω'')) ≤
      eLpNorm V 2 (μ.prod (volume.restrict Ω')) := by
  have hslice : ∀ᵐ t ∂μ,
      eLpNorm (diffQuot k h (fun x => U (t, x))) 2 (volume.restrict Ω'') ≤
        eLpNorm (fun x => V (t, x)) 2 (volume.restrict Ω') := by
    filter_upwards [(Lp.memLp U).prodMk_left (by norm_num),
      (Lp.memLp V).prodMk_left (by norm_num), hweak] with t hU hV ht
    exact eLpNorm_diffQuot_le_eLpNorm_weakPartial_local hΩ hΩ' hΩ'' hΩ'c hΩ'Ω
      hΩ''c hU hV k ht hh0 hthick hh
  have hDQ : StronglyMeasurable
      (fun p : Z × E => diffQuot k h (fun x => U (p.1, x)) p.2) := by
    by_cases hz : h = 0
    · simp only [hz, diffQuot_zero_h, Pi.zero_apply]
      exact stronglyMeasurable_const
    · simp only [diffQuot_apply_of_ne k hz]
      simp only [div_eq_mul_inv]
      exact (((Lp.stronglyMeasurable U).comp_measurable
        (measurable_fst.prodMk (measurable_snd.add_const
          (h • EuclideanSpace.single k 1)))).sub
          (Lp.stronglyMeasurable U)).mul stronglyMeasurable_const
  calc
    _ = eLpNorm (fun t => eLpNorm (diffQuot k h (fun x => U (t, x)))
        2 (volume.restrict Ω'')) 2 μ :=
      (eLpNorm_eLpNorm (by norm_num) hDQ.aestronglyMeasurable).symm
    _ ≤ eLpNorm (fun t => eLpNorm (fun x => V (t, x))
        2 (volume.restrict Ω')) 2 μ := by
      apply eLpNorm_mono_enorm_ae
        (aestronglyMeasurable_eLpNorm_prodMk_left (by norm_num) hDQ.aestronglyMeasurable)
      simpa only [enorm_eq_self] using hslice
    _ = _ := eLpNorm_eLpNorm (by norm_num) (Lp.stronglyMeasurable V).aestronglyMeasurable

end DifferentialGeometry.Analysis.Sobolev
