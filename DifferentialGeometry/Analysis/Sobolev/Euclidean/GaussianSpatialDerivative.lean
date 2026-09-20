import DifferentialGeometry.Analysis.Sobolev.Euclidean.GaussianDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.SpatialLp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem ae_eq_of_ae_ae_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {f g : X × Y → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (hfg : ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[ν] fun y => g (x, y)) :
    f =ᵐ[μ.prod ν] g := by
  have hmk : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun q => hf.mk f q = hg.mk g q)
      (hf.stronglyMeasurable_mk.measurableSet_eq_fun hg.stronglyMeasurable_mk)).2
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk, hfg] with x hfx hgx hfgx
    filter_upwards [hfx, hgx, hfgx] with y hyf hyg hye
    exact hyf.symm.trans (hye.trans hyg)
  exact hf.ae_eq_mk.trans (hmk.trans hg.ae_eq_mk.symm)

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem spatial_fderiv_exp_neg_add_ae_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : ℝ × E → ℝ} (hf : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) f)
    {c : ℝ → ℝ} (hc : LocallyLipschitzOn (Icc a b) c) (i : Fin d) :
    let u := fun q : ℝ × E => Real.exp (-f q + c q.1)
    (fun q : ℝ × E => fderiv ℝ (fun x => u (q.1, x)) q.2
      (EuclideanSpace.single i 1))
      =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)]
        fun q => -u q * fderiv ℝ (fun x => f (q.1, x)) q.2
          (EuclideanSpace.single i 1) := by
  intro u
  let S := Icc a b ×ˢ closure Ω
  let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
  obtain ⟨C, hC⟩ := hc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hp : LipschitzOnWith 1 (Prod.fst : ℝ × E → ℝ) S :=
    LipschitzWith.prod_fst.lipschitzOnWith
  have hcp : LipschitzOnWith C (fun q : ℝ × E => c q.1) S := by
    simpa only [mul_one, Function.comp_def] using hC.comp hp (fun _ hq => hq.1)
  have hcl : LocallyLipschitzOn S (fun q : ℝ × E => c q.1) := by
    intro q hq
    exact ⟨C, S, self_mem_nhdsWithin, hcp⟩
  have hu : LocallyLipschitzOn S u := by
    apply locallyLipschitzOn_iff_restrict.mpr
    exact (Real.contDiff_exp : ContDiff ℝ 1 Real.exp).locallyLipschitz.comp
      (hf.neg.add hcl).restrict
  have hum : AEStronglyMeasurable u ν := by
    have htop : MemLp u ∞ ν := by
      change MemLp u ∞ ((volume.restrict (Icc a b)).prod (volume.restrict Ω))
      rw [Measure.prod_restrict]
      exact hu.continuousOn.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
        (measurableSet_Icc.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
    exact htop.aestronglyMeasurable
  have hdu := (memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu 2 i).aestronglyMeasurable
  have hdf := (memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hf 2 i).aestronglyMeasurable
  apply ae_eq_of_ae_ae_eq hdu (hum.neg.mul hdf)
  obtain ⟨D, hD⟩ := hf.exists_lipschitzOnWith_of_compact (isCompact_Icc.prod hΩc)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hfl : LipschitzOnWith D (fun x : E => f (t, x)) (closure Ω) := by
    simpa only [mul_one, Function.comp_def] using
      hD.comp (LipschitzWith.prodMk_left t).lipschitzOnWith (fun _ hx => ⟨ht, hx⟩)
  have hfs : LocallyLipschitzOn (closure Ω) (fun x : E => f (t, x)) := by
    intro x hx
    exact ⟨D, closure Ω, self_mem_nhdsWithin, hfl⟩
  exact fderiv_exp_neg_add_const_ae_of_locallyLipschitzOn hΩ hΩc hfs (c t) i

theorem spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn
    {a b : ℝ} (ha : 0 < a) {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : ℝ × E → ℝ} (hf : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) f)
    (n : ℝ) (i : Fin d) :
    let u := fun q : ℝ × E => Real.exp (-f q - n / 2 * Real.log q.1 -
      n / 2 * Real.log (4 * Real.pi))
    (fun q : ℝ × E => fderiv ℝ (fun x => u (q.1, x)) q.2
      (EuclideanSpace.single i 1))
      =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)]
        fun q => -u q * fderiv ℝ (fun x => f (q.1, x)) q.2
          (EuclideanSpace.single i 1) := by
  have hc : LocallyLipschitzOn (Icc a b)
      (fun t : ℝ => -n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hd : ContDiffAt ℝ 1
        (fun t : ℝ => -n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi)) t :=
      (contDiffAt_const.mul (Real.contDiffAt_log.mpr ht0.ne')).sub contDiffAt_const
    obtain ⟨C, V, hV, hLip⟩ := hd.exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  simpa only [sub_eq_add_neg, neg_div, neg_mul, add_assoc] using
    spatial_fderiv_exp_neg_add_ae_of_locallyLipschitzOn hΩ hΩc hf hc i

end DifferentialGeometry.Analysis.Sobolev.Euclidean
