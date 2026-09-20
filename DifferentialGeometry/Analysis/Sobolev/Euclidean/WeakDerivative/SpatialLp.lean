import DifferentialGeometry.Analysis.Sobolev.Euclidean.LocallyLipschitz.ChainRule
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_spatial_fderiv_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) u)
    (p : ℝ≥0∞) (i : Fin d) :
    MemLp (fun q : ℝ × E =>
      fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) p
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (measure_mono (μ := (volume : Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hu.exists_lipschitzOnWith_of_compact (isCompact_Icc.prod hΩc)
  obtain ⟨g, hg, hug⟩ := hC.extend_real
  have hgSlice (t : ℝ) : LipschitzWith C (fun x : E => g (t, x)) := by
    simpa only [mul_one, Function.comp_def] using hg.comp (LipschitzWith.prodMk_left t)
  have hgMem : MemLp (fun q : ℝ × E =>
      fderiv ℝ (fun x => g (q.1, x)) q.2 (EuclideanSpace.single i 1)) p
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
    apply MemLp.of_bound
      (measurable_fderiv_apply_const_with_param ℝ
        (f := fun (t : ℝ) (x : E) => g (t, x)) hg.continuous
        (EuclideanSpace.single i (1 : ℝ))).aestronglyMeasurable
      ((C : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)
    apply Eventually.of_forall
    intro q
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hgSlice q.1))
        (norm_nonneg _))
  apply hgMem.ae_eq
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hΩ.measurableSet)] with q hq
  have hlocal : (fun x : E => u (q.1, x)) =ᶠ[𝓝 q.2] fun x => g (q.1, x) := by
    filter_upwards [hΩ.mem_nhds hq.2] with x hx
    exact hug ⟨hq.1, subset_closure hx⟩
  exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hlocal.fderiv_eq.symm

theorem exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) u)
    (p : ℝ≥0∞) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    ∃ U : Lp ℝ p ν, ∃ K : Fin d → Lp ℝ p ν,
      (U =ᵐ[ν] u) ∧
      (∀ i, K i =ᵐ[ν] fun q =>
        fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) ∧
      ∀ i, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω := by
  intro ν
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (measure_mono (μ := (volume : Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  have huMem : MemLp u p ν := by
    have htop : MemLp u ∞ ν := by
      change MemLp u ∞ ((volume.restrict (Icc a b)).prod (volume.restrict Ω))
      rw [Measure.prod_restrict]
      exact hu.continuousOn.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
        (measurableSet_Icc.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
    exact htop.mono_exponent le_top
  let D : Fin d → ℝ × E → ℝ := fun i q =>
    fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)
  have hDMem (i : Fin d) : MemLp (D i) p ν :=
    memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu p i
  let U : Lp ℝ p ν := huMem.toLp u
  let K : Fin d → Lp ℝ p ν := fun i => (hDMem i).toLp (D i)
  have hU : U =ᵐ[ν] u := huMem.coeFn_toLp
  have hK (i : Fin d) : K i =ᵐ[ν] D i := (hDMem i).coeFn_toLp
  refine ⟨U, K, hU, hK, ?_⟩
  obtain ⟨C, hC⟩ := hu.exists_lipschitzOnWith_of_compact (isCompact_Icc.prod hΩc)
  intro i
  filter_upwards [Measure.ae_ae_of_ae_prod hU, Measure.ae_ae_of_ae_prod (hK i),
    ae_restrict_mem measurableSet_Icc] with t htU htK ht
  have hslice : LipschitzOnWith C (fun x : E => u (t, x)) Ω := by
    simpa only [mul_one, Function.comp_def] using
      hC.comp (LipschitzWith.prodMk_left t).lipschitzOnWith
        (fun x hx => ⟨ht, subset_closure hx⟩)
  exact (hasWeakPartialDeriv_fderiv_of_lipschitzOnWith hΩ hslice i).congr_ae
    (Filter.EventuallyEq.symm htU) (Filter.EventuallyEq.symm htK)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
