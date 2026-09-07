import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
variable {mu : Measure E} [SFinite mu]

omit [BorelSpace E] in
theorem integral_fderiv_normal_half_space_of_integrable
    {u : E × Real → F} {a : Real}
    (hc : ContinuousOn u (univ ×ˢ Ici a))
    (hd : DifferentiableOn Real u (univ ×ˢ Ioi a))
    (hi : Integrable (fun p => fderiv Real u p (0, 1))
      (mu.prod (volume.restrict (Ioi a))))
    (hzero : ∀ᵐ x ∂mu, Tendsto (fun t : Real => u (x, t)) atTop (𝓝 0)) :
    ∫ p, fderiv Real u p (0, 1) ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, u (x, a) ∂mu := by
  rw [integral_prod _ hi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae, hzero] with x hx hxzero
  have hc' : ContinuousWithinAt (fun t : Real => u (x, t)) (Ici a) a := by
    refine (hc (x, a) ⟨mem_univ _, self_mem_Ici⟩).comp
      (continuous_const.prodMk continuous_id).continuousWithinAt ?_
    intro t ht
    exact ⟨mem_univ _, ht⟩
  have hd' (t : Real) (ht : t ∈ Ioi a) :
      HasDerivAt (fun s : Real => u (x, s)) (fderiv Real u (x, t) (0, 1)) t := by
    have hdiff : DifferentiableAt Real u (x, t) :=
      (hd (x, t) ⟨mem_univ _, ht⟩).differentiableAt
        ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ _, ht⟩)
    exact hdiff.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto hc' hd' hx hxzero

omit [SFinite mu] [CompleteSpace F] [NormedSpace Real E] [NormedSpace Real F] in
private theorem integrableOn_of_continuousOn_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts mu] {f : E → F} {s : Set E}
    (hf : ContinuousOn f s) (hcs : HasCompactSupport f) (hs : IsClosed s) :
    IntegrableOn f s mu := by
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  rw [IntegrableOn, Measure.restrict_restrict (isClosed_tsupport _).measurableSet]
  exact (hf.mono inter_subset_right).integrableOn_compact (hcs.inter_right hs)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem hasCompactSupport_fderivWithin
    {u : E → F} (hcs : HasCompactSupport u) (s : Set E) :
    HasCompactSupport (fderivWithin Real u s) := by
  apply hcs.mono'
  intro x hx
  by_contra hnot
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hnot).fderivWithin_eq_of_nhds
    (𝕜 := Real) (s := s)
  exact hx (by simpa using hz)

omit [CompleteSpace F] in
private theorem integrable_fderivWithin_half_space_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts mu] {u : E × Real → F} {a : Real}
    (hu : ContDiffOn Real 1 u (univ ×ˢ Ici a)) (hcs : HasCompactSupport u) :
    Integrable (fderivWithin Real u (univ ×ˢ Ici a))
      (mu.prod (volume.restrict (Ioi a))) := by
  have hcont := hu.continuousOn_fderivWithin
    (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici a)) le_rfl
  have h := integrableOn_of_continuousOn_of_hasCompactSupport
    (mu := mu.prod volume) hcont (hasCompactSupport_fderivWithin hcs _)
      (isClosed_univ.prod isClosed_Ici)
  have h' := h.mono_set (prod_mono Subset.rfl Ioi_subset_Ici_self)
  simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using h'

omit [SFinite mu] [BorelSpace E] [CompleteSpace F] in
private theorem fderivWithin_half_space_eq_fderiv_ae {u : E × Real → F} (a : Real) :
    ∀ᵐ p ∂(mu.prod (volume.restrict (Ioi a))),
      fderivWithin Real u (univ ×ˢ Ici a) p = fderiv Real u p := by
  have hmem : ∀ᵐ p ∂(mu.prod (volume.restrict (Ioi a))), p.2 ∈ Ioi a := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).mpr
    filter_upwards with x
    exact ae_restrict_mem measurableSet_Ioi
  filter_upwards [hmem] with p hp
  apply fderivWithin_of_mem_nhds
  exact mem_of_superset ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ _, hp⟩)
    (prod_mono Subset.rfl Ioi_subset_Ici_self)

theorem integral_fderivWithin_normal_half_space_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts mu] {u : E × Real → F} {a : Real}
    (hu : ContDiffOn Real 1 u (univ ×ˢ Ici a)) (hcs : HasCompactSupport u) :
    ∫ p, fderivWithin Real u (univ ×ˢ Ici a) p (0, 1)
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, u (x, a) ∂mu := by
  let s : Set (E × Real) := univ ×ˢ Ici a
  have hint : Integrable (fun p => fderivWithin Real u s p (0, 1))
      (mu.prod (volume.restrict (Ioi a))) :=
    (integrable_fderivWithin_half_space_of_hasCompactSupport hu hcs).apply_continuousLinearMap _
  have heq : ∀ᵐ p ∂(mu.prod (volume.restrict (Ioi a))),
      fderivWithin Real u s p = fderiv Real u p := fderivWithin_half_space_eq_fderiv_ae a
  calc
    _ = ∫ p, fderiv Real u p (0, 1) ∂(mu.prod (volume.restrict (Ioi a))) :=
      integral_congr_ae (heq.mono fun p hp => congrArg (fun L => L (0, 1)) hp)
    _ = _ := by
      apply integral_fderiv_normal_half_space_of_integrable hu.continuousOn
        ((hu.differentiableOn one_ne_zero).mono (prod_mono Subset.rfl Ioi_subset_Ici_self))
        (hint.congr (heq.mono fun p hp => congrArg (fun L => L (0, 1)) hp))
      filter_upwards with x
      have hiso : Isometry (fun t : Real => (x, t)) := by
        apply Isometry.of_dist_eq
        intro t r
        simp
      have hslice := hcs.comp_isClosedEmbedding hiso.isClosedEmbedding
      rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hslice
      exact (hslice.filter_mono atTop_le_cocompact).tendsto

theorem integral_smul_fderivWithin_normal_add_fderivWithin_smul_half_space_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts mu]
    {phi : E × Real → Real} {u : E × Real → F} {a : Real}
    (hphi : ContDiffOn Real 1 phi (univ ×ˢ Ici a))
    (hu : ContDiffOn Real 1 u (univ ×ˢ Ici a))
    (hcs : HasCompactSupport (fun p => phi p • u p)) :
    ∫ p, phi p • fderivWithin Real u (univ ×ˢ Ici a) p (0, 1) +
        fderivWithin Real phi (univ ×ˢ Ici a) p (0, 1) • u p
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, phi (x, a) • u (x, a) ∂mu := by
  have h := integral_fderivWithin_normal_half_space_of_hasCompactSupport
    (mu := mu) (hphi.smul hu) hcs
  convert h using 1
  · apply integral_congr_ae
    have hmem : ∀ᵐ p ∂(mu.prod (volume.restrict (Ioi a))), p.2 ∈ Ioi a := by
      apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).mpr
      filter_upwards with x
      exact ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with p hp
    have hps : p ∈ univ ×ˢ Ici a := ⟨mem_univ _, mem_Ici.mpr (mem_Ioi.mp hp).le⟩
    rw [fderivWithin_smul (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici a) p hps)
      (hphi.differentiableOn one_ne_zero p hps) (hu.differentiableOn one_ne_zero p hps)]
    rfl
  · rfl

omit [SFinite mu] [CompleteSpace F] in
theorem integral_fderivWithin_tangent_half_space_eq_zero_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {u : E × Real → F} {a : Real}
    (hu : ContDiffOn Real 1 u (univ ×ˢ Ici a)) (hcs : HasCompactSupport u) (v : E) :
    ∫ p, fderivWithin Real u (univ ×ˢ Ici a) p (v, 0)
        ∂(mu.prod (volume.restrict (Ioi a))) = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hint := (integrable_fderivWithin_half_space_of_hasCompactSupport (mu := mu) hu hcs)
    |>.apply_continuousLinearMap (v, 0)
  rw [integral_prod_symm _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hut : ContDiff Real 1 (fun x : E => u (x, t)) := by
    rw [← contDiffOn_univ]
    refine hu.comp (contDiff_id.prodMk contDiff_const).contDiffOn ?_
    intro x _
    exact ⟨mem_univ _, mem_Ici.mpr (mem_Ioi.mp ht).le⟩
  have hiso : Isometry (fun x : E => (x, t)) := by
    apply Isometry.of_dist_eq
    intro x y
    simp
  have hcut : HasCompactSupport (fun x : E => u (x, t)) :=
    hcs.comp_isClosedEmbedding hiso.isClosedEmbedding
  have hu_int : Integrable (fun x : E => u (x, t)) mu :=
    hut.continuous.integrable_of_hasCompactSupport hcut
  have hdu_int : Integrable (fun x : E => fderiv Real (fun y => u (y, t)) x v) mu :=
    ((hut.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply Real hcut v)
  have hd (x : E) : fderiv Real (fun y => u (y, t)) x v =
      fderivWithin Real u (univ ×ˢ Ici a) (x, t) (v, 0) := by
    have hmem : univ ×ˢ Ici a ∈ 𝓝 (x, t) :=
      mem_of_superset ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ _, ht⟩)
        (prod_mono Subset.rfl Ioi_subset_Ici_self)
    have hdiff : DifferentiableAt Real u (x, t) :=
      (hu.differentiableOn one_ne_zero (x, t)
        ⟨mem_univ _, mem_Ici.mpr (mem_Ioi.mp ht).le⟩).differentiableAt hmem
    rw [fderivWithin_of_mem_nhds hmem]
    exact congrArg (fun L : E →L[Real] F => L v)
      (hdiff.hasFDerivAt.comp x
        ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))).fderiv
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := mu) (f := fun _ : E => (1 : Real)) (g := fun x : E => u (x, t)) (v := v)
    (by simp) (by simpa only [one_smul] using hdu_int)
    (by simpa only [one_smul] using hu_int)
    (by intro x _; exact differentiableAt_const (1 : Real))
    (fun x _ => hut.differentiable one_ne_zero x)
  simpa [hd] using hibp

omit [SFinite mu] in
theorem integral_trace_fderivWithin_half_space_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {u : E × Real → E × Real} {a : Real}
    (hu : ContDiffOn Real 1 u (univ ×ˢ Ici a)) (hcs : HasCompactSupport u) :
    ∫ p, LinearMap.trace Real (E × Real)
        (fderivWithin Real u (univ ×ˢ Ici a) p).toLinearMap
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, (u (x, a)).2 ∂mu := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let nu := mu.prod (volume.restrict (Ioi a))
  let D := fderivWithin Real u (univ ×ˢ Ici a)
  have hDint : Integrable D nu := integrable_fderivWithin_half_space_of_hasCompactSupport hu hcs
  let A := ∫ p, D p ∂nu
  have htangent (v : E) : A (v, 0) = 0 := by
    rw [ContinuousLinearMap.integral_apply hDint]
    exact integral_fderivWithin_tangent_half_space_eq_zero_of_hasCompactSupport hu hcs v
  have hnormal : A (0, 1) = -∫ x, u (x, a) ∂mu := by
    rw [ContinuousLinearMap.integral_apply hDint]
    exact integral_fderivWithin_normal_half_space_of_hasCompactSupport hu hcs
  have hD : (∫ p, D p ∂nu) =
      (ContinuousLinearMap.snd Real E Real).smulRight (-∫ x, u (x, a) ∂mu) := by
    apply ContinuousLinearMap.ext
    intro v
    change A v = _
    conv_lhs => rw [show v = (v.1, 0) + v.2 • (0, 1) by ext <;> simp]
    rw [map_add, map_smul, htangent, hnormal, zero_add]
    rfl
  let trLinear : ((E × Real) →L[Real] (E × Real)) →ₗ[Real] Real :=
    { toFun := fun L => LinearMap.trace Real (E × Real) L.toLinearMap
      map_add' := by intro L K; exact map_add (LinearMap.trace Real (E × Real)) _ _
      map_smul' := by intro c L; exact map_smul (LinearMap.trace Real (E × Real)) c _ }
  let tr := trLinear.toContinuousLinearMap
  have htrace := tr.integral_comp_comm hDint
  change (∫ p, LinearMap.trace Real (E × Real) (D p).toLinearMap ∂nu) =
    LinearMap.trace Real (E × Real) (∫ p, D p ∂nu).toLinearMap at htrace
  rw [htrace, hD]
  change LinearMap.trace Real (E × Real)
    ((LinearMap.snd Real E Real).smulRight (-∫ x, u (x, a) ∂mu)) = _
  rw [LinearMap.trace_smulRight]
  have hiso : Isometry (fun x : E => (x, a)) := by
    apply Isometry.of_dist_eq
    intro x y
    simp
  have hboundCont : Continuous (fun x : E => u (x, a)) := by
    rw [← continuousOn_univ]
    refine hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn ?_
    intro x _
    exact ⟨mem_univ _, self_mem_Ici⟩
  have hboundary : Integrable (fun x : E => u (x, a)) mu :=
    hboundCont.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding hiso.isClosedEmbedding)
  change -(∫ x, u (x, a) ∂mu).2 = _
  rw [snd_integral hboundary]

omit [SFinite mu] in
theorem integral_mul_trace_fderivWithin_add_fderivWithin_half_space_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {phi : E × Real → Real} {u : E × Real → E × Real} {a : Real}
    (hphi : ContDiffOn Real 1 phi (univ ×ˢ Ici a))
    (hu : ContDiffOn Real 1 u (univ ×ˢ Ici a))
    (hcs : HasCompactSupport (fun p => phi p • u p)) :
    ∫ p, phi p * LinearMap.trace Real (E × Real)
          (fderivWithin Real u (univ ×ˢ Ici a) p).toLinearMap +
        fderivWithin Real phi (univ ×ˢ Ici a) p (u p)
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, phi (x, a) * (u (x, a)).2 ∂mu := by
  have h := integral_trace_fderivWithin_half_space_of_hasCompactSupport
    (mu := mu) (hphi.smul hu) hcs
  convert h using 1
  · apply integral_congr_ae
    have hmem : ∀ᵐ p ∂(mu.prod (volume.restrict (Ioi a))), p.2 ∈ Ioi a := by
      apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).mpr
      filter_upwards with x
      exact ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with p hp
    have hps : p ∈ univ ×ˢ Ici a := ⟨mem_univ _, mem_Ici.mpr (mem_Ioi.mp hp).le⟩
    rw [fderivWithin_smul (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici a) p hps)
      (hphi.differentiableOn one_ne_zero p hps) (hu.differentiableOn one_ne_zero p hps)]
    change _ = LinearMap.trace Real (E × Real)
      (phi p • (fderivWithin Real u (univ ×ˢ Ici a) p).toLinearMap +
        (fderivWithin Real phi (univ ×ˢ Ici a) p).toLinearMap.smulRight (u p))
    rw [map_add, map_smul, LinearMap.trace_smulRight]
    rfl
  · rfl

theorem integral_fderiv_normal_half_space_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts mu]
    {u : E × Real → F} (hu : ContDiff Real 1 u) (hcs : HasCompactSupport u) (a : Real) :
    ∫ p, fderiv Real u p (0, 1) ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, u (x, a) ∂mu := by
  refine (integral_congr_ae ?_).trans
    (integral_fderivWithin_normal_half_space_of_hasCompactSupport (a := a) hu.contDiffOn hcs)
  filter_upwards [fderivWithin_half_space_eq_fderiv_ae (u := u) (mu := mu) a] with p hp
  rw [hp]

theorem integral_smul_fderiv_normal_add_fderiv_smul_half_space_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts mu]
    {phi : E × Real → Real} {u : E × Real → F}
    (hphi : ContDiff Real 1 phi) (hu : ContDiff Real 1 u)
    (hcs : HasCompactSupport (fun p => phi p • u p)) (a : Real) :
    ∫ p, phi p • fderiv Real u p (0, 1) + fderiv Real phi p (0, 1) • u p
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, phi (x, a) • u (x, a) ∂mu := by
  refine (integral_congr_ae ?_).trans
    (integral_smul_fderivWithin_normal_add_fderivWithin_smul_half_space_of_hasCompactSupport
      (a := a) hphi.contDiffOn hu.contDiffOn hcs)
  filter_upwards [fderivWithin_half_space_eq_fderiv_ae (u := u) (mu := mu) a,
    fderivWithin_half_space_eq_fderiv_ae (u := phi) (mu := mu) a] with p hp hq
  rw [hp, hq]

omit [SFinite mu] [CompleteSpace F] in
theorem integral_fderiv_tangent_half_space_eq_zero_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {u : E × Real → F} (hu : ContDiff Real 1 u) (hcs : HasCompactSupport u)
    (a : Real) (v : E) :
    ∫ p, fderiv Real u p (v, 0) ∂(mu.prod (volume.restrict (Ioi a))) = 0 := by
  refine (integral_congr_ae ?_).trans
    (integral_fderivWithin_tangent_half_space_eq_zero_of_hasCompactSupport
      (a := a) hu.contDiffOn hcs v)
  filter_upwards [fderivWithin_half_space_eq_fderiv_ae (u := u) (mu := mu) a] with p hp
  rw [hp]

omit [SFinite mu] in
theorem integral_trace_fderiv_half_space_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {u : E × Real → E × Real} (hu : ContDiff Real 1 u) (hcs : HasCompactSupport u)
    (a : Real) :
    ∫ p, LinearMap.trace Real (E × Real) (fderiv Real u p).toLinearMap
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, (u (x, a)).2 ∂mu := by
  refine (integral_congr_ae ?_).trans
    (integral_trace_fderivWithin_half_space_of_hasCompactSupport (a := a) hu.contDiffOn hcs)
  filter_upwards [fderivWithin_half_space_eq_fderiv_ae (u := u) (mu := mu) a] with p hp
  rw [hp]

omit [SFinite mu] in
theorem integral_mul_trace_fderiv_add_fderiv_half_space_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {phi : E × Real → Real} {u : E × Real → E × Real}
    (hphi : ContDiff Real 1 phi) (hu : ContDiff Real 1 u)
    (hcs : HasCompactSupport (fun p => phi p • u p)) (a : Real) :
    ∫ p, phi p * LinearMap.trace Real (E × Real) (fderiv Real u p).toLinearMap +
        fderiv Real phi p (u p) ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, phi (x, a) * (u (x, a)).2 ∂mu := by
  refine (integral_congr_ae ?_).trans
    (integral_mul_trace_fderivWithin_add_fderivWithin_half_space_of_hasCompactSupport
      (a := a) hphi.contDiffOn hu.contDiffOn hcs)
  filter_upwards [fderivWithin_half_space_eq_fderiv_ae (u := u) (mu := mu) a,
    fderivWithin_half_space_eq_fderiv_ae (u := phi) (mu := mu) a] with p hp hq
  rw [hp, hq]

end DifferentialGeometry.Analysis
