import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Deformation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.EssentialClass
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology CurveShortening

private theorem upper_slope_of_comparison {W f : ℝ → ℝ} {a b t L : ℝ}
    (ht : t ∈ Ico a b) (heq : W t = f t)
    (hcompare : ∀ h : ℝ, 0 < h → t + h ≤ b → W (t + h) ≤ f (t + h))
    (hd : HasDerivWithinAt f L (Icc a b) t) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t + h ≤ b →
      (W (t + h) - W t) / h ≤ L + epsilon := by
  intro epsilon hepsilon
  have hevent := hd.limsup_slope_le (by linarith : L < L + epsilon)
  obtain ⟨delta, hdelta, hclose⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨delta, hdelta, ?_⟩
  intro h hh htb
  have hball : t + h ∈ Metric.ball t delta := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh.1]
    exact hh.2
  have hwindow : t + h ∈ Icc a b \ {t} := by
    refine ⟨⟨?_, htb⟩, ?_⟩
    · linarith [ht.1, hh.1]
    · simp only [mem_singleton_iff]
      linarith [hh.1]
  have hslope : (f (t + h) - f t) / h < L + epsilon := by
    have hc := hclose ⟨hball, hwindow⟩
    change slope f t (t + h) < L + epsilon at hc
    simpa only [slope, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hc
  calc
    (W (t + h) - W t) / h ≤ (f (t + h) - f t) / h := by
      rw [heq]
      exact div_le_div_of_nonneg_right (sub_le_sub_right (hcompare h hh.1 htb) _) hh.1.le
    _ ≤ L + epsilon := hslope.le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

private theorem classWidth_le_affine_familyMaximum_add
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ)
    (Γ : Width.RegularRepresentative (I := I) ξ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Width.classWidth (B.family.metric b) ξ ≤
      affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) +
        2 * epsilon := by
  classical
  obtain ⟨sigma, K, hsigma, hK, hlong, hshort⟩ :=
    rfs_essential_short_family (B.family.metric b)
  let ell := min sigma (min 1 (epsilon / (K + 1)))
  have hell : 0 < ell := lt_min hsigma (lt_min (by norm_num) (div_pos hepsilon (by positivity)))
  have hellsigma : ell ≤ sigma := min_le_left _ _
  have hellone : ell ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have helldiv : ell ≤ epsilon / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : K * ell ^ 2 ≤ epsilon := by
    have hprod : ell * (K + 1) ≤ epsilon := (le_div_iff₀ (by positivity)).mp helldiv
    have hsquare : ell ^ 2 ≤ ell := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsquare hK
    nlinarith
  obtain ⟨_N, ⟨e⟩⟩ := Width.smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨_lambda, _, _, _solutions, deformed, _, _, _, hclass, _, halt⟩ :=
    rfs_family_deformation B hdim e Γ.1 epsilon ell hepsilon hell
  let tb : Icc a b := ⟨b, B.lt.le, le_rfl⟩
  let Γb : Width.RegularRepresentative (I := I) ξ :=
    ⟨deformed tb, (hclass tb).2.trans Γ.2⟩
  have hmono (p : Sphere 2) :
      affineComparison B.family a b (Width.regularLeastArea (B.family.metric a) (Γ.1 p)) ≤
        affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) :=
    (affineComparison_strictMono B.family a b).monotone
      (Width.regularLeastArea_le_familyMaximum (B.family.metric a) Γ.1 p)
  obtain ⟨p, hp⟩ := hlong ξ hessential Γb ell hell hellsigma
  have hnonneg : 0 ≤
      affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) + epsilon := by
    rcases halt p with hshortp | hlongp
    · exact False.elim ((not_lt_of_ge hp) hshortp)
    · have harea := Width.regularLeastArea_nonneg (B.family.metric b) (Γb.1 p)
      have hm := hmono p
      dsimp only [Γb, tb] at harea
      linarith
  have hmax : Width.familyMaximum (B.family.metric b) Γb.1 ≤
      affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) +
        2 * epsilon := by
    obtain ⟨q, hq⟩ := Width.familyMaximum_attained (B.family.metric b) Γb.1
    rw [hq]
    rcases halt q with hshortq | hlongq
    · have harea := (hshort (Γb.1 q) ell hell hellsigma hshortq).trans hsmall
      linarith
    · have hm := hmono q
      change Width.regularLeastArea (B.family.metric b)
        ((deformed ⟨b, B.lt.le, le_rfl⟩) q) ≤ _
      linarith
  exact (Width.classWidth_le_familyMaximum (B.family.metric b) ξ Γb).trans hmax

private theorem integrated_class_width_endpoints
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ) :
    0 ≤ Width.classWidth (B.family.metric b) ξ ∧
      Width.classWidth (B.family.metric b) ξ ≤
        affineComparison B.family a b (Width.classWidth (B.family.metric a) ξ) ∧
      areaIntegratingFactor B.family a b * Width.classWidth (B.family.metric b) ξ ≤
        Width.classWidth (B.family.metric a) ξ -
          2 * Real.pi * ∫ v in a..b, areaIntegratingFactor B.family a v := by
  have hfamily (Γ : Width.RegularRepresentative (I := I) ξ) :
      Width.classWidth (B.family.metric b) ξ ≤
        affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) := by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have h := classWidth_le_affine_familyMaximum_add B hdim ξ hessential Γ
      (div_pos hepsilon (by norm_num) : 0 < epsilon / 2)
    linarith
  have hlower : areaIntegratingFactor B.family a b * Width.classWidth (B.family.metric b) ξ +
      2 * Real.pi * (∫ v in a..b, areaIntegratingFactor B.family a v) ≤
        Width.classWidth (B.family.metric a) ξ := by
    apply le_csInf (Width.representativeMaxima_nonempty (B.family.metric a) ξ)
    rintro _ ⟨Γ, rfl⟩
    have h := (le_inv_mul_iff₀ (areaIntegratingFactor_pos B.family a b)).mp (hfamily Γ)
    linarith
  have hintegrated : areaIntegratingFactor B.family a b * Width.classWidth (B.family.metric b) ξ ≤
      Width.classWidth (B.family.metric a) ξ -
        2 * Real.pi * ∫ v in a..b, areaIntegratingFactor B.family a v := by linarith
  exact ⟨Width.classWidth_nonneg (B.family.metric b) ξ,
    (le_inv_mul_iff₀ (areaIntegratingFactor_pos B.family a b)).mpr hintegrated, hintegrated⟩

theorem rfs_integrated_class_width (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      0 ≤ Width.classWidth (B.family.metric t) ξ ∧
      Width.classWidth (B.family.metric t) ξ ≤
        affineComparison B.family s t (Width.classWidth (B.family.metric s) ξ) ∧
      areaIntegratingFactor B.family s t * Width.classWidth (B.family.metric t) ξ ≤
        Width.classWidth (B.family.metric s) ξ -
          2 * Real.pi * ∫ v in s..t, areaIntegratingFactor B.family s v := by
  intro s hs t ht
  rcases eq_or_lt_of_le ht.1 with hst | hst
  · subst t
    simp only [affineComparison_self, areaIntegratingFactor, intervalIntegral.integral_same,
      mul_zero, Real.exp_zero, one_mul, sub_zero, le_refl, and_true]
    exact Width.classWidth_nonneg (B.family.metric s) ξ
  · let B' : RicciBackground (I := I) (M := Q) D s t :=
      { B with
        lt := hst
        regular := fun u hu => B.regular ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        ricci_bound := fun u hu => B.ricci_bound u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        riemann_bound := fun u hu => B.riemann_bound u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        nablaRicci_bound := fun u hu =>
          B.nablaRicci_bound u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩ }
    exact integrated_class_width_endpoints B' hdim ξ hessential

theorem rfs_smooth_class_width (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ) :
    ContinuousOn (fun t => Width.classWidth (B.family.metric t) ξ) (Icc a b) ∧
      (∀ t ∈ Ico a b, ∀ epsilon > 0, ∃ delta > 0,
        ∀ h ∈ Ioo (0 : ℝ) delta, t + h ≤ b →
          (Width.classWidth (B.family.metric (t + h)) ξ -
            Width.classWidth (B.family.metric t) ξ) / h ≤
            -2 * Real.pi - halfScalarMinimum B.family t *
              Width.classWidth (B.family.metric t) ξ + epsilon) ∧
      ∀ t ∈ Icc a b, ∀ v ∈ Ioc t b,
        0 < 2 * Real.pi * (∫ u in t..v, areaIntegratingFactor B.family t u) ∧
        2 * Real.pi * (∫ u in t..v, areaIntegratingFactor B.family t u) ≤
          Width.classWidth (B.family.metric t) ξ := by
  have hcomparison := rfs_integrated_class_width B hdim ξ hessential
  refine ⟨?_, ?_, ?_⟩
  · exact (Width.continuousOn_classWidth_metricFamily D B.family.metric B.smooth ξ).mono
      (fun t ht => D.regular_subset (B.regular ht))
  · intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have hd := (rfs_width_affine_comparison B).1 t ht'
      (Width.classWidth (B.family.metric t) ξ) t ht'
    simp only [affineComparison_self] at hd
    apply upper_slope_of_comparison
      (W := fun u => Width.classWidth (B.family.metric u) ξ)
      (f := fun v => affineComparison B.family t v (Width.classWidth (B.family.metric t) ξ))
      ht (by simp only [affineComparison_self]) ?_ hd
    intro h hh htb
    exact (hcomparison t ht' (t + h) ⟨by linarith, htb⟩).2.1
  · intro t ht v hv
    have hfactor : ContinuousOn (areaIntegratingFactor B.family t) (Icc t v) :=
      (areaIntegratingFactor_continuousOn B ht).mono
        (fun u hu => ⟨ht.1.trans hu.1, hu.2.trans hv.2⟩)
    have hpositive : 0 < ∫ u in t..v, areaIntegratingFactor B.family t u :=
      intervalIntegral.integral_pos hv.1 hfactor
        (fun u _ => (areaIntegratingFactor_pos B.family t u).le)
        ⟨t, ⟨le_rfl, hv.1.le⟩, areaIntegratingFactor_pos B.family t t⟩
    obtain ⟨hW, _, hbound⟩ := hcomparison t ht v ⟨hv.1.le, hv.2⟩
    have hproduct : 0 ≤ areaIntegratingFactor B.family t v *
        Width.classWidth (B.family.metric v) ξ :=
      mul_nonneg (areaIntegratingFactor_pos B.family t v).le hW
    exact ⟨mul_pos (mul_pos (by norm_num) Real.pi_pos) hpositive, by linarith⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
