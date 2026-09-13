import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ClassWidth
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

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
    {D : RealTimeInterval}

include hT2 hCompact hConnected hBoundary

abbrev RampFamilyDeformation (a b : ℝ) (hab : a < b)
    (G : SolutionFamily (I := I) (M := Q)) : Prop :=
  ∀ (d : ℕ) (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (epsilon ell : ℝ),
    0 < epsilon → 0 < ell →
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 ∧
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn G.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn G.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((deformed t) p).1 z = (solutions p).projection z t) ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
          (∀ p, |regularLeastArea (G.metric a) ((deformed ⟨a, le_rfl, hab.le⟩) p) -
            regularLeastArea (G.metric a) (Γ p)| < epsilon) ∧
          ∀ p,
            loopLength (G.metric b)
              (((deformed ⟨b, hab.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
            regularLeastArea (G.metric b) ((deformed ⟨b, hab.le, le_rfl⟩) p) ≤
              affineComparison G a b (regularLeastArea (G.metric a) (Γ p)) + epsilon

theorem rfs_rampFamilyDeformation_of_family_deformation {a b : ℝ}
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3) :
    ∀ (s t : ℝ) (hst : s < t), a ≤ s → t ≤ b → RampFamilyDeformation s t hst B.family := by
  intro s t hst hs ht d e Γ epsilon ell hepsilon hell
  let B' : RicciBackground (I := I) (M := Q) D s t :=
    { B with
      lt := hst
      regular := fun u hu => B.regular ⟨hs.trans hu.1, hu.2.trans ht⟩
      ricci_bound := fun u hu => B.ricci_bound u ⟨hs.trans hu.1, hu.2.trans ht⟩
      riemann_bound := fun u hu => B.riemann_bound u ⟨hs.trans hu.1, hu.2.trans ht⟩
      nablaRicci_bound := fun u hu =>
        B.nablaRicci_bound u ⟨hs.trans hu.1, hu.2.trans ht⟩ }
  exact rfs_family_deformation B' hdim e Γ epsilon ell hepsilon hell

omit [SigmaCompactSpace Q] in
private theorem classWidth_le_affine_familyMaximum_add_of_deformation {a b : ℝ} (hab : a < b)
    (G : SolutionFamily (I := I) (M := Q))
    (hdeform : RampFamilyDeformation a b hab G)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ)
    (Γ : Width.RegularRepresentative (I := I) ξ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Width.classWidth (G.metric b) ξ ≤
      affineComparison G a b (Width.familyMaximum (G.metric a) Γ.1) +
        2 * epsilon := by
  classical
  obtain ⟨sigma, K, hsigma, hK, hlong, hshort⟩ :=
    rfs_essential_short_family (G.metric b)
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
    hdeform _ e Γ.1 epsilon ell hepsilon hell
  let tb : Icc a b := ⟨b, hab.le, le_rfl⟩
  let Γb : Width.RegularRepresentative (I := I) ξ :=
    ⟨deformed tb, (hclass tb).2.trans Γ.2⟩
  have hmono (p : Sphere 2) :
      affineComparison G a b (Width.regularLeastArea (G.metric a) (Γ.1 p)) ≤
        affineComparison G a b (Width.familyMaximum (G.metric a) Γ.1) :=
    (affineComparison_strictMono G a b).monotone
      (Width.regularLeastArea_le_familyMaximum (G.metric a) Γ.1 p)
  obtain ⟨p, hp⟩ := hlong ξ hessential Γb ell hell hellsigma
  have hnonneg : 0 ≤ affineComparison G a b (Width.familyMaximum (G.metric a) Γ.1) + epsilon := by
    rcases halt p with hshortp | hlongp
    · exact False.elim ((not_lt_of_ge hp) hshortp)
    · have harea := Width.regularLeastArea_nonneg (G.metric b) (Γb.1 p)
      have hm := hmono p
      dsimp only [Γb, tb] at harea
      linarith
  have hmax : Width.familyMaximum (G.metric b) Γb.1 ≤
      affineComparison G a b (Width.familyMaximum (G.metric a) Γ.1) +
        2 * epsilon := by
    obtain ⟨q, hq⟩ := Width.familyMaximum_attained (G.metric b) Γb.1
    rw [hq]
    rcases halt q with hshortq | hlongq
    · have harea := (hshort (Γb.1 q) ell hell hellsigma hshortq).trans hsmall
      linarith
    · have hm := hmono q
      change Width.regularLeastArea (G.metric b) ((deformed ⟨b, hab.le, le_rfl⟩) q) ≤ _
      linarith
  exact (Width.classWidth_le_familyMaximum (G.metric b) ξ Γb).trans hmax

omit [SigmaCompactSpace Q] in
private theorem integrated_class_width_endpoints_of_deformation {a b : ℝ} (hab : a < b)
    (G : SolutionFamily (I := I) (M := Q))
    (hdeform : RampFamilyDeformation a b hab G)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ) :
    0 ≤ Width.classWidth (G.metric b) ξ ∧
      Width.classWidth (G.metric b) ξ ≤
        affineComparison G a b (Width.classWidth (G.metric a) ξ) ∧
      areaIntegratingFactor G a b * Width.classWidth (G.metric b) ξ ≤
        Width.classWidth (G.metric a) ξ -
          2 * Real.pi * ∫ v in a..b, areaIntegratingFactor G a v := by
  have hfamily (Γ : Width.RegularRepresentative (I := I) ξ) :
      Width.classWidth (G.metric b) ξ ≤
        affineComparison G a b (Width.familyMaximum (G.metric a) Γ.1) := by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have h := classWidth_le_affine_familyMaximum_add_of_deformation hab G hdeform ξ hessential Γ
      (div_pos hepsilon (by norm_num) : 0 < epsilon / 2)
    linarith
  have hlower : areaIntegratingFactor G a b * Width.classWidth (G.metric b) ξ +
      2 * Real.pi * (∫ v in a..b, areaIntegratingFactor G a v) ≤
        Width.classWidth (G.metric a) ξ := by
    apply le_csInf (Width.representativeMaxima_nonempty (G.metric a) ξ)
    rintro _ ⟨Γ, rfl⟩
    have h := (le_inv_mul_iff₀ (areaIntegratingFactor_pos G a b)).mp (hfamily Γ)
    linarith
  have hintegrated : areaIntegratingFactor G a b * Width.classWidth (G.metric b) ξ ≤
      Width.classWidth (G.metric a) ξ -
        2 * Real.pi * ∫ v in a..b, areaIntegratingFactor G a v := by linarith
  exact ⟨Width.classWidth_nonneg (G.metric b) ξ,
    (le_inv_mul_iff₀ (areaIntegratingFactor_pos G a b)).mpr hintegrated, hintegrated⟩

omit [SigmaCompactSpace Q] in
theorem rfs_integrated_class_width_of_rampFamilyDeformation {a b : ℝ}
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdeform : ∀ (s t : ℝ) (hst : s < t), a ≤ s → t ≤ b →
      RampFamilyDeformation s t hst B.family)
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
  · exact integrated_class_width_endpoints_of_deformation hst B.family
      (hdeform s t hst hs.1 ht.2) ξ hessential

omit [SigmaCompactSpace Q] in
theorem rfs_smooth_class_width_of_rampFamilyDeformation {a b : ℝ}
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdeform : ∀ (s t : ℝ) (hst : s < t), a ≤ s → t ≤ b →
      RampFamilyDeformation s t hst B.family)
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
  have hcomparison := rfs_integrated_class_width_of_rampFamilyDeformation B hdeform ξ hessential
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
