import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

omit [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem exists_exp_mul_sub_one_lt (k : ℝ) (hk : 0 ≤ k) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, Real.exp (k * h) - 1 < θ := by
  have hcont : Continuous fun h : ℝ => Real.exp (k * h) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuous_iff.mp hcont 0 θ hθ
  refine ⟨δ, hδpos, fun h hh => ?_⟩
  have hd : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]
    exact hh.2
  have h1 := hδ h hd
  rw [Real.dist_eq, mul_zero, Real.exp_zero] at h1
  have h2 : 0 ≤ Real.exp (k * h) - 1 := by
    have h3 : (1 : ℝ) ≤ Real.exp (k * h) := Real.one_le_exp (mul_nonneg hk hh.1.le)
    linarith
  rwa [abs_of_nonneg h2] at h1

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem le_exp_mul_of_right_slope_bound (F : ℝ → ℝ) {s t k : ℝ} (hst : s ≤ t)
    (hcont : ContinuousOn F (Icc s t))
    (hslope : ∀ v ∈ Ico s t, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ t →
      (F (v + h) - F v) / h ≤ k * F v + ε) :
    F t ≤ Real.exp (k * (t - s)) * F s := by
  have hDini : ∀ v ∈ Ico s t, v ∉ (∅ : Finset ℝ) → ∀ ε > 0, ∃ δ > 0,
      ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ t →
        (F (v + h) - F v) / h ≤ -(-k) * F v + 0 + ε := by
    intro v hv _ ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hslope v hv ε hε
    exact ⟨δ, hδpos, fun h hh hb => by
      simpa only [neg_neg, add_zero] using hδ h hh hb⟩
  have hmain := rfs_csf_area_comparison_ode F (fun _ : ℝ => -k) (fun _ : ℝ => 0) s t hst
    hcont continuousOn_const continuousOn_const ∅ hDini
  have hInt : (∫ w in s..t, (-k : ℝ)) = -k * (t - s) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hzero : (∫ v in s..t, Real.exp (∫ w in s..v, (-k : ℝ)) * (0 : ℝ)) = 0 := by
    simp
  rw [hInt, hzero, add_zero] at hmain
  have hexp : Real.exp (k * (t - s)) * Real.exp (-k * (t - s)) = 1 := by
    rw [← Real.exp_add, show k * (t - s) + -k * (t - s) = 0 by ring, Real.exp_zero]
  calc F t = (Real.exp (k * (t - s)) * Real.exp (-k * (t - s))) * F t := by
        rw [hexp, one_mul]
    _ = Real.exp (k * (t - s)) * (Real.exp (-k * (t - s)) * F t) := by ring
    _ ≤ Real.exp (k * (t - s)) * F s :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_nonneg _)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem le_exp_mul_of_exp_integral_bound (A J : ℝ → ℝ) {s b k : ℝ} (hk : 0 ≤ k)
    (hJnn : ∀ v ∈ Icc s b, 0 ≤ J v)
    (hJcont : ContinuousOn J (Icc s b))
    (hint : ∀ s' ∈ Icc s b, ∀ u ∈ Icc s' b,
      A u ≤ Real.exp (k * (u - s')) * (A s' + ∫ v in s'..u, J v))
    {t : ℝ} (ht : t ∈ Ico s b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (A (t + h) - A t) / h ≤ k * A t + J t + ε := by
  have htIcc : t ∈ Icc s b := ⟨ht.1, ht.2.le⟩
  have h2pos : 0 < ε / 2 := by linarith
  obtain ⟨δJ, hδJpos, hδJ⟩ :=
    (Metric.continuousWithinAt_iff.mp (hJcont.continuousWithinAt htIcc)) (ε / 2) h2pos
  set P : ℝ := k * |A t| + (J t + ε / 2) with hP
  have hPpos : 0 < P := by
    have h1 : 0 ≤ k * |A t| := mul_nonneg hk (abs_nonneg _)
    have h2 : 0 ≤ J t := hJnn t htIcc
    rw [hP]
    linarith
  obtain ⟨δe, hδepos, hδe⟩ :=
    exists_exp_mul_sub_one_lt k hk (θ := (ε / 2) / P) (div_pos h2pos hPpos)
  refine ⟨min δJ δe, lt_min hδJpos hδepos, fun h hh hb => ?_⟩
  have hh0 : 0 < h := hh.1
  have hhδJ : h < δJ := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hhδe : h < δe := lt_of_lt_of_le hh.2 (min_le_right _ _)
  have hth : t ≤ t + h := by linarith
  have htIcc' : t + h ∈ Icc s b := ⟨by linarith [ht.1, hh0], hb⟩
  have hJv : ∀ v ∈ Icc t (t + h), J v ≤ J t + ε / 2 := by
    intro v hv
    have hvIcc : v ∈ Icc s b := ⟨le_trans ht.1 hv.1, le_trans hv.2 hb⟩
    have hd : dist v t < δJ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
      linarith [hv.2]
    have h1 := hδJ (x := v) hvIcc hd
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.mp h1).2]
  have hintJ : (∫ v in t..t + h, J v) ≤ h * (J t + ε / 2) := by
    have h1 : IntervalIntegrable J volume t (t + h) :=
      (hJcont.mono (Icc_subset_Icc ht.1 hb)).intervalIntegrable_of_Icc hth
    have h2 := intervalIntegral.integral_mono_on hth h1
      (continuous_const.intervalIntegrable (μ := volume) t (t + h)) hJv
    simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] using h2
  have hu := hint t htIcc (t + h) ⟨hth, hb⟩
  rw [add_sub_cancel_left] at hu
  have hstep : A (t + h) ≤ Real.exp (k * h) * (A t + h * (J t + ε / 2)) :=
    hu.trans (mul_le_mul_of_nonneg_left (by linarith [hintJ]) (Real.exp_nonneg _))
  have hφnn : 0 ≤ Real.exp (k * h) - 1 := by
    have h := Real.one_le_exp (mul_nonneg hk hh0.le)
    linarith
  have hEk : (Real.exp (k * h) - 1) / h ≤ k * Real.exp (k * h) := by
    rw [div_le_iff₀ hh0]
    have h := exp_increment_le k h h hk hh0.le le_rfl
    linarith
  have hkE : k ≤ (Real.exp (k * h) - 1) / h := by
    rw [le_div_iff₀ hh0]
    have h := Real.add_one_le_exp (k * h)
    linarith
  have hEcase : ((Real.exp (k * h) - 1) / h) * A t ≤
      k * A t + k * (Real.exp (k * h) - 1) * |A t| := by
    rcases le_total 0 (A t) with hA | hA
    · have h1 : ((Real.exp (k * h) - 1) / h) * A t ≤
          (k * Real.exp (k * h)) * A t := mul_le_mul_of_nonneg_right hEk hA
      have h2 : (k * Real.exp (k * h)) * A t =
          k * A t + k * (Real.exp (k * h) - 1) * |A t| := by
        rw [abs_of_nonneg hA]
        ring
      linarith [h1, h2.le, h2.ge]
    · have h1 : ((Real.exp (k * h) - 1) / h) * A t ≤ k * A t :=
        mul_le_mul_of_nonpos_right hkE hA
      have h2 : 0 ≤ k * (Real.exp (k * h) - 1) * |A t| := by
        have h3 : 0 ≤ k * (Real.exp (k * h) - 1) := mul_nonneg hk hφnn
        exact mul_nonneg h3 (abs_nonneg _)
      linarith
  have hφlt : Real.exp (k * h) - 1 < (ε / 2) / P := hδe h ⟨hh0, hhδe⟩
  have hPle : (Real.exp (k * h) - 1) * P ≤ ε / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hφlt.le hPpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hPpos)] at h1
  have hPe : (Real.exp (k * h) - 1) * P = k * (Real.exp (k * h) - 1) * |A t| +
      (Real.exp (k * h) - 1) * (J t + ε / 2) := by
    rw [hP]
    ring
  have hE2 : Real.exp (k * h) * (J t + ε / 2) =
      (J t + ε / 2) + (Real.exp (k * h) - 1) * (J t + ε / 2) := by
    ring
  have hmain2 : ((Real.exp (k * h) - 1) / h) * A t +
      Real.exp (k * h) * (J t + ε / 2) ≤ k * A t + J t + ε := by
    linarith [hEcase, hE2.le, hE2.ge, hPle, hPe.le, hPe.ge]
  have hAh : A (t + h) - A t ≤
      h * (((Real.exp (k * h) - 1) / h) * A t + Real.exp (k * h) * (J t + ε / 2)) := by
    have h2 : Real.exp (k * h) * (A t + h * (J t + ε / 2)) =
        (Real.exp (k * h) - 1) * A t + A t +
          h * (Real.exp (k * h) * (J t + ε / 2)) := by
      ring
    rw [h2] at hstep
    have h3 : h * (((Real.exp (k * h) - 1) / h) * A t) = (Real.exp (k * h) - 1) * A t := by
      field_simp
    linarith [hstep, h3.le, h3.ge]
  rw [div_le_iff₀ hh0]
  exact (hAh.trans (mul_le_mul_of_nonneg_left hmain2 hh0.le)).trans
    (le_of_eq (mul_comm h (k * A t + J t + ε)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem ProductCurve.length_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ)
    (c : ProductCurve M) : 0 ≤ c.length g lambda t := by
  rw [ProductCurve.length, ProductCurve.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg g lambda x t))

def curveShorteningTotalCurvatureSlope (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve M,
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    ContinuousOn (fun t => c.totalCurvature B.family.metric lambda t +
      c.length B.family.metric lambda t) (Icc a b) ∧
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      ((c.totalCurvature B.family.metric lambda (t + h) +
          c.length B.family.metric lambda (t + h)) -
        (c.totalCurvature B.family.metric lambda t +
          c.length B.family.metric lambda t)) / h ≤
        (B.C + B.B₀) * (c.totalCurvature B.family.metric lambda t +
          c.length B.family.metric lambda t) + ε

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem curveShorteningTotalCurvatureBound_of_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (h : curveShorteningTotalCurvatureSlope (I := I) (M := M) B) :
    curveShorteningTotalCurvatureBound (I := I) (M := M) B := by
  intro lambda hlambda hlambda_one c hc t ht
  obtain ⟨hcont, hslope⟩ := h lambda hlambda hlambda_one c hc
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hmain := le_exp_mul_of_right_slope_bound
    (fun u => c.totalCurvature B.family.metric lambda u + c.length B.family.metric lambda u)
    (k := B.C + B.B₀) ht.1 (hcont.mono hsub) ?_
  · exact hmain
  · intro v hv ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hslope v ⟨hv.1, lt_of_lt_of_le hv.2 ht.2⟩ ε hε
    exact ⟨δ, hδpos, fun h hh hb => hδ h hh (le_trans hb ht.2)⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem totalCurvature_add_length_le_exp_at_left_endpoint
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (c : ProductCurve M) :
    c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a ≤
      Real.exp ((B.C + B.B₀) * (a - a)) *
        (c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a) := by
  rw [sub_self, mul_zero, Real.exp_zero, one_mul]

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem totalCurvature_add_length_le_of_curvature_zero
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (c : ProductCurve M)
    (hlength : ∀ t ∈ Icc a b, c.length B.family.metric lambda t ≤
      Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a)
    (hcurv : ∀ t ∈ Icc a b, c.totalCurvature B.family.metric lambda t = 0) :
    ∀ t ∈ Icc a b,
      c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
      Real.exp ((B.C + B.B₀) * (t - a)) *
        (c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a) := by
  have hC : 0 ≤ B.C := by
    rw [RicciBackground.C]
    nlinarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hLnn : ∀ t, 0 ≤ c.length B.family.metric lambda t :=
    fun t => ProductCurve.length_nonneg B.family.metric lambda t c
  intro t ht
  have hexp : Real.exp (B.B₀ * (t - a)) ≤ Real.exp ((B.C + B.B₀) * (t - a)) := by
    rw [Real.exp_le_exp]
    nlinarith [ht.1, hC]
  have h1 : c.length B.family.metric lambda t ≤
      Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a := hlength t ht
  have h2 : Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a ≤
      Real.exp ((B.C + B.B₀) * (t - a)) * c.length B.family.metric lambda a :=
    mul_le_mul_of_nonneg_right hexp (hLnn a)
  have h3 : c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t =
      c.length B.family.metric lambda t := by
    rw [hcurv t ht, zero_add]
  have h4 : c.totalCurvature B.family.metric lambda a + c.length B.family.metric lambda a =
      c.length B.family.metric lambda a := by
    rw [hcurv a ⟨le_rfl, B.lt.le⟩, zero_add]
  rw [h3, h4]
  exact h1.trans h2

def curveShorteningLeastAreaIntegratedBound
    (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (γ : ℝ → ContinuousFreeLoop M),
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) →
    ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      loopFamilyLeastArea B.family.metric γ t ≤
        Real.exp (2 * B.B₀ * (t - s)) *
          (loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem curveShorteningLeastAreaIntegratedBound_of_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (h : curveShorteningLeastAreaSlope (I := I) (M := M) B) :
    curveShorteningLeastAreaIntegratedBound (I := I) (M := M) B :=
  fun γ hγ hcont s hs t ht => rfs_csf_swept_annulus B h γ hγ hcont s t hs ht

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem curveShorteningLeastAreaSlope_of_integratedBound
    (B : RicciBackground (I := I) (M := M) D a b)
    (h : curveShorteningLeastAreaIntegratedBound (I := I) (M := M) B) :
    curveShorteningLeastAreaSlope (I := I) (M := M) B := by
  intro γ hγ hcont t ht ε hε
  have hJnn : ∀ v ∈ Icc a b,
      0 ≤ (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v :=
    fun v _ => CurveMap.sweptDensity_nonneg (curveOfLoopFamily γ) B.family.metric (Icc a b) v
  have hint : ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      loopFamilyLeastArea B.family.metric γ u ≤
        Real.exp (2 * B.B₀ * (u - s)) *
          (loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..u, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) :=
    fun s hs u hu => h γ hγ hcont s hs u hu
  exact le_exp_mul_of_exp_integral_bound
    (fun u => loopFamilyLeastArea B.family.metric γ u)
    (fun v => (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v)
    (k := 2 * B.B₀) (mul_nonneg (by norm_num) B.B₀_nonneg) hJnn
    (continuousOn_sweptDensity B γ hγ) hint ht hε

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem curveShorteningLeastAreaSlope_iff_integratedBound
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningLeastAreaSlope (I := I) (M := M) B ↔
      curveShorteningLeastAreaIntegratedBound (I := I) (M := M) B :=
  ⟨curveShorteningLeastAreaIntegratedBound_of_slope B,
    curveShorteningLeastAreaSlope_of_integratedBound B⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem exists_right_slope_bound_data (k : ℝ) (hk : 0 ≤ k) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Icc (0 : ℝ) 1) ∧
      ∀ v ∈ Ico (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ 1 →
        (F (v + h) - F v) / h ≤ k * F v + ε := by
  refine ⟨fun _ => 1, continuousOn_const,
    fun v hv ε hε => ⟨1, one_pos, fun h hh hb => ?_⟩⟩
  rw [sub_self, zero_div]
  linarith [hk, hε]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem loopFamilyLeastArea_eq_zero_of_subsingleton [Subsingleton M]
    (g : ℝ → SmoothRiemannianMetric I M) (γ : ℝ → ContinuousFreeLoop M) (t : ℝ) :
    loopFamilyLeastArea g γ t = 0 := by
  have hmem : Width.diskArea (g t) (fun _ : Width.Disk => γ t 0) ∈
      Width.competitorAreas (g t) (γ t) := by
    refine ⟨⟨Width.constantLipschitzDisk (g t) (γ t 0), fun θ => ?_⟩, rfl⟩
    exact Subsingleton.elim _ _
  have h0 : Width.diskArea (g t) (fun _ : Width.Disk => γ t 0) = 0 :=
    Width.diskArea_const (g t) (γ t 0)
  rw [h0] at hmem
  refine le_antisymm ?_ ?_
  · exact csInf_le (Width.competitorAreas_bddBelow (g t) (γ t)) hmem
  · rw [loopFamilyLeastArea]
    exact le_csInf ⟨_, hmem⟩ (fun u hu => by
      rcases hu with ⟨v, rfl⟩
      exact Width.diskArea_nonneg (g t) v.1.map)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem sweptDensity_eq_zero_of_subsingleton [Subsingleton M]
    (g : ℝ → SmoothRiemannianMetric I M) (γ : ℝ → ContinuousFreeLoop M)
    (J : Set ℝ) (t : ℝ) :
    (curveOfLoopFamily γ).sweptDensity g J t = 0 := by
  have hvel : ∀ x, (curveOfLoopFamily γ).velocity (I := I) J x t = 0 := by
    intro x
    unfold CurveMap.velocity
    have hlift : (curveOfLoopFamily γ).lift x =
        fun _ : ℝ => (curveOfLoopFamily γ).lift x t := by
      funext u
      exact Subsingleton.elim _ _
    rw [hlift]
    rw [mfderivWithin_const (𝕜 := ℝ) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (E' := E) (H' := H) (I' := I) (M' := M) (s := J) (x := t)
      (c := (curveOfLoopFamily γ).lift x t)]
    exact zero_apply 1
  have hpt : (fun x : ℝ => Real.sqrt (((curveOfLoopFamily γ).normSq g
        ((curveOfLoopFamily γ).velocity (I := I) J) x t)) * (curveOfLoopFamily γ).speed g x t) =
      fun _ : ℝ => 0 := by
    funext x
    have hns : (curveOfLoopFamily γ).normSq g
        ((curveOfLoopFamily γ).velocity (I := I) J) x t = 0 := by
      rw [CurveMap.normSq, hvel x]
      simp
    rw [hns]
    simp
  rw [CurveMap.sweptDensity, hpt, intervalIntegral.integral_zero]

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem curveShorteningLeastAreaSlope_of_subsingleton [Subsingleton M]
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningLeastAreaSlope (I := I) (M := M) B := by
  intro γ hγ hcont t ht ε hε
  refine ⟨1, one_pos, fun h hh hb => ?_⟩
  rw [loopFamilyLeastArea_eq_zero_of_subsingleton B.family.metric γ (t + h),
    loopFamilyLeastArea_eq_zero_of_subsingleton B.family.metric γ t,
    sweptDensity_eq_zero_of_subsingleton B.family.metric γ (Icc a b) t]
  simp only [sub_self, zero_div, mul_zero, zero_add]
  linarith [hε]

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem curveShorteningLeastAreaIntegratedBound_of_subsingleton [Subsingleton M]
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningLeastAreaIntegratedBound (I := I) (M := M) B :=
  curveShorteningLeastAreaIntegratedBound_of_slope B
    (curveShorteningLeastAreaSlope_of_subsingleton B)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
