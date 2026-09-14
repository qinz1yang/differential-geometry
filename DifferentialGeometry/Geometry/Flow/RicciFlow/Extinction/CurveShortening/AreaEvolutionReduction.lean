import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolutionFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolutionCountermodel

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
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

omit hBoundary hT2 hCompact hNonempty [SigmaCompactSpace M] in
theorem areaIntegratingFactor_eq_exp_integral_div (G : SolutionFamily (I := I) (M := M))
    (s v : ℝ) :
    areaIntegratingFactor G s v = Real.exp (∫ w in s..v, scalarMinimum G w / 2) := by
  rw [areaIntegratingFactor, intervalIntegral.integral_div]
  congr 1
  ring

def LoopFamilyWindowComparison (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
    areaIntegratingFactor B.family s u * loopFamilyLeastArea B.family.metric γ u ≤
      loopFamilyLeastArea B.family.metric γ s +
        ∫ v in s..u, areaIntegratingFactor B.family s v *
          (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_window (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hwindow : LoopFamilyWindowComparison (I := I) (M := M) B γ) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) := by
  have hwindow' : ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      Real.exp (∫ w in s..u, scalarMinimum B.family w / 2) *
          loopFamilyLeastArea B.family.metric γ u ≤
        loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..u, Real.exp (∫ w in s..v, scalarMinimum B.family w / 2) *
            (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) := by
    intro s hs u hu
    have h := hwindow s hs u hu
    simpa only [areaIntegratingFactor_eq_exp_integral_div] using h
  exact rfs_csf_immersed_area_of_continuousOn_leastArea_of_window B γ hγ hi
    (continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr) hwindow'

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_iff_window (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    (ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        LoopFamilyWindowComparison (I := I) (M := M) B γ ∧
        LoopFamilyLeastAreaSlopeBound (I := I) (M := M) B γ) ↔
      LoopFamilyWindowComparison (I := I) (M := M) B γ := by
  constructor
  · intro h
    exact h.2.1
  · intro hwindow
    refine ⟨continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr, hwindow, ?_⟩
    refine rfs_csf_slope_le_of_window_comparison B γ
      (continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr)
      (continuousOn_loopFamily_areaError B γ hγ hi) ?_
    intro s hs u hu
    have h := hwindow s hs u hu
    simpa only [areaIntegratingFactor_eq_exp_integral_div] using h

omit [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_of_window (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hwindow : LoopFamilyWindowComparison (I := I) (M := M) B γ) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε :=
  (rfs_csf_immersed_area_of_window B γ hγ hi hctr hwindow).2.2

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_of_immersed_area_conclusion
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (h : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε)) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε :=
  h.2.2

omit [SigmaCompactSpace M] in
theorem two_pi_add_half_scalarMinimum_mul_le_areaError_of_localMin
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hwindow : LoopFamilyWindowComparison (I := I) (M := M) B γ)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (hmin : ∀ s ∈ Ioo a b,
      loopFamilyLeastArea B.family.metric γ t ≤ loopFamilyLeastArea B.family.metric γ s) :
    2 * Real.pi + scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 ≤
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t := by
  have hslope :=
    (rfs_csf_immersed_area_of_window B γ hγ hi hctr hwindow).2.2
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδpos, hδ⟩ := hslope t ⟨ht.1.le, ht.2⟩ ε hε
  set k : ℝ := min (δ / 2) ((b - t) / 2) with hk
  have hkpos : 0 < k := lt_min (by linarith) (by linarith [ht.2])
  have hkδ : k < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hkb : t + k < b := by
    have h1 : k ≤ (b - t) / 2 := min_le_right _ _
    linarith
  have hmem : t + k ∈ Ioo a b := ⟨by linarith [hkpos, ht.1], hkb⟩
  have hle := hδ k ⟨hkpos, hkδ⟩ hkb.le
  have hnonneg : 0 ≤ (loopFamilyLeastArea B.family.metric γ (t + k) -
      loopFamilyLeastArea B.family.metric γ t) / k :=
    div_nonneg (sub_nonneg.mpr (hmin (t + k) hmem)) hkpos.le
  linarith

omit hNonempty [SigmaCompactSpace M] in
theorem loopFamilyLeastArea_integral_decay_of_window_comparison
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hwindow : LoopFamilyWindowComparison (I := I) (M := M) B γ)
    (hforce : ∀ v ∈ Icc a b,
      -2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v ≤ 0) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
        loopFamilyLeastArea B.family.metric γ s := by
  intro s hs t ht
  have hst : s ≤ t := ht.1
  have hFcont : ContinuousOn (fun v : ℝ => -2 * Real.pi +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) (Icc a b) :=
    continuousOn_const.add (continuousOn_loopFamily_areaError B γ hγ hi)
  have hφcont : ContinuousOn (fun v : ℝ => areaIntegratingFactor B.family s v) (Icc s t) := by
    have hpr : ContinuousOn (fun v : ℝ => ∫ w in s..v, scalarMinimum B.family w) (Icc s t) := by
      have hc : ContinuousOn (scalarMinimum B.family) (uIcc s t) := by
        rw [uIcc_of_le hst]
        exact (RicciBackground.continuousOn_scalarMinimum B).mono
          (Icc_subset_Icc hs.1 ht.2)
      have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
        (f := scalarMinimum B.family) hc.intervalIntegrable (left_mem_uIcc (a := s) (b := t))
      simpa only [uIcc_of_le hst] using h
    have h1 : ContinuousOn
        (fun v : ℝ => (1 / 2 : ℝ) * (∫ w in s..v, scalarMinimum B.family w)) (Icc s t) :=
      continuousOn_const.mul hpr
    exact (Real.continuous_exp.comp_continuousOn h1).congr fun v _ => rfl
  have hint : IntervalIntegrable (fun v : ℝ => areaIntegratingFactor B.family s v *
      (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v))
      volume s t := by
    have hmul : ContinuousOn (fun v : ℝ => areaIntegratingFactor B.family s v *
        (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v))
        (uIcc s t) := by
      rw [uIcc_of_le hst]
      exact hφcont.mul (hFcont.mono (Icc_subset_Icc hs.1 ht.2))
    exact hmul.intervalIntegrable
  have hnonpos : (∫ v in s..t, areaIntegratingFactor B.family s v *
      (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ≤ 0 := by
    have h1 : ∀ v ∈ Icc s t, areaIntegratingFactor B.family s v *
        (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) ≤ 0 :=
      fun v hv => mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
        (hforce v ⟨le_trans hs.1 hv.1, le_trans hv.2 ht.2⟩)
    calc (∫ v in s..t, areaIntegratingFactor B.family s v *
          (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v))
        ≤ ∫ v in s..t, (0 : ℝ) := intervalIntegral.integral_mono_on hst hint
          intervalIntegrable_const h1
      _ = 0 := by simp
  have hkey := hwindow s hs t ht
  linarith

omit hNonempty [SigmaCompactSpace M] in
theorem loopFamilyLeastArea_le_of_window_comparison_of_scalarMinimum_nonneg
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hwindow : LoopFamilyWindowComparison (I := I) (M := M) B γ)
    (hforce : ∀ v ∈ Icc a b,
      -2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v ≤ 0)
    (hS : ∀ v ∈ Icc a b, 0 ≤ scalarMinimum B.family v) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      loopFamilyLeastArea B.family.metric γ t ≤ loopFamilyLeastArea B.family.metric γ s := by
  intro s hs t ht
  have h1 := loopFamilyLeastArea_integral_decay_of_window_comparison
    B γ hγ hi hwindow hforce s hs t ht
  have hint : 0 ≤ ∫ w in s..t, scalarMinimum B.family w :=
    intervalIntegral.integral_nonneg ht.1 fun w hw =>
      hS w ⟨le_trans hs.1 hw.1, le_trans hw.2 ht.2⟩
  have hE1 : 1 ≤ areaIntegratingFactor B.family s t := by
    rw [areaIntegratingFactor]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hint)
  have hAs : 0 ≤ loopFamilyLeastArea B.family.metric γ s :=
    loopFamilyLeastArea_nonneg B.family.metric γ hγ hctr s hs
  have hAt : 0 ≤ loopFamilyLeastArea B.family.metric γ t :=
    loopFamilyLeastArea_nonneg B.family.metric γ hγ hctr t ⟨le_trans hs.1 ht.1, ht.2⟩
  simpa using (mul_le_mul_of_nonneg_right hE1 hAt).trans h1

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_boundary_isotopy_of_constantLoopFamily_identity
    (γ : ℝ → ContinuousFreeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t') (t₀ : ℝ) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  refine ⟨1, one_pos, fun _ => Diffeomorph.refl I M ∞, ?_, ?_, ?_⟩
  · simpa only [Diffeomorph.coe_refl, id_eq] using
      (contMDiffOn_fst (I := I) (J := 𝓘(ℝ, ℝ)) (n := ∞)
        (s := univ ×ˢ (Icc a b ∩ Ioo (t₀ - 1) (t₀ + 1))))
  · intro p
    rfl
  · intro t _ z
    exact congrArg (fun f : ContinuousFreeLoop M => f z) (hconst t₀ t)

omit [SigmaCompactSpace M] in
theorem not_loopFamilyWindowComparison_of_static_family
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hstatic : ∀ t, B.family.metric t = B.family.metric a)
    (hfixed : ∀ t, γ t = γ a)
    (hErr : (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) a = 0)
    (hS : 0 ≤ scalarMinimum B.family a) :
    ¬ LoopFamilyWindowComparison (I := I) (M := M) B γ :=
  fun hwindow =>
    not_rfs_csf_embedded_area_of_static_family B γ hγ hctr hstatic hfixed hErr hS
      (rfs_csf_embedded_area_of_window B γ hγ hi hctr hwindow)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
