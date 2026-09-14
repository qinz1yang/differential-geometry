import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolutionReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyDiskAreaVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MinimalDiskAreaVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MinimalDiskAreaVariationReduction

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
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

def CurveShorteningTransportedAreaDiniBound (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ t ∈ Ico a b, ∀ u : Width.DiskCompetitor (B.family.metric t) (γ t),
    Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t →
    ∀ φ : ℝ → M → M,
      (∀ x : M, φ 0 x = x) →
      (∀ h : ℝ, Continuous (φ h)) →
      (∀ h : ℝ, 0 < h → t + h ≤ b →
        ∀ θ : Surgery.Topology.Circle, φ h (γ t θ) = γ (t + h) θ) →
      (∀ h : ℝ, 0 < h → t + h ≤ b → ∃ L : ℝ≥0,
        ∀ x y : M, riemannianEDistOf (B.family.metric (t + h)) (φ h x) (φ h y) ≤
          (L : ℝ≥0∞) * riemannianEDistOf (B.family.metric t) x y) →
      ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
            Width.diskArea (B.family.metric t) u.1.map) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε

def LoopFamilyDiskAreaDiniVariation (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ t ∈ Ico a b, ∃ (u : Width.DiskCompetitor (B.family.metric t) (γ t))
      (φ : ℝ → M → M),
    Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t ∧
    (∀ x : M, φ 0 x = x) ∧
    (∀ h : ℝ, Continuous (φ h)) ∧
    (∀ h : ℝ, 0 < h → t + h ≤ b →
      ∀ θ : Surgery.Topology.Circle, φ h (γ t θ) = γ (t + h) θ) ∧
    (∀ h : ℝ, 0 < h → t + h ≤ b → ∃ L : ℝ≥0,
      ∀ z w : Width.Disk,
        riemannianEDistOf (B.family.metric (t + h)) (φ h (u.1.map z)) (φ h (u.1.map w)) ≤
          (L : ℝ≥0∞) * edist z w) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem curveShorteningTransportedAreaDiniBound_of_transportedAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : CurveShorteningTransportedAreaVariation (I := I) (M := M) B γ) :
    CurveShorteningTransportedAreaDiniBound (I := I) (M := M) B γ := by
  intro t ht u hu φ hid hcont htraj hlip ε hε
  obtain ⟨c, hc, htend⟩ := hvar t ht u hu φ hid hcont htraj hlip
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp htend) (ε / 2) (by linarith)
  refine ⟨δ, hδpos, fun h hh hb => ?_⟩
  have hdist : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]
    exact hh.2
  have h1 := hδ (Set.mem_Ioi.mpr hh.1) hdist
  rw [Real.dist_eq] at h1
  linarith [(abs_lt.mp h1).2]

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyDiskAreaDiniVariation_of_loopFamilyDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : LoopFamilyDiskAreaVariation (I := I) (M := M) B γ) :
    LoopFamilyDiskAreaDiniVariation (I := I) (M := M) B γ := by
  intro t ht
  obtain ⟨u, φ, harea, hid, hcont, htraj, hlip, c, hc, htend⟩ := hvar t ht
  refine ⟨u, φ, harea, hid, hcont, htraj, hlip, ?_⟩
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp htend) (ε / 2) (by linarith)
  refine ⟨δ, hδpos, fun h hh hb => ?_⟩
  have hdist : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]
    exact hh.2
  have h1 := hδ (Set.mem_Ioi.mpr hh.1) hdist
  rw [Real.dist_eq] at h1
  linarith [(abs_lt.mp h1).2]

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem curveShorteningTransportedAreaDiniBound_of_eventually_eq_of_nonneg
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hRHS : ∀ t ∈ Ico a b, 0 ≤ -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t)
    (hz : ∀ t ∈ Ico a b, ∀ (u : Width.DiskCompetitor (B.family.metric t) (γ t))
      (φ : ℝ → M → M), ∀ᶠ h in 𝓝[>] (0 : ℝ),
        Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map = 0) :
    CurveShorteningTransportedAreaDiniBound (I := I) (M := M) B γ := by
  intro t ht u hu φ hid hcont htraj hlip ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hz t ht u φ))
  refine ⟨min δ 1, lt_min hδpos one_pos, fun h hh hb => ?_⟩
  have hδlt : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]
    exact lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hzero := hδ hδlt (Set.mem_Ioi.mpr hh.1)
  rw [hzero, zero_div]
  linarith [hRHS t ht, hε]

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem not_curveShorteningTransportedAreaDiniBound_of_eventually_eq
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hmin : ∃ u : Width.DiskCompetitor (B.family.metric t) (γ t),
      Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t)
    (hiso : ∃ φ : ℝ → M → M,
      (∀ x : M, φ 0 x = x) ∧
      (∀ h : ℝ, Continuous (φ h)) ∧
      (∀ h : ℝ, 0 < h → t + h ≤ b →
        ∀ θ : Surgery.Topology.Circle, φ h (γ t θ) = γ (t + h) θ) ∧
      ∀ h : ℝ, 0 < h → t + h ≤ b → ∃ L : ℝ≥0,
        ∀ x y : M, riemannianEDistOf (B.family.metric (t + h)) (φ h x) (φ h y) ≤
          (L : ℝ≥0∞) * riemannianEDistOf (B.family.metric t) x y)
    (hth : -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t < 0)
    (hz : ∀ (u : Width.DiskCompetitor (B.family.metric t) (γ t)) (φ : ℝ → M → M),
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map = 0) :
    ¬ CurveShorteningTransportedAreaDiniBound (I := I) (M := M) B γ := by
  intro hvar
  obtain ⟨u, hu⟩ := hmin
  obtain ⟨φ, hid, hcont, htraj, hlip⟩ := hiso
  obtain ⟨δ, hδpos, hδ⟩ := hvar t ht u hu φ hid hcont htraj hlip
    (-(-2 * Real.pi - scalarMinimum B.family t *
      loopFamilyLeastArea B.family.metric γ t / 2 +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t) / 2) (by linarith)
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hz u φ))
  have hkpos : 0 < min (δ / 2) (min (δ' / 2) ((b - t) / 2)) :=
    lt_min (by linarith) (lt_min (by linarith) (by linarith [ht.2]))
  refine absurd (hδ (min (δ / 2) (min (δ' / 2) ((b - t) / 2)))
    ⟨hkpos, lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩ ?_) (not_le.mpr ?_)
  · have h1 : min (δ / 2) (min (δ' / 2) ((b - t) / 2)) ≤ (b - t) / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  · have hδlt : dist (min (δ / 2) (min (δ' / 2) ((b - t) / 2))) 0 < δ' := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hkpos]
      exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
    have hzero := hδ' hδlt (Set.mem_Ioi.mpr hkpos)
    rw [hzero, zero_div]
    linarith

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_of_loopFamilyDiskAreaDiniVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : LoopFamilyDiskAreaDiniVariation (I := I) (M := M) B γ) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  intro t ht ε hε
  obtain ⟨u, φ, harea, hid, hcont, htraj, hlip, hdini⟩ := hvar t ht
  obtain ⟨δ, hδpos, hδ⟩ := hdini ε hε
  refine ⟨δ, hδpos, fun h hh hb => ?_⟩
  have hpos : 0 < h := hh.1
  have hle : loopFamilyLeastArea B.family.metric γ (t + h) ≤
      Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) := by
    obtain ⟨L, hL⟩ := hlip h hpos hb
    let f : C(M, M) := ⟨φ h, hcont h⟩
    let hv : Width.DiskCompetitor (B.family.metric (t + h)) (γ (t + h)) :=
      ⟨{ map := f.comp u.1.map
         isLipschitz := ⟨L, fun z w => by
           change riemannianEDistOf (B.family.metric (t + h)) (φ h (u.1.map z))
             (φ h (u.1.map w)) ≤ (L : ℝ≥0∞) * edist z w
           exact hL z w⟩ },
        fun θ => by
          rw [ContinuousMap.comp_apply, u.2 θ]
          exact htraj h hpos hb θ⟩
    have hmem : Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z))
        ∈ Width.competitorAreas (B.family.metric (t + h)) (γ (t + h)) :=
      ⟨hv, by
        simp only [hv, f]
        congr 1⟩
    exact csInf_le (Width.competitorAreas_bddBelow _ _) hmem
  have hsub : loopFamilyLeastArea B.family.metric γ (t + h) -
      loopFamilyLeastArea B.family.metric γ t ≤
      Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
        Width.diskArea (B.family.metric t) u.1.map := by
    have h1 : loopFamilyLeastArea B.family.metric γ t =
        Width.diskArea (B.family.metric t) u.1.map := harea.symm
    linarith [hle, h1]
  have hstep : (loopFamilyLeastArea B.family.metric γ (t + h) -
      loopFamilyLeastArea B.family.metric γ t) / h ≤
      (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
        Width.diskArea (B.family.metric t) u.1.map) / h :=
    div_le_div_of_nonneg_right hsub hpos.le
  exact hstep.trans (hδ h hh hb)

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_loopFamilyDiskAreaDiniVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hvar : LoopFamilyDiskAreaDiniVariation (I := I) (M := M) B γ) :
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
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) :=
  rfs_csf_immersed_area_of_slope B γ hγ hi hctr
    (rfs_csf_embedded_area_of_loopFamilyDiskAreaDiniVariation B γ hvar)

omit [SigmaCompactSpace M] in
theorem loopFamilyWindowComparison_of_loopFamilyDiskAreaDiniVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hvar : LoopFamilyDiskAreaDiniVariation (I := I) (M := M) B γ) :
    LoopFamilyWindowComparison (I := I) (M := M) B γ :=
  (rfs_csf_immersed_area_of_slope B γ hγ hi hctr
    (rfs_csf_embedded_area_of_loopFamilyDiskAreaDiniVariation B γ hvar)).2.1

omit [SigmaCompactSpace M] in
theorem loopFamilyWindowComparison_of_loopFamilyDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hvar : LoopFamilyDiskAreaVariation (I := I) (M := M) B γ) :
    LoopFamilyWindowComparison (I := I) (M := M) B γ :=
  loopFamilyWindowComparison_of_loopFamilyDiskAreaDiniVariation B γ hγ hi hctr
    (loopFamilyDiskAreaDiniVariation_of_loopFamilyDiskAreaVariation B γ hvar)

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyDiskAreaDiniVariation_of_attainment_and_transportedAreaDiniBound
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hmin : CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ)
    (hiso : CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ)
    (hvar : CurveShorteningTransportedAreaDiniBound (I := I) (M := M) B γ) :
    LoopFamilyDiskAreaDiniVariation (I := I) (M := M) B γ := by
  intro t ht
  obtain ⟨u, hu⟩ := hmin t ht
  obtain ⟨φ, hid, hcont, htraj, hlip⟩ := hiso t ht
  refine ⟨u, φ, hu, hid, hcont, htraj, ?_, ?_⟩
  · intro h hpos hb
    obtain ⟨L, hL⟩ := hlip h hpos hb
    obtain ⟨V, hV⟩ := u.1.isLipschitz
    refine ⟨L * V, fun z w => ?_⟩
    calc riemannianEDistOf (B.family.metric (t + h)) (φ h (u.1.map z)) (φ h (u.1.map w))
        ≤ (L : ℝ≥0∞) *
            riemannianEDistOf (B.family.metric t) (u.1.map z) (u.1.map w) := hL _ _
      _ ≤ (L : ℝ≥0∞) * ((V : ℝ≥0∞) * edist z w) := mul_le_mul' le_rfl (hV z w)
      _ = ((L * V : ℝ≥0)) * edist z w := by rw [ENNReal.coe_mul, mul_assoc]
  · exact hvar t ht u hu φ hid hcont htraj hlip

omit [SigmaCompactSpace M] in
theorem loopFamilyWindowComparison_of_attainment_and_transportedAreaDiniBound
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hmin : CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ)
    (hiso : CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ)
    (hvar : CurveShorteningTransportedAreaDiniBound (I := I) (M := M) B γ) :
    LoopFamilyWindowComparison (I := I) (M := M) B γ :=
  loopFamilyWindowComparison_of_loopFamilyDiskAreaDiniVariation B γ hγ hi hctr
    (loopFamilyDiskAreaDiniVariation_of_attainment_and_transportedAreaDiniBound
      B γ hmin hiso hvar)

omit [SigmaCompactSpace M] in
theorem loopFamilyWindowComparison_of_attainment_and_transportedAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hmin : CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ)
    (hiso : CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ)
    (hvar : CurveShorteningTransportedAreaVariation (I := I) (M := M) B γ) :
    LoopFamilyWindowComparison (I := I) (M := M) B γ :=
  loopFamilyWindowComparison_of_loopFamilyDiskAreaVariation B γ hγ hi hctr
    (loopFamilyDiskAreaVariation_of_minimalDiskAreaVariation B γ
      (minimalDiskAreaVariation_of_attainment_and_areaVariation B γ hmin hiso hvar))

omit [SigmaCompactSpace M] in
theorem not_loopFamilyDiskAreaDiniVariation_of_static_family
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hstatic : ∀ t, B.family.metric t = B.family.metric a)
    (hfixed : ∀ t, γ t = γ a)
    (hErr : (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) a = 0)
    (hS : 0 ≤ scalarMinimum B.family a) :
    ¬ LoopFamilyDiskAreaDiniVariation (I := I) (M := M) B γ :=
  fun hvar =>
    not_loopFamilyWindowComparison_of_static_family B γ hγ hi hctr hstatic hfixed hErr hS
      (loopFamilyWindowComparison_of_loopFamilyDiskAreaDiniVariation B γ hγ hi hctr hvar)

omit [SigmaCompactSpace M] in
theorem loopFamilyWindowComparison_of_plateauDiskDensity_of_boundaryIsotopy_of_areaDiniBound
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hslice : ∀ t ∈ Ico a b, ∃ (u : Width.SmoothDisk (I := I) (Q := M))
        (σ : Width.SmoothWeaklyMonotoneCircleMap),
      (∀ θ : Surgery.Topology.Circle, u.map (Width.diskBoundary θ) = γ t (σ.map θ)) ∧
      ∀ v : Width.SmoothDisk (I := I) (Q := M),
        (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ t θ) →
          Width.diskArea (B.family.metric t) u.map ≤
            Width.diskArea (B.family.metric t) v.map)
    (hdensity : ∀ t ∈ Ico a b,
      Width.PlateauDiskDensity (I := I) (Q := M) (B.family.metric t) (γ t))
    (hiso : CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ)
    (hvar : CurveShorteningTransportedAreaDiniBound (I := I) (M := M) B γ) :
    LoopFamilyWindowComparison (I := I) (M := M) B γ :=
  loopFamilyWindowComparison_of_attainment_and_transportedAreaDiniBound B γ hγ hi hctr
    (curveShorteningLeastAreaAttainment_of_plateauDiskDensity B γ hγ hctr hslice hdensity)
    hiso hvar

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
