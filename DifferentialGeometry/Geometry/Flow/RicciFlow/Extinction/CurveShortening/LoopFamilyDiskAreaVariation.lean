import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolutionCountermodel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity

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

include hBoundary hT2 hCompact hNonempty

def LoopFamilyDiskAreaVariation (B : RicciBackground (I := I) (M := M) D a b)
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
    ∃ c : ℝ, c ≤ -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t ∧
      Tendsto (fun h : ℝ =>
        (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 c)

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_of_loopFamilyDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : LoopFamilyDiskAreaVariation (I := I) (M := M) B γ) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  intro t ht ε hε
  obtain ⟨u, φ, harea, hid, hcont, htraj, hlip, c, hc, htend⟩ := hvar t ht
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp htend) (ε / 2) hε2
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
  have hdist : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact hh.2
  have hlt : (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
      Width.diskArea (B.family.metric t) u.1.map) / h < c + ε / 2 := by
    have h1 := hδ (Set.mem_Ioi.mpr hpos) hdist
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.mp h1).2]
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
  have htail : c + ε / 2 ≤ -2 * Real.pi - scalarMinimum B.family t *
      loopFamilyLeastArea B.family.metric γ t / 2 +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by linarith
  exact hstep.trans (hlt.le.trans htail)

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyDiskAreaVariation_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (h : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
    LoopFamilyDiskAreaVariation (I := I) (M := M) B γ := by
  intro t ht
  obtain ⟨u, φ, harea, hid, hcont, htraj, hlip, c, hc, htend⟩ := h t ht
  refine ⟨u, φ, harea, hid, hcont, htraj, ?_, c, hc, htend⟩
  intro hh hpos hb
  obtain ⟨L, hL⟩ := hlip hh hpos hb
  obtain ⟨V, hV⟩ := u.1.isLipschitz
  refine ⟨L * V, fun z w => ?_⟩
  calc riemannianEDistOf (B.family.metric (t + hh)) (φ hh (u.1.map z)) (φ hh (u.1.map w))
      ≤ (L : ℝ≥0∞) * riemannianEDistOf (B.family.metric t) (u.1.map z) (u.1.map w) :=
        hL (u.1.map z) (u.1.map w)
    _ ≤ (L : ℝ≥0∞) * ((V : ℝ≥0∞) * edist z w) := mul_le_mul' le_rfl (hV z w)
    _ = ((L * V : ℝ≥0) : ℝ≥0∞) * edist z w := by
        rw [ENNReal.coe_mul, mul_assoc]

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_loopFamilyDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hvar : LoopFamilyDiskAreaVariation (I := I) (M := M) B γ) :
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
    (rfs_csf_embedded_area_of_loopFamilyDiskAreaVariation B γ hvar)

omit hNonempty [SigmaCompactSpace M] in
theorem not_loopFamilyDiskAreaVariation_of_static_family
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hstatic : ∀ t, B.family.metric t = B.family.metric a)
    (hfixed : ∀ t, γ t = γ a)
    (hErr : (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) a = 0)
    (hS : 0 ≤ scalarMinimum B.family a) :
    ¬ LoopFamilyDiskAreaVariation (I := I) (M := M) B γ :=
  fun hvar => not_rfs_csf_embedded_area_of_static_family B γ hγ hctr hstatic hfixed hErr hS
    (rfs_csf_embedded_area_of_loopFamilyDiskAreaVariation B γ hvar)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.Geometry

theorem exists_lipschitzOn_with_not_lipschitzWith_two :
    ∃ f : ℝ → ℝ, LipschitzOnWith 2 f (Icc (0 : ℝ) 1) ∧ ¬ LipschitzWith 2 f := by
  refine ⟨fun x => x ^ 2, ?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    have hfact : |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by
      rw [← abs_mul]
      congr 1
      ring
    rw [hfact]
    have hsum : |x + y| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
    calc |x - y| * |x + y| ≤ |x - y| * 2 :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = 2 * |x - y| := by ring
  · rw [lipschitzWith_iff_dist_le_mul]
    intro h
    have h3 := h 3 0
    rw [Real.dist_eq, Real.dist_eq] at h3
    norm_num at h3

end DifferentialGeometry.Geometry
