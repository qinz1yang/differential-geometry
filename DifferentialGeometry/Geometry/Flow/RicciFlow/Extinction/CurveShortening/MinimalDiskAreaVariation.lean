import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Comparison

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

def MinimalDiskAreaVariation (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ t ∈ Ico a b, ∃ (u : Width.DiskCompetitor (B.family.metric t) (γ t))
      (φ : ℝ → M → M),
    Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t ∧
    (∀ x : M, φ 0 x = x) ∧
    (∀ h : ℝ, Continuous (φ h)) ∧
    (∀ h : ℝ, 0 < h → t + h ≤ b →
      ∀ θ : Surgery.Topology.Circle, φ h (γ t θ) = γ (t + h) θ) ∧
    (∀ h : ℝ, 0 < h → t + h ≤ b → ∃ L : ℝ≥0,
      ∀ x y : M, riemannianEDistOf (B.family.metric (t + h)) (φ h x) (φ h y) ≤
        (L : ℝ≥0∞) * riemannianEDistOf (B.family.metric t) x y) ∧
    ∃ c : ℝ, c ≤ -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t ∧
      Tendsto (fun h : ℝ =>
        (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 c)

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
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
         isLipschitz := by
           obtain ⟨V, hV⟩ := u.1.isLipschitz
           refine ⟨L * V, fun z w => ?_⟩
           exact (hL (u.1.map z) (u.1.map w)).trans (by
             simpa only [ENNReal.coe_mul, mul_assoc] using
               mul_le_mul' (le_refl (L : ℝ≥0∞)) (hV z w)) },
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

omit hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_continuousOn_leastArea_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hA : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b))
    (hvar : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
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
  rfs_csf_immersed_area_of_continuousOn_leastArea_of_slope B γ hγ hi hA
    (rfs_csf_embedded_area_of_minimalDiskAreaVariation B γ hvar)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
