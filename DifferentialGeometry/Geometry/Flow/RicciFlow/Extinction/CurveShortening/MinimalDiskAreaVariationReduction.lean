import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolutionFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LeastAreaAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity

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

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def CurveShorteningLeastAreaAttainment (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ t ∈ Ico a b, ∃ u : Width.DiskCompetitor (B.family.metric t) (γ t),
    Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def CurveShorteningLipschitzBoundaryIsotopy (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ t ∈ Ico a b, ∃ φ : ℝ → M → M,
    (∀ x : M, φ 0 x = x) ∧
    (∀ h : ℝ, Continuous (φ h)) ∧
    (∀ h : ℝ, 0 < h → t + h ≤ b →
      ∀ θ : Surgery.Topology.Circle, φ h (γ t θ) = γ (t + h) θ) ∧
    ∀ h : ℝ, 0 < h → t + h ≤ b → ∃ L : ℝ≥0,
      ∀ x y : M, riemannianEDistOf (B.family.metric (t + h)) (φ h x) (φ h y) ≤
        (L : ℝ≥0∞) * riemannianEDistOf (B.family.metric t) x y

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def CurveShorteningTransportedAreaVariation (B : RicciBackground (I := I) (M := M) D a b)
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
      ∃ c : ℝ, c ≤ -2 * Real.pi - scalarMinimum B.family t *
            loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t ∧
        Tendsto (fun h : ℝ =>
          (Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
            Width.diskArea (B.family.metric t) u.1.map) / h)
          (𝓝[>] (0 : ℝ)) (𝓝 c)

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem curveShorteningLeastAreaAttainment_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
    CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ := by
  intro t ht
  obtain ⟨u, φ, harea, -⟩ := hvar t ht
  exact ⟨u, harea⟩

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem curveShorteningLipschitzBoundaryIsotopy_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
    CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ := by
  intro t ht
  obtain ⟨u, φ, -, hid, hcont, htraj, hlip, -⟩ := hvar t ht
  exact ⟨φ, hid, hcont, htraj, hlip⟩

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem minimalDiskAreaVariation_of_attainment_and_areaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hmin : CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ)
    (hiso : CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ)
    (hvar : CurveShorteningTransportedAreaVariation (I := I) (M := M) B γ) :
    MinimalDiskAreaVariation (I := I) (M := M) B γ := by
  intro t ht
  obtain ⟨u, hu⟩ := hmin t ht
  obtain ⟨φ, hid, hcont, htraj, hlip⟩ := hiso t ht
  obtain ⟨c, hc, htend⟩ := hvar t ht u hu φ hid hcont htraj hlip
  exact ⟨u, φ, hu, hid, hcont, htraj, hlip, c, hc, htend⟩

omit hNonempty [SigmaCompactSpace M] in
theorem curveShorteningLeastAreaAttainment_of_plateauDiskDensity
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hslice : ∀ t ∈ Ico a b, ∃ (u : Width.SmoothDisk (I := I) (Q := M))
        (σ : Width.SmoothWeaklyMonotoneCircleMap),
      (∀ θ : Surgery.Topology.Circle, u.map (Width.diskBoundary θ) = γ t (σ.map θ)) ∧
      ∀ v : Width.SmoothDisk (I := I) (Q := M),
        (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ t θ) →
          Width.diskArea (B.family.metric t) u.map ≤
            Width.diskArea (B.family.metric t) v.map)
    (hdensity : ∀ t ∈ Ico a b,
      Width.PlateauDiskDensity (I := I) (Q := M) (B.family.metric t) (γ t)) :
    CurveShorteningLeastAreaAttainment (I := I) (M := M) B γ :=
  exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea B γ hγ hctr hslice hdensity

omit hNonempty [SigmaCompactSpace M] in
theorem curveShorteningLeastAreaAttainment_constLoops
    (B : RicciBackground (I := I) (M := M) D a b) (q : M) :
    CurveShorteningLeastAreaAttainment (I := I) (M := M) B (fun _ => constantLoops q) := by
  intro t ht
  refine ⟨Width.constantDiskCompetitor (B.family.metric t) q, ?_⟩
  have hD : Width.diskArea (B.family.metric t)
      (Width.constantDiskCompetitor (B.family.metric t) q).1.map = 0 :=
    Width.diskArea_const (B.family.metric t) q
  have hA : loopFamilyLeastArea B.family.metric (fun _ => constantLoops q) t = 0 := by
    change sInf (Width.competitorAreas (B.family.metric t) (constantLoops q)) = 0
    exact Width.leastArea_const (B.family.metric t) q
  rw [hD, hA]

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem curveShorteningLipschitzBoundaryIsotopy_of_subsingleton
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    [Subsingleton M] :
    CurveShorteningLipschitzBoundaryIsotopy (I := I) (M := M) B γ := by
  intro t ht
  refine ⟨fun _ x => x, fun x => rfl, fun h => continuous_id, ?_, ?_⟩
  · intro h hpos hb θ
    exact Subsingleton.elim _ _
  · intro h hpos hb
    refine ⟨1, fun x y => ?_⟩
    rw [Subsingleton.elim y x, riemannianEDistOf_self, riemannianEDistOf_self]
    simp

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem not_curveShorteningTransportedAreaVariation_of_eventually_eq
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
    ¬ CurveShorteningTransportedAreaVariation (I := I) (M := M) B γ := by
  intro hvar
  obtain ⟨u, hu⟩ := hmin
  obtain ⟨φ, hid, hcont, htraj, hlip⟩ := hiso
  obtain ⟨c, hc, htend⟩ := hvar t ht u hu φ hid hcont htraj hlip
  have hc0 : c = 0 := tendsto_div_eq_zero_of_eventually_eq_zero (hz u φ) htend
  linarith

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem curveShorteningTransportedAreaVariation_of_eventually_eq_of_nonneg
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hRHS : ∀ t ∈ Ico a b, 0 ≤ -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t)
    (hz : ∀ t ∈ Ico a b, ∀ (u : Width.DiskCompetitor (B.family.metric t) (γ t))
      (φ : ℝ → M → M),
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map = 0) :
    CurveShorteningTransportedAreaVariation (I := I) (M := M) B γ := by
  intro t ht u hu φ hid hcont htraj hlip
  refine ⟨0, hRHS t ht, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hz t ht u φ] with h hh
  rw [hh, zero_div]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
