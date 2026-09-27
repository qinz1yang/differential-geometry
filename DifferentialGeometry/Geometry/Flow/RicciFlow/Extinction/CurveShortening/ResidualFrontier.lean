import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolutionReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.GenericCurvesFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometryFrontier

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry

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
private theorem metricRm04StandardAt_eq_zero_of_first_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (Y Z W : TangentSpace I x) :
    metricRm04StandardAt g x 0 Y Z W = 0 := by
  rw [metricRm04StandardAt_apply]
  exact (metricRm04At g x).map_coord_zero 0 (by simp [vec4])

omit hBoundary hT2 hCompact hNonempty [SigmaCompactSpace M] in
theorem hasAmbientGaussEquation_of_subsingleton
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M) (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (hs : Subsingleton (EuclideanSpace ℝ (Fin m))) :
    hasAmbientGaussEquation U F g h := by
  intro x X Y Z W
  have hX : X = (0 : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x) := hs.elim X 0
  have hmfX : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x)
      (0 : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x) = (0 : TangentSpace I (F x)) :=
    ContinuousLinearMap.map_zero _
  have hL : metricRm04StandardAt h x X Y Z W = 0 :=
    (congrArg (fun Z' : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x =>
      metricRm04StandardAt h x Z' Y Z W) hX).trans
      (metricRm04StandardAt_eq_zero_of_first_eq_zero h x Y Z W)
  have hAmb : metricRm04StandardAt g (F x)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) X)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) Y)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) Z)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) W) = 0 := by
    have h0 : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) X =
        (0 : TangentSpace I (F x)) := by
      rw [hX]; exact hmfX
    exact (congrArg (fun Z' : TangentSpace I (F x) => metricRm04StandardAt g (F x) Z'
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) Y)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) Z)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x) W)) h0).trans
      (metricRm04StandardAt_eq_zero_of_first_eq_zero g (F x) _ _ _)
  have hIIXW : ((secondFundamentalFormAmbientAt h g (fun y : U => F y) x) X) W = 0 := by
    rw [hX, ContinuousLinearMap.map_zero]
    exact zero_apply W
  have hIIXZ : ((secondFundamentalFormAmbientAt h g (fun y : U => F y) x) X) Z = 0 := by
    rw [hX, ContinuousLinearMap.map_zero]
    exact zero_apply Z
  rw [hL, hAmb, hIIXW, hIIXZ]
  simp

omit [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_iff_window (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    LoopFamilyLeastAreaSlopeBound (I := I) (M := M) B γ ↔
      LoopFamilyWindowComparison (I := I) (M := M) B γ := by
  constructor
  · intro hbound
    exact (rfs_csf_immersed_area_of_slope B γ hγ hi hctr hbound).2.1
  · intro hwindow
    exact rfs_csf_slope_le_of_window_comparison B γ
      (continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr)
      (continuousOn_loopFamily_areaError B γ hγ hi)
      (fun s hs u hu => by
        have h := hwindow s hs u hu
        simpa only [areaIntegratingFactor_eq_exp_integral_div] using h)

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyWindowComparison_of_leastArea_eq_zero
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hzero : ∀ t ∈ Icc a b, loopFamilyLeastArea B.family.metric γ t = 0)
    (hF : ∀ v ∈ Icc a b, 0 ≤ -2 * Real.pi +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) :
    LoopFamilyWindowComparison (I := I) (M := M) B γ := by
  intro s hs u hu
  have hsu : s ≤ u := hu.1
  have huab : u ∈ Icc a b := ⟨le_trans hs.1 hsu, hu.2⟩
  rw [hzero u huab, hzero s hs, mul_zero, zero_add]
  refine intervalIntegral.integral_nonneg hsu fun v hv => mul_nonneg (le_of_lt (Real.exp_pos _)) ?_
  exact hF v ⟨le_trans hs.1 hv.1, le_trans hv.2 hu.2⟩

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_leastArea_eq_zero
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hzero : ∀ t ∈ Icc a b, loopFamilyLeastArea B.family.metric γ t = 0)
    (hF : ∀ v ∈ Icc a b, 0 ≤ -2 * Real.pi +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) :
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
  have hcont : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) :=
    continuousOn_const.congr fun t ht => hzero t ht
  refine ⟨hcont, loopFamilyWindowComparison_of_leastArea_eq_zero B γ hzero hF, ?_⟩
  intro t ht ε hε
  refine ⟨1, one_pos, fun h hh hb => ?_⟩
  have htmem : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hthmem : t + h ∈ Icc a b := ⟨by linarith [ht.1, hh.1], hb⟩
  rw [hzero (t + h) hthmem, hzero t htmem]
  have ht' := hF t htmem
  have h0 : (0 : ℝ) ≤ -2 * Real.pi +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by linarith
  simpa using h0

omit hBoundary hT2 hCompact hNonempty [SigmaCompactSpace M] in
theorem not_loopFamilyEmbeddedOffFinset_of_constantLoop
    (p : M) (hab : a < b) :
    ¬ LoopFamilyEmbeddedOffFinset (M := M) (fun _ : ℝ => constantLoops p) (Icc a b) := by
  rintro ⟨exceptional, hexc⟩
  have hdiff : (Icc a b \ (↑exceptional : Set ℝ)).Nonempty :=
    ((Set.Icc_infinite hab).sdiff (Finset.finite_toSet exceptional)).nonempty
  obtain ⟨t, ht, htne⟩ := hdiff
  have hinj := (hexc t ht htne).injective
  have hconst : (constantLoops p) (0 : Surgery.Topology.Circle) =
      (constantLoops p) ((1 / 2 : ℝ) : Surgery.Topology.Circle) := by
    simp [constantLoops]
  have hne : (0 : Surgery.Topology.Circle) ≠ ((1 / 2 : ℝ) : Surgery.Topology.Circle) := by
    intro h
    have h' : ((1 / 2 : ℝ) : Surgery.Topology.Circle) = 0 := h.symm
    rw [AddCircle.coe_eq_zero_of_pos_iff (p := (1 : ℝ)) one_pos (by norm_num)] at h'
    obtain ⟨n, hn⟩ := h'
    have hn' : (n : ℝ) = 1 / 2 := by simpa using hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0] at hn'
      norm_num at hn'
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
      linarith
  exact hne (hinj hconst)

omit hBoundary hT2 hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyEmbeddedOffFinset_empty (γ : ℝ → ContinuousFreeLoop M) :
    LoopFamilyEmbeddedOffFinset (M := M) γ (∅ : Set ℝ) :=
  LoopFamilyEmbeddedOffFinset.of_slicewiseEmbedding fun t ht => (Set.notMem_empty t ht).elim

omit [CompleteSpace E] [SigmaCompactSpace M] hT2 hCompact hNonempty hBoundary in
theorem curveShorteningUniformLocalDependence_iff_familyExtension
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {d : ℝ} (had : a < d)
    (hex : ∀ c₀ : SmoothImmersion (I := I) (M := M), ∃ c : CurveMap M,
      c.IsSolutionOn B.family.metric (Icc a d) ∧ ∀ z, c z a = c₀.map z) :
    (∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
        curveShorteningLoopFamilyExtension (I := I) (M := M) B d had e) ↔
      CurveShorteningUniformLocalDependence (I := I) (M := M) B d := by
  constructor
  · intro H
    exact curveShorteningUniformLocalDependence_of_familyExtension B had H hex
  · intro hdep N e
    exact curveShorteningLoopFamilyExtension_of_uniformLocalDependence B had e hdep

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
