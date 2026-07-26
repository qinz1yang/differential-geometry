import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Metric.DistanceScaling
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity

set_option autoImplicit false

/-!
# Pointwise lower bounds for small geodesic balls

This file extracts the inexpensive local consequence of normal-coordinate
density continuity needed by dyadic scale selection.  It does not use a
Bishop--Gromov comparison theorem.
-/

noncomputable section

open scoped Topology Manifold ContDiff Bundle ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure
open Bundle Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every positive-radius explicit-metric ball has positive finite real volume
on a compact manifold. -/
theorem edist_vol_pos
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (a : M) {r : ℝ} (hr : 0 < r) :
    0 < (riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}).toReal := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let U : Set M :=
    {x : M | riemannianEDistOf (I := I) g a x < ENNReal.ofReal r}
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact isOpen_lt
      (by
        unfold riemannianEDistOf
        exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g a)
      continuous_const
  have hUne : U.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [U, mem_setOf_eq, riemannianEDistOf,
      Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  letI : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  exact ENNReal.toReal_pos (hUopen.measure_pos μ hUne).ne' (measure_ne_top μ U)

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

omit [T2Space M] [SigmaCompactSpace M] in
/-- Around the centre of a normal chart, its scalar volume density has a
strictly positive lower bound on one model ball. -/
private theorem normal_dens_lower
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
      ∀ w ∈ Metric.ball (0 : E) δ,
        c ≤ normalChartDensity (I := I) g p w := by
  let Ψ := expMapDiffeo (I := I) g p
  let U : Set E := Ψ.source ∩
    Ψ ⁻¹' (trivializationAt E (TangentSpace I) p).baseSet
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact Ψ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      Ψ.open_source (trivializationAt E (TangentSpace I) p).open_baseSet
  have hzero_src : (0 : E) ∈ Ψ.source := by
    simpa only [Ψ] using zero_mem_expMapDiffeo_source (I := I) g p
  have hzeroU : (0 : E) ∈ U := by
    refine ⟨hzero_src, ?_⟩
    change Ψ (0 : E) ∈ (trivializationAt E (TangentSpace I) p).baseSet
    rw [show Ψ (0 : E) = p by simpa only [Ψ] using expMapDiffeo_zero (I := I) g p]
    exact mem_baseSet_trivializationAt E (TangentSpace I) p
  have hcont : ContinuousOn (normalChartDensity (I := I) g p) U := by
    simpa only [normalChartDensity, Ψ] using
      paramDensity_continuousOn_chart (I := I) g p Ψ hUopen
        Set.inter_subset_left (fun w hw => hw.2)
  have hzero_pos : 0 < normalChartDensity (I := I) g p 0 := by
    simpa only [normalChartDensity, Ψ] using
      paramDensity_pos (I := I) g Ψ hzero_src
  let c : ℝ := normalChartDensity (I := I) g p 0 / 2
  have hc : 0 < c := half_pos hzero_pos
  have hc_lt : c < normalChartDensity (I := I) g p 0 := by
    dsimp only [c]
    linarith
  have hcontAt : ContinuousAt (normalChartDensity (I := I) g p) 0 :=
    hcont.continuousAt (hUopen.mem_nhds hzeroU)
  have hdens_nhds :
      {w : E | c < normalChartDensity (I := I) g p w} ∈ 𝓝 (0 : E) :=
    (tendsto_order.1 hcontAt).1 c hc_lt
  have hsafe : U ∩ {w : E | c < normalChartDensity (I := I) g p w} ∈
      𝓝 (0 : E) :=
    Filter.inter_mem (hUopen.mem_nhds hzeroU) hdens_nhds
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hsafe
  refine ⟨c, δ, hc, hδ, ?_⟩
  intro w hw
  exact (hδsub hw).2.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma sqrt_inner_le_norm
    (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    Real.sqrt (g.inner p w w) ≤ (Real.sqrt ‖g.inner p‖ + 1) * ‖w‖ := by
  have hop : |g.inner p w w| ≤ ‖g.inner p‖ * ‖w‖ * ‖w‖ := by
    simpa only [Real.norm_eq_abs] using (g.inner p).le_opNorm₂ w w
  have hquad : g.inner p w w ≤ ‖g.inner p‖ * ‖w‖ ^ 2 := by
    calc
      g.inner p w w ≤ |g.inner p w w| := le_abs_self _
      _ ≤ ‖g.inner p‖ * ‖w‖ * ‖w‖ := hop
      _ = ‖g.inner p‖ * ‖w‖ ^ 2 := by ring
  have hsqrt := Real.sqrt_le_sqrt hquad
  rw [Real.sqrt_mul (norm_nonneg (g.inner p)), Real.sqrt_sq (norm_nonneg w)] at hsqrt
  exact hsqrt.trans (by
    nlinarith [Real.sqrt_nonneg ‖g.inner p‖, norm_nonneg w])

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma exists_inner_bound
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ w : E,
      Real.sqrt (g.inner p w w) ≤ C * ‖w‖ := by
  refine ⟨Real.sqrt ‖g.inner p‖ + 1, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg ‖g.inner p‖]
  · exact sqrt_inner_le_norm (I := I) g p

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every fixed centre has a positive normalized-volume lower bound on all
sufficiently small realized geodesic balls. -/
theorem exists_ball_vol_low
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M] [CompactSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ∀ s : ℝ, 0 < s → s ≤ ρ →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ε * s ^ Module.finrank ℝ E ≤
        (riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s)).toReal := by
  obtain ⟨c, δ, hc, hδ, hdens⟩ := normal_dens_lower (I := I) g p
  obtain ⟨ρv, hρv, hvol⟩ :=
    exists_metricBall_vol_ge_sc_local (I := I) (M := M) g hEnorm p
  have hC2 : 0 < expMapC2Radius (I := I) g p := expMapC2Radius_pos (I := I) g p
  obtain ⟨C, hC1, hinner⟩ := exists_inner_bound (I := I) g p
  have hC : 0 < C := zero_lt_one.trans_le hC1
  let a : ℝ := 1 / (2 * C)
  have ha : 0 < a := one_div_pos.mpr (mul_pos (by norm_num) hC)
  have ha_le : a ≤ 1 := by
    dsimp only [a]
    rw [div_le_one₀ (mul_pos (by norm_num) hC)]
    linarith
  let unitBallVol : ℝ≥0∞ :=
    (modelHaar (E := E)) (Metric.ball (0 : E) (1 : ℝ))
  let unitVol : ℝ := unitBallVol.toReal
  have hunitVol : 0 < unitVol := by
    dsimp only [unitVol, unitBallVol]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos (μ := modelHaar (E := E))
        (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
      (measure_ball_lt_top (μ := modelHaar (E := E))
        (x := (0 : E)) (r := (1 : ℝ))).ne
  let ε : ℝ := c * a ^ Module.finrank ℝ E * unitVol
  have hε : 0 < ε := mul_pos (mul_pos hc (by positivity)) hunitVol
  let ρ : ℝ := min δ (min ρv (expMapC2Radius (I := I) g p))
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min hδ (lt_min hρv hC2)
  refine ⟨ε, ρ, hε, hρ, ?_⟩
  intro s hs hsρ
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hsδ : s ≤ δ := hsρ.trans (min_le_left _ _)
  have hsρv : s ≤ ρv := hsρ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsC2 : s ≤ expMapC2Radius (I := I) g p :=
    hsρ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlower := hvol (c := c) (R := a * s) (s := s)
    (mul_pos ha hs)
    ((mul_le_of_le_one_left hs.le ha_le).trans hsC2)
    (by
      intro w hw
      have hwnorm : ‖w‖ < a * s := by
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      have hCa : C * a = 1 / 2 := by
        dsimp only [a]
        field_simp
      have : Real.sqrt (g.inner p w w) < s / 2 := by
        calc
          Real.sqrt (g.inner p w w) ≤ C * ‖w‖ := hinner w
          _ < C * (a * s) := mul_lt_mul_of_pos_left hwnorm hC
          _ = s / 2 := by rw [← mul_assoc, hCa]; ring
      exact this.trans_le ((half_le_self hs.le).trans hsρv))
    (by
      intro w hw
      have hwnorm : ‖w‖ < a * s := by
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      have hCa : C * a = 1 / 2 := by
        dsimp only [a]
        field_simp
      calc
        Real.sqrt (g.inner p w w) ≤ C * ‖w‖ := hinner w
        _ < C * (a * s) := mul_lt_mul_of_pos_left hwnorm hC
        _ = s / 2 := by rw [← mul_assoc, hCa]; ring
        _ < s := half_lt_self hs)
    (by
      intro w hw
      apply hdens w
      have hwnorm : ‖w‖ < a * s := by
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      have : ‖w‖ < δ := hwnorm.trans_le
        ((mul_le_of_le_one_left hs.le ha_le).trans hsδ)
      simpa only [Metric.mem_ball, dist_zero_right] using this)
  letI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hlower
  have hpow : 0 ≤ (a * s) ^ Module.finrank ℝ E := by positivity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal hpow] at hreal
  dsimp only [ε, unitVol]
  convert hreal using 1
  simp only [unitBallVol]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every fixed centre has a positive normalized-volume lower bound on small
balls for an explicitly supplied smooth Riemannian metric. -/
theorem exists_edist_vol
    [T3Space M] [ConnectedSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ∀ s : ℝ, 0 < s → s ≤ ρ →
      ε * s ^ Module.finrank ℝ E ≤
        (riemannianVolumeMeasure (I := I) (M := M) g
          {x : M | riemannianEDistOf (I := I) g p x < ENNReal.ofReal s}).toReal := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := inferInstance
  have hEnorm : ∀ x : M, ∀ w : TangentSpace I x,
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)) := by
    intro x w
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  obtain ⟨ε, ρ, hε, hρ, hvol⟩ :=
    exists_ball_vol_low (I := I) (M := M) g hEnorm p
  refine ⟨ε, ρ, hε, hρ, ?_⟩
  intro s hs hsρ
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hset : Metric.ball p s =
      {x : M | riemannianEDistOf (I := I) g p x < ENNReal.ofReal s} := by
    ext x
    simp only [Metric.mem_ball, mem_setOf_eq, riemannianEDistOf]
    rw [dist_comm]
    rw [HopfRinow.riemMetric_dist_eq (I := I) (M := M) p x]
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (Exponential.riemannianEDist_ne_top (I := I) p x)).symm
  rw [← hset]
  exact hvol s hs hsρ

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
