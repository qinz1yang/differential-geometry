import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalConjugateRadius
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.VolumeLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Bundle Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem intrinsicFrame_rm04_bound_of_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {ρ K : ℝ}
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal ρ →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    {z : E} (hz : ‖z‖ < ρ) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
      (intrinsicFramedExp (I := I) g hEnorm p z) 4
      (metricRm04At (I := I) g (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K := by
  apply hRm
  have hdist := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p
    (normalFrame (I := I) g p z) (s := 0) (t := 1) zero_le_one
  have hbound : riemannianEDist I p (intrinsicFramedExp (I := I) g hEnorm p z) ≤
      ENNReal.ofReal ‖z‖ := by
    change riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (normalFrame (I := I) g p z) 1) ≤
        ENNReal.ofReal ‖z‖
    simpa only [intrinsicGeodesic_zero, normalFrame_sqrt, sub_zero, mul_one] using hdist
  exact hbound.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).2 hz)

variable [CompleteSpace E]

theorem intrInj_ge_cgt_of_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {K ρ R r₀ s : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hRρ : R ≤ ρ)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal ρ →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    (herror : ∀ a : ℝ, 0 ≤ a → a ≤ R →
      gronwallBound 0 (max (Real.sqrt (Module.finrank ℝ E : ℝ) * K * a ^ 2) 1)
        (Real.sqrt (Module.finrank ℝ E : ℝ) * K * a ^ 2) 1 ≤ 1 / 4)
    (hr₀ : 0 < r₀)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4) :
    ENNReal.ofReal (r₀ / 2) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
      (riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
        intrinsicPullVol (I := I) g hEnorm p (r₀ + s)) ≤
      intrinsicInjRadius (I := I) g hEnorm p := by
  have hrad : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (intrinsicFramedExp (I := I) g hEnorm p z) 4
        (metricRm04At (I := I) g (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K := by
    intro z hz
    apply intrinsicFrame_rm04_bound_of_ball (I := I) g hEnorm p hRm
    linarith
  exact intrinsicInjRadius_ge_cheeger_gromov_taylor_on (I := I) g hEnorm p hK hR hRpi hrad
    (intrinsicFrame_localOn_of_local_curvature (I := I) g hEnorm p hK.le hRρ hRm herror)
    hr₀ hfit hquarter

theorem exists_uniform_local_cgt_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 < K) :
    ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ R ≤ Real.pi / Real.sqrt K ∧ ∀ p : M,
      (∀ y : M, riemannianEDist I p y < ENNReal.ofReal ρ →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
          (metricRm04At (I := I) g y)) ≤ K) →
      ENNReal.ofReal (R / 16) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal (R / 8)} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal (R / 8)} +
          intrinsicPullVol (I := I) g hEnorm p (R / 4)) ≤
        intrinsicInjRadius (I := I) g hEnorm p := by
  obtain ⟨r, hr, hrρ, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) hρ hK.le
  let R : ℝ := min r (Real.pi / Real.sqrt K)
  have hR : 0 < R := lt_min hr (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK))
  have hRr : R ≤ r := min_le_left _ _
  have hRρ : R ≤ ρ := hRr.trans hrρ
  have hRpi : R ≤ Real.pi / Real.sqrt K := min_le_right _ _
  refine ⟨R, hR, hRρ, hRpi, ?_⟩
  intro p hRm
  have hCGT := intrInj_ge_cgt_of_ball (I := I) g hEnorm p hK hR hRρ hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRr))
    (r₀ := R / 8) (s := R / 8) (by positivity)
    (by linarith) (by linarith)
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  simpa only [hhalf, hadd] using hCGT

private local instance localCGTMeasurableE : MeasurableSpace E := borel E
private local instance localCGTBorelE : BorelSpace E := ⟨rfl⟩

variable [T2Space (TangentBundle I M)] [ConnectedSpace M]

theorem intrInj_ge_vol_of_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {K ρ R r₀ s q : ℝ} {v : ENNReal}
    (hK : 0 < K) (hR : 0 < R) (hRρ : R ≤ ρ)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal ρ →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    (herror : ∀ a : ℝ, 0 ≤ a → a ≤ R →
      gronwallBound 0 (max (Real.sqrt (Module.finrank ℝ E : ℝ) * K * a ^ 2) 1)
        (Real.sqrt (Module.finrank ℝ E : ℝ) * K * a ^ 2) 1 ≤ 1 / 4)
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hvol : v ≤ riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal s}) :
    ENNReal.ofReal (r₀ / 2) * v /
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
          ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) s) +
        (volume : Measure E).toSphere Set.univ *
          ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (r₀ + s))) ≤
      intrinsicInjRadius (I := I) g hEnorm p := by
  have hball : ∀ y : M, y ∈ Metric.eball p (ENNReal.ofReal (3 * R / 4)) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K := by
    intro y hy
    apply hRm
    have hy' : edist p y < ENNReal.ofReal (3 * R / 4) := Metric.mem_eball'.mp hy
    rw [IsRiemannianManifold.out (I := I) p y] at hy'
    exact hy'.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  exact intrinsicInj_ge_vol (I := I) g hEnorm p hK hR hRpi hball
    (intrinsicFrame_localOn_of_local_curvature (I := I) g hEnorm p hK.le hRρ hRm herror)
    hr₀ hs hfit hquarter hq hRic hvol

theorem exists_uniform_local_volume_inj_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ρ K q : ℝ} (hρ : 0 < ρ) (hK : 0 < K) (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ R ≤ Real.pi / Real.sqrt K ∧
      ∀ (p : M) (v : ENNReal),
      (∀ y : M, riemannianEDist I p y < ENNReal.ofReal ρ →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
          (metricRm04At (I := I) g y)) ≤ K) →
      v ≤ riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I p y < ENNReal.ofReal (R / 8)} →
      ENNReal.ofReal (R / 16) * v /
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 8)) +
          (volume : Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (R / 4))) ≤
        intrinsicInjRadius (I := I) g hEnorm p := by
  obtain ⟨r, hr, hrρ, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) hρ hK.le
  let R : ℝ := min r (Real.pi / Real.sqrt K)
  have hR : 0 < R := lt_min hr (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK))
  have hRr : R ≤ r := min_le_left _ _
  have hRρ : R ≤ ρ := hRr.trans hrρ
  have hRpi : R ≤ Real.pi / Real.sqrt K := min_le_right _ _
  refine ⟨R, hR, hRρ, hRpi, ?_⟩
  intro p v hRm hvol
  have hCGT := intrInj_ge_vol_of_ball (I := I) g hEnorm p hK hR hRρ hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRr))
    (r₀ := R / 8) (s := R / 8) (by positivity) (by positivity)
    (by linarith) (by linarith) hq hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  simpa only [hhalf, hadd] using hCGT

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
