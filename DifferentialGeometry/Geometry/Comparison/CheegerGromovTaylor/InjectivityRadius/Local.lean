import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.LocalVolume
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
import DifferentialGeometry.Geometry.Comparison.Volume.LocalDoubling
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

open DifferentialGeometry.Geometry.Curvature MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

section LocalMetricInjectivity

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

open scoped Bundle

private theorem sqrt_normSq_le_of_curvature_bound
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ} (hr : 0 < r)
    (hRm : ∀ y ∈ riemannianBallOf (I := I) g x r,
      r ^ 4 * Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y) ≤ 1) :
    ∀ y ∈ riemannianBallOf (I := I) g x r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y)) ≤
        1 / r ^ 2 := by
  intro y hy
  have h := hRm y hy
  have hr4 : 0 < r ^ 4 := by positivity
  have hN : Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y) ≤ 1 / r ^ 4 := by
    refine (le_div_iff₀ hr4).mpr ?_
    simpa only [mul_comm] using h
  have h4 : Real.sqrt (1 / r ^ 4) = 1 / r ^ 2 := by
    have hsq : (1 : ℝ) / r ^ 4 = (1 / r ^ 2) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (by positivity)]
  linarith [Real.sqrt_le_sqrt hN, h4]

private theorem ricciTensor_lower_of_curvature_bound [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) {r q₀ : ℝ} (hr : 0 < r)
    (hq₀ : q₀ = (Module.finrank ℝ E : ℝ) /
      Real.sqrt (((Module.finrank ℝ E - 1 : ℕ)) : ℝ))
    (hK : ∀ y ∈ riemannianBallOf (I := I) g x r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y)) ≤ 1 / r ^ 2) :
    ∀ y ∈ riemannianBallOf (I := I) g x r, ∀ w : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2) * g.inner y w w ≤
        ricciTensor (I := I) g y w w := by
  have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  intro y hy w
  rcases eq_or_ne (Module.finrank ℝ E) 1 with hn1 | hn1
  · have hz : metricRm04At (I := I) (M := M) g y = 0 :=
      metricRm04At_eq_zero_of_finrank_le_one (I := I) g (by omega) y
    have hb : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) (M := M) g y)) ≤ 0 := by
      have hzero : (Tensor0SBundle.tensor0SMetricData (I := I) g y 4).inner
          (0 : Tensor0SBundle.Tensor0SSpace 4 I y) 0 = 0 :=
        (Tensor0SBundle.MetricFiberData.inner_self_eq_zero_iff _ _).mpr rfl
      rw [hz, Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S, hzero, Real.sqrt_zero]
    have h := DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := I) g hb w
    have hc : -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2) = 0 := by
      rw [hq₀, hn1]
      norm_num
    rw [hc]
    simpa using h
  · have h2 : 2 ≤ Module.finrank ℝ E := by omega
    have h := DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := I) g (hK y hy) w
    have hcoef : -((Module.finrank ℝ E : ℝ) ^ 2 * (1 / r ^ 2)) =
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2) := by
      have hsq : Real.sqrt (((Module.finrank ℝ E - 1 : ℕ)) : ℝ) ^ 2 =
          (((Module.finrank ℝ E - 1 : ℕ)) : ℝ) := Real.sq_sqrt (by positivity)
      have hne : (((Module.finrank ℝ E - 1 : ℕ)) : ℝ) ≠ 0 := by
        have : Module.finrank ℝ E - 1 ≠ 0 := by omega
        exact_mod_cast this
      rw [hq₀, div_pow, div_pow, hsq]
      field_simp [hr.ne', hne]
    rw [hcoef] at h
    exact h

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem ball_volume_lower_bound_of_ricci_lower_bound [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {kappa q₀ : ℝ} {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (x : M)
    (hkappa : 0 < kappa) {r : ℝ} (hr : 0 < r)
    (hq₀ : q₀ = (Module.finrank ℝ E : ℝ) /
      Real.sqrt (((Module.finrank ℝ E - 1 : ℕ)) : ℝ))
    (hric : ∀ y ∈ riemannianBallOf (I := I) g x r, ∀ w : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2) * g.inner y w w ≤
        ricciTensor (I := I) g y w w)
    (hvol : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r))
    [hsc : SigmaCompactSpace (connectedComponentOpen (I := I) x)]
    {c₁ : ℝ} (hc₁pos : 0 < c₁) (hc₁one : c₁ ≤ 1) :
    ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E *
        DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
          q₀ (Module.finrank ℝ E - 1) (c₁ / 8) /
        DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
          q₀ (Module.finrank ℝ E - 1) 1) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        (riemannianBallOf (I := I) g x (c₁ * r / 8)) := by
  classical
  have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hq₀nn : 0 ≤ q₀ := by
    rw [hq₀]
    exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  set hvA : ℝ := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
    q₀ (Module.finrank ℝ E - 1) (c₁ / 8) with hvAdef
  set hvB : ℝ := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
    q₀ (Module.finrank ℝ E - 1) (c₁ / 4) with hvBdef
  set hv1 : ℝ := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
    q₀ (Module.finrank ℝ E - 1) 1 with hv1def
  have hv1pos : 0 < hv1 := by
    rw [hv1def]
    exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos hq₀nn (by norm_num)
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : Bundle.RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let metricM : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := metricM.toPseudoEMetricSpace
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let : @CompleteSpace M metricM.toUniformSpace := hg.complete
  have hEnormM : ∀ y : M, ∀ v : TangentSpace I y,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)) :=
    fun y v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  let U : TopologicalSpace.Opens M := connectedComponentOpen (I := I) x
  let gU : SmoothRiemannianMetric I U := g.restrictOpen U
  let : SigmaCompactSpace U := hsc
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I) x
  let : IsManifold I 1 U :=
    IsManifold.of_le (I := I) (M := U) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace U := Manifold.metrizableSpace I U
  let : T3Space U := inferInstance
  let : Bundle.RiemannianBundle (fun y : U => TangentSpace I y) := ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : U => TangentSpace I y) :=
    ⟨⟨gU.inner, gU.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let metricU : EMetricSpace U := EMetricSpace.ofRiemannianMetric I U
  let : PseudoEMetricSpace U := metricU.toPseudoEMetricSpace
  let : IsRiemannianManifold I U := ⟨fun _ _ => rfl⟩
  have hgU : RiemannianMetricComplete gU :=
    DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen (I := I) g x hg
  let : @CompleteSpace U metricU.toUniformSpace := hgU.complete
  have hEnormU : ∀ y : U, ∀ v : TangentSpace I y,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gU.inner y v v)) :=
    fun y v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) gU y v
  have hqnn : 0 ≤ q₀ / r := by
    rw [hq₀]
    exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hr.le
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let xU : U := connectedComponentPoint (I := I) x
  have hEdist : ∀ y : U, Manifold.riemannianEDist I xU y =
      Manifold.riemannianEDist I x (y : M) := by
    intro y
    have h := DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen
      (I := I) g x y xU
    rw [Manifold.riemannianEDist_comm (I := I) (x := xU) (y := y)]
    exact h.trans (Manifold.riemannianEDist_comm (I := I) (x := (y : M)) (y := (xU : M)))
  have hEdistOf : ∀ y : U,
      riemannianEDistOf (I := I) g x (y : M) = Manifold.riemannianEDist I xU y :=
    fun y => (hEdist y).symm
  have hRicU : ∀ y : U, Manifold.riemannianEDist I xU y < ENNReal.ofReal r →
      ∀ w : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2) * gU.inner y w w ≤
        ricciTensor (I := I) gU y w w := by
    intro y hy w
    have hyM : riemannianEDistOf (I := I) g x (y : M) < ENNReal.ofReal r := by
      rw [hEdistOf y]; exact hy
    have hM := hric (y : M) (by simpa only [riemannianBallOf, Set.mem_ofPred_eq] using hyM) w
    rw [DifferentialGeometry.SmoothRiemannianMetric.restrictOpen_inner (I := I) g U y w w,
      DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen (I := I) g U y w w,
      mfderiv_subtype_val_apply]
    exact hM
  have hmeas : ∀ ρ : ℝ, MeasurableSet (riemannianBallOf (I := I) g x ρ) := by
    intro ρ
    have hd : Continuous (fun y : M => riemannianEDistOf (I := I) g x y) := by
      simpa only [riemannianEDistOf] using
        DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist (I := I) g x
    exact (isOpen_lt hd continuous_const).measurableSet
  have hsubset : ∀ ρ : ℝ, riemannianBallOf (I := I) g x ρ ⊆ (U : Set M) := fun ρ =>
    DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen (I := I) g x ρ
  have hpre : ∀ ρ : ℝ, (Subtype.val ⁻¹' riemannianBallOf (I := I) g x ρ : Set U) =
      {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal ρ} := by
    intro ρ
    ext y
    simp only [Set.mem_preimage, riemannianBallOf, Set.mem_ofPred_eq]
    rw [hEdistOf y]
  have hvolTransport : ∀ ρ : ℝ, riemannianVolumeMeasure (I := I) (M := U) gU
        {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal ρ}
      = riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf (I := I) g x ρ) := by
    intro ρ
    rw [← hpre ρ]
    exact DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
      (I := I) g U (hmeas ρ) (hsubset ρ)
  have hs : 0 < c₁ * r / 8 := by positivity
  have hsR : c₁ * r / 8 ≤ r := by nlinarith [hc₁one, hr]
  have hs2 : c₁ * r / 8 + c₁ * r / 8 = c₁ * r / 4 := by ring
  have h4r : c₁ * r / 4 ≤ r := by nlinarith [hc₁one, hr]
  have hRicU' : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ricciBoundedBelowOn
      (I := I) gU {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal r}
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2)) :=
    fun y hy w => hRicU y hy w
  have hseg := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentBall_vol_rel_endpoint_of_ricciBoundedBelowOn
    (I := I) (M := U) gU hEnormU xU (q := q₀ / r) (s := c₁ * r / 8) (R₀ := r) hqnn hs hsR hRicU'
  have hscaleS : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8) = r ^ Module.finrank ℝ E * hvA := by
    have h := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_scale
      q₀ r (c₁ / 8) (Module.finrank ℝ E - 1) hr
    have h2 : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := by omega
    have harg : c₁ * r / 8 = r * (c₁ / 8) := by ring
    rw [harg, h, h2]
  have hscaleR : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      (q₀ / r) (Module.finrank ℝ E - 1) r = r ^ Module.finrank ℝ E * hv1 := by
    have h := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_scale
      q₀ r 1 (Module.finrank ℝ E - 1) hr
    have h2 : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := by omega
    simpa only [mul_one, h2, hv1def] using h
  have hscaleB : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8 + c₁ * r / 8) = r ^ Module.finrank ℝ E * hvB := by
    have h := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_scale
      q₀ r (c₁ / 4) (Module.finrank ℝ E - 1) hr
    have h2 : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := by omega
    have harg : c₁ * r / 8 + c₁ * r / 8 = r * (c₁ / 4) := by ring
    rw [harg, h, h2]
  have hcomb : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) *
        ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
          (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8)) ≤
      ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
          (q₀ / r) (Module.finrank ℝ E - 1) r) *
        riemannianVolumeMeasure (I := I) (M := U) gU
          {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal (c₁ * r / 8)} := by
    have hVlow : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := U) gU
          {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal r} := by
      rw [hvolTransport r]
      exact hvol
    calc ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) *
          ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
            (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8))
        ≤ riemannianVolumeMeasure (I := I) (M := U) gU
            {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal r} *
          ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
            (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8)) := by gcongr
      _ ≤ ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
            (q₀ / r) (Module.finrank ℝ E - 1) r) *
          riemannianVolumeMeasure (I := I) (M := U) gU
            {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal (c₁ * r / 8)} := hseg
  have hcomb' : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E * hvA) ≤
      ENNReal.ofReal (r ^ Module.finrank ℝ E * hv1) *
        riemannianVolumeMeasure (I := I) (M := U) gU
          {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal (c₁ * r / 8)} := by
    rw [hscaleS, hscaleR] at hcomb
    exact hcomb
  have hvolU : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1) ≤
      riemannianVolumeMeasure (I := I) (M := U) gU
        {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal (c₁ * r / 8)} := by
    have hden : (0 : ℝ) < r ^ Module.finrank ℝ E * hv1 :=
      mul_pos (pow_pos hr _) hv1pos
    have hne : ENNReal.ofReal (r ^ Module.finrank ℝ E * hv1) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hden
    have hmul : ENNReal.ofReal (r ^ Module.finrank ℝ E * hv1) *
          ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1) =
        ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) *
          ENNReal.ofReal (r ^ Module.finrank ℝ E * hvA) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ Module.finrank ℝ E * hv1),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ kappa * r ^ Module.finrank ℝ E)]
      congr 1
      have hrn : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
      field_simp [hrn, hv1pos.ne']
    have hmain : ENNReal.ofReal (r ^ Module.finrank ℝ E * hv1) *
          ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1) ≤
        ENNReal.ofReal (r ^ Module.finrank ℝ E * hv1) *
          riemannianVolumeMeasure (I := I) (M := U) gU
            {y : U | Manifold.riemannianEDist I xU y < ENNReal.ofReal (c₁ * r / 8)} := by
      rw [hmul]
      exact hcomb'
    exact (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).mp hmain
  rw [hvAdef, hv1def] at hvolU
  rw [← hvolTransport (c₁ * r / 8)]
  exact hvolU
omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem injOn_expMap_of_cgt_volume_bound [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {kappa q₀ c₁ sig hvA hvB hv1 const₀ iot r : ℝ}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (x : M)
    [hps : PseudoEMetricSpace M]
    [hrb : Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [hrm : IsRiemannianManifold I M] [hcp : CompleteSpace M]
    [hcc : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    [hEmeas : MeasurableSpace E] [hEborel : BorelSpace E]
    (hEnormM : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := I) (M := M) g)
    (hkappa : 0 < kappa) (hr : 0 < r) (hc₁pos : 0 < c₁)
    (hq₀nn : 0 ≤ q₀)
    (hvAdef : hvA = DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      q₀ (Module.finrank ℝ E - 1) (c₁ / 8))
    (hvBdef : hvB = DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      q₀ (Module.finrank ℝ E - 1) (c₁ / 4))
    (hv1def : hv1 = DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      q₀ (Module.finrank ℝ E - 1) 1)
    (hsigdef : sig = (Module.finrank ℝ E : ℝ) *
      DifferentialGeometry.Geometry.Riemannian.VolumeComparison.euclideanUnitBallVolume
        (Module.finrank ℝ E))
    (hconstdef : const₀ = sig * (hvA + hvB))
    (hiotdef : iot = c₁ * kappa * hvA / (32 * hv1 * const₀))
    (hCGT : ENNReal.ofReal (c₁ * r / 8 / 2) *
        ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1) /
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
            ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
              (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8)) +
          (volume : Measure E).toSphere Set.univ *
            ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
              (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8 + c₁ * r / 8))) ≤
      DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicInjRadius (I := I) g hEnormM x) :
    Set.InjOn (fun v : TangentSpace I x =>
      DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I) g x v)
      {v | Real.sqrt (g.inner x v v) < iot * r} := by
  have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hvApos : 0 < hvA := by
    rw [hvAdef]
    exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos
      hq₀nn (by positivity)
  have hvBpos : 0 < hvB := by
    rw [hvBdef]
    exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos
      hq₀nn (by positivity)
  have hv1pos : 0 < hv1 := by
    rw [hv1def]
    exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos
      hq₀nn (by norm_num)
  have hsigpos : 0 < sig := by
    rw [hsigdef]
    exact mul_pos (by exact_mod_cast hn)
      (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.euclideanUnitBallVolume_pos _)
  have hconstpos : 0 < const₀ := by
    rw [hconstdef]
    exact mul_pos hsigpos (add_pos hvApos hvBpos)
  have hsphereE : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ =
      ENNReal.ofReal sig := by
    rw [hsigdef]
    exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.euclideanSphereArea_eq
      (Module.finrank ℝ E) (by omega)
  have hsphereM : (volume : Measure E).toSphere Set.univ = ENNReal.ofReal sig := by
    rw [DifferentialGeometry.Geometry.Riemannian.VolumeComparison.volSphere_finrank (E := E), hsphereE]
  have hscaleS : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8) = r ^ Module.finrank ℝ E * hvA := by
    have h := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_scale
      q₀ r (c₁ / 8) (Module.finrank ℝ E - 1) hr
    have h2 : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := by omega
    have harg : c₁ * r / 8 = r * (c₁ / 8) := by ring
    rw [harg, h, h2, hvAdef]
  have hscaleB : DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
      (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8 + c₁ * r / 8) =
        r ^ Module.finrank ℝ E * hvB := by
    have h := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_scale
      q₀ r (c₁ / 4) (Module.finrank ℝ E - 1) hr
    have h2 : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := by omega
    have harg : c₁ * r / 8 + c₁ * r / 8 = r * (c₁ / 4) := by ring
    rw [harg, h, h2, hvBdef]
  have hD : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
        ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
          (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8)) +
      (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
          (q₀ / r) (Module.finrank ℝ E - 1) (c₁ * r / 8 + c₁ * r / 8)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ E * const₀) := by
    rw [hsphereE, hsphereM, hscaleS, hscaleB]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ sig),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ sig),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [hconstdef]
    ring
  have hCGT' : ENNReal.ofReal (c₁ * r / 16) *
        ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1) /
        ENNReal.ofReal (r ^ Module.finrank ℝ E * const₀) ≤
      DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicInjRadius (I := I) g hEnormM x := by
    have h1 : (c₁ * r / 8) / 2 = c₁ * r / 16 := by ring
    rw [hD, h1] at hCGT
    exact hCGT
  have hratio : ENNReal.ofReal (c₁ * r / 16) *
        ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1) /
        ENNReal.ofReal (r ^ Module.finrank ℝ E * const₀) =
      ENNReal.ofReal (c₁ * r * kappa * hvA / (16 * hv1 * const₀)) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c₁ * r / 16),
      ← ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < r ^ Module.finrank ℝ E * const₀)]
    congr 1
    have hrn : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
    field_simp [hrn, hv1pos.ne', hconstpos.ne']
  have hlt : ENNReal.ofReal (iot * r) <
      ENNReal.ofReal (c₁ * r * kappa * hvA / (16 * hv1 * const₀)) := by
    have hreal : iot * r < c₁ * r * kappa * hvA / (16 * hv1 * const₀) := by
      rw [hiotdef, lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * hv1 * const₀)]
      have hnum : 0 < c₁ * r * kappa * hvA := by positivity
      have hden : 0 < 32 * hv1 * const₀ := by positivity
      field_simp
      nlinarith [hnum, hden, hv1pos, hconstpos]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by rw [hiotdef]; positivity)).2 hreal
  have hkey : ENNReal.ofReal (iot * r) <
      DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicInjRadius (I := I) g hEnormM x :=
    hlt.trans_le (by rw [← hratio]; exact hCGT')
  exact DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.injOn_expMap_ball_of_intrinsicInjRadius
    (I := I) g hEnormM x hkey
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem local_metric_injectivity [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
        [T2Space (TangentBundle I M)] (g : SmoothRiemannianMetric I M),
        RiemannianMetricComplete g → ∀ x : M, ∀ r : ℝ, 0 < r →
          (∀ y ∈ riemannianBallOf (I := I) g x r,
            r ^ 4 * Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y) ≤ 1) →
          ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E) ≤
            riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r) →
          Set.InjOn (fun v : TangentSpace I x =>
            DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I) g x v)
            {v | Real.sqrt (g.inner x v v) < iota * r} := by
  classical
  have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨c, hcpos, hc⟩ :=
    DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.exists_uniform_gronwall_scale
      (Module.finrank ℝ E) hn
  set c₁ : ℝ := min c 1 with hc₁def
  have hc₁pos : 0 < c₁ := lt_min hcpos zero_lt_one
  have hc₁c : c₁ ≤ c := min_le_left _ _
  have hc₁one : c₁ ≤ 1 := min_le_right _ _
  set q₀ : ℝ := (Module.finrank ℝ E : ℝ) /
    Real.sqrt (((Module.finrank ℝ E - 1 : ℕ)) : ℝ) with hq₀def
  have hq₀nn : 0 ≤ q₀ := div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  set hvA : ℝ := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
    q₀ (Module.finrank ℝ E - 1) (c₁ / 8) with hvAdef
  set hvB : ℝ := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
    q₀ (Module.finrank ℝ E - 1) (c₁ / 4) with hvBdef
  set hv1 : ℝ := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume
    q₀ (Module.finrank ℝ E - 1) 1 with hv1def
  have hvApos : 0 < hvA := by
    rw [hvAdef]; exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos hq₀nn (by positivity)
  have hvBpos : 0 < hvB := by
    rw [hvBdef]; exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos hq₀nn (by positivity)
  have hv1pos : 0 < hv1 := by
    rw [hv1def]; exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicRadialVolume_pos hq₀nn (by norm_num)
  set sig : ℝ := (Module.finrank ℝ E : ℝ) *
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.euclideanUnitBallVolume
      (Module.finrank ℝ E) with hsigdef
  have hsigpos : 0 < sig := by
    rw [hsigdef]; exact mul_pos (by exact_mod_cast hn)
      (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.euclideanUnitBallVolume_pos _)
  set const₀ : ℝ := sig * (hvA + hvB) with hconstdef
  have hconstpos : 0 < const₀ := by
    rw [hconstdef]; exact mul_pos hsigpos (add_pos hvApos hvBpos)
  set iot : ℝ := c₁ * kappa * hvA / (32 * hv1 * const₀) with hiotdef
  have hiotpos : 0 < iot := by
    rw [hiotdef]
    exact div_pos (mul_pos (mul_pos hc₁pos hkappa) hvApos)
      (mul_pos (mul_pos (by norm_num : (0:ℝ) < 32) hv1pos) hconstpos)
  refine ⟨iot, hiotpos, ?_⟩
  intro M _ _ _ _ _ _ g hg x r hr hRm hvol
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : Bundle.RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let metricM : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := metricM.toPseudoEMetricSpace
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let : @CompleteSpace M metricM.toUniformSpace := hg.complete
  have hEnormM : ∀ y : M, ∀ v : TangentSpace I y,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)) :=
    fun y v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  let U : TopologicalSpace.Opens M := connectedComponentOpen (I := I) x
  let gU : SmoothRiemannianMetric I U := g.restrictOpen U
  let : SigmaCompactSpace U := (isClosed_connectedComponent (x := x)).sigmaCompactSpace
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I) x
  let : IsManifold I 1 U :=
    IsManifold.of_le (I := I) (M := U) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace U := Manifold.metrizableSpace I U
  let : T3Space U := inferInstance
  let : Bundle.RiemannianBundle (fun y : U => TangentSpace I y) := ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : U => TangentSpace I y) :=
    ⟨⟨gU.inner, gU.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let metricU : EMetricSpace U := EMetricSpace.ofRiemannianMetric I U
  let : PseudoEMetricSpace U := metricU.toPseudoEMetricSpace
  let : IsRiemannianManifold I U := ⟨fun _ _ => rfl⟩
  have hgU : RiemannianMetricComplete gU :=
    DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen (I := I) g x hg
  let : @CompleteSpace U metricU.toUniformSpace := hgU.complete
  have hEnormU : ∀ y : U, ∀ v : TangentSpace I y,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gU.inner y v v)) :=
    fun y v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) gU y v
  have hKpos : 0 < (1 : ℝ) / r ^ 2 := by positivity
  have hs : 0 < c₁ * r / 8 := by positivity
  have hs2 : c₁ * r / 8 + c₁ * r / 8 = c₁ * r / 4 := by ring
  have h4r : c₁ * r / 4 ≤ r := by nlinarith [hc₁one, hr]
  have hqnn : 0 ≤ q₀ / r := div_nonneg hq₀nn hr.le
  have hsc : SigmaCompactSpace (connectedComponentOpen (I := I) x) :=
    (isClosed_connectedComponent (x := x)).sigmaCompactSpace
  have hK := sqrt_normSq_le_of_curvature_bound (I := I) g x hr hRm
  have hric := ricciTensor_lower_of_curvature_bound (I := I) (q₀ := q₀) g x hr hq₀def hK
  have hvolM := ball_volume_lower_bound_of_ricci_lower_bound (I := I) (kappa := kappa) (q₀ := q₀) g hg x
    hkappa hr hq₀def hric hvol (hsc := hsc) hc₁pos hc₁one
  rw [← hvAdef, ← hv1def] at hvolM
  have hRmK : ∀ y : M, Manifold.riemannianEDist I x y < ENNReal.ofReal r →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) (M := M) g y)) ≤ 1 / r ^ 2 := by
    intro y hy
    rw [← DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnormM x y] at hy
    exact hK y (by simpa only [riemannianBallOf, Set.mem_ofPred_eq] using hy)
  have hsqrtK : Real.sqrt (1 / r ^ 2) = 1 / r := by
    have hsq : (1 : ℝ) / r ^ 2 = (1 / r) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hRpos : 0 < c₁ * r := mul_pos hc₁pos hr
  have hRpi : c₁ * r ≤ Real.pi / Real.sqrt (1 / r ^ 2) := by
    have hpir : Real.pi / (1 / r) = Real.pi * r := by field_simp
    rw [hsqrtK, hpir]
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [hc₁one, hr]
  have hloc : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicFramedExp
        (I := I) g hEnormM x)
      (Metric.ball (0 : E) (c₁ * r)) := by
    refine DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicFrame_localOn_of_local_curvature
      (I := I) (M := M) g hEnormM x (K := 1 / r ^ 2) (R := r) (r := c₁ * r)
      (le_of_lt hKpos) ?_ ?_ ?_
    · nlinarith [hc₁one, hr]
    · intro y hy
      exact hRmK y hy
    · intro t ht0 htr
      have hcr : c / Real.sqrt (1 / r ^ 2) = c * r := by
        rw [hsqrtK, one_div, div_eq_mul_inv, inv_inv]
      have ht : t ≤ c / Real.sqrt (1 / r ^ 2) := by
        rw [hcr]
        exact htr.trans (mul_le_mul_of_nonneg_right hc₁c hr.le)
      exact hc (1 / r ^ 2) hKpos t ht0 ht
  have hcpt : @IsCompact M (metricM.toPseudoEMetricSpace).toUniformSpace.toTopologicalSpace
      (Metric.closedEBall x (ENNReal.ofReal (c₁ * r / 8))) := by
    have h := RiemannianMetricComplete.closedEBall_isCompact (I := I) (g := g) hg x (c₁ * r / 8)
    have hset : Metric.closedEBall x (ENNReal.ofReal (c₁ * r / 8)) =
        riemannianClosedBallOf (I := I) g x (c₁ * r / 8) := by
      ext y
      simp only [Metric.closedEBall, riemannianClosedBallOf, Set.mem_ofPred_eq]
      rw [IsRiemannianManifold.out (I := I) y x,
        Manifold.riemannianEDist_comm (I := I) (x := y) (y := x)]
      rfl
    rwa [hset]
  have hRmBall : ∀ y : M, y ∈ Metric.eball x (ENNReal.ofReal (3 * (c₁ * r) / 4)) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) (M := M) g y)) ≤ 1 / r ^ 2 := by
    intro y hy
    have hyr : Manifold.riemannianEDist I x y < ENNReal.ofReal r := by
      have h : edist y x < ENNReal.ofReal (3 * (c₁ * r) / 4) := by
        simpa only [Metric.eball, Set.mem_ofPred_eq] using hy
      rw [IsRiemannianManifold.out (I := I) y x,
        Manifold.riemannianEDist_comm (I := I) (x := y) (y := x)] at h
      exact h.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith [hc₁one, hr]))
    exact hRmK y hyr
  have hRicBall : ∀ y : M,
      Manifold.riemannianEDist I x y < ENNReal.ofReal (c₁ * r / 8 + c₁ * r / 8) →
      ∀ w : TangentSpace I y,
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q₀ / r) ^ 2) * g.inner y w w ≤
          ricciTensor (I := I) g y w w := by
    intro y hy w
    refine hric y ?_ w
    rw [hs2] at hy
    rw [← DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnormM x y] at hy
    exact (by simpa only [riemannianBallOf, Set.mem_ofPred_eq] using
      hy.trans_le (ENNReal.ofReal_le_ofReal h4r))
  have hfit : c₁ * r / 8 + 2 * (c₁ * r / 8) < c₁ * r := by nlinarith [hr, hc₁pos]
  have hquarter : c₁ * r / 8 < c₁ * r / 4 := by nlinarith [hr, hc₁pos]
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hCGT := DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrInj_ge_vol_of_local_ball
    (I := I) (M := M) g hEnormM x (K := 1 / r ^ 2) (R := c₁ * r)
    (r₀ := c₁ * r / 8) (s := c₁ * r / 8) (q := q₀ / r)
    (v := ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * hvA / hv1))
    hKpos hRpos hRpi hRmBall hloc hs hs hfit hquarter hqnn hRicBall hcpt hvolM
  exact injOn_expMap_of_cgt_volume_bound (I := I) (M := M) (q₀ := q₀) (c₁ := c₁) (sig := sig)
    (hvA := hvA) (hvB := hvB) (hv1 := hv1) (const₀ := const₀) (iot := iot)
    g x hEnormM hkappa hr hc₁pos hq₀nn hvAdef hvBdef hv1def hsigdef hconstdef
    hiotdef hCGT

end LocalMetricInjectivity

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
