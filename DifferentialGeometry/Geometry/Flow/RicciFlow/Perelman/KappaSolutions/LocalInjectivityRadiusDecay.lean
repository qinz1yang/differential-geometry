import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCGTInjectivity
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovNonpositiveLocal
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.Basic
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.InjectivityRadiusDecay.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Manifold MeasureTheory Metric Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance localCGMeasurableSpaceE : MeasurableSpace E := borel E

private local instance localCGBorelSpaceE : BorelSpace E := ⟨rfl⟩

omit [CompleteSpace E] in
theorem riemannianVolumeMeasure_ball_le_hyperbolic_of_ricciBoundedBelowOn
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  have heq : (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace =
      ‹PseudoEMetricSpace M› := by
    apply PseudoEMetricSpace.ext
    ext y z
    change riemannianEDist I y z = edist y z
    exact (IsRiemannianManifold.out (I := I) y z).symm
  have hc : @CompleteSpace M (EMetricSpace.ofRiemannianMetric I M).toUniformSpace := by
    rw [heq]
    infer_instance
  have hproper := HopfRinow.properSpace_riemMetric (I := I) hc g hEnorm
  have hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall x (ENNReal.ofReal R)) := by
    let m : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    have hm : m.toPseudoEMetricSpace = ‹PseudoEMetricSpace M› := by
      exact heq
    rw [← hm]
    let : MetricSpace M := m
    let : PseudoEMetricSpace M := m.toPseudoEMetricSpace
    let : ProperSpace M := hproper
    have hset : Metric.closedEBall x (ENNReal.ofReal R) = Metric.closedBall x R := by
      ext y
      simp only [Metric.mem_closedEBall, Metric.mem_closedBall, edist_dist,
        ENNReal.ofReal_le_ofReal_iff hR.le]
    rw [hset]
    exact isCompact_closedBall x R
  exact riemannianVolumeMeasure_ball_le_hyperbolic_of_isCompact_closedEBall g hEnorm x hq hR hcpt
    (fun y v hy ↦ hRic y hy v)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem PointedRiemannianManifold.riemannianEDistOf_eq_edist
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) := Y.riemBundle (I := I)
    letI : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
    ∀ y z : Y.M, riemannianEDistOf (I := I) Y.metric y z = edist y z := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) := Y.riemBundle (I := I)
  let : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  intro y z
  rw [IsRiemannianManifold.out (I := I)]
  rfl

omit [CompleteSpace E] [I.Boundaryless] in
private lemma hyperbolicRadialVolume_add_shift_le
    (d : ℕ) {q s D : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hD : 0 ≤ D) :
    hyperbolicRadialVolume q d (D + s) ≤
      (2 ^ (d + 1) * Real.exp (q * (d : ℝ) * s)) *
        Real.exp ((q * (d : ℝ) + (d + 1 : ℕ) / s) * D) *
          hyperbolicRadialVolume q d s := by
  have hsR : s ≤ D + s := by linarith
  have hratio := hyperbolicRadialVolume_ratio_le d hq hs hsR
  have hsdiv : 0 ≤ D / s := div_nonneg hD hs.le
  have hone : 1 + D / s ≤ Real.exp (D / s) := by
    simpa only [add_comm] using Real.add_one_le_exp (D / s)
  have hfrac : (D + s) / (s / 2) = 2 * (1 + D / s) := by
    field_simp
    ring
  have hbase : 0 ≤ 2 * (1 + D / s) := by positivity
  have hpow :
      ((D + s) / (s / 2)) ^ (d + 1) ≤ (2 * Real.exp (D / s)) ^ (d + 1) := by
    rw [hfrac]
    exact pow_le_pow_left₀ hbase (mul_le_mul_of_nonneg_left hone (by norm_num)) _
  calc
    hyperbolicRadialVolume q d (D + s)
        ≤ Real.exp (q * (d : ℝ) * (D + s)) *
            ((D + s) / (s / 2)) ^ (d + 1) *
              hyperbolicRadialVolume q d s := hratio
    _ ≤ Real.exp (q * (d : ℝ) * (D + s)) *
            (2 * Real.exp (D / s)) ^ (d + 1) *
              hyperbolicRadialVolume q d s := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
            ((pow_nonneg (by positivity : 0 ≤ s / 2) _).trans
              (hyperbolicRadialVolume_ge d hq hs))
    _ = (2 ^ (d + 1) * Real.exp (q * (d : ℝ) * s)) *
          Real.exp ((q * (d : ℝ) + (d + 1 : ℕ) / s) * D) *
            hyperbolicRadialVolume q d s := by
          rw [mul_pow, ← Real.exp_nat_mul (D / s) (d + 1)]
          calc
            Real.exp (q * (d : ℝ) * (D + s)) *
                  (2 ^ (d + 1) * Real.exp ((d + 1 : ℕ) * (D / s))) *
                  hyperbolicRadialVolume q d s =
                2 ^ (d + 1) *
                  (Real.exp (q * (d : ℝ) * (D + s)) *
                    Real.exp ((d + 1 : ℕ) * (D / s))) *
                  hyperbolicRadialVolume q d s := by ring
            _ = 2 ^ (d + 1) *
                  Real.exp (q * (d : ℝ) * (D + s) + (d + 1 : ℕ) * (D / s)) *
                  hyperbolicRadialVolume q d s := by rw [Real.exp_add]
            _ = 2 ^ (d + 1) *
                  Real.exp (q * (d : ℝ) * s +
                      (q * (d : ℝ) + (d + 1 : ℕ) / s) * D) *
                  hyperbolicRadialVolume q d s := by
                congr 3
                ring
            _ = (2 ^ (d + 1) * Real.exp (q * (d : ℝ) * s)) *
                  Real.exp ((q * (d : ℝ) + (d + 1 : ℕ) / s) * D) *
                  hyperbolicRadialVolume q d s := by
                rw [Real.exp_add]
                ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
theorem bonnet_myers_ricciTensor_at_le
    (g : SmoothRiemannianMetric I M) {y : M} {Rm : ℝ} (v : TangentSpace I y)
    (hRm : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) (M := M) g y)) ≤ Rm) :
    -((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * (g.inner y v v : ℝ) ≤
      ricciTensor (I := I) g y v v := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g y
  let A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
    (metricRm04At (I := I) (M := M) g y))
  have hfinrank : Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E := by
    have hy : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H y
    exact ((trivializationAt E (TangentSpace I) y).linearEquivAt ℝ y hy).finrank_eq
  have hcomp : ∀ i j,
      |metricRicciAt (I := I) (M := M) g y
          (vec2 (I := I) (basis i) (basis j))| ≤
        (Module.finrank ℝ E : ℝ) * A := by
    intro i j
    simpa [A, hfinrank] using metricRicciComp_le (I := I) g basis hON i j
  have hunit : ∀ u : TangentSpace I y, g.inner y u u = 1 →
      |metricRicciAt (I := I) (M := M) g y (vec2 (I := I) u u)| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * A := by
    intro u hu
    have h := ricci_unitSphere_le_of_componentBound
      (I := I) g (metricRicciAt (I := I) (M := M) g y) basis hON
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hcomp u hu
    simpa [A, hfinrank, pow_two, mul_assoc] using h
  have hquad := tensor02_quadForm_abs_le_of_unit_bound
    (I := I) g (metricRicciAt (I := I) (M := M) g y) hunit v
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) g y v v] at hquad
  have hinner : 0 ≤ g.inner y v v := by
    rcases eq_or_ne v 0 with hv | hv
    · subst hv
      simp
    · exact (g.pos y v hv).le
  have hcoef :
      (Module.finrank ℝ E : ℝ) ^ 2 * A ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Rm :=
    mul_le_mul_of_nonneg_left (by simpa only [A] using hRm) (sq_nonneg _)
  have habs : |ricciTensor (I := I) g y v v| ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * Rm) * g.inner y v v :=
    hquad.trans (mul_le_mul_of_nonneg_right hcoef hinner)
  simpa only [neg_mul] using (abs_le.mp habs).1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma shift_exp_mul_decay
    {shift lower s C D : ℝ} (hshift : shift ≠ 0) :
    (shift * Real.exp (C * D)) *
        ((lower / shift) * s * Real.exp (-C * D)) = lower * s := by
  field_simp
  calc
    Real.exp (C * D) * lower * s * Real.exp (-(C * D)) =
        lower * s * (Real.exp (C * D) * Real.exp (-(C * D))) := by ring
    _ = lower * s := by
      rw [← Real.exp_add]
      ring_nf
      norm_num

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma ofReal_add_mul {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal c + ENNReal.ofReal b * ENNReal.ofReal c =
      ENNReal.ofReal ((a + b) * c) := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_mul (add_nonneg ha hb)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
theorem normSq0S_metricRm04At_le_curvDerivNorm
    (g : SmoothRiemannianMetric I M) (x : M) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
        (metricRm04At (I := I) (M := M) g x)) ≤
      curvDerivNorm (I := I) 0 g x := by
  have h0 : curvCovDeriv (I := I) (M := M) g 0 = metricRm04 (I := I) (M := M) g := rfl
  rw [curvDerivNorm, curvDerivNormSq, h0, metricRm04_apply]

theorem exists_ball_injectivity_radius_decay
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (base : BaseInjBound (I := I) X)
    (A : ℝ) (hA : 0 < A)
    (K : ℝ) (hK : 0 ≤ K)
    (hrm : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      ∀ y : (X.obj k).M,
        edist (X.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj k).metric y 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I)
            (M := (X.obj k).M) (X.obj k).metric y)) ≤ K)
    (hpull : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      letI : RiemannianBundle (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle (I := I)
      letI : (y : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I y) :=
        (X.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X.obj k).M :=
        MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
      letI : IsRiemannianManifold I (X.obj k).M := ⟨fun _ _ => rfl⟩
      ∀ (x : (X.obj k).M)
        (hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)))
        (q R : ℝ), 0 ≤ q → 0 < R →
        (∀ z, z ∈ Metric.ball (0 : E) R → z ≠ 0 →
          ∀ t, t ∈ Set.Ioo (0 : ℝ) 1 →
            ¬ IsConjVec (I := I) (X.obj k).metric hEnorm x
              ((t • normalFrame (I := I) (X.obj k).metric x z : TangentSpace I x) : E)) →
        ricciBoundedBelowOn (I := I) (X.obj k).metric
          {y : (X.obj k).M | riemannianEDist I x y < ENNReal.ofReal R}
          (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
        intrinsicPullVol (I := I) (X.obj k).metric hEnorm x R ≤
          (MeasureTheory.volume : MeasureTheory.Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R)) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
        ∀ x : (X.obj k).M,
          edist (X.obj k).basepoint x ≤ ENNReal.ofReal A →
            HasInjRadiusAt (I := I) (X.obj k) x
              (a * (min base.ρ 1) ^ Module.finrank ℝ E *
                Real.exp (-C * (edist (X.obj k).basepoint x).toReal)) := by
  classical
  let n : Nat := Module.finrank ℝ E
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let d : Nat := n - 1
  have hdSucc : d + 1 = n := by
    dsimp only [d]
    omega
  let K' : ℝ := K + 1
  have hK' : 0 < K' := by
    dsimp only [K']
    linarith
  have hK'nonneg : 0 ≤ K' := hK'.le
  have hKle : K ≤ K' := by
    dsimp only [K']
    linarith
  let q : ℝ := (n : ℝ) * Real.sqrt K'
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨rCtrl, hrCtrl, hrCtrlLe, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) (R := 3) (K := K')
      (by norm_num) hK'nonneg
  let b : ℝ := min base.ρ 1
  have hb : 0 < b := lt_min base.pos one_pos
  have hb1 : b ≤ 1 := min_le_right _ _
  have hbRho : b ≤ base.ρ := min_le_left _ _
  let s : ℝ := min (rCtrl / 10) (min (Real.pi / (10 * Real.sqrt K')) (b / 2))
  have hsqrtK' : 0 < Real.sqrt K' := Real.sqrt_pos.mpr hK'
  have hs : 0 < s := by
    dsimp only [s]
    exact lt_min (by positivity)
      (lt_min (div_pos Real.pi_pos (mul_pos (by norm_num) hsqrtK')) (by positivity))
  have hs_le_rCtrl_div : s ≤ rCtrl / 10 := min_le_left _ _
  have hs_bhalf : s ≤ b / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hs_pi : s ≤ Real.pi / (10 * Real.sqrt K') :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hs_le_rCtrl : s ≤ rCtrl := by linarith
  have h5s_le_rCtrl : 5 * s ≤ rCtrl := by linarith
  have h5s_le_three : 5 * s ≤ 3 := h5s_le_rCtrl.trans hrCtrlLe
  have hs_le_half : s ≤ 1 / 2 := by linarith
  have hs_le_one : s ≤ 1 := by linarith
  have htwo_s_le_rCtrl : 2 * s ≤ rCtrl := by linarith
  have hs_rho : s < base.ρ := by
    have h2 : b / 2 < b := by linarith
    exact hs_bhalf.trans_lt (h2.trans_le hbRho)
  have h5s_pos : 0 < 5 * s := by linarith
  have h5s_pi : 5 * s ≤ Real.pi / Real.sqrt K' := by
    have h2 : 5 * (Real.pi / (10 * Real.sqrt K')) = Real.pi / (2 * Real.sqrt K') := by ring
    have h3 : Real.pi / (2 * Real.sqrt K') ≤ Real.pi / Real.sqrt K' :=
      div_le_div_of_nonneg_left Real.pi_pos.le hsqrtK' (by linarith)
    linarith
  have h3m5s : 3 * (5 * s) / 4 ≤ 3 := by linarith
  let dens : ℝ := Real.sqrt (((1 / 2 : ℝ) * modelCoeffMin (E := E) ^ 2) ^ n)
  let unitVol : ℝ := ((modelHaar (E := E)) (Metric.ball (0 : E) 1)).toReal
  let lowerC : ℝ := dens * unitVol
  let shiftC : ℝ := 2 ^ n * Real.exp (q * (d : ℝ) * s)
  let sphereB : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)).toReal
  let sphereP : ℝ := (((volume : Measure E).toSphere Set.univ)).toReal
  let upperC : ℝ := 2 ^ n * Real.exp (q * (d : ℝ) * (2 * s))
  let C : ℝ := q * (d : ℝ) + (n : ℝ) / s
  let a : ℝ := (s / 2) * lowerC / (shiftC * ((sphereB + sphereP) * upperC))
  have hdens : 0 < dens := by
    dsimp only [dens]
    apply Real.sqrt_pos.mpr
    apply pow_pos
    exact mul_pos (by norm_num) (sq_pos_of_pos (modelCoeffMin_pos (E := E)))
  have hunit : 0 < unitVol := by
    dsimp only [unitVol]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos (modelHaar (E := E)) (0 : E) one_pos).ne'
      measure_ball_lt_top.ne
  have hlower : 0 < lowerC := mul_pos hdens hunit
  have hshift : 0 < shiftC :=
    mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  have hfinEucl : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hn
  have hsphereB : 0 < sphereB := by
    dsimp only [sphereB]
    exact ENNReal.toReal_pos
      (Measure.measure_univ_pos.mpr
        (Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin n))))).ne'
      (measure_lt_top _ _).ne
  have hsphereP : 0 ≤ sphereP := ENNReal.toReal_nonneg
  have hspheres : 0 < sphereB + sphereP := add_pos_of_pos_of_nonneg hsphereB hsphereP
  have hupper : 0 < upperC :=
    mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos (mul_pos (div_pos hs (by norm_num)) hlower)
      (mul_pos hshift (mul_pos hspheres hupper))
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg hq (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) hs.le)
  refine ⟨a, C, ha, hCnonneg, ?_⟩
  intro k
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  intro x hx
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let : ConnectedSpace (X.obj k).M := hconn k
  let : IsRiemannianManifold I (X.obj k).M := ⟨fun _ _ => rfl⟩
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (X.obj k).metric y w
  have hRmBallOf : ∀ p : (X.obj k).M,
      edist (X.obj k).basepoint p ≤ ENNReal.ofReal A →
      ∀ y : (X.obj k).M, riemannianEDist I p y < ENNReal.ofReal 3 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj k).metric y 4
          (metricRm04At (I := I) (M := (X.obj k).M) (X.obj k).metric y)) ≤ K' := by
    intro p hp y hy
    have hy' : edist p y < ENNReal.ofReal 3 := by
      rw [← IsRiemannianManifold.out (I := I)] at hy
      exact hy
    have hbp : edist (X.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) := by
      calc
        edist (X.obj k).basepoint y ≤ edist (X.obj k).basepoint p + edist p y :=
          edist_triangle (X.obj k).basepoint p y
        _ ≤ ENNReal.ofReal A + ENNReal.ofReal 3 := add_le_add hp hy'.le
        _ = ENNReal.ofReal (A + 3) :=
          (ENNReal.ofReal_add hA.le (by norm_num)).symm
        _ ≤ ENNReal.ofReal (2 * A + 3) := ENNReal.ofReal_le_ofReal (by linarith)
    exact (hrm k y hbp).trans hKle
  have hmetricOf : ∀ p : (X.obj k).M, edist (X.obj k).basepoint p ≤ ENNReal.ofReal A →
      ∀ z ∈ Metric.ball (0 : E) rCtrl, ∀ v : E,
        (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
            intrinsicFrameMetric (I := I) (X.obj k).metric hEnorm p z v v ∧
          intrinsicFrameMetric (I := I) (X.obj k).metric hEnorm p z v v ≤
            2 * ‖v‖ ^ 2 := by
    intro p hp z hz v
    have hzr : ‖z‖ < rCtrl := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact intrinsicFrameMetric_bounds_of_local_curvature (I := I) (X.obj k).metric
      hEnorm p hK'nonneg (hRmBallOf p hp) (hzr.trans_le hrCtrlLe)
      (herror ‖z‖ (norm_nonneg _) hzr.le) v
  have hlocalOf : ∀ p : (X.obj k).M, edist (X.obj k).basepoint p ≤ ENNReal.ofReal A →
      IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
        (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm p)
        (Metric.ball (0 : E) rCtrl) := by
    intro p hp
    exact intrinsicFrame_localOn_of_local_curvature (I := I) (X.obj k).metric hEnorm p
      hK'nonneg hrCtrlLe (hRmBallOf p hp) (fun t ht htr => herror t ht htr)
  have hbple : edist (X.obj k).basepoint (X.obj k).basepoint ≤ ENNReal.ofReal A := by
    simp
  have hlocalS : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm (X.obj k).basepoint)
      (Metric.ball (0 : E) s) := by
    intro z
    exact hlocalOf (X.obj k).basepoint hbple
      ⟨z.1, Metric.ball_subset_ball hs_le_rCtrl z.2⟩
  have hinjS : Set.InjOn
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm (X.obj k).basepoint)
      (Metric.ball (0 : E) s) :=
    (base.bound k).injOn_ball (hcomplete.complete k) hs_rho
  have hmetricS : ∀ z ∈ Metric.ball (0 : E) s, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
          intrinsicFrameMetric (I := I) (X.obj k).metric hEnorm
            (X.obj k).basepoint z v v ∧
        intrinsicFrameMetric (I := I) (X.obj k).metric hEnorm
            (X.obj k).basepoint z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro z hz v
    exact hmetricOf (X.obj k).basepoint hbple z
      (Metric.ball_subset_ball hs_le_rCtrl hz) v
  obtain ⟨baseChart⟩ := exists_intrinsic_ball_chart (I := I) (X.obj k).metric hEnorm
    (X.obj k).basepoint hlocalS hinjS
  let V0 : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := (X.obj k).M) (X.obj k).metric
      {y : (X.obj k).M |
        riemannianEDist I (X.obj k).basepoint y < ENNReal.ofReal s}
  have hV0raw :
      ENNReal.ofReal dens * (modelHaar (E := E)) (Metric.ball (0 : E) s) ≤ V0 := by
    simpa only [dens, V0, smallNormalBall] using
      (intrinsicBall_vol_ge (I := I) (X.obj k).metric hEnorm (X.obj k).basepoint
        hs baseChart hmetricS)
  have hunitEq :
      (modelHaar (E := E)) (Metric.ball (0 : E) 1) = ENNReal.ofReal unitVol :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hV0 : ENNReal.ofReal (lowerC * s ^ n) ≤ V0 := by
    calc
      ENNReal.ofReal (lowerC * s ^ n) =
          (ENNReal.ofReal dens * ENNReal.ofReal unitVol) *
            ENNReal.ofReal (s ^ n) := by
        rw [ENNReal.ofReal_mul hlower.le, ENNReal.ofReal_mul hdens.le]
      _ = ENNReal.ofReal dens *
          (ENNReal.ofReal (s ^ n) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
        rw [hunitEq]
        ac_rfl
      _ = ENNReal.ofReal dens *
          (modelHaar (E := E)) (Metric.ball (0 : E) s) := by
        rw [modelHaar_ball (E := E) hs]
      _ ≤ V0 := hV0raw
  let D : ℝ := (edist (X.obj k).basepoint x).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  have hDleA : D ≤ A := ENNReal.toReal_le_of_le_ofReal hA.le hx
  have hedistTop : edist (X.obj k).basepoint x ≠ (⊤ : ENNReal) := by
    rw [IsRiemannianManifold.out (I := I)]
    exact riemannianEDist_ne_top (I := I) (X.obj k).basepoint x
  have hdist : riemannianEDist I (X.obj k).basepoint x = ENNReal.ofReal D := by
    dsimp only [D]
    exact (ENNReal.ofReal_toReal hedistTop).symm
  let Vx : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := (X.obj k).M) (X.obj k).metric
      {y : (X.obj k).M | riemannianEDist I x y < ENNReal.ofReal s}
  let VxR : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := (X.obj k).M) (X.obj k).metric
      {y : (X.obj k).M | riemannianEDist I x y < ENNReal.ofReal (D + s)}
  have hV0shift : V0 ≤ VxR :=
    measure_mono (edistBall_shift (I := I) (a := (X.obj k).basepoint) (b := x)
      (t := D) (ρ := s) hdist.le hD hs.le)
  have hRicAmb : ricciBoundedBelowOn (I := I) (X.obj k).metric
      {y : (X.obj k).M |
        edist (X.obj k).basepoint y < ENNReal.ofReal (2 * A + 3)}
      (-(((n - 1 : ℕ) : ℝ) * q ^ 2)) := by
    by_cases hn1 : n = 1
    · have hzero : ((n - 1 : ℕ) : ℝ) * q ^ 2 = 0 := by
        rw [hn1]
        norm_num
      rw [hzero, neg_zero]
      exact ricciBoundedBelowOn_of_global (I := I)
        (ricci_dim1_bddBelow (by simpa only [n] using hn1) (X.obj k).metric)
    · have hn2 : 2 ≤ n := by omega
      intro y hy v
      have hric := bonnet_myers_ricciTensor_at_le (I := I) (X.obj k).metric v
        ((hrm k y hy.le).trans hKle)
      have hq2 : q ^ 2 = (n : ℝ) ^ 2 * K' := by
        dsimp only [q]
        rw [mul_pow, Real.sq_sqrt hK'.le]
      have hinner : 0 ≤ (X.obj k).metric.inner y v v := by
        rcases eq_or_ne v 0 with hv | hv
        · subst hv
          simp
        · exact ((X.obj k).metric.pos y v hv).le
      have hkappa : -(((n - 1 : ℕ) : ℝ) * q ^ 2) ≤ -((n : ℝ) ^ 2 * K') := by
        rw [neg_le_neg_iff, hq2]
        have hone : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
          have h1 : 1 ≤ n - 1 := by omega
          exact_mod_cast h1
        have hbase : 0 ≤ (n : ℝ) ^ 2 * K' := mul_nonneg (sq_nonneg _) hK'.le
        calc
          (n : ℝ) ^ 2 * K' = 1 * ((n : ℝ) ^ 2 * K') := by rw [one_mul]
          _ ≤ ((n - 1 : ℕ) : ℝ) * ((n : ℝ) ^ 2 * K') :=
            mul_le_mul_of_nonneg_right hone hbase
      calc
        -(((n - 1 : ℕ) : ℝ) * q ^ 2) * (X.obj k).metric.inner y v v
            ≤ -((n : ℝ) ^ 2 * K') * (X.obj k).metric.inner y v v :=
          mul_le_mul_of_nonneg_right hkappa hinner
        _ ≤ ricciTensor (I := I) (X.obj k).metric y v v := hric
  have hRicMono : ∀ {r : ℝ}, 0 ≤ r → r ≤ A + 2 →
      ricciBoundedBelowOn (I := I) (X.obj k).metric
        {y : (X.obj k).M | riemannianEDist I x y < ENNReal.ofReal r}
        (-(((n - 1 : ℕ) : ℝ) * q ^ 2)) := by
    intro r hr0 hr
    refine ricciBoundedBelowOn_mono ?_ hRicAmb
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    have hy' : edist x y < ENNReal.ofReal r := by
      rw [← IsRiemannianManifold.out (I := I)] at hy
      exact hy
    calc
      edist (X.obj k).basepoint y ≤ edist (X.obj k).basepoint x + edist x y :=
        edist_triangle (X.obj k).basepoint x y
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal r := add_le_add hx hy'.le
      _ = ENNReal.ofReal (A + r) := (ENNReal.ofReal_add hA.le hr0).symm
      _ < ENNReal.ofReal (2 * A + 3) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < 2 * A + 3)]
        linarith
  have hDpos : 0 < D + s := by linarith
  have hsD : s ≤ D + s := by linarith
  have hrel : VxR * ENNReal.ofReal (hyperbolicRadialVolume q d s) ≤
      ENNReal.ofReal (hyperbolicRadialVolume q d (D + s)) * Vx := by
    simpa only [VxR, Vx, d] using
      (segmentBall_vol_rel_endpoint_of_ricciBoundedBelowOn (I := I)
        (X.obj k).metric hEnorm x hq hs hsD
        (hRicMono (r := D + s) (by linarith) (by linarith [hDleA])))
  have hmodelShift : hyperbolicRadialVolume q d (D + s) ≤
      (shiftC * Real.exp (C * D)) * hyperbolicRadialVolume q d s := by
    simpa only [shiftC, C, hdSucc, mul_assoc] using
      (hyperbolicRadialVolume_add_shift_le d hq hs hD)
  have hshiftExpPos : 0 < shiftC * Real.exp (C * D) :=
    mul_pos hshift (Real.exp_pos _)
  have hmodelSPos : 0 < hyperbolicRadialVolume q d s :=
    hyperbolicRadialVolume_pos hq hs
  have hmodelS0 : ENNReal.ofReal (hyperbolicRadialVolume q d s) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmodelSPos
  have hmodelShiftE : ENNReal.ofReal (hyperbolicRadialVolume q d (D + s)) ≤
      ENNReal.ofReal (shiftC * Real.exp (C * D)) *
        ENNReal.ofReal (hyperbolicRadialVolume q d s) := by
    calc
      ENNReal.ofReal (hyperbolicRadialVolume q d (D + s))
          ≤ ENNReal.ofReal
              ((shiftC * Real.exp (C * D)) * hyperbolicRadialVolume q d s) :=
        ENNReal.ofReal_le_ofReal hmodelShift
      _ = ENNReal.ofReal (shiftC * Real.exp (C * D)) *
            ENNReal.ofReal (hyperbolicRadialVolume q d s) := by
        rw [ENNReal.ofReal_mul hshiftExpPos.le]
  have hVxRel : VxR ≤ ENNReal.ofReal (shiftC * Real.exp (C * D)) * Vx := by
    apply (ENNReal.mul_le_mul_iff_left hmodelS0 ENNReal.ofReal_ne_top).mp
    calc
      VxR * ENNReal.ofReal (hyperbolicRadialVolume q d s)
          ≤ ENNReal.ofReal (hyperbolicRadialVolume q d (D + s)) * Vx := hrel
      _ ≤ (ENNReal.ofReal (shiftC * Real.exp (C * D)) *
              ENNReal.ofReal (hyperbolicRadialVolume q d s)) * Vx := by
        gcongr
      _ = (ENNReal.ofReal (shiftC * Real.exp (C * D)) * Vx) *
            ENNReal.ofReal (hyperbolicRadialVolume q d s) := by
        ac_rfl
  let low : ℝ := (lowerC / shiftC) * s ^ n * Real.exp (-C * D)
  have hlow : 0 < low := by
    dsimp only [low]
    exact mul_pos
      (mul_pos (div_pos hlower hshift) (pow_pos hs _))
      (Real.exp_pos _)
  have hlowMul : (shiftC * Real.exp (C * D)) * low = lowerC * s ^ n := by
    dsimp only [low]
    exact shift_exp_mul_decay hshift.ne'
  have hVxLow : ENNReal.ofReal low ≤ Vx := by
    apply (ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_ne_zero_iff.mpr hshiftExpPos) ENNReal.ofReal_ne_top).mp
    rw [← ENNReal.ofReal_mul hshiftExpPos.le, hlowMul]
    exact hV0.trans (hV0shift.trans hVxRel)
  have hmodelOne : hyperbolicRadialVolume q d s ≤ upperC * s ^ n := by
    calc
      hyperbolicRadialVolume q d s
          ≤ s ^ (d + 1) * Real.exp (q * (d : ℝ) * s) :=
        hyperbolicRadialVolume_le d hq hs.le
      _ = s ^ n * Real.exp (q * (d : ℝ) * s) := by rw [hdSucc]
      _ ≤ 2 ^ n * s ^ n * Real.exp (q * (d : ℝ) * (2 * s)) := by
        have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have hsnn : 0 ≤ s ^ n := pow_nonneg hs.le _
        have hqd : 0 ≤ q * (d : ℝ) := mul_nonneg hq (Nat.cast_nonneg _)
        have hexp : Real.exp (q * (d : ℝ) * s) ≤
            Real.exp (q * (d : ℝ) * (2 * s)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hqd)
        calc
          s ^ n * Real.exp (q * (d : ℝ) * s)
              ≤ s ^ n * Real.exp (q * (d : ℝ) * (2 * s)) :=
            mul_le_mul_of_nonneg_left hexp hsnn
          _ ≤ 2 ^ n * s ^ n * Real.exp (q * (d : ℝ) * (2 * s)) := by
            have hle : s ^ n ≤ 2 ^ n * s ^ n := by
              calc
                s ^ n = 1 * s ^ n := (one_mul _).symm
                _ ≤ 2 ^ n * s ^ n := mul_le_mul_of_nonneg_right h1 hsnn
            exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = upperC * s ^ n := by
        dsimp only [upperC]
        ring
  have hsphereBEq :
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ) =
        ENNReal.ofReal sphereB :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hspherePEq :
      ((MeasureTheory.volume : Measure E).toSphere Set.univ) = ENNReal.ofReal sphereP :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hVxUpper : Vx ≤ ENNReal.ofReal sphereB * ENNReal.ofReal (upperC * s ^ n) := by
    calc
      Vx ≤
          ((MeasureTheory.volume : Measure
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ) *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) s) :=
        riemannianVolumeMeasure_ball_le_hyperbolic_of_ricciBoundedBelowOn (I := I)
          (X.obj k).metric
          hEnorm x hq hs (hRicMono (r := s) hs.le (by linarith))
      _ = ENNReal.ofReal sphereB * ENNReal.ofReal (hyperbolicRadialVolume q d s) := by
        rw [hsphereBEq]
      _ ≤ ENNReal.ofReal sphereB * ENNReal.ofReal (upperC * s ^ n) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hmodelOne) (by positivity)
  let P : ENNReal := intrinsicPullVol (I := I) (X.obj k).metric hEnorm x (2 * s)
  have hno : ∀ z, z ∈ Metric.ball (0 : E) (2 * s) → z ≠ 0 →
      ∀ t, t ∈ Set.Ioo (0 : ℝ) 1 →
        ¬ IsConjVec (I := I) (X.obj k).metric hEnorm x
          ((t • normalFrame (I := I) (X.obj k).metric x z : TangentSpace I x) : E) := by
    intro z hz hz0 t ht
    have htz : t • z ∈ Metric.ball (0 : E) rCtrl := by
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      calc
        t * ‖z‖ < 1 * ‖z‖ := mul_lt_mul_of_pos_right ht.2 (norm_pos_iff.mpr hz0)
        _ = ‖z‖ := one_mul _
        _ < 2 * s := hz
        _ ≤ rCtrl := htwo_s_le_rCtrl
    have hraw := intrinsicFrame_not_conj (I := I) (X.obj k).metric hEnorm x (t • z)
      (c := (1 / 2 : ℝ)) (by norm_num) (fun v => (hmetricOf x hx (t • z) htz v).1)
    simpa only [map_smul] using hraw
  have hPUpper : P ≤ ENNReal.ofReal sphereP * ENNReal.ofReal (upperC * s ^ n) := by
    have hp := hpull k x hEnorm q (2 * s) hq (by linarith) hno
      (hRicMono (r := 2 * s) (by linarith) (by linarith))
    calc
      P ≤ ((MeasureTheory.volume : Measure E).toSphere Set.univ) *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) (2 * s)) :=
        hp
      _ = ENNReal.ofReal sphereP *
            ENNReal.ofReal (hyperbolicRadialVolume q d (2 * s)) := by
        rw [hspherePEq]
      _ ≤ ENNReal.ofReal sphereP * ENNReal.ofReal (upperC * s ^ n) := by
        gcongr
        calc
          hyperbolicRadialVolume q d (2 * s) ≤
              (2 * s) ^ (d + 1) * Real.exp (q * (d : ℝ) * (2 * s)) :=
            hyperbolicRadialVolume_le d hq (by linarith)
          _ = 2 ^ n * s ^ n * Real.exp (q * (d : ℝ) * (2 * s)) := by
            rw [hdSucc, mul_pow]
          _ = upperC * s ^ n := by
            dsimp only [upperC]
            ring
  have hden : 0 < (sphereB + sphereP) * (upperC * s ^ n) :=
    mul_pos hspheres (mul_pos hupper (pow_pos hs _))
  have hDen : Vx + P ≤ ENNReal.ofReal ((sphereB + sphereP) * (upperC * s ^ n)) := by
    calc
      Vx + P ≤ ENNReal.ofReal sphereB * ENNReal.ofReal (upperC * s ^ n) +
            ENNReal.ofReal sphereP * ENNReal.ofReal (upperC * s ^ n) :=
        add_le_add hVxUpper hPUpper
      _ = ENNReal.ofReal ((sphereB + sphereP) * (upperC * s ^ n)) :=
        ofReal_add_mul hsphereB.le hsphereP
  have hlocalFive : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (5 * s)) := by
    intro z
    exact hlocalOf x hx ⟨z.1, Metric.ball_subset_ball h5s_le_rCtrl z.2⟩
  have hRmFive : ∀ z : E, ‖z‖ < 3 * (5 * s) / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj k).metric
        (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x z) 4
        (metricRm04At (I := I) (M := (X.obj k).M) (X.obj k).metric
          (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x z))) ≤ K' := by
    intro z hz
    exact intrinsicFrame_rm04_bound_of_ball (I := I) (X.obj k).metric hEnorm x
      (ρ := 3) (K := K') (hRmBallOf x hx) (by linarith)
  have hcgt :
      ENNReal.ofReal (s / 2) * Vx / (Vx + P) ≤
        intrinsicInjRadius (I := I) (X.obj k).metric hEnorm x := by
    simpa only [Vx, P, two_mul] using
      (intrinsicInjRadius_ge_cheeger_gromov_taylor_on (I := I) (K := K') (R := 5 * s)
        (r₀ := s) (s := s) (X.obj k).metric hEnorm x hK' h5s_pos h5s_pi hRmFive
        hlocalFive hs (by linarith) (by linarith))
  have hratio :
      ENNReal.ofReal ((s / 2) * low / ((sphereB + sphereP) * (upperC * s ^ n))) ≤
        ENNReal.ofReal (s / 2) * Vx / (Vx + P) := by
    rw [ENNReal.ofReal_div_of_pos hden,
      ENNReal.ofReal_mul (by positivity : 0 ≤ s / 2)]
    exact ENNReal.div_le_div (by gcongr) hDen
  have hratioEq :
      (s / 2) * low / ((sphereB + sphereP) * (upperC * s ^ n)) =
        a * Real.exp (-C * D) := by
    have hsn : s ^ n ≠ 0 := pow_ne_zero n hs.ne'
    dsimp only [low, a]
    field_simp
  have hfinal : ENNReal.ofReal (a * Real.exp (-C * D)) ≤
      intrinsicInjRadius (I := I) (X.obj k).metric hEnorm x := by
    have h1 := hratio.trans hcgt
    rwa [hratioEq] at h1
  refine ⟨?_, ?_⟩
  · exact mul_pos (mul_pos ha (pow_pos hb _)) (Real.exp_pos _)
  · intro hcomplete'
    have hle :
        a * (min base.ρ 1) ^ Module.finrank ℝ E * Real.exp (-C * D) ≤
          a * Real.exp (-C * D) := by
      have hpown : (min base.ρ 1) ^ Module.finrank ℝ E ≤ 1 :=
        pow_le_one₀ hb.le hb1
      calc
        a * (min base.ρ 1) ^ Module.finrank ℝ E * Real.exp (-C * D)
            ≤ a * 1 * Real.exp (-C * D) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpown ha.le) (Real.exp_pos _).le
        _ = a * Real.exp (-C * D) := by ring
    exact (ENNReal.ofReal_le_ofReal hle).trans (by
      simpa only [D, PointedRiemannianManifold.intrinsicInjRadius] using hfinal)

theorem exists_pos_injectivity_radius_on_ball
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (base : BaseInjBound (I := I) X)
    (A : ℝ) (hA : 0 < A)
    (K : ℝ) (hK : 0 ≤ K)
    (hrm : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      ∀ y : (X.obj k).M,
        edist (X.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj k).metric y 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I)
            (M := (X.obj k).M) (X.obj k).metric y)) ≤ K)
    (hpull : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      letI : RiemannianBundle (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle (I := I)
      letI : (y : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I y) :=
        (X.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X.obj k).M :=
        MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
      letI : IsRiemannianManifold I (X.obj k).M := ⟨fun _ _ => rfl⟩
      ∀ (x : (X.obj k).M)
        (hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)))
        (q R : ℝ), 0 ≤ q → 0 < R →
        (∀ z, z ∈ Metric.ball (0 : E) R → z ≠ 0 →
          ∀ t, t ∈ Set.Ioo (0 : ℝ) 1 →
            ¬ IsConjVec (I := I) (X.obj k).metric hEnorm x
              ((t • normalFrame (I := I) (X.obj k).metric x z : TangentSpace I x) : E)) →
        ricciBoundedBelowOn (I := I) (X.obj k).metric
          {y : (X.obj k).M | riemannianEDist I x y < ENNReal.ofReal R}
          (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
        intrinsicPullVol (I := I) (X.obj k).metric hEnorm x R ≤
          (MeasureTheory.volume : MeasureTheory.Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R)) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
        ∀ x : (X.obj k).M,
          edist (X.obj k).basepoint x ≤ ENNReal.ofReal A →
            HasInjRadiusAt (I := I) (X.obj k) x rho := by
  obtain ⟨a, C, ha, hC, hdec⟩ :=
    exists_ball_injectivity_radius_decay (I := I) X hcomplete hconn base A hA K hK hrm hpull
  refine ⟨a * (min base.ρ 1) ^ Module.finrank ℝ E * Real.exp (-C * A), ?_, ?_⟩
  · exact mul_pos (mul_pos ha (pow_pos (lt_min base.pos one_pos) _)) (Real.exp_pos _)
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    intro x hx
    have hDleA : (edist (X.obj k).basepoint x).toReal ≤ A :=
      ENNReal.toReal_le_of_le_ofReal hA.le hx
    refine (hdec k x hx).mono ?_ ?_
    · exact mul_pos (mul_pos ha (pow_pos (lt_min base.pos one_pos) _)) (Real.exp_pos _)
    · have hmono : Real.exp (-C * A) ≤ Real.exp (-C * (edist (X.obj k).basepoint x).toReal) :=
        Real.exp_le_exp.mpr (by nlinarith [hC, hDleA])
      exact mul_le_mul_of_nonneg_left hmono
        (mul_nonneg ha.le (pow_nonneg (lt_min base.pos one_pos).le _))

theorem exists_uniform_injectivity_radius_on_ball_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : Real, 0 < A → ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (A : Real) (hA : 0 < A) :
    ∃ ρ : Real, 0 < ρ ∧ ∀ᶠ i in atTop,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      let _ : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
      ∀ x : (X.obj i).M,
        edist (X.obj i).basepoint x ≤ ENNReal.ofReal A →
          HasInjRadiusAt (I := I) (X.obj i) x ρ := by
  classical
  obtain ⟨C, hC, hbound⟩ := hjets (2 * A + 3) (by linarith) 0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound
  let σ : Nat → Nat := fun k => N + k
  let X' := X.subseq σ
  have hcomplete' : SeqMetricComplete (I := I) X' := hcomplete.subseq σ
  have hconn' : ∀ k : Nat,
      let _ : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      ConnectedSpace (X'.obj k).M := PointedRiemannianSeq.connected_subseq hconn σ
  have hinj' : BaseInjBound (I := I) X' := hinj.subseq σ
  have hrm' : ∀ k : Nat,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : T2Space (X'.obj k).M := (X'.obj k).t2
      letI : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
      ∀ y : (X'.obj k).M,
        edist (X'.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X'.obj k).metric y 4
          (metricRm04At (I := I) (M := (X'.obj k).M) (X'.obj k).metric y)) ≤ C := by
    intro k
    let : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    let : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    let : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    let : T2Space (X'.obj k).M := (X'.obj k).t2
    let : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
    let : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
    intro y hy
    have hy' : riemannianEDistOf (I := I) (X'.obj k).metric
        (X'.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) := by
      rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X'.obj k)]
      exact hy
    have hjet := hN (σ k) (Nat.le_add_right N k) y hy'
    exact (normSq0S_metricRm04At_le_curvDerivNorm (I := I)
      (X'.obj k).metric y).trans hjet
  have hpull' : ∀ k : Nat,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
      letI : T2Space (X'.obj k).M := (X'.obj k).t2
      letI : T2Space (TangentBundle I (X'.obj k).M) := (X'.obj k).t2TangentBundle
      letI : RiemannianBundle (fun y : (X'.obj k).M => TangentSpace I y) :=
        (X'.obj k).riemBundle (I := I)
      letI : (y : (X'.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
        (X'.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X'.obj k).M => TangentSpace I y) := (X'.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X'.obj k).M :=
        MetricComplete.complete (I := I) (X'.obj k) (hcomplete'.complete k)
      letI : IsRiemannianManifold I (X'.obj k).M := ⟨fun _ _ => rfl⟩
      ∀ (x : (X'.obj k).M)
        (hEnorm : ∀ (y : (X'.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X'.obj k).metric.inner y w w)))
        (q R : Real), 0 ≤ q → 0 < R →
        (∀ z, z ∈ Metric.ball (0 : E) R → z ≠ 0 →
          ∀ t, t ∈ Set.Ioo (0 : Real) 1 →
            ¬ IsConjVec (I := I) (X'.obj k).metric hEnorm x
              ((t • normalFrame (I := I) (X'.obj k).metric x z : TangentSpace I x) : E)) →
        ricciBoundedBelowOn (I := I) (X'.obj k).metric
          {y : (X'.obj k).M | riemannianEDist I x y < ENNReal.ofReal R}
          (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)) →
        intrinsicPullVol (I := I) (X'.obj k).metric hEnorm x R ≤
          (MeasureTheory.volume : MeasureTheory.Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) R) := by
    intro k
    let : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    let : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    let : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    let : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
    let : T2Space (X'.obj k).M := (X'.obj k).t2
    let : T2Space (TangentBundle I (X'.obj k).M) := (X'.obj k).t2TangentBundle
    let : RiemannianBundle (fun y : (X'.obj k).M => TangentSpace I y) :=
      (X'.obj k).riemBundle (I := I)
    let : (y : (X'.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X'.obj k).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun y : (X'.obj k).M => TangentSpace I y) := (X'.obj k).riemBundle_cont (I := I)
    let : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
    let : CompleteSpace (X'.obj k).M :=
      MetricComplete.complete (I := I) (X'.obj k) (hcomplete'.complete k)
    let : IsRiemannianManifold I (X'.obj k).M := ⟨fun _ _ => rfl⟩
    intro x hEnorm q R hq hR hno hRic
    exact intrinsicPullVol_le_hyperbolic_of_ricciBoundedBelowOn
      (I := I) (X'.obj k).metric hEnorm x hq hR hno hRic
  obtain ⟨ρ, hρ, hdec⟩ :=
    exists_pos_injectivity_radius_on_ball (I := I) X' hcomplete' hconn' hinj' A hA C hC hrm' hpull'
  refine ⟨ρ, hρ, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact hdec k

end CheegerGromovCompactness
end DifferentialGeometry
