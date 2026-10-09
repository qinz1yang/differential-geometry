import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Geometry.Metric.CylinderRotation
import DifferentialGeometry.Geometry.Metric.Pullback.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace (Metric.sphere (0 : E) 1 × ℝ) := borel _
private local instance : BorelSpace (Metric.sphere (0 : E) 1 × ℝ) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem roundCylinder_ball_isOpen (p : Metric.sphere (0 : E) 1 × ℝ) (r : ℝ) :
    IsOpen (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) p r) :=
  isOpen_lt (by
    unfold riemannianEDistOf
    exact Riemannian.continuous_riemannianEDist _ p) continuous_const

theorem riemannianVolumeMeasure_roundCylinder_ball_eq
    (p q : Metric.sphere (0 : E) 1 × ℝ) (r : ℝ) :
    riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
        (roundCylinderMetric (E := E) (n := n))
        (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) p r) =
      riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
        (roundCylinderMetric (E := E) (n := n))
        (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) q r) := by
  let e := (ℝ ∙ ((p.1 : E) - q.1))ᗮ.reflection
  let Φ := roundCylinderDiffeomorph (n := n) e (q.2 - p.2)
  have hΦ : Φ p = q := by
    rw [roundCylinderDiffeomorph_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact Submodule.reflection_sub
        ((mem_sphere_zero_iff_norm.mp p.1.property).trans
          (mem_sphere_zero_iff_norm.mp q.1.property).symm)
    · dsimp only
      ring
  let g := roundCylinderMetric (E := E) (n := n)
  have hmetric : Diffeomorph.pullbackMetric g Φ = g :=
    pullback_roundCylinderMetric_roundCylinderDiffeomorph e _
  have hpre : Φ.symm ⁻¹' riemannianBallOf g p r = riemannianBallOf g q r := by
    ext x
    have hd := Diffeomorph.pullbackMetric_edist g Φ p (Φ.symm x)
    rw [hmetric, hΦ, Φ.apply_symm_apply] at hd
    change riemannianEDistOf g p (Φ.symm x) < ENNReal.ofReal r ↔
      riemannianEDistOf g q x < ENNReal.ofReal r
    rw [hd]
  have hμ := riemannianVolumeMeasure_pullback g Φ
  rw [hmetric] at hμ
  have hh := congrArg (fun μ => μ (riemannianBallOf g p r)) hμ
  rw [Measure.map_apply Φ.symm.continuous.measurable (roundCylinder_ball_isOpen p r).measurableSet,
    hpre] at hh
  exact hh

theorem exists_pos_le_riemannianVolumeMeasure_roundCylinder_ball
    {r : ℝ} (hr : 0 < r) :
    ∃ v : ℝ, 0 < v ∧ ∀ p : Metric.sphere (0 : E) 1 × ℝ,
      ENNReal.ofReal v ≤
        riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
          (roundCylinderMetric (E := E) (n := n))
          (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) p r) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank ℝ E by rw [show Module.finrank ℝ E = n + 1 from Fact.out]; omega)
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1)).mpr zero_le_one
  let p : Metric.sphere (0 : E) 1 × ℝ := (⟨u, hu⟩, 0)
  let g := roundCylinderMetric (E := E) (n := n)
  let μ := riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ) g
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hpos : 0 < μ (riemannianBallOf g p r) := by
    apply (roundCylinder_ball_isOpen p r).measure_pos μ
    refine ⟨p, ?_⟩
    change riemannianEDistOf g p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨v, _, hv, hbound⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  refine ⟨v, ENNReal.ofReal_pos.mp hv, ?_⟩
  intro q
  exact hbound.le.trans_eq (riemannianVolumeMeasure_roundCylinder_ball_eq p q r)

end DifferentialGeometry.Geometry.Measure

namespace DifferentialGeometry.Geometry.Measure

open Bundle

open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]

private local instance : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ 2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem roundCylinder_ball_volume_mul_cube_le
    (p : Metric.sphere (0 : E) 1 × ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    riemannianVolumeMeasure ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
        (roundCylinderMetric (E := E) (n := 2))
        (riemannianBallOf (roundCylinderMetric (E := E) (n := 2)) p 1) * ENNReal.ofReal (r ^ 3) ≤
      riemannianVolumeMeasure ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
        (roundCylinderMetric (E := E) (n := 2))
        (riemannianBallOf (roundCylinderMetric (E := E) (n := 2)) p r) := by
  let I := (𝓡 2).prod 𝓘(ℝ)
  let M := Metric.sphere (0 : E) 1 × ℝ
  let g : SmoothRiemannianMetric I M := roundCylinderMetric (E := E) (n := 2)
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2) × ℝ)
      (TangentSpace I : M → Type _) := ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let _ : EMetricSpace M := EMetricSpace.ofT0PseudoEMetricSpace M
  let _ : IsRiemannianManifold I M := inferInstance
  have hmetric : g = (scaleMetric 2 (by norm_num) (Geometry.roundMetric (E := E) (n := 2))).prod
      (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    change (roundCylinderMetric (E := E) (n := 2)).inner x v w = _
    rw [roundCylinderMetric, cylinderMetric_inner, SmoothRiemannianMetric.prod_inner]
    congr 1
    change v.2 * w.2 = w.2 * v.2
    ring
  have hcomplete : RiemannianMetricComplete g := by
    rw [hmetric]
    exact (RiemannianMetricComplete.of_compact _).prod euclideanMetric_complete
  have hcompact : IsCompact (Metric.closedEBall p (ENNReal.ofReal (1 : ℝ))) := by
    have hset : Metric.closedEBall p (ENNReal.ofReal (1 : ℝ)) =
        {x : M | riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal 1} := by
      ext x
      rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I) p x]
      rfl
    rw [hset]
    exact hcomplete.closedEBall_isCompact p 1
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hbg := bishop_gromov_of_isCompact_closedEBall g hEnorm p
    (q := 0) (R := 1) (s := r) le_rfl hr hr1 hcompact (by
      intro y v _
      rw [ricciTensor_roundCylinder]
      simp only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, neg_zero, zero_mul]
      exact metric_inner_self_nonneg (Geometry.roundMetric (E := E) (n := 2)) y.1 v.1)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim, show (3 : ℕ) - 1 = 2 by decide, hyperbolicRadialVolume_zero,
    hyperbolicRadialVolume_zero] at hbg
  norm_num only [Nat.cast_ofNat, show (2 : ℕ) + 1 = 3 by decide, one_pow] at hbg
  have hmul := mul_le_mul' hbg (le_rfl : ENNReal.ofReal (3 : ℝ) ≤ ENNReal.ofReal (3 : ℝ))
  have hcoef : ENNReal.ofReal (r ^ 3 / 3) * ENNReal.ofReal (3 : ℝ) = ENNReal.ofReal (r ^ 3) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hr.le _) (by norm_num))]
    congr 1
    ring
  have hthird : ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (3 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    norm_num
  rw [mul_assoc, hcoef] at hmul
  have hrhs (v : ℝ≥0∞) : ENNReal.ofReal (1 / 3 : ℝ) * v * ENNReal.ofReal (3 : ℝ) = v := by
    calc
      _ = (ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (3 : ℝ)) * v := by ring
      _ = v := by rw [hthird, one_mul]
  rw [hrhs] at hmul
  exact hmul

theorem exists_pos_mul_cube_le_riemannianVolumeMeasure_roundCylinder_ball :
    ∃ ν : ℝ, 0 < ν ∧ ∀ p : Metric.sphere (0 : E) 1 × ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ENNReal.ofReal (ν * r ^ 3) ≤
        riemannianVolumeMeasure ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
          (roundCylinderMetric (E := E) (n := 2))
          (riemannianBallOf (roundCylinderMetric (E := E) (n := 2)) p r) := by
  obtain ⟨ν, hν, hvol⟩ := exists_pos_le_riemannianVolumeMeasure_roundCylinder_ball
    (E := E) (n := 2) (by norm_num : (0 : ℝ) < 1)
  refine ⟨ν, hν, fun p r hr hr1 => ?_⟩
  rw [ENNReal.ofReal_mul hν.le]
  exact (mul_le_mul' (hvol p) le_rfl).trans (roundCylinder_ball_volume_mul_cube_le p hr hr1)

end DifferentialGeometry.Geometry.Measure
