import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SimplyConnectedSpaceForm
import DifferentialGeometry.Geometry.Metric.Sphere.Round.BallVolumeBound

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_isometry_roundSphereThree_of_constantCurvature
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]
    [T2Space Z] [CompactSpace Z] [SimplyConnectedSpace Z]
    (h : SmoothRiemannianMetric I3 Z)
    (hcc : ∀ z (v w : TangentSpace I3 z),
      metricRm04At h z (fun i : Fin 4 => ![v, w, w, v] i) =
        (1 / 6 : ℝ) * (h.inner z v v * h.inner z w w - (h.inner z v w) ^ 2)) :
    ∃ Φ : Z ≃ₘ⟮I3, I3⟯ RoundSphereThree, ∀ z (v w : TangentSpace I3 z),
      roundSphereThreeMetric.inner (Φ z) (mfderiv I3 I3 Φ z v) (mfderiv I3 I3 Φ z w) =
        h.inner z v w := by
  have hsec : ∀ x : Z, ∀ X Y : TangentSpace I3 x,
      metricRm04StandardAt (I := I3) (M := Z) h x X Y Y X =
        (1 / 6 : ℝ) * (h.inner x X X * h.inner x Y Y - h.inner x X Y * h.inner x X Y) := by
    intro x X Y
    have hvec : vec4 X Y Y X = (fun i : Fin 4 => ![X, Y, Y, X] i) := by
      funext i
      fin_cases i <;> simp [vec4]
    rw [metricRm04StandardAt_apply, hvec, hcc, sq]
  obtain ⟨Φ, hΦ⟩ := exists_isometry_round_sphere_of_constant_positive_sectional_curvature
    (I := I3) (M := Z) (n := 3) (by norm_num) (by simp [ThreeSpace]) h (1 / 6) (by norm_num) hsec
  refine ⟨Φ, fun z v w => ?_⟩
  change 6 * (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner (Φ z)
      (mfderiv I3 I3 Φ z v) (mfderiv I3 I3 Φ z w) = h.inner z v w
  rw [hΦ z v w]
  ring

theorem ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_roundSphereThree_univ :
    ENNReal.ofReal (8 * Real.sqrt 6 * Real.pi) ≤
      riemannianVolumeMeasure I3 RoundSphereThree roundSphereThreeMetric univ := by
  have hround := ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ
  have hscale := volume_scale_apply (I := I3) (M := RoundSphereThree) 6 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) univ
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hscale
  have hpow : ENNReal.ofReal (Real.sqrt 6) ^ 3 = ENNReal.ofReal (6 * Real.sqrt 6) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg 6)]
    congr 1
    have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    rw [pow_succ, hsq]
  have hconst : 8 * Real.sqrt 6 * Real.pi = 6 * Real.sqrt 6 * (4 * Real.pi / 3) := by ring
  change ENNReal.ofReal (8 * Real.sqrt 6 * Real.pi) ≤
    riemannianVolumeMeasure I3 RoundSphereThree
      (scaleMetric (I := I3) 6 (by norm_num)
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))) univ
  rw [hscale, hpow, hconst, ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' le_rfl hround

theorem ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_univ_of_constantCurvature
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]
    [T2Space Z] [CompactSpace Z] [SimplyConnectedSpace Z]
    (h : SmoothRiemannianMetric I3 Z)
    (hcc : ∀ z (v w : TangentSpace I3 z),
      metricRm04At h z (fun i : Fin 4 => ![v, w, w, v] i) =
        (1 / 6 : ℝ) * (h.inner z v v * h.inner z w w - (h.inner z v w) ^ 2)) :
    ENNReal.ofReal (8 * Real.sqrt 6 * Real.pi) ≤ riemannianVolumeMeasure I3 Z h univ := by
  obtain ⟨Φ, hΦ⟩ := exists_isometry_roundSphereThree_of_constantCurvature h hcc
  have hsand := riemannianVolumeMeasure_image_sandwich h roundSphereThreeMetric
    Φ.toPartialDiffeomorph isOpen_univ (subset_univ _) isCompact_univ (subset_univ _)
    one_pos one_pos
    (fun y _ v => by
      rw [one_mul]
      exact (hΦ y v v).symm.le)
    (fun y _ v => by
      rw [one_mul]
      exact (hΦ y v v).le)
  have himage : (Φ.toPartialDiffeomorph : Z → RoundSphereThree) '' univ = univ :=
    image_univ_of_surjective Φ.surjective
  have hupper := hsand.2
  rw [himage] at hupper
  have hone : ENNReal.ofReal (Real.sqrt (1 ^ Module.finrank ℝ ThreeSpace)) = 1 := by
    simp
  rw [hone, one_mul] at hupper
  exact ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_roundSphereThree_univ.trans
    hupper

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem SpatialRoundComponent.volume_lower_of_simplyConnected
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M} {U : Set M}
    (D : SpatialRoundComponent g eps x U) [SimplyConnectedSpace U] :
    ENNReal.ofReal (4 * Real.sqrt 3 * Real.pi /
        (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 M g U := by
  let _ := D.topology
  let _ := D.charted
  let _ := D.smooth
  let _ := D.t2
  let _ := D.compact
  set Q := metricScalarAt g x
  have hQ : 0 < Q := D.Q_pos
  let e : D.Z ≃ₜ U :=
    ((Homeomorph.Set.univ D.Z).symm.trans (Homeomorph.setCongr D.source_eq.symm)).trans
      (D.map.toOpenPartialHomeomorph.toHomeomorphSourceTarget.trans
        (Homeomorph.setCongr D.target_eq))
  let _ : SimplyConnectedSpace D.Z := e.toHomotopyEquiv.simplyConnectedSpace
  have hvolZ :=
    ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_univ_of_constantCurvature
      D.metric D.constant_curvature
  have hsand := riemannianVolumeMeasure_image_sandwich D.metric g D.map isOpen_univ
    (by rw [D.source_eq]) isCompact_univ (subset_univ _)
    (by positivity : (0 : ℝ) < 2 * Q) (by positivity : (0 : ℝ) < 2 / Q)
    (fun y _ v => by
      have hb := (D.metric_bounds y v).1
      nlinarith)
    (fun y _ v => by
      have hb := (D.metric_bounds y v).2
      rw [div_mul_eq_mul_div, le_div_iff₀ hQ]
      nlinarith)
  have himage : (D.map : D.Z → M) '' univ = U := by
    have h1 : (D.map : D.Z → M) '' univ = (D.map : D.Z → M) '' D.map.source := by
      rw [D.source_eq]
    exact h1.trans (D.map.toPartialEquiv.image_source_eq_target.trans D.target_eq)
  have hlower := hsand.1
  rw [himage] at hlower
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hlower
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsQ : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hsqrt : Real.sqrt ((2 * Q) ^ 3) = 2 * Real.sqrt 2 * (Q * Real.sqrt Q) := by
    have hnn : 0 ≤ 2 * Real.sqrt 2 * (Q * Real.sqrt Q) := by positivity
    rw [show (2 * Q) ^ 3 = (2 * Real.sqrt 2 * (Q * Real.sqrt Q)) ^ 2 by
      have hexp : (2 * Real.sqrt 2 * (Q * Real.sqrt Q)) ^ 2 =
          4 * Real.sqrt 2 ^ 2 * Q ^ 2 * Real.sqrt Q ^ 2 := by ring
      rw [hexp, hs2, hsQ]
      ring]
    exact Real.sqrt_sq hnn
  have hsix : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have hQs : 0 < Q * Real.sqrt Q := mul_pos hQ (Real.sqrt_pos.mpr hQ)
  have hprod : ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) *
      ENNReal.ofReal (4 * Real.sqrt 3 * Real.pi / (Q * Real.sqrt Q)) =
      ENNReal.ofReal (8 * Real.sqrt 6 * Real.pi) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsqrt, hsix]
    congr 1
    field_simp
    ring
  have hB0 : ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) ≠ 0 := by
    rw [hsqrt]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hchain : ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) *
      ENNReal.ofReal (4 * Real.sqrt 3 * Real.pi / (Q * Real.sqrt Q)) ≤
      ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) * riemannianVolumeMeasure I3 M g U := by
    rw [hprod]
    exact hvolZ.trans hlower
  exact (ENNReal.mul_le_mul_iff_right hB0 ENNReal.ofReal_ne_top).mp hchain

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
