import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopShift
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Curvature and volume of the sphere loop, uniformly in the length (S-FIXTURE-C2b, K2, G2 file 2)

All constants come from the cylinder `S² × ℝ` through the shifted coverings of
`SphereLoopShift`, so none of them depends on the length `ℓ` or on the shift:

* `loopMetric_sectional_FXC2`: `sec ≥ 0` at every point (local pullback of the cylinder);
* `exists_loop_curvature_bounds_FXC2`: `∃ A, ∀ ℓ, ∀ k ≤ K, |∇ᵏ Rm| ≤ A` everywhere;
* `loopVolume_ge_cyl_FXC2`: the volume of the loop ball of radius `ε ≤ ℓ/2` at `π_a (z, 0)` is at
  least the volume of the cylinder ball at `(z, 0)` (the covering is injective on the ball);
* `exists_loop_volume_FXC2`: `∃ w > 0, ∀ ℓ ≥ 2ε, ∀ a, w ≤ vol B(π_a (z, 0), ε)`.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- A local diffeomorphism of every order is one of order `1`. -/
theorem isLocalDiffeomorph_one_of_top_FXC2 {E F H G M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace G] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) : IsLocalDiffeomorph I J 1 f := by
  intro x
  obtain ⟨Φ, hx, hΦ⟩ := hf x
  exact ⟨{ Φ with
    contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
    contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }, hx, hΦ⟩

theorem loopMetric_sectional_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (y : SphereLoop_FXC2) :
    SectionalBoundedBelowAt (loopMetric_FXC2 ℓ hℓ) y 0 := by
  obtain ⟨x, rfl⟩ := (loopCoverS_isCoveringMap_FXC2 ℓ 0 hℓ).2 y
  intro v w
  let D := (loopCoverS_isLocalDiffeomorph_FXC2 ℓ 0 hℓ).mfderivToContinuousLinearEquiv
    (by decide) x
  obtain ⟨v', rfl⟩ : ∃ v', D v' = v := ⟨D.symm v, D.apply_symm_apply v⟩
  obtain ⟨w', rfl⟩ : ∃ w', D w' = w := ⟨D.symm w, D.apply_symm_apply w⟩
  have h := slimSphereMetric_sectional_nonneg x v' w'
  have hr := Curvature.metricRm04StandardAt_localPullMetric (loopMetric_FXC2 ℓ hℓ)
    (loopCoverS_FXC2 ℓ 0) (loopCoverS_isLocalDiffeomorph_FXC2 ℓ 0 hℓ) x v' w' w' v'
  rw [localPull_loopMetricS_FXC2] at hr
  rw [zero_mul] at h ⊢
  exact hr ▸ h

theorem exists_loop_curvature_bounds_FXC2 (K : ℕ) :
    ∃ A : ℝ, ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), ∀ k ≤ K, ∀ y : SphereLoop_FXC2,
      curvDerivNorm k (loopMetric_FXC2 ℓ hℓ) y ≤ A := by
  obtain ⟨A, hA⟩ := exists_slimSphere_curvature_bounds K
  refine ⟨A, fun ℓ hℓ k hk y => ?_⟩
  obtain ⟨x, rfl⟩ := (loopCoverS_isCoveringMap_FXC2 ℓ 0 hℓ).2 y
  have h := curvDerivNorm_localPullMetric (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ 0)
    (loopCoverS_isLocalDiffeomorph_FXC2 ℓ 0 hℓ) k x
  rw [localPull_loopMetricS_FXC2] at h
  rw [← h]
  exact hA k hk x

theorem loopVolume_ge_cyl_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) {ε : ℝ} (hε : 0 < ε) (h2 : 2 * ε ≤ ℓ)
    (z : S2) :
    Integral.Measure.riemannianVolumeMeasure IC sphereCylinder slimSphereMetric
        (Metric.ball ((z, 0) : sphereCylinder) ε) ≤
      Integral.Measure.riemannianVolumeMeasure IC SphereLoop_FXC2 (loopMetric_FXC2 ℓ hℓ)
        {y | riemannianEDistOf (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a (z, 0)) y <
          ENNReal.ofReal ε} := by
  let _ : MeasurableSpace sphereCylinder := borel _
  have _ : BorelSpace sphereCylinder := ⟨rfl⟩
  set U : Set sphereCylinder := Metric.ball ((z, 0) : sphereCylinder) ε with hU
  have hf1 : IsLocalDiffeomorphOn IC IC 1 (loopCoverS_FXC2 ℓ a) U :=
    (isLocalDiffeomorph_one_of_top_FXC2
      (loopCoverS_isLocalDiffeomorph_FXC2 ℓ a hℓ)).isLocalDiffeomorphOn U
  have hnear : ∀ x ∈ U, |x.2| < ε := fun x hx => by
    have h1 := cyl_snd_le_dist_FXC2 x (z, 0)
    have h2 : dist x (z, 0) < ε := hx
    exact lt_of_le_of_lt (by simpa using h1) h2
  have hinj : Set.InjOn (loopCoverS_FXC2 ℓ a) U := by
    intro x hx y hy hxy
    obtain ⟨h1, n, hn⟩ := (loopCoverS_eq_iff_FXC2 a hℓ).mp hxy
    have hxn := hnear x hx
    have hyn := hnear y hy
    have hnl : |(n : ℝ) * ℓ| < ℓ := by
      have : (n : ℝ) * ℓ = y.2 - x.2 := by linarith
      rw [this]
      calc |y.2 - x.2| ≤ |y.2| + |x.2| := abs_sub _ _
        _ < ε + ε := add_lt_add hyn hxn
        _ ≤ ℓ := by linarith
    have hn0 : n = 0 := by
      by_contra hne
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
        exact_mod_cast this
      rw [abs_mul, abs_of_pos hℓ] at hnl
      nlinarith
    subst hn0
    exact Prod.ext h1 (by simpa using hn.symm)
  obtain ⟨Φ, hs, ht, hΦ⟩ := hf1.exists_partialDiffeomorph_of_injOn Metric.isOpen_ball
    ⟨(z, 0), mem_ball_self hε⟩ hinj
  have hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace IC x, slimSphereMetric.inner x v w =
      (loopMetric_FXC2 ℓ hℓ).inner (Φ.toPartialEquiv x) (mfderiv IC IC Φ.toPartialEquiv x v)
        (mfderiv IC IC Φ.toPartialEquiv x w) := by
    intro x _ v w
    have hfun : (Φ.toPartialEquiv : sphereCylinder → SphereLoop_FXC2) = loopCoverS_FXC2 ℓ a := hΦ
    rw [hfun]
    exact (loopCoverS_inner_FXC2 ℓ a hℓ x v w).symm
  have hvol := Integral.Measure.riemannianVolumeMeasure_image_of_partialIsometry
    slimSphereMetric (loopMetric_FXC2 ℓ hℓ) Φ hmet (A := U) Metric.isOpen_ball.measurableSet
    (by rw [hs])
  have hfun : (Φ.toPartialEquiv : sphereCylinder → SphereLoop_FXC2) = loopCoverS_FXC2 ℓ a := hΦ
  rw [hfun] at hvol
  rw [hvol]
  refine MeasureTheory.measure_mono ?_
  rintro _ ⟨x, hx, rfl⟩
  have hd := loopDist_le_cylS_FXC2 ℓ a hℓ x (z, 0)
  change riemannianEDistOf (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a (z, 0))
    (loopCoverS_FXC2 ℓ a x) < ENNReal.ofReal ε
  have hx' : dist x (z, 0) < ε := hx
  rw [riemannianEDistOf_comm]
  have hne := riemannianEDistOf_ne_top (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a x)
    (loopCoverS_FXC2 ℓ a (z, 0))
  rw [← ENNReal.ofReal_toReal hne]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (lt_of_le_of_lt hd hx')

theorem exists_loop_volume_FXC2 {ε : ℝ} (hε : 0 < ε) (z : S2) :
    ∃ w : ℝ, 0 < w ∧ ∀ (ℓ a : ℝ) (hℓ : 0 < ℓ), 2 * ε ≤ ℓ →
      ENNReal.ofReal w ≤
        Integral.Measure.riemannianVolumeMeasure IC SphereLoop_FXC2 (loopMetric_FXC2 ℓ hℓ)
          {y | riemannianEDistOf (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a (z, 0)) y <
            ENNReal.ofReal ε} := by
  have hpos : MeasureTheory.Measure.IsOpenPosMeasure
      (Integral.Measure.riemannianVolumeMeasure IC sphereCylinder slimSphereMetric) :=
    Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure slimSphereMetric
  have h0 : 0 < Integral.Measure.riemannianVolumeMeasure IC sphereCylinder slimSphereMetric
      (Metric.ball ((z, 0) : sphereCylinder) ε) :=
    Metric.isOpen_ball.measure_pos _ ⟨(z, 0), mem_ball_self hε⟩
  obtain ⟨w, hw, hwμ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h0
  refine ⟨(w : ℝ), by exact_mod_cast hw, fun ℓ a hℓ h2 => ?_⟩
  exact (by simpa using hwμ.le : ENNReal.ofReal (w : ℝ) ≤ _).trans
    (loopVolume_ge_cyl_FXC2 ℓ a hℓ hε h2 z)

end DifferentialGeometry.Geometry.Collapse
