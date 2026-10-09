import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AdditiveDistance
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance scalarBoundAdditiveDistanceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem ricciFlow_additive_distance_bound_of_scalar_upper
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    (hconnected : ConnectedSpace M) {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ s ∈ Icc a b,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hoperator : ∀ s ∈ Icc a b, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric s) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hscalar : ∀ s ∈ Icc a b, ∀ x : M, S.scalar s x ≤ C) (x y : M) :
    0 ≤ (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
      (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ∧
    (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
        (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ≤
      (10 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * C) * (b - a) := by
  let d : ℝ := (Module.finrank ℝ E : ℝ) - 1
  have hd : 0 < d := by
    have htwo : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    dsimp only [d]
    linarith
  have hRic : ∀ s ∈ Icc a b, ∀ z : M, ∀ v : TangentSpace I z,
      0 ≤ S.ricciAt s z (vec2 v v) ∧
        S.ricciAt s z (vec2 v v) ≤ d * (C / d) * (S.base.metric s).inner z v v := by
    intro s hs z v
    change 0 ≤ metricRicciAt (I := I) (S.base.metric s) z (vec2 v v) ∧
      metricRicciAt (I := I) (S.base.metric s) z (vec2 v v) ≤
        d * (C / d) * (S.base.metric s).inner z v v
    refine ⟨metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (S.base.metric s) z (hoperator s hs z) v, ?_⟩
    rw [mul_div_cancel₀ C hd.ne']
    have hupper := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (S.base.metric s) z (hoperator s hs z) v
    have hR : metricScalarAt (I := I) (S.base.metric s) z ≤ C := hscalar s hs z
    have hRhalf : metricScalarAt (I := I) (S.base.metric s) z / 2 ≤ C := by linarith
    have hv : 0 ≤ (S.base.metric s).inner z v v := by
      by_cases hz : v = 0
      · simp [hz]
      · exact ((S.base.metric s).pos z v hz).le
    exact hupper.trans (mul_le_mul_of_nonneg_right hRhalf hv)
  have hraw := ricciFlow_additive_distance_bound_of_ricci_upper S hS hdim hconnected
    hab (div_nonneg hC hd.le) hslab hregular hcomplete hRic x y
  have hsq : (d * Real.sqrt (C / d)) ^ 2 = d * C := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hC hd.le)]
    calc
      d ^ 2 * (C / d) = d * (d * (C / d)) := by ring
      _ = d * C := by rw [mul_div_cancel₀ C hd.ne']
  have hfactor : d * Real.sqrt (C / d) = Real.sqrt (d * C) := by
    calc
      d * Real.sqrt (C / d) = Real.sqrt ((d * Real.sqrt (C / d)) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg hd.le (Real.sqrt_nonneg _))).symm
      _ = Real.sqrt (d * C) := congrArg Real.sqrt hsq
  have hconstant : (10 / 3 : ℝ) * d * Real.sqrt (C / d) * (b - a) =
      (10 / 3 : ℝ) * Real.sqrt (d * C) * (b - a) := by
    calc
      _ = (10 / 3 : ℝ) * (d * Real.sqrt (C / d)) * (b - a) := by ring
      _ = _ := by rw [hfactor]
  change 0 ≤ (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
      (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ∧
    (riemannianEDistOf (I := I) (S.base.metric a) x y).toReal -
        (riemannianEDistOf (I := I) (S.base.metric b) x y).toReal ≤
      (10 / 3 : ℝ) * d * Real.sqrt (C / d) * (b - a) at hraw
  rw [hconstant] at hraw
  exact hraw

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
