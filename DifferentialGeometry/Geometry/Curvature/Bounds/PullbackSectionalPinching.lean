import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalRestriction
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalPinching

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

private theorem sectional_pinching_of_localPullMetric
    (h : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) {l u : ℝ}
    (hlower : SectionalBoundedBelowAt (localPullMetric h f hf) x l)
    (hupper : ∀ v w : TangentSpace I x, LinearIndependent ℝ ![v, w] →
      sectionalCurvature (localPullMetric h f hf) x v w ≤ u) :
    SectionalBoundedBelowAt h (f x) l ∧
      ∀ v w : TangentSpace J (f x), LinearIndependent ℝ ![v, w] →
        sectionalCurvature h (f x) v w ≤ u := by
  let D := hf.mfderivToContinuousLinearEquiv (by simp) x
  have hD (v : TangentSpace I x) : D v = mfderiv I J f x v := rfl
  constructor
  · intro v w
    obtain ⟨a, rfl⟩ := D.surjective v
    obtain ⟨b, rfl⟩ := D.surjective w
    simpa only [hD, localPullMetric_inner, metricRm04StandardAt_localPullMetric] using
      hlower a b
  · intro v w hvw
    obtain ⟨a, rfl⟩ := D.surjective v
    obtain ⟨b, rfl⟩ := D.surjective w
    have hab : LinearIndependent ℝ ![a, b] := by
      have hm := hvw.map' D.symm.toLinearMap (LinearMap.ker_eq_bot.mpr D.symm.injective)
      convert hm using 1
      ext j
      fin_cases j <;> simp
    have hb := hupper a b hab
    rw [sectionalCurvature_eq_metricRm04StandardAt_div] at hb ⊢
    simpa only [hD, localPullMetric_inner, metricRm04StandardAt_localPullMetric] using hb

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness

universe uE uH uM uF uH' uN

theorem exists_pos_sectional_pinching_of_pullback_metricDerivNorm_le
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∃ ε > 0,
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] (H : Type uH) [TopologicalSpace H]
        (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] (H' : Type uH') [TopologicalSpace H']
        (J : ModelWithCorners ℝ F H') [J.Boundaryless]
        (N : Type uN) [TopologicalSpace N] [ChartedSpace H' N]
        [IsManifold J ∞ N] [T2Space N]
        (Φ : PartialDiffeomorph I J M N ∞) (U : TopologicalSpace.Opens M)
        (hU : (U : Set M) ⊆ Φ.source)
        (G : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (x : U),
        let hΦ := isLocalDiffeomorph_restrict_open (I := I) (J := J) U
          (fun y => Φ.isLocalDiffeomorphAt I J ∞ (hU y.property))
        (∀ k : ℕ, k ≤ 2 →
          metricDerivNorm k (localPullMetric h (fun y : U => Φ y) hΦ)
            (G.restrictOpen U) (G.restrictOpen U) x ≤ ε) →
        (∀ v w : TangentSpace I x, LinearIndependent ℝ ![v, w] →
          sectionalCurvature G (x : M) v w = -κ) →
        SectionalBoundedBelowAt h (Φ x) (-(κ + η)) ∧
          ∀ v w : TangentSpace J (Φ x), LinearIndependent ℝ ![v, w] →
            sectionalCurvature h (Φ x) v w ≤ -(κ - η) := by
  obtain ⟨ε, hε, hpinch⟩ :=
    exists_pos_sectional_pinching_of_metricDerivNorm_le.{uE, uH, uM} hκ hη
  refine ⟨ε, hε, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ F _ _ _ H' _ J _ N _ _ _ _ Φ U hU G h x
    hΦ hsmall hsec
  have hsecU (v w : TangentSpace I x) (hvw : LinearIndependent ℝ ![v, w]) :
      sectionalCurvature (G.restrictOpen U) x v w = -κ := by
    rw [sectionalCurvature_restrictOpen]
    exact hsec v w hvw
  have hb := hpinch E H I U (localPullMetric h (fun y : U => Φ y) hΦ)
    (G.restrictOpen U) x hsmall hsecU
  exact sectional_pinching_of_localPullMetric h (fun y : U => Φ y) hΦ x hb.1 hb.2

end DifferentialGeometry.Geometry.Curvature
