import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Filter
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped ContDiff _root_.Manifold _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem centralVariationAcceleration_eq_zero_of_geodesic_germ
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (b : ℝ)
    {beta : ℝ → M}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u ↦ f u b) 0)
    (hbeta : HasGeodesicEquationAt (I := I) g beta 0)
    (heq : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta) :
    centralVariationAcceleration (I := I) g f b = 0 := by
  exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
    (I := I) g (fun u ↦ f u b) 0 hf
    (HasGeodesicEquationAt.congr_of_eventuallyEq_at heq.eq_of_nhds heq hbeta)

theorem centralVariationAcceleration_eq_zero_of_isGeodesicAt_germ
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (b : ℝ) {beta : ℝ → M}
    (hbeta : IsGeodesicAt (I := I) g beta 0)
    (heq : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta) :
    centralVariationAcceleration (I := I) g f b = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun u ↦ f u b) := by
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ ↦ (u, b)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  exact centralVariationAcceleration_eq_zero_of_geodesic_germ g f b
    (hcurve.contMDiffAt.of_le
      (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8)))
    (IsGeodesicAt.hasGeodesicEquationAt (I := I) g hbeta) heq

theorem centralVariationAcceleration_eq_zero_of_eventually_constant
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (c : ℝ) (p : M)
    (heq : (fun u ↦ f u c) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ p) :
    centralVariationAcceleration (I := I) g f c = 0 := by
  have hvel : ∀ᶠ u in 𝓝 (0 : ℝ),
      mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r c) u (1 : ℝ) =
        (0 : TangentSpace I (f u c)) := by
    filter_upwards [heq.eventually_nhds] with u hu
    have hueq : (fun r ↦ f r c) =ᶠ[𝓝 u] fun _ ↦ p := hu
    rw [hueq.mfderiv_eq, mfderiv_const]
    rfl
  change covDerivAlong (I := I) g (fun u ↦ f u c)
    (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r c) u (1 : ℝ)) 0 = 0
  calc
    _ = covDerivAlong (I := I) g (fun u ↦ f u c)
        (fun u ↦ (0 : TangentSpace I (f u c))) 0 :=
      covDerivAlong_congr_of_eventuallyEq (I := I) g (fun u ↦ f u c) hvel
    _ = 0 := covDerivAlong_zero (I := I) g (fun u ↦ f u c) 0

end DifferentialGeometry.Geometry.Riemannian.Variation
