import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.Metric.CompactSourceLipschitz
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

section

noncomputable section

open Manifold Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem diskMapEnergyDensity_comp_eq_pullback
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {z : ℂ → F} {x : ℂ}
    (hr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (z x))
    (hz : DifferentiableAt ℝ z x) :
    diskMapEnergyDensity g (r ∘ z) x =
      (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
        pullbackMetricCoefficients g r (z x)
          (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2 := by
  have hchain : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (r ∘ z) x =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (z x)).comp (fderiv ℝ z x) := by
    rw [mfderiv_comp x hr hz.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  simp only [diskMapEnergyDensity, diskMapPartial, hchain,
    pullbackMetricCoefficients_apply, Function.comp_apply]
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_riemannian_lipschitz_disk_of_lipschitz_retraction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ) :
    ∃ C : ℝ≥0, ∀ (z : ℂ → F) (L : ℝ≥0), LipschitzWith L z →
      MapsTo z (Metric.closedBall (0 : ℂ) 1) (range Φ) →
      ∀ (γ : freeLoop M) (τ : C(loopCircle, loopCircle)),
        (∀ θ, z (diskBoundary θ) = Φ (γ (τ θ))) →
        ∃ u : C(closedDisk, M),
          (∀ x, u x = r (z x)) ∧
          (∀ x, Φ (u x) = z x) ∧
          (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (↑(C * L) : ℝ≥0∞) * edist x y) ∧
          diskTrace u = γ.comp τ ∧
          IntegrableOn (diskMapEnergyDensity g (diskExtension u))
            (Metric.closedBall (0 : ℂ) 1) ∧
          IntegrableOn (fun x =>
            (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
              pullbackMetricCoefficients g r (z x)
                (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2)
            (Metric.closedBall (0 : ℂ) 1) ∧
          (∫ x in Metric.closedBall (0 : ℂ) 1,
            diskMapEnergyDensity g (diskExtension u) x) =
          ∫ x in Metric.closedBall (0 : ℂ) 1,
            (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
              pullbackMetricCoefficients g r (z x)
                (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2 := by
  obtain ⟨C, hC⟩ := exists_compact_source_riemannian_lipschitz g hU hr
    (isCompact_range hΦ) hΦU
  refine ⟨C, fun z L hz hzΦ γ τ htrace => ?_⟩
  have hzU : ∀ x : closedDisk, z x ∈ U := fun x => hΦU (hzΦ x.property)
  let u : C(closedDisk, M) :=
    ⟨fun x => r (z x),
      hr.continuousOn.comp_continuous (hz.continuous.comp continuous_subtype_val) hzU⟩
  have hu (x : closedDisk) : u x = r (z x) := rfl
  have hΦu (x : closedDisk) : Φ (u x) = z x := by
    obtain ⟨p, hp⟩ := hzΦ x.property
    rw [hu, ← hp, hleft p]
  have hLip (x y : closedDisk) :
      riemannianEDistOf g (u x) (u y) ≤ (↑(C * L) : ℝ≥0∞) * edist x y := by
    apply (hC (z x) (hzΦ x.property) (z y) (hzΦ y.property)).trans
    calc
      (C : ℝ≥0∞) * edist (z x) (z y) ≤
          (C : ℝ≥0∞) * ((L : ℝ≥0∞) * edist (x : ℂ) (y : ℂ)) := by
        gcongr
        exact hz x y
      _ = (↑(C * L) : ℝ≥0∞) * edist x y := by
        simp only [ENNReal.coe_mul, mul_assoc, Subtype.edist_eq]
  have ht : diskTrace u = γ.comp τ := by
    ext θ
    change r (z (diskBoundary θ)) = γ (τ θ)
    rw [htrace θ, hleft]
  have he : IntegrableOn (diskMapEnergyDensity g (diskExtension u))
      (Metric.closedBall (0 : ℂ) 1) := integrable_diskMapEnergyDensity g hLip
  have heq : diskMapEnergyDensity g (diskExtension u) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)] fun x =>
        (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
          pullbackMetricCoefficients g r (z x)
            (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2 := by
    filter_upwards [ae_disk_interior, ae_restrict_of_ae hz.ae_differentiableAt] with x hx hdx
    have hxr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (z x) :=
      ((hr (z x) (hΦU (hzΦ (Metric.ball_subset_closedBall hx)))).contMDiffAt
        (hU.mem_nhds (hΦU (hzΦ (Metric.ball_subset_closedBall hx))))).mdifferentiableAt
          one_ne_zero
    have hloc : diskExtension u =ᶠ[𝓝 x] r ∘ z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      exact diskExtension_coe u ⟨y, Metric.ball_subset_closedBall hy⟩
    have henergy : diskMapEnergyDensity g (diskExtension u) x =
        diskMapEnergyDensity g (r ∘ z) x := by
      unfold diskMapEnergyDensity diskMapPartial
      rw [hloc.mfderiv_eq, hloc.eq_of_nhds]
      rfl
    exact henergy.trans (diskMapEnergyDensity_comp_eq_pullback g hxr hdx)
  exact ⟨u, hu, hΦu, hLip, ht, he, he.congr heq, integral_congr_ae heq⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Manifold Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T3Space M] [PreconnectedSpace M]

theorem exists_riemannian_lipschitz_disk_of_compact_source
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {r : F → M} {U K : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ (z : ℂ → F) (L : ℝ≥0), LipschitzWith L z →
      MapsTo z (Metric.closedBall (0 : ℂ) 1) K →
      ∀ (γ : freeLoop M) (τ : C(loopCircle, loopCircle)),
        (∀ θ, r (z (diskBoundary θ)) = γ (τ θ)) →
        ∃ u : C(closedDisk, M),
          (∀ x, u x = r (z x)) ∧
          (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (↑(C * L) : ℝ≥0∞) * edist x y) ∧
          diskTrace u = γ.comp τ ∧
          IntegrableOn (diskMapEnergyDensity g (diskExtension u))
            (Metric.closedBall (0 : ℂ) 1) ∧
          IntegrableOn (fun x =>
            (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
              pullbackMetricCoefficients g r (z x)
                (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2)
            (Metric.closedBall (0 : ℂ) 1) ∧
          riemannianDiskEnergy g u =
            ∫ x in Metric.closedBall (0 : ℂ) 1,
              (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
                pullbackMetricCoefficients g r (z x)
                  (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2 := by
  obtain ⟨C, hC⟩ := exists_compact_source_riemannian_lipschitz g hU hr hK hKU
  refine ⟨C, fun z L hz hzK γ τ htrace => ?_⟩
  have hzU : ∀ x : closedDisk, z x ∈ U := fun x => hKU (hzK x.property)
  let u : C(closedDisk, M) :=
    ⟨fun x => r (z x),
      hr.continuousOn.comp_continuous (hz.continuous.comp continuous_subtype_val) hzU⟩
  have hu (x : closedDisk) : u x = r (z x) := rfl
  have hLip (x y : closedDisk) :
      riemannianEDistOf g (u x) (u y) ≤ (↑(C * L) : ℝ≥0∞) * edist x y := by
    apply (hC (z x) (hzK x.property) (z y) (hzK y.property)).trans
    calc
      (C : ℝ≥0∞) * edist (z x) (z y) ≤
          (C : ℝ≥0∞) * ((L : ℝ≥0∞) * edist (x : ℂ) (y : ℂ)) := by
        gcongr
        exact hz x y
      _ = (↑(C * L) : ℝ≥0∞) * edist x y := by
        simp only [ENNReal.coe_mul, mul_assoc, Subtype.edist_eq]
  have ht : diskTrace u = γ.comp τ := by
    ext θ
    exact htrace θ
  have he := integrable_diskMapEnergyDensity g hLip
  have heq : diskMapEnergyDensity g (diskExtension u) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)] fun x =>
        (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
          pullbackMetricCoefficients g r (z x)
            (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2 := by
    filter_upwards [ae_disk_interior, ae_restrict_of_ae hz.ae_differentiableAt] with x hx hdx
    have hzU : z x ∈ U := hKU (hzK (Metric.ball_subset_closedBall hx))
    have hxr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (z x) :=
      (hr.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt one_ne_zero
    have hloc : diskExtension u =ᶠ[𝓝 x] r ∘ z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      exact diskExtension_coe u ⟨y, Metric.ball_subset_closedBall hy⟩
    have henergy : diskMapEnergyDensity g (diskExtension u) x =
        diskMapEnergyDensity g (r ∘ z) x := by
      unfold diskMapEnergyDensity diskMapPartial
      rw [hloc.mfderiv_eq, hloc.eq_of_nhds]
      rfl
    exact henergy.trans (diskMapEnergyDensity_comp_eq_pullback g hxr hdx)
  exact ⟨u, hu, hLip, ht, he, he.congr heq, integral_congr_ae heq⟩

end DifferentialGeometry.Geometry

end

end
