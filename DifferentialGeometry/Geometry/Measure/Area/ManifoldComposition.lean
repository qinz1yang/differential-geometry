import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher










noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
theorem riemannianAreaDensity_eq_zero_of_model_subsingleton [Subsingleton E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℂ → M) (z : ℂ) :
    riemannianAreaDensity g u z = 0 := by
  let : Subsingleton (TangentSpace 𝓘(ℝ, E) (u z)) := ‹Subsingleton E›
  have hzero : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z = 0 := by ext; exact Subsingleton.elim _ _
  simp [riemannianAreaDensity, hzero, tangentTwoJacobian]

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem eventuallyEq_const_of_model_subsingleton [Subsingleton E]
    {X : Type*} [TopologicalSpace X] {u : X → M} {x : X} (hu : ContinuousAt u x) :
    u =ᶠ[𝓝 x] (fun _ => u x) := by
  filter_upwards [hu ((chartAt E (u x)).open_source.mem_nhds (mem_chart_source E (u x)))] with y hy
  exact (chartAt E (u x)).injOn hy (mem_chart_source E (u x)) (Subsingleton.elim _ _)

theorem riemannian_lipschitz_comp {X : Type*} [PseudoEMetricSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    {u : X → M} {f : M → N} {C L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (x y : X) : riemannianEDistOf h ((f ∘ u) x) ((f ∘ u) y) ≤
      (↑(L * C) : ℝ≥0∞) * edist x y := by
  apply (hf (u x) (u y)).trans
  calc
    (L : ℝ≥0∞) * riemannianEDistOf g (u x) (u y) ≤
        (L : ℝ≥0∞) * ((C : ℝ≥0∞) * edist x y) := by gcongr; exact hu x y
    _ = (↑(L * C) : ℝ≥0∞) * edist x y := by simp only [ENNReal.coe_mul, mul_assoc]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T3Space M] [T3Space N]

set_option backward.isDefEq.respectTransparency false in

theorem riemannianAreaDensity_comp_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    {u : ℂ → M} {f : M → N} {z : ℂ} {L : ℝ≥0}
    (hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z)
    (hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (f ∘ u) z)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y) :
    riemannianAreaDensity h (f ∘ u) z ≤ (L : ℝ) ^ 2 * riemannianAreaDensity g u z := by
  by_cases hF : Module.finrank ℝ F = 0
  · let : Subsingleton F := Module.finrank_zero_iff.mp hF
    rw [riemannianAreaDensity_eq_zero_of_model_subsingleton]
    exact mul_nonneg (sq_nonneg _) (riemannianAreaDensity_nonneg g u z)
  let : NeZero (Module.finrank ℝ F) := ⟨hF⟩
  by_cases hE : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hE
    have heq : (f ∘ u) =ᶠ[𝓝 z] (fun _ => f (u z)) :=
      (eventuallyEq_const_of_model_subsingleton (E := E) hu.continuousAt).fun_comp f
    rw [riemannianAreaDensity_congr h heq, riemannianAreaDensity_const]
    exact mul_nonneg (sq_nonneg _) (riemannianAreaDensity_nonneg g u z)
  let : NeZero (Module.finrank ℝ E) := ⟨hE⟩
  apply tangentTwoJacobian_le_of_combinations g h L.coe_nonneg
  intro a b
  have hb := metric_differential_le_of_edist_le g h hu hcomp (fun y => hf (u z) (u y))
    (a • (1 : ℂ) + b • Complex.I)
  simpa only [map_add, map_smul] using hb

variable [CompactSpace M] [CompactSpace N]


theorem ae_riemannianAreaDensity_comp_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    {u : ℂ → M} {f : M → N} {C L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y) :
    ∀ᵐ z ∂volume, riemannianAreaDensity h (f ∘ u) z ≤
      (L : ℝ) ^ 2 * riemannianAreaDensity g u z := by
  filter_upwards [ae_mdifferentiableAt_of_riemannian_lipschitz g hu,
    ae_mdifferentiableAt_of_riemannian_lipschitz h (riemannian_lipschitz_comp g h hu hf)] with z hz hcomp
  exact riemannianAreaDensity_comp_le g h hz hcomp hf


theorem riemannianArea_comp_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    {u : ℂ → M} {f : M → N} {C L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (s : Set ℂ) [IsFiniteMeasure (volume.restrict s)] :
    riemannianArea h (f ∘ u) s ≤ (L : ℝ) ^ 2 * riemannianArea g u s := by
  have hi := integral_mono_ae
    (integrableOn_riemannianAreaDensity_of_lipschitz h (riemannian_lipschitz_comp g h hu hf) s)
    ((integrableOn_riemannianAreaDensity_of_lipschitz g hu s).const_mul ((L : ℝ) ^ 2))
    (ae_restrict_of_ae (ae_riemannianAreaDensity_comp_le g h hu hf))
  simpa only [integral_const_mul, riemannianArea] using hi

local instance : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
  isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne


theorem riemannianDiskArea_comp_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    {u : closedDisk → M} {f : M → N} {C L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y) :
    riemannianDiskArea h (f ∘ u) ≤ (L : ℝ) ^ 2 * riemannianDiskArea g u :=
  riemannianArea_comp_le g h (diskExtension_riemannian_lipschitz g hu) hf _

end DifferentialGeometry.Geometry
