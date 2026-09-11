import DifferentialGeometry.Topology.LoopSpace.PeriodicDescent
import DifferentialGeometry.Topology.LoopSpace.Lipschitz
import DifferentialGeometry.Geometry.Metric.CompactSourceCurves
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz










noncomputable section

open Set Function ContinuousMap Manifold Bundle DifferentialGeometry
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smoothing_metric_lipschitz_constant
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) {r : F → M} {U S : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ≥0, ∀ (φ : ContDiffBump (0 : ℝ)) (γ : freeLoop M) (V : ℝ≥0),
      (∀ θ η, riemannianEDistOf g (γ θ) (γ η) ≤ (V : ℝ≥0∞) * edist θ η) →
      (∀ θ, averagedLoop φ ((⟨e, he.continuous⟩ : C(M, F)).comp γ) θ ∈ S) →
      ∀ θ η, riemannianEDistOf g
        (r (averagedLoop φ ((⟨e, he.continuous⟩ : C(M, F)).comp γ) θ))
        (r (averagedLoop φ ((⟨e, he.continuous⟩ : C(M, F)).comp γ) η)) ≤
          ((C * V : ℝ≥0) : ℝ≥0∞) * edist θ η := by
  obtain ⟨Ce, _, hCe⟩ := DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff g he
  obtain ⟨Cr, hCr⟩ := DifferentialGeometry.Geometry.exists_compact_source_curve_lipschitz g hU hr hS hSU
  refine ⟨Cr * Ce, fun φ γ V hγ hregion θ η => ?_⟩
  let A : freeLoop F := (⟨e, he.continuous⟩ : C(M, F)).comp γ
  have hA : LipschitzWith (Ce * V) A := by
    intro θ η
    calc
      edist (A θ) (A η) ≤ (Ce : ℝ≥0∞) * riemannianEDistOf g (γ θ) (γ η) := hCe _ _
      _ ≤ (Ce : ℝ≥0∞) * ((V : ℝ≥0∞) * edist θ η) := by gcongr; exact hγ θ η
      _ = ((Ce * V : ℝ≥0) : ℝ≥0∞) * edist θ η := by rw [ENNReal.coe_mul, mul_assoc]
  have hAlift : LipschitzWith (Ce * V) (fun t : ℝ => A (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using hA.comp loopCircle_projection_lipschitz
  let b := DifferentialGeometry.Analysis.smoothPeriodic φ (fun t : ℝ => A (t : loopCircle))
  have hb : ContDiff ℝ 1 b :=
    (DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ hAlift.continuous).of_le (by exact_mod_cast le_top)
  have hbLip := DifferentialGeometry.Analysis.smoothPeriodic_lipschitz φ hAlift
  have hbS (t : ℝ) : b t ∈ S := hregion (t : loopCircle)
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hrlift : LipschitzWith (Cr * (Ce * V))
      (fun t : ℝ => r (averagedLoop φ A (t : loopCircle))) :=
    fun x y => hCr (Ce * V) b hb hbLip hbS x y
  have hresult := (loop_lipschitz_of_lift (γ := fun θ => r (averagedLoop φ A θ)) hrlift).edist_le_mul θ η
  simpa only [mul_assoc, A] using! hresult

end DifferentialGeometry.Topology
