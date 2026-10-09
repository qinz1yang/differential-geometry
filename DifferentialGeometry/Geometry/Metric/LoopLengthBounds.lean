import DifferentialGeometry.Geometry.Metric.CurveVariation
import DifferentialGeometry.Geometry.Metric.LoopDistance
import DifferentialGeometry.Topology.LoopSpace.Lipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry Function
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem riemannianCurveSpeed_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) (t : ℝ) :
    riemannianCurveSpeed g (fun _ => q) t = 0 := by
  unfold riemannianCurveSpeed
  rw [mfderiv_const]
  change Real.sqrt (g.inner q 0 0) = 0
  simp only [map_zero, Real.sqrt_zero]


theorem riemannianCurveLength_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : M) (a b : ℝ) : riemannianCurveLength g (fun _ => q) a b = 0 := by
  simp [riemannianCurveLength, riemannianCurveELength, riemannianCurveSpeed_const]

variable [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem loopPoint_edist_le_length (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (θ : loopCircle) :
    riemannianEDistOf g (γ 0) (γ θ) ≤
      ENNReal.ofReal (riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1) := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hγ' : LipschitzWith C γ := hγ
  have hr : LipschitzWith C (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! hγ'.comp loopCircle_projection_lipschitz
  have hvar := riemannianCurveVariation_eq_elength g hr 0 1
  change eVariationOn (fun t : ℝ => γ (t : loopCircle)) (Icc 0 1) =
    riemannianCurveELength g (fun t => γ (t : loopCircle)) 0 1 at hvar
  rw [riemannianCurveLength,
    ENNReal.ofReal_toReal (riemannianCurveELength_ne_top_of_lipschitz g hr 0 1), ← hvar]
  let a := AddCircle.equivIco (1 : ℝ) 0 θ
  have ha : (a.val : loopCircle) = θ := AddCircle.coe_equivIco
  have hamem : a.val ∈ Icc (0 : ℝ) 1 := ⟨a.property.1, by simpa only [zero_add] using a.property.2.le⟩
  change edist (γ 0) (γ θ) ≤ _
  rw [← ha]
  exact eVariationOn.edist_le (fun t : ℝ => γ (t : loopCircle))
    (x := 0) (y := a.val) ⟨le_rfl, zero_le_one⟩ hamem



theorem loopDistance_from_constant_le_length (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y) :
    (riemannianLoopDistance g (ContinuousMap.const loopCircle (γ 0)) γ : ℝ) ≤
      riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 := by
  have h : (riemannianLoopDistance g (ContinuousMap.const loopCircle (γ 0)) γ : ℝ≥0∞) ≤
      ENNReal.ofReal (riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1) := by
    rw [riemannianLoopDistance_coe]
    exact iSup_le (fun θ => loopPoint_edist_le_length g γ hγ θ)
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (riemannianCurveLength_nonneg g _ _ _)] using h'

end DifferentialGeometry.Geometry
