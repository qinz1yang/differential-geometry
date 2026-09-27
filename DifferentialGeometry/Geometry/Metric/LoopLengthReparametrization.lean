import DifferentialGeometry.Geometry.Metric.CurveLengthReparametrization
import DifferentialGeometry.Geometry.Metric.LoopDistance
import DifferentialGeometry.Topology.LoopSpace.AffineLift



noncomputable section

open Bundle Manifold Set DifferentialGeometry Function
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem loop_length_comp_affineCircleMap (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C D : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {ψ : ℝ → ℝ} (hc : Continuous ψ) (hm : Monotone ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    (hcomp : ∀ x y, riemannianEDistOf g (γ (affineCircleMap ψ hc hp x))
      (γ (affineCircleMap ψ hc hp y)) ≤ (D : ℝ≥0∞) * edist x y) :
    riemannianCurveLength g (fun t : ℝ => γ (affineCircleMap ψ hc hp (t : loopCircle))) 0 1 =
      riemannianCurveLength g (fun t : ℝ => γ (t : loopCircle)) 0 1 := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hγ' : LipschitzWith C γ := hγ
  have hcomp' : LipschitzWith D (γ ∘ affineCircleMap ψ hc hp) := hcomp
  have hγreal : LipschitzWith C (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! hγ'.comp loopCircle_projection_lipschitz
  have hcompreal : LipschitzWith D (fun t : ℝ => γ (ψ t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def, affineCircleMap_coe] using!
      hcomp'.comp loopCircle_projection_lipschitz
  have hperiod : Periodic (fun t : ℝ => γ (t : loopCircle)) 1 := by
    intro t
    simp only [QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]
  exact riemannianCurveLength_comp_monotone_lift g hγreal hperiod hc hm hp hcompreal

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem riemannianLoopDistance_le_of_pointwise (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ δ : freeLoop M) {B : ℝ≥0}
    (h : ∀ θ, riemannianEDistOf g (γ θ) (δ θ) ≤ (B : ℝ≥0∞)) :
    riemannianLoopDistance g γ δ ≤ B := by
  apply ENNReal.coe_le_coe.mp
  rw [riemannianLoopDistance_coe]
  exact iSup_le h

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem loopDistance_precompose_le (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) {C B : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (ψ φ : C(loopCircle, loopCircle)) (h : ∀ θ, dist (ψ θ) (φ θ) ≤ B) :
    riemannianLoopDistance g (γ.comp ψ) (γ.comp φ) ≤ C * B := by
  apply riemannianLoopDistance_le_of_pointwise
  intro θ
  apply (hγ (ψ θ) (φ θ)).trans
  rw [ENNReal.coe_mul]
  apply mul_le_mul' le_rfl
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (h θ)

end DifferentialGeometry.Geometry
