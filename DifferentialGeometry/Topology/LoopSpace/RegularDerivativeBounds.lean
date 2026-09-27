import DifferentialGeometry.Topology.LoopSpace.RegularBounds
import DifferentialGeometry.Geometry.Metric.CurveLength



noncomputable section

open Set Function ContinuousMap Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_regular_loop_lipschitz_factor (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ C : ℝ≥0, ∀ (γ : regularLoop E M) (θ η : loopCircle),
      riemannianEDistOf g (γ.val θ) (γ.val η) ≤
        ((C * ‖regularLoopDerivative e (he.of_le (by exact_mod_cast le_top)) γ‖₊ : ℝ≥0) : ℝ≥0∞) *
          edist θ η := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ := exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨C, hC⟩ := exists_compact_source_curve_lipschitz g hU
    (hr.of_le (by exact_mod_cast le_top)) (isCompact_range he.continuous) heU
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  refine ⟨C, fun γ θ η => ?_⟩
  let D := ‖regularLoopDerivative e he₁ γ‖₊
  have hLip : LipschitzWith D (fun t : ℝ => e (γ.val (t : loopCircle))) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((regularLoop_embedded_contDiff e he₁ γ).differentiable one_ne_zero)
    intro t
    exact_mod_cast (regularLoopDerivative e he₁ γ).norm_coe_le_norm (t : loopCircle)
  have hlift : LipschitzWith (C * D) (fun t : ℝ => γ.val (t : loopCircle)) := by
    intro x y
    have h := hC D (fun t : ℝ => e (γ.val (t : loopCircle)))
      (regularLoop_embedded_contDiff e he₁ γ) hLip (fun _ => mem_range_self _) x y
    simpa only [hleft] using! h
  exact loop_lipschitz_of_lift hlift θ η



theorem regularLoop_riemannian_lipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : regularLoop E M) :
    ∃ L : ℝ≥0, ∀ θ η, riemannianEDistOf g (γ.val θ) (γ.val η) ≤ (L : ℝ≥0∞) * edist θ η := by
  obtain ⟨n, e, _, _, he, hemb, hi, _⟩ := exists_compact_embedding_and_retraction (E := E) (M := M)
  obtain ⟨C, hC⟩ := exists_regular_loop_lipschitz_factor g e he hemb.isEmbedding hi
  exact ⟨_, hC γ⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] [Nonempty M] in
theorem loop_arclength_le_of_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M} {L : ℝ≥0}
    (hγ : ∀ θ η, riemannianEDistOf g (γ θ) (γ η) ≤ (L : ℝ≥0∞) * edist θ η) :
    riemannianCurveLength g (fun t : ℝ => γ (t : loopCircle)) 0 1 ≤ L := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hγ' : LipschitzWith L γ := hγ
  have hlift : LipschitzWith L (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! hγ'.comp loopCircle_projection_lipschitz
  have h := riemannianCurveELength_le_of_lipschitz g hlift 0 1
  simp only [sub_zero, ENNReal.ofReal_one, mul_one] at h
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top h).trans_eq (ENNReal.coe_toReal L)

end DifferentialGeometry.Topology
