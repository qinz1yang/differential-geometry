import DifferentialGeometry.Geometry.Measure.Area.LeastArea
import DifferentialGeometry.Geometry.Measure.Area.ManifoldComposition







noncomputable section

open Bundle Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T3Space M] [T3Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuous_of_riemannian_map_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    {f : M → N} {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y) :
    Continuous f := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact continuous_of_riemannian_lipschitz h hf

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompactSpace M] [CompactSpace N]


def postcomposeLipschitzContractibleLoop
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    (f : M → N) {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (γ : lipschitzContractibleLoop g) : lipschitzContractibleLoop h := by
  refine ⟨ContractibleLoop.postcompose ⟨f, continuous_of_riemannian_map_lipschitz g h hf⟩ γ.val, ?_⟩
  obtain ⟨C, hγ⟩ := γ.property
  exact ⟨L * C, riemannian_lipschitz_comp g h hγ hf⟩



theorem postcompose_spanningDisk_competitor
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    (f : M → N) {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : u ∈ spanningDiskCompetitors g γ) :
    let fc : C(M, N) := ⟨f, continuous_of_riemannian_map_lipschitz g h hf⟩;
    fc.comp u ∈ spanningDiskCompetitors h (fc.comp γ) ∧
      riemannianDiskArea h (fc.comp u) ≤ (L : ℝ) ^ 2 * riemannianDiskArea g u := by
  obtain ⟨ht, C, hC⟩ := hu
  refine ⟨⟨?_, L * C, riemannian_lipschitz_comp g h hC hf⟩,
    riemannianDiskArea_comp_le g h hC hf⟩
  ext θ
  exact congrArg f (congrArg (fun δ : freeLoop M => δ θ) ht)

variable [Nonempty M] [PreconnectedSpace M]



theorem leastSpanningArea_postcompose_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (h : SmoothRiemannianMetric 𝓘(ℝ, F) N)
    (f : M → N) {L : ℝ≥0}
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (γ : lipschitzContractibleLoop g) :
    leastSpanningArea h (postcomposeLipschitzContractibleLoop g h f hf γ) ≤
      (L : ℝ) ^ 2 * leastSpanningArea g γ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < (L : ℝ) ^ 2 + 1 := by positivity
  obtain ⟨u, hu, ha⟩ := exists_spanningDisk_area_lt g γ (div_pos hε hden)
  obtain ⟨hv, hvarea⟩ := postcompose_spanningDisk_competitor g h f hf hu
  have hle := leastSpanningArea_le_competitor h (postcomposeLipschitzContractibleLoop g h f hf γ) hv
  have hb := mul_le_mul_of_nonneg_left ha.le (sq_nonneg (L : ℝ))
  have hc : (L : ℝ) ^ 2 * (ε / ((L : ℝ) ^ 2 + 1)) ≤ ε := by
    calc
      _ ≤ ((L : ℝ) ^ 2 + 1) * (ε / ((L : ℝ) ^ 2 + 1)) := by gcongr; linarith
      _ = ε := mul_div_cancel₀ ε hden.ne'
  linarith [hle.trans hvarea]

end DifferentialGeometry.Geometry
