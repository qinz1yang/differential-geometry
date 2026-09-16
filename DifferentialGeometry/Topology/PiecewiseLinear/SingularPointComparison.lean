import DifferentialGeometry.Topology.PiecewiseLinear.SingularPointEmbedding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_embedding_heightSingularPoints_with_levelPolygons_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {R : Geometry.SimplicialComplex ℝ E} {f : E → ℝ} {a p : E}
    (hp : p ∈ heightSingularPoints K.space ℓ)
    (hsub : heightSingularPoints R.space f \ {a} ⊆
      heightSingularPoints K.space ℓ \ {p})
    (hpoints : ∀ q ∈ K.vertices \ {p},
      (levelPolygons R.space f (f q)).encard ≤
        (levelPolygons K.space ℓ (ℓ q)).encard) :
    ∃ e : heightSingularPoints R.space f ↪ heightSingularPoints K.space ℓ,
      (∀ q : heightSingularPoints R.space f, (q : E) = a → (e q : E) = p) ∧
      (∀ q : heightSingularPoints R.space f, (q : E) ≠ a → (e q : E) = q) ∧
      ∀ q : heightSingularPoints R.space f, (q : E) ≠ a →
        (levelPolygons R.space f (f q)).encard ≤
          (levelPolygons K.space ℓ (ℓ (e q))).encard := by
  obtain ⟨e, hea, hene⟩ :=
    exists_embedding_heightSingularPoints_of_sdiff_subset hp hsub
  refine ⟨e, hea, hene, ?_⟩
  intro q hqa
  have hqold := hsub
    ⟨q.property, by simpa only [mem_singleton_iff] using hqa⟩
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun g : E →ₗ[ℝ] ℝ => g x) hz
  have hqvertex := heightSingularPoints_subset_vertices K
    hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
    hdimE ℓ.toLinearMap hlinear hinj hqold.1
  have hqp : (q : E) ≠ p := by
    simpa only [mem_singleton_iff] using hqold.2
  have hle := hpoints q ⟨hqvertex, hqp⟩
  simpa only [hene q hqa] using hle

end DifferentialGeometry.Topology.PiecewiseLinear
