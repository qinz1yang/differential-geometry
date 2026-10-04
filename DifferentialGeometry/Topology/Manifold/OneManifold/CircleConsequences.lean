import DifferentialGeometry.Topology.Manifold.OneManifold.CircleClassification
import DifferentialGeometry.Topology.Manifold.CircleComponents
import DifferentialGeometry.Topology.Manifold.SubmersionFiber

/-!
# Consumer forms of the classification of compact boundaryless one-manifolds

* `nonempty_diffeomorph_circle`: the form requested by lane W4-FCb (model `𝓡 1`).
* `exists_circle_embedding_connectedComponent'` and
  `finite_connectedComponents_and_exists_circle_embedding`: every component of a compact
  boundaryless one-manifold is a smoothly embedded circle, and there are finitely many; no
  vector field is assumed (compare `CircleComponents.lean`).
* `nonempty_circle_diffeomorph_regularFiber`: a compact connected regular fibre of a submersion
  whose source has one dimension more than its target is a circle (the circle clause of LC83).
-/

set_option autoImplicit false

open Set Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold.OneManifold

theorem nonempty_diffeomorph_circle {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C] [IsManifold (𝓡 1) ∞ C] [CompactSpace C]
    [ConnectedSpace C] [T2Space C] :
    Nonempty (C ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) := by
  obtain ⟨e⟩ := nonempty_circle_diffeomorph_of_finrank_eq_one (EuclideanSpace ℝ (Fin 1))
    (EuclideanSpace ℝ (Fin 1)) C (𝓡 1) (by simp)
  exact ⟨e.symm⟩

section Components

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {J : ModelWithCorners ℝ E H} [J.Boundaryless] [IsManifold J ∞ M] [T2Space M] [CompactSpace M]

theorem exists_circle_embedding_connectedComponent' (hdim : Module.finrank ℝ E = 1) (x : M) :
    ∃ γ : Circle → M, IsSmoothEmbedding (𝓡 1) J ∞ γ ∧ range γ = connectedComponent x := by
  let : LocallyConnectedSpace H := J.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let U : TopologicalSpace.Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : CompactSpace U := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨D⟩ := nonempty_circle_diffeomorph_of_finrank_eq_one E H U J hdim
  have hD := isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D.isLocalDiffeomorph D.injective
  refine ⟨Subtype.val ∘ D, (IsSmoothEmbedding.of_opens U).comp hD (by simp), ?_⟩
  have hsurj : range (D : Circle → U) = univ := D.surjective.range_eq
  rw [range_comp, hsurj, image_univ, Subtype.range_coe_subtype]
  rfl

theorem finite_connectedComponents_and_exists_circle_embedding
    (hdim : Module.finrank ℝ E = 1) :
    Finite (ConnectedComponents M) ∧
      ∀ x : M, ∃ γ : Circle → M, IsSmoothEmbedding (𝓡 1) J ∞ γ ∧
        range γ = connectedComponent x := by
  let : LocallyConnectedSpace H := J.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  exact ⟨inferInstance, exists_circle_embedding_connectedComponent' hdim⟩

end Components

section RegularFiber

variable {E F H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem nonempty_circle_diffeomorph_regularFiber [T2Space M]
    (f : M → N) (y : N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, f x = y → Function.Surjective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hcpt : IsCompact {x | f x = y}) (hconn : IsConnected {x | f x = y}) :
    letI := regularFiberChartedSpace f y hf hreg
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)⟯
      {x : M // f x = y}) := by
  let := regularFiberChartedSpace f y hf hreg
  have := regularFiberIsManifold f y hf hreg
  have : CompactSpace {x : M // f x = y} := isCompact_iff_compactSpace.mp hcpt
  have : ConnectedSpace {x : M // f x = y} := isConnected_iff_connectedSpace.mp hconn
  exact nonempty_circle_diffeomorph_of_finrank_eq_one _ _ _
    𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) (by simp; omega)

end RegularFiber

end DifferentialGeometry.Topology.Manifold.OneManifold
