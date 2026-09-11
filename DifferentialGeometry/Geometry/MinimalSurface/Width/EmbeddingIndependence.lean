import DifferentialGeometry.Geometry.MinimalSurface.Width.Class



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M] {n m : ℕ}


def regularSphereFamilyChange
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : M → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 a)
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    regularSphereFamily a ha := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  have hΓ := (continuous_regularContractibleLoop_iff e he₁ (fun k => Γ k)).mp Γ.continuous
  have hnew : Continuous[inferInstance, regularLoopTopology a ha]
      (fun k => (Γ k).val) :=
    @Continuous.comp _ _ _ inferInstance (regularLoopTopology e he₁)
      (regularLoopTopology a ha) (fun k => (Γ k).val) id
      (continuous_regularLoopTopology_change e he hemb hi a ha) hΓ
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology a ha
  exact ⟨fun k => Γ k, (continuous_regularContractibleLoop_iff a ha _).mpr hnew⟩


theorem regularSphereFamilyChange_mem
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : M → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 a)
    (hamb : _root_.Topology.IsEmbedding a)
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) (ξ : loopFamilyClass M) :
    regularSphereFamilyChange e he hemb hi a ha Γ ∈ regularFamilyRepresentatives a ha hamb ξ ↔
      Γ ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ := Iff.rfl

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M] [T3Space M] {n m : ℕ}


theorem regularFamilyMaximum_change (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : M → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 a)
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    regularFamilyMaximum g a ha (regularSphereFamilyChange e he hemb hi a ha Γ) =
      regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ := rfl


theorem classFamilyMaxima_eq_embedding (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : M → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (hai : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) a p))
    (ξ : loopFamilyClass M) :
    classFamilyMaxima g e (he.of_le (by exact_mod_cast le_top)) hemb ξ =
      classFamilyMaxima g a (ha.of_le (by exact_mod_cast le_top)) hamb ξ := by
  apply Subset.antisymm
  · rintro _ ⟨Γ, hΓ, rfl⟩
    exact ⟨regularSphereFamilyChange e he hemb hi a _ Γ,
      (regularSphereFamilyChange_mem e he hemb hi a _ hamb Γ ξ).mpr hΓ, rfl⟩
  · rintro _ ⟨Γ, hΓ, rfl⟩
    exact ⟨regularSphereFamilyChange a ha hamb hai e _ Γ,
      (regularSphereFamilyChange_mem a ha hamb hai e _ hemb Γ ξ).mpr hΓ, rfl⟩



theorem classWidth_eq_embedding (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (a : M → EuclideanSpace ℝ (Fin m))
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (hai : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) a p))
    (ξ : loopFamilyClass M) :
    classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ =
      classWidth g a (ha.of_le (by exact_mod_cast le_top)) hamb ξ :=
  congrArg sInf (classFamilyMaxima_eq_embedding g e he hemb hi a ha hamb hai ξ)

end DifferentialGeometry.Geometry
