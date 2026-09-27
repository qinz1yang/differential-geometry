import DifferentialGeometry.Topology.LoopSpace.RegularRepresentatives
import DifferentialGeometry.Topology.LoopSpace.FamilySphere



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


abbrev regularSphereFamily (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) :=
  @ContinuousMap familySphere (regularContractibleLoop E M) inferInstance
    (regularContractibleLoopTopology e he)


def regularSphereFamilyInclusion (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e)
    (Γ : regularSphereFamily e he) : C(familySphere, contractibleLoop M) :=
  letI : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he
  (⟨regularContractibleLoopInclusion, continuous_regularContractibleLoopInclusion e he hemb⟩ :
    C(regularContractibleLoop E M, contractibleLoop M)).comp Γ


def regularFamilyRepresentatives (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e)
    (ξ : loopFamilyClass M) : Set (regularSphereFamily e he) :=
  {Γ | LoopFamily.classOf (regularSphereFamilyInclusion e he hemb Γ) = ξ}

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]



theorem regularFamilyRepresentatives_nonempty
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e) (ξ : loopFamilyClass M) :
    (regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ).Nonempty := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  obtain ⟨Γ, hΓ⟩ := LoopFamily.exists_representative ξ
  obtain ⟨S, H, _, _⟩ := exists_regular_contractible_representative g e he hemb Γ
  refine ⟨S, ?_⟩
  change LoopFamily.classOf (regularSphereFamilyInclusion e he₁ hemb S) = ξ
  rw [← hΓ]
  exact (LoopFamily.classOf_eq_iff _ _).mpr ⟨H.symm⟩

end DifferentialGeometry.Topology
