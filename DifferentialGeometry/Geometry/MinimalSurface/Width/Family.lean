import DifferentialGeometry.Geometry.Measure.Area.LeastAreaContinuity
import DifferentialGeometry.Topology.LoopSpace.RegularFamily



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]
  {n : ℕ}


def regularFamilyAreaValues (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (Γ : regularSphereFamily e he) : Set ℝ := Set.range (fun k => regularLeastArea g (Γ k))

omit [PreconnectedSpace M] in
theorem regularFamilyAreaValues_nonempty (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (Γ : regularSphereFamily e he) : (regularFamilyAreaValues g e he Γ).Nonempty :=
  Set.range_nonempty _


theorem regularFamilyAreaValues_bddAbove (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    BddAbove (regularFamilyAreaValues g e (he.of_le (by exact_mod_cast le_top)) Γ) := by
  let : TopologicalSpace (regularContractibleLoop E M) :=
    regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))
  exact (isCompact_range ((continuous_regularLeastArea g e he hemb hi).comp Γ.continuous)).bddAbove



def regularFamilyMaximum (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (Γ : regularSphereFamily e he) : ℝ := sSup (regularFamilyAreaValues g e he Γ)


theorem regularFamilyMaximum_isLUB (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    IsLUB (regularFamilyAreaValues g e (he.of_le (by exact_mod_cast le_top)) Γ)
      (regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ) :=
  isLUB_csSup (regularFamilyAreaValues_nonempty g e _ Γ)
    (regularFamilyAreaValues_bddAbove g e he hemb hi Γ)


theorem regularLeastArea_le_familyMaximum (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) (k : familySphere) :
    regularLeastArea g (Γ k) ≤ regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ :=
  (regularFamilyMaximum_isLUB g e he hemb hi Γ).1 ⟨k, rfl⟩


theorem regularFamilyMaximum_attained (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    ∃ k, regularLeastArea g (Γ k) = regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ := by
  let : TopologicalSpace (regularContractibleLoop E M) :=
    regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))
  obtain ⟨k, _, hk⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    ((continuous_regularLeastArea g e he hemb hi).comp Γ.continuous).continuousOn
  refine ⟨k, le_antisymm (regularLeastArea_le_familyMaximum g e he hemb hi Γ k) ?_⟩
  apply (regularFamilyMaximum_isLUB g e he hemb hi Γ).2
  rintro _ ⟨j, rfl⟩
  exact hk (mem_univ j)


theorem regularFamilyMaximum_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    0 ≤ regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ :=
  (regularLeastArea_nonneg g (Γ familySphereBasepoint)).trans
    (regularLeastArea_le_familyMaximum g e he hemb hi Γ familySphereBasepoint)

end DifferentialGeometry.Geometry
