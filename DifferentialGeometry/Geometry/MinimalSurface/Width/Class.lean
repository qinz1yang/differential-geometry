import DifferentialGeometry.Geometry.MinimalSurface.Width.Family







noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]
  {n : ℕ}


def classFamilyMaxima (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (hemb : _root_.Topology.IsEmbedding e) (ξ : loopFamilyClass M) : Set ℝ :=
  regularFamilyMaximum g e he '' regularFamilyRepresentatives e he hemb ξ

omit [PreconnectedSpace M] in
theorem classFamilyMaxima_nonempty (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e) (ξ : loopFamilyClass M) :
    (classFamilyMaxima g e (he.of_le (by exact_mod_cast le_top)) hemb ξ).Nonempty :=
  (regularFamilyRepresentatives_nonempty g e he hemb ξ).image _


theorem classFamilyMaxima_bddBelow (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    BddBelow (classFamilyMaxima g e (he.of_le (by exact_mod_cast le_top)) hemb ξ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Γ, _, rfl⟩
  exact regularFamilyMaximum_nonneg g e he hemb hi Γ



def classWidth (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (hemb : _root_.Topology.IsEmbedding e) (ξ : loopFamilyClass M) : ℝ :=
  sInf (classFamilyMaxima g e he hemb ξ)


theorem classWidth_isGLB (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    IsGLB (classFamilyMaxima g e (he.of_le (by exact_mod_cast le_top)) hemb ξ)
      (classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ) :=
  isGLB_csInf (classFamilyMaxima_nonempty g e he hemb ξ)
    (classFamilyMaxima_bddBelow g e he hemb hi ξ)


theorem classWidth_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    0 ≤ classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ := by
  apply (classWidth_isGLB g e he hemb hi ξ).2
  rintro _ ⟨Γ, _, rfl⟩
  exact regularFamilyMaximum_nonneg g e he hemb hi Γ


theorem classWidth_le_familyMaximum (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M)
    {Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))}
    (hΓ : Γ ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ) :
    classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ ≤
      regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ :=
  (classWidth_isGLB g e he hemb hi ξ).1 ⟨Γ, hΓ, rfl⟩

omit [PreconnectedSpace M] in
theorem exists_regularFamily_maximum_lt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e) (ξ : loopFamilyClass M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top)),
      Γ ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ ∧
      regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ <
        classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ + ε := by
  obtain ⟨a, ⟨Γ, hΓ, rfl⟩, ha⟩ := exists_lt_of_csInf_lt
    (classFamilyMaxima_nonempty g e he hemb ξ)
    (show classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ <
      classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ + ε by linarith)
  exact ⟨Γ, hΓ, ha⟩


def constantRegularSphereFamily (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (q : M) : regularSphereFamily e he :=
  @ContinuousMap.const familySphere (regularContractibleLoop E M) inferInstance
    (regularContractibleLoopTopology e he) (regularContractibleLoopConst q)

omit [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem constantRegularSphereFamily_mem (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 e)
    (hemb : _root_.Topology.IsEmbedding e) (q : M) :
    constantRegularSphereFamily e he q ∈ regularFamilyRepresentatives e he hemb
      (LoopFamily.nullClass q) := rfl


theorem regularFamilyMaximum_constant (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (q : M) :
    regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top))
      (constantRegularSphereFamily e (he.of_le (by exact_mod_cast le_top)) q) = 0 := by
  obtain ⟨k, hk⟩ := regularFamilyMaximum_attained g e he hemb hi
    (constantRegularSphereFamily e (he.of_le (by exact_mod_cast le_top)) q)
  exact hk.symm.trans (regularLeastArea_constant g q)


theorem classWidth_nullClass (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (q : M) : classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb
      (LoopFamily.nullClass q) = 0 := by
  apply le_antisymm _ (classWidth_nonneg g e he hemb hi _)
  exact (classWidth_le_familyMaximum g e he hemb hi _
    (constantRegularSphereFamily_mem e _ hemb q)).trans_eq
      (regularFamilyMaximum_constant g e he hemb hi q)

end DifferentialGeometry.Geometry
