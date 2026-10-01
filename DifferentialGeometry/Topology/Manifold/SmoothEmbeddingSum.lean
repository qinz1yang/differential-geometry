import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def sumInlRange (Q D : Type*) [TopologicalSpace Q] [TopologicalSpace D] :
    TopologicalSpace.Opens (Q ⊕ D) :=
  ⟨range (Sum.inl : Q → Q ⊕ D), Topology.IsOpenEmbedding.inl.isOpen_range⟩

def sumInlCorestrict {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (q : Q) : sumInlRange Q D :=
  ⟨Sum.inl q, ⟨q, rfl⟩⟩

theorem sumInlCorestrict_val {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (q : Q) : ((sumInlCorestrict (D := D) q : sumInlRange Q D) : Q ⊕ D) = Sum.inl q := rfl

noncomputable def sumInlRangeInv {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (u : sumInlRange Q D) : Q := Classical.choose u.2

theorem sumInlRangeInv_spec {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (u : sumInlRange Q D) : Sum.inl (sumInlRangeInv u) = u.1 := Classical.choose_spec u.2

theorem sumInlRangeInv_corestrict {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (q : Q) : sumInlRangeInv (sumInlCorestrict (D := D) q) = q :=
  Sum.inl_injective (by rw [sumInlRangeInv_spec]; rfl)

theorem sumInlCorestrict_rangeInv {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (u : sumInlRange Q D) : sumInlCorestrict (D := D) (sumInlRangeInv u) = u :=
  Subtype.ext (sumInlRangeInv_spec u)

theorem continuous_sumInlRangeInv {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D] :
    Continuous (sumInlRangeInv (Q := Q) (D := D)) := by
  refine (Topology.IsEmbedding.inl (X := Q) (Y := D)).continuous_iff.mpr ?_
  have h : (Sum.inl ∘ sumInlRangeInv (Q := Q) (D := D)) =
      (Subtype.val : sumInlRange Q D → Q ⊕ D) :=
    funext fun u => sumInlRangeInv_spec u
  rw [h]
  exact continuous_subtype_val

theorem contMDiff_sumInlRangeInv {Q D : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D] :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (sumInlRangeInv (Q := Q) (D := D)) := by
  intro u
  have hφ : IsImmersionAt (𝓡 3) (𝓡 3) ∞ (Sum.inl : Q → Q ⊕ D) (sumInlRangeInv u) :=
    IsImmersion.isImmersionAt
      (IsImmersionOfComplement.sumInl (I := 𝓡 3) (M := Q) (M' := D)).isImmersion _
  rw [ContMDiffAt.iff_comp_isImmersionAt hφ]
  refine ⟨continuous_sumInlRangeInv.continuousAt, ?_⟩
  have h : (Sum.inl ∘ sumInlRangeInv (Q := Q) (D := D)) =
      (Subtype.val : sumInlRange Q D → Q ⊕ D) :=
    funext fun u => sumInlRangeInv_spec u
  rw [h]
  exact contMDiff_subtype_val.contMDiffAt

theorem continuous_sumInlCorestrict {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D] :
    Continuous (sumInlCorestrict (Q := Q) (D := D)) := by
  refine Topology.IsEmbedding.subtypeVal.continuous_iff.mpr ?_
  have h : (Subtype.val ∘ sumInlCorestrict (Q := Q) (D := D)) = (Sum.inl : Q → Q ⊕ D) :=
    funext fun q => sumInlCorestrict_val q
  rw [h]
  exact continuous_inl

theorem contMDiff_sumInlCorestrict {Q D : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D] :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (sumInlCorestrict (Q := Q) (D := D)) := by
  intro q
  have hφ : IsImmersionAt (𝓡 3) (𝓡 3) ∞
      (Subtype.val : sumInlRange Q D → Q ⊕ D) (sumInlCorestrict q) :=
    IsImmersion.isImmersionAt (IsImmersion.of_opens (sumInlRange Q D)) _
  rw [ContMDiffAt.iff_comp_isImmersionAt hφ]
  refine ⟨continuous_sumInlCorestrict.continuousAt, ?_⟩
  have h : (Subtype.val ∘ sumInlCorestrict (Q := Q) (D := D)) = (Sum.inl : Q → Q ⊕ D) :=
    funext fun q => sumInlCorestrict_val q
  rw [h]
  exact (IsSmoothEmbedding.sumInl (I := 𝓡 3) (M := Q) (M' := D)).contMDiff.contMDiffAt

noncomputable def sumInlRangeDiffeomorph {Q D : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D] :
    Diffeomorph (𝓡 3) (𝓡 3) (sumInlRange Q D) Q ∞ where
  toEquiv :=
    { toFun := sumInlRangeInv
      invFun := sumInlCorestrict
      left_inv := fun u => sumInlCorestrict_rangeInv u
      right_inv := fun q => sumInlRangeInv_corestrict q }
  contMDiff_toFun := contMDiff_sumInlRangeInv
  contMDiff_invFun := contMDiff_sumInlCorestrict

theorem isSmoothEmbedding_of_comp_sumInl {M Q D : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q] [TopologicalSpace D]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D]
    (f : M → Q) (h : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ((Sum.inl : Q → Q ⊕ D) ∘ f)) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f := by
  let f' : M → sumInlRange Q D := fun x => sumInlCorestrict (Q := Q) (D := D) (f x)
  have hval : (Subtype.val ∘ f') = ((Sum.inl : Q → Q ⊕ D) ∘ f) := rfl
  have hf' : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
      (𝓡∂ 3) (𝓡 3) (sumInlRange Q D) f' (by rw [hval]; exact h)
  have hout := hf'.diffeomorph_comp (sumInlRangeDiffeomorph (Q := Q) (D := D))
  convert hout using 1
  funext x
  exact (sumInlRangeInv_corestrict (Q := Q) (D := D) (f x)).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
