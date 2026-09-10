import DifferentialGeometry.Topology.Covering.ImmersionLift
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology

variable {E F H H' W M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace W] [ChartedSpace H W]
  [TopologicalSpace M] [ChartedSpace H' M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}

theorem contMDiff_comp_partialDiffeomorph
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : ContMDiff I J ∞ f) (hsub : range f ⊆ φ.source) :
    ContMDiff I J ∞ (φ ∘ f) :=
  contMDiffOn_univ.mp (φ.contMDiffOn_toFun.comp hf.contMDiffOn (fun x _ ↦ hsub (mem_range_self x)))

theorem isEmbedding_comp_partialDiffeomorph
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : IsEmbedding f) (hsub : range f ⊆ φ.source) : IsEmbedding (φ ∘ f) := by
  let f' : W → φ.source := fun x ↦ ⟨f x, hsub (mem_range_self x)⟩
  have hf' : IsEmbedding f' := IsEmbedding.subtypeVal.of_comp_iff.mp hf
  exact φ.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding.comp hf'

theorem isSmoothEmbedding_comp_partialDiffeomorph [IsManifold J ∞ N]
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : IsSmoothEmbedding I J ∞ f) (hsub : range f ⊆ φ.source) :
    IsSmoothEmbedding I J ∞ (φ ∘ f) := by
  have hlocal : IsLocalDiffeomorphOn J J ∞ φ.symm (range (φ ∘ f)) := by
    rintro ⟨y, x, rfl⟩
    exact φ.symm.isLocalDiffeomorphAt J J ∞ (φ.map_source (hsub (mem_range_self x)))
  exact ⟨(isImmersionOfComplement_of_lift_through_localDiffeomorphOn hlocal
    hf.isImmersion.isImmersionOfComplement_complement
    (contMDiff_comp_partialDiffeomorph φ hf.contMDiff hsub).continuous
    (fun x ↦ φ.left_inv (hsub (mem_range_self x)))).isImmersion,
    isEmbedding_comp_partialDiffeomorph φ hf.isEmbedding hsub⟩

theorem injective_mfderiv_comp_partialDiffeomorph
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hsub : range f ⊆ φ.source) (x : W) :
    Function.Injective (mfderiv I J (φ ∘ f) x) := by
  have hmd : φ.toOpenPartialHomeomorph.MDifferentiable J J :=
    ⟨φ.contMDiffOn_toFun.mdifferentiableOn (by decide),
      φ.contMDiffOn_invFun.mdifferentiableOn (by decide)⟩
  change Function.Injective (mfderiv I J (φ.toOpenPartialHomeomorph ∘ f) x)
  rw [mfderiv_comp x (hmd.mdifferentiableAt (hsub (mem_range_self x)))
    (hf.mdifferentiable (by decide) x)]
  exact (hmd.mfderiv_injective (hsub (mem_range_self x))).comp (hinj x)

end Poincare.Topology
