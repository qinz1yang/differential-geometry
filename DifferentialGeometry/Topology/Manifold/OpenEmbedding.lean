import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Topology.Manifold.InverseFunction

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

def diffeomorphOntoImage (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (hinj : Injective f) : M ≃ₘ⟮I, J⟯ hf.image := by
  let e : M ≃ hf.image := Equiv.ofInjective f hinj
  refine
    { toEquiv := e
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff hf.image e).mp hf.contMDiff
      contMDiff_invFun := ?_ }
  intro y
  let x := e.symm y
  have hxy : f x = (y : N) := Equiv.apply_ofInjective_symm hinj y
  have hsmooth : ContMDiffAt J I ∞ (fun z : hf.image ↦ (hf x).localInverse z) y := by
    apply contMDiffAt_subtype_iff.mpr
    rw [← hxy]
    exact (hf x).localInverse_contMDiffAt
  apply hsmooth.congr_of_eventuallyEq
  have hnear : ∀ᶠ z : hf.image in 𝓝 y, (z : N) ∈ (hf x).localInverse.source :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hf x).localInverse_open_source.mem_nhds (hxy ▸ (hf x).localInverse_mem_source))
  filter_upwards [hnear] with z hz
  apply hinj
  exact (Equiv.apply_ofInjective_symm hinj z).trans
    ((hf x).localInverse_right_inv hz).symm

@[simp]
theorem diffeomorphOntoImage_apply (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (hinj : Injective f) (x : M) : (diffeomorphOntoImage f hf hinj x : N) = f x :=
  rfl

theorem diffeomorphOntoImage_symm_apply (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (hinj : Injective f) (y : hf.image) :
    f ((diffeomorphOntoImage f hf hinj).symm y) = (y : N) :=
  Equiv.apply_ofInjective_symm hinj y

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem isLocalDiffeomorph_of_injective_mfderiv
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (himm : ∀ x, Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsLocalDiffeomorph I J ∞ f := by
  intro x
  let D : E →L[ℝ] F := mfderiv I J f x
  let A : E ≃L[ℝ] F :=
    (D.toLinearMap.linearEquivOfInjective (himm x) hdim).toContinuousLinearEquiv
  exact isLocalDiffeomorphAt_of_hasMFDerivAt_equiv f hf x A
    ((hf.mdifferentiable (by decide) x).hasMFDerivAt)

theorem isOpenEmbedding_of_injective_immersion
    (f : M → N) (hf : ContMDiff I J ∞ f) (hinj : Injective f)
    (himm : ∀ x, Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : _root_.Topology.IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf.continuous hinj
    (isLocalDiffeomorph_of_injective_mfderiv f hf himm hdim).isOpenMap

theorem exists_diffeomorph_onto_range_of_injective_immersion
    (f : M → N) (hf : ContMDiff I J ∞ f) (hinj : Injective f)
    (himm : ∀ x, Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ (V : Opens N) (Φ : M ≃ₘ⟮I, J⟯ V),
      (V : Set N) = range f ∧ (∀ x, (Φ x : N) = f x) ∧
        ∀ y : V, f (Φ.symm y) = (y : N) := by
  let hloc := isLocalDiffeomorph_of_injective_mfderiv f hf himm hdim
  exact ⟨hloc.image, diffeomorphOntoImage f hloc hinj, rfl,
    diffeomorphOntoImage_apply f hloc hinj, diffeomorphOntoImage_symm_apply f hloc hinj⟩

end DifferentialGeometry.Topology.Manifold
