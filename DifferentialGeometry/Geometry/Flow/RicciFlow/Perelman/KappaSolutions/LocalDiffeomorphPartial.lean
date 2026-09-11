import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Filter Manifold Set Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
  [TopologicalSpace N] [ChartedSpace G N]

def partialDiffeomorphOfInjectiveLocalDiffeomorph (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    PartialDiffeomorph I J M N ∞ := by
  let hopen := hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
  let e := hopen.toOpenPartialHomeomorph f
  refine {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hf.contMDiff.contMDiffOn
    contMDiffOn_invFun := ?_ }
  change ContMDiffOn J I ∞ e.symm e.target
  intro y hy
  have hyrange : y ∈ range f := by
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_target] using hy
  obtain ⟨x, rfl⟩ := hyrange
  obtain ⟨Ψ, hx, hagree⟩ := hf x
  have htarget : f x ∈ Ψ.target := by
    rw [hagree hx]
    exact Ψ.toPartialEquiv.map_source hx
  have heq : (e.symm : N → M) =ᶠ[nhds (f x)] (Ψ.symm : N → M) := by
    filter_upwards [Ψ.open_target.mem_nhds htarget] with q hq
    have hright : f (Ψ.symm q) = q :=
      (hagree (Ψ.toPartialEquiv.map_target hq)).trans (Ψ.toPartialEquiv.right_inv hq)
    have hqrange : q ∈ range f := ⟨Ψ.symm q, hright⟩
    apply hinj
    exact (hopen.toOpenPartialHomeomorph_right_inv f hqrange).trans hright.symm
  have hInv := Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)
  exact (hInv.congr_of_eventuallyEq heq).contMDiffWithinAt


@[simp] theorem partialDiffeomorphOfInjectiveLocalDiffeomorph_apply (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) (x : M) :
    partialDiffeomorphOfInjectiveLocalDiffeomorph f hf hinj x = f x := rfl


@[simp] theorem partialDiffeomorphOfInjectiveLocalDiffeomorph_source (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    (partialDiffeomorphOfInjectiveLocalDiffeomorph f hf hinj).source = univ := rfl


@[simp] theorem partialDiffeomorphOfInjectiveLocalDiffeomorph_target (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    (partialDiffeomorphOfInjectiveLocalDiffeomorph f hf hinj).target = range f := by
  exact (hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj).toOpenPartialHomeomorph_target f

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
