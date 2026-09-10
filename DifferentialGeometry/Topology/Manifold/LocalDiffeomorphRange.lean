/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Filter Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

def diffeomorphRangeOfInjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) :
    Diffeomorph I J M hf.image ∞ := by
  let he : IsOpenEmbedding f :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  let h := he.isEmbedding.toHomeomorph
  refine { h.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact (ContMDiff.subtypeVal_comp_iff hf.image h).mp hf.contMDiff
  · intro y
    let x := h.symm y
    have hxy : f x = (y : N) := congrArg Subtype.val (h.apply_symm_apply y)
    have hi : ContMDiffAt J I ∞ (hf x).localInverse (y : N) := by
      rw [← hxy]
      exact (hf x).localInverse_contMDiffAt
    have hlocal : ContMDiffAt J I ∞ (fun z : hf.image ↦ (hf x).localInverse (z : N)) y :=
      hi.comp y (contMDiff_subtype_val (U := hf.image)).contMDiffAt
    apply hlocal.congr_of_eventuallyEq
    have hmem : (y : N) ∈ (hf x).localInverse.source := by
      rw [← hxy]
      exact (hf x).localInverse_mem_source
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hf x).localInverse.open_source.mem_nhds hmem)] with z hz
    apply hinj
    exact (congrArg Subtype.val (h.apply_symm_apply z)).trans
      ((hf x).localInverse_right_inv hz).symm

@[simp]
theorem diffeomorphRangeOfInjective_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) (x : M) :
    (diffeomorphRangeOfInjective hf hinj x : N) = f x := rfl

end DifferentialGeometry.Topology
