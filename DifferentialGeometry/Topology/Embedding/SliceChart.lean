/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import DifferentialGeometry.External.TauCeti.Geometry.Manifold.LocallyFlat.Smooth

open scoped ContDiff Manifold

namespace Manifold

open Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

theorem IsSmoothEmbedding.exists_contMDiffOn_slice_chart [J.Boundaryless]
    (h : IsSmoothEmbedding I J n f) (x : M) :
    ∃ Φ : OpenPartialHomeomorph N (E × h.isImmersion.complement), f x ∈ Φ.source ∧
      ContMDiffOn J 𝓘(𝕜, E × h.isImmersion.complement) n Φ Φ.source ∧
      ContMDiffOn 𝓘(𝕜, E × h.isImmersion.complement) J n Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range f) =
        Φ.target ∩ (range I ×ˢ ({0} : Set h.isImmersion.complement)) :=
  (h.isImmersion.isImmersionOfComplement_complement x).exists_contMDiffOn_slice_chart
    h.isEmbedding.isInducing

end Manifold
