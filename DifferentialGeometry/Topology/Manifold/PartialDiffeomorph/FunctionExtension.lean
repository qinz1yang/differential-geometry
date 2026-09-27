/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.FunctionExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {J : ModelWithCorners ℝ F G}
  {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem exists_contMDiff_extension_of_hasCompactSupport
    (c : PartialDiffeomorph I J M N ∞) {k : N → Q}
    (hk : ContMDiffOn J 𝓘(ℝ, Q) ∞ k c.target) (hkc : HasCompactSupport k)
    (hkv : tsupport k ⊆ c.target) :
    ∃ h : M → Q, ContMDiff I 𝓘(ℝ, Q) ∞ h ∧ HasCompactSupport h ∧
      EqOn h (k ∘ c) c.source ∧ tsupport h = c.symm '' tsupport k ∧
      tsupport h ⊆ c.source ∧ EqOn h 0 c.sourceᶜ := by
  let U : TopologicalSpace.Opens M := ⟨c.source, c.open_source⟩
  let d := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo c
    (U := U) (Subset.refl c.source)
  have htarget : c '' (U : Set M) = c.target :=
    c.toOpenPartialHomeomorph.image_source_eq_target
  obtain ⟨h, hh, hhc, hval, hs, hsource, hzero⟩ :=
    d.exists_contMDiff_extension_of_hasCompactSupport (htarget.symm ▸ hk) hkc
      (fun y hy => by
        change y ∈ c '' (U : Set M)
        rw [htarget]
        exact hkv hy)
  refine ⟨h, hh, hhc, ?_, ?_, hsource, hzero⟩
  · intro x hx
    exact hval ⟨x, hx⟩
  · rw [hs]
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨⟨y, by
        change y ∈ c '' (U : Set M)
        rw [htarget]
        exact hkv hy⟩, hy, rfl⟩

end PartialDiffeomorph
