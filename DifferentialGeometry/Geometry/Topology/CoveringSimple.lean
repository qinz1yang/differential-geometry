import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Coverings of simply connected spaces

This file packages the elementary global step used after a local geometric map
has been upgraded to a covering map.
-/

open Function
open scoped Manifold ContDiff

noncomputable section

namespace IsLocalHomeomorph

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

/-- A local homeomorphism from a nonempty compact space to a connected
Hausdorff space is surjective. -/
theorem surjective_compact
    [CompactSpace E] [Nonempty E] [T2Space X] [ConnectedSpace X]
    (hf : IsLocalHomeomorph f) : Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := by
    rw [← Set.image_univ]
    exact hf.isOpenMap Set.univ isOpen_univ
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf.continuous).isClosed
  have hrange : Set.range f = Set.univ :=
    (show IsClopen (Set.range f) from ⟨hclosed, hopen⟩).eq_univ
      (Set.range_nonempty f)
  intro x
  have hx : x ∈ Set.range f := by
    rw [hrange]
    exact Set.mem_univ x
  exact hx

/-- A local homeomorphism from a compact Hausdorff space to a Hausdorff space
is a covering map. -/
theorem covering_compact
    [CompactSpace E] [T2Space E] [T2Space X]
    (hf : IsLocalHomeomorph f) : IsCoveringMap f := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsCoveringMapOn.of_openPartialHomeomorph hf.continuous
  intro e _he
  obtain ⟨φ, heφ, hφ⟩ := hf e
  exact ⟨φ, heφ, hφ.symm⟩

end IsLocalHomeomorph

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

/-- A covering map from a nonempty preconnected space to a locally path
connected simply connected space is bijective. -/
theorem bijective_sc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hf : IsCoveringMap f) : Function.Bijective f := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  obtain ⟨s, ⟨hs0, hsp⟩, -⟩ :=
    hf.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e₀) e₀ rfl
  have hfs : Function.RightInverse s f := by
    intro x
    have h := congrFun hsp x
    simpa using h
  refine ⟨?_, hfs.surjective⟩
  have hsf : (⇑s ∘ f) = id := by
    refine hf.eq_of_comp_eq
      (g₁ := ⇑s ∘ f) (g₂ := id)
      (s.continuous.comp hf.continuous) continuous_id ?_ e₀ ?_
    · funext e
      simp only [Function.comp_apply, id_eq, hfs (f e)]
    · simp only [Function.comp_apply, id_eq, hs0]
  have hli : Function.LeftInverse s f := fun e => congrFun hsf e
  exact hli.injective

/-- A covering map satisfying the hypotheses of `bijective_sc`, packaged as a
homeomorphism. -/
noncomputable def homeomorph_sc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hf : IsCoveringMap f) : E ≃ₜ X :=
  (Equiv.ofBijective f hf.bijective_sc).toHomeomorphOfContinuousOpen
    hf.continuous hf.isOpenMap

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 F' H'}
variable [ChartedSpace H E] [IsManifold I ∞ E]
variable [ChartedSpace H' X] [IsManifold I' ∞ X]

/-- A smooth covering local diffeomorphism onto a simply connected manifold is
a global diffeomorphism. -/
noncomputable def diffeomorph_sc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hf : IsCoveringMap f) (hloc : IsLocalDiffeomorph I I' ∞ f) :
    Diffeomorph I I' E X ∞ :=
  hloc.diffeomorphOfBijective hf.bijective_sc

omit [IsManifold I ∞ E] [IsManifold I' ∞ X] in
@[simp] theorem coe_diffeomorph_sc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hf : IsCoveringMap f) (hloc : IsLocalDiffeomorph I I' ∞ f) :
    ⇑(hf.diffeomorph_sc hloc) = f := rfl

end Smooth

end IsCoveringMap

end
