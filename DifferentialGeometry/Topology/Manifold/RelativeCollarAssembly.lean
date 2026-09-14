import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.Manifold.BoundaryTransitionFlow
import DifferentialGeometry.Topology.Manifold.CollarStraighteningProducer

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Collar

universe u

abbrev RelativeCollarUnitSpace := EuclideanHalfSpace 1

def relativeCollarUnit : RelativeCollarUnitSpace := ⟨0, by norm_num⟩

structure RelativeCollarTransitionFlowWitness {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × RelativeCollarUnitSpace) M ∞) (ε : ℝ) where
  toSelfDiff : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞
  delta : ℝ
  delta_pos : 0 < delta
  delta_le : delta ≤ ε
  matches_source : ∀ (p : S) (t : RelativeCollarUnitSpace),
    t.1 0 < delta → toSelfDiff (c₀ (p, t)) = c₁ (p, t)
  fixes_outside : Set.EqOn toSelfDiff id
    (c₀ '' {q : S × RelativeCollarUnitSpace | q.2.1 0 < ε})ᶜ

theorem relativeCollarTransitionFlowWitness_exists_of_eq {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {c : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × RelativeCollarUnitSpace) M ∞} {ε : ℝ} (hε : 0 < ε) :
    Nonempty (RelativeCollarTransitionFlowWitness c c ε) :=
  ⟨{ toSelfDiff := Diffeomorph.refl _ _ _
     delta := ε
     delta_pos := hε
     delta_le := le_rfl
     matches_source := by intro p t _; rfl
     fixes_outside := by intro x _; rfl }⟩

theorem relativeCollarTransitionFlowWitness_exists_of_eq_at_unit {S : Type u}
    [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {c : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × RelativeCollarUnitSpace) M ∞} {ε : ℝ} (hε : 0 < ε) :
    ∃ W : RelativeCollarTransitionFlowWitness c c ε, W.delta = ε :=
  ⟨{ toSelfDiff := Diffeomorph.refl _ _ _
     delta := ε
     delta_pos := hε
     delta_le := le_rfl
     matches_source := fun _ _ _ => rfl
     fixes_outside := fun _ _ => rfl }, rfl⟩

theorem relativeCollarTransitionFlowWitness_forces_nonidentity
    {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × RelativeCollarUnitSpace) M ∞} {ε : ℝ}
    (W : RelativeCollarTransitionFlowWitness c₀ c₁ ε)
    {p : S} {t : RelativeCollarUnitSpace}
    (ht : t.1 0 < W.delta) (hne : c₀ (p, t) ≠ c₁ (p, t)) :
    W.toSelfDiff (c₀ (p, t)) ≠ c₀ (p, t) := by
  intro h
  exact hne (h.symm.trans (W.matches_source p t ht))

theorem relativeCollarTransitionFlowWitness_fixes_of_not_mem {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × RelativeCollarUnitSpace) M ∞} {ε : ℝ}
    (W : RelativeCollarTransitionFlowWitness c₀ c₁ ε)
    {x : M} (hx : x ∉ c₀ '' {q : S × RelativeCollarUnitSpace | q.2.1 0 < ε}) :
    W.toSelfDiff x = x :=
  W.fixes_outside hx

theorem boundaryCollarStraighteningWithPrescribedSupport_of_transitionFlowWitness
    (h : ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
      [IsManifold (𝓡 2) ∞ S]
      {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
      [IsManifold (𝓡∂ 3) ∞ M]
      (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
        (S × RelativeCollarUnitSpace) M ∞),
      (∀ p : S, (p, relativeCollarUnit) ∈ c₀.source ∧
        (p, relativeCollarUnit) ∈ c₁.source) →
      (∀ p : S, c₀ (p, relativeCollarUnit) = c₁ (p, relativeCollarUnit)) →
      (∀ p : S, c₀ (p, relativeCollarUnit) ∈ (𝓡∂ 3).boundary M) →
      ∀ ε : ℝ, 0 < ε → Nonempty (RelativeCollarTransitionFlowWitness c₀ c₁ ε)) :
    BoundaryCollarStraighteningWithPrescribedSupport.{u} := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy ε hε
  obtain ⟨W⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  exact ⟨W.delta, W.delta_pos, W.delta_le, W.toSelfDiff, W.matches_source, W.fixes_outside⟩

theorem transitionFlowWitness_fixes_unit {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × RelativeCollarUnitSpace) M ∞} {ε : ℝ}
    (W : RelativeCollarTransitionFlowWitness c₀ c₁ ε) (p : S)
    (hmem : c₀ (p, relativeCollarUnit) ∉ c₀ '' {q : S × RelativeCollarUnitSpace |
      q.2.1 0 < ε}) :
    W.toSelfDiff (c₀ (p, relativeCollarUnit)) = c₀ (p, relativeCollarUnit) :=
  W.fixes_outside hmem

def relativeCollarTransitionMap {S : Type*} (η : ℝ → ℝ)
    (c₀ c₁ : S → EuclideanSpace ℝ (Fin 1)) (s : ℝ) (p : S) : EuclideanSpace ℝ (Fin 1) :=
  c₀ p + η s • (c₁ p - c₀ p)

theorem relativeCollarTransitionMap_seam {S : Type*} (η : ℝ → ℝ)
    (c₀ c₁ : S → EuclideanSpace ℝ (Fin 1)) (p : S)
    (hseam : c₀ p = c₁ p) (s : ℝ) :
    relativeCollarTransitionMap η c₀ c₁ s p = c₀ p := by
  rw [relativeCollarTransitionMap, hseam, sub_self, smul_zero, add_zero]

theorem relativeCollarTransitionMap_of_eq_one {S : Type*} (η : ℝ → ℝ)
    (c₀ c₁ : S → EuclideanSpace ℝ (Fin 1)) (p : S) {s : ℝ} (hs : η s = 1) :
    relativeCollarTransitionMap η c₀ c₁ s p = c₁ p := by
  rw [relativeCollarTransitionMap, hs, one_smul]
  abel

theorem relativeCollarTransitionMap_of_eq_zero {S : Type*} (η : ℝ → ℝ)
    (c₀ c₁ : S → EuclideanSpace ℝ (Fin 1)) (p : S) {s : ℝ} (hs : η s = 0) :
    relativeCollarTransitionMap η c₀ c₁ s p = c₀ p := by
  rw [relativeCollarTransitionMap, hs, zero_smul, add_zero]

end DifferentialGeometry.Topology.Collar
