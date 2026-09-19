/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.EmbeddedProjection
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell

/-!
# Singular disks projected through PL covering maps
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

def map (D : SingularTwoCell M) {p : M → N} (hp : IsPL 3 3 p) : SingularTwoCell N where
  domain := D.domain
  isPLBall_domain := D.isPLBall_domain
  toFun := p ∘ D
  isPLOn := hp.comp_isPLOn D.isPLOn

@[simp]
theorem map_domain (D : SingularTwoCell M) {p : M → N} (hp : IsPL 3 3 p) :
    (D.map hp).domain = D.domain :=
  rfl

@[simp]
theorem map_apply (D : SingularTwoCell M) {p : M → N} (hp : IsPL 3 3 p)
    (x : EuclideanSpace ℝ (Fin 2)) : D.map hp x = p (D x) :=
  rfl

theorem range_boundary_map (D : SingularTwoCell M) {p : M → N} (hp : IsPL 3 3 p) :
    range (D.map hp).boundary = p '' range D.boundary :=
  range_comp p D.boundary

theorem locally_injective_fiber_le_map (D : SingularTwoCell M) {p : M → N}
    (hpl : IsPL 3 3 p) (hp : IsCoveringMap p) (hD : D.IsNonsingular) {n : ℕ∞}
    (hcard : ∀ y, (p ⁻¹' {y}).encard ≤ n) :
    (∀ x ∈ (D.map hpl).domain,
      ∃ U ∈ 𝓝[(D.map hpl).domain] x, InjOn (D.map hpl) U) ∧
      ∀ y, ((D.map hpl).domain ∩ (D.map hpl) ⁻¹' {y}).encard ≤ n :=
  Covering.locally_injective_fiber_le_of_isCoveringMap hp D.continuousOn hD hcard

theorem exists_projected_singular_two_cell (D : SingularTwoCell M) {p : M → N}
    (hpl : IsPL 3 3 p) (hp : IsCoveringMap p) (hD : D.IsNonsingular)
    (hcard : ∀ y, (p ⁻¹' {y}).encard = 2) :
    ∃ A : SingularTwoCell N,
      A.domain = D.domain ∧ (∀ x, A x = p (D x)) ∧
      (∀ x ∈ A.domain, ∃ U ∈ 𝓝[A.domain] x, InjOn A U) ∧
      (∀ y, (A.domain ∩ A ⁻¹' {y}).encard ≤ 2) ∧
      range A.boundary = p '' range D.boundary := by
  obtain ⟨hloc, htwo⟩ := D.locally_injective_fiber_le_map hpl hp hD (fun y => (hcard y).le)
  exact ⟨D.map hpl, rfl, fun _ => rfl, hloc, htwo, D.range_boundary_map hpl⟩

end DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell
