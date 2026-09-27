import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

namespace PartialDiffeomorph

open Set Manifold
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P] {n : WithTop ℕ∞}

theorem trans_apply (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n)
    (x : M) : (Φ.trans Ψ) x = Ψ (Φ x) := rfl

theorem trans_source (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n) :
    (Φ.trans Ψ).source = Φ.source ∩ Φ ⁻¹' Ψ.source := by
  rw [show (Φ.trans Ψ).source = (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).source from rfl]
  exact PartialEquiv.trans_source _ _

theorem symm_source (Φ : PartialDiffeomorph I J M N n) : Φ.symm.source = Φ.target := rfl

theorem symm_target (Φ : PartialDiffeomorph I J M N n) : Φ.symm.target = Φ.source := rfl

theorem symm_toPartialEquiv_source (Φ : PartialDiffeomorph I J M N n) :
    Φ.symm.toPartialEquiv.source = Φ.target := rfl

theorem symm_toPartialEquiv_target (Φ : PartialDiffeomorph I J M N n) :
    Φ.symm.toPartialEquiv.target = Φ.source := rfl

theorem symm_apply_apply (Φ : PartialDiffeomorph I J M N n) {x : M} (hx : x ∈ Φ.source) :
    Φ.symm (Φ x) = x := Φ.toPartialEquiv.left_inv hx

theorem apply_symm_apply (Φ : PartialDiffeomorph I J M N n) {y : N} (hy : y ∈ Φ.target) :
    Φ (Φ.symm y) = y := Φ.toPartialEquiv.right_inv hy

end PartialDiffeomorph
