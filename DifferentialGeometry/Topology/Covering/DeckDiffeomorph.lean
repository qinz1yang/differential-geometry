import DifferentialGeometry.Topology.Covering.DeckGroup
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H]
variable {G : Type*} [TopologicalSpace G]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω}

theorem IsLocalDiffeomorph.contMDiff_of_comp_eq_self
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    {φ : M → M} (hφ : Continuous φ) (hcomp : p ∘ φ = p) :
    ContMDiff I I n φ := by
  intro x
  have hpx := hp (φ x)
  refine (hpx.localInverse_contMDiffAt.comp_of_eq
    hp.contMDiff.contMDiffAt (congrFun hcomp x).symm).congr_of_eventuallyEq ?_
  have hevent : ∀ᶠ y in 𝓝 x, φ y ∈ hpx.localInverse.target :=
    hφ.continuousAt
      (hpx.localInverse.open_target.mem_nhds hpx.localInverse_mem_target)
  filter_upwards [hevent] with y hy
  change φ y = hpx.localInverse (p y)
  rw [← congrFun hcomp y]
  exact (hpx.localInverse_left_inv hy).symm

theorem coveringDeckGroup_contMDiff
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) :
    ContMDiff I I n (fun x : M => γ • x) :=
  IsLocalDiffeomorph.contMDiff_of_comp_eq_self hp γ.property.1 (by
    funext x
    exact coveringDeckGroup_map γ x)

noncomputable def coveringDeckGroupDiffeomorph
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) : M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := γ.1
  contMDiff_toFun := coveringDeckGroup_contMDiff hp γ
  contMDiff_invFun := by
    change ContMDiff I I n (fun x : M => γ⁻¹ • x)
    exact coveringDeckGroup_contMDiff hp γ⁻¹

@[simp] theorem coveringDeckGroupDiffeomorph_apply
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) (x : M) :
    coveringDeckGroupDiffeomorph hp γ x = γ • x :=
  rfl

@[simp] theorem coveringDeckGroupDiffeomorph_symm_apply
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) (x : M) :
    (coveringDeckGroupDiffeomorph hp γ).symm x = γ⁻¹ • x :=
  rfl

end DifferentialGeometry
