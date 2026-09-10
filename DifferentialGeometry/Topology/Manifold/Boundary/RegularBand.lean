import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold Topology
namespace Poincare.Manifold.Boundary
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {I : ModelWithCorners ℝ E H}


theorem exists_regular_boundary_band {r : M → ℝ} (hr : Continuous r)
    (hpositive : ∀ x, I.IsInteriorPoint x → 0 < r x)
    {W : Set M} (hW : IsOpen W) (hBW : I.boundary M ⊆ W)
    {V : (x : M) → TangentSpace I x}
    (hunit : ∀ x ∈ W, (mfderiv I 𝓘(ℝ, ℝ) r x) (V x) = (1 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ r ⁻¹' Iic δ ⊆ W ∧
      (∀ x, mfderiv I 𝓘(ℝ, ℝ) r x = 0 → δ < r x) ∧
      ∀ x, r x = δ → mfderiv I 𝓘(ℝ, ℝ) r x ≠ 0 := by
  have hp : ∀ x ∈ Wᶜ, 0 < r x := fun x hx =>
    hpositive x ((I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr (fun hb => hx (hBW hb)))
  obtain ⟨ε,hε,hεr⟩ := hW.isClosed_compl.isCompact.exists_forall_le' hr.continuousOn hp
  have hδ : 0 < ε / 2 := half_pos hε
  have hband : r ⁻¹' Iic (ε / 2) ⊆ W := by
    intro x hx
    by_contra hxW
    have hh := hεr x hxW
    change r x ≤ ε / 2 at hx
    linarith
  have hcritical : ∀ x, mfderiv I 𝓘(ℝ, ℝ) r x = 0 → ε / 2 < r x := by
    intro x hx
    by_contra hsmall
    have hh := hunit x (hband (le_of_not_gt hsmall))
    rw [hx] at hh
    change (0 : ℝ) = 1 at hh
    exact zero_ne_one hh
  exact ⟨ε/2,hδ,hband,hcritical,fun x hx hc => (ne_of_lt (hcritical x hc)) hx.symm⟩

end Poincare.Manifold.Boundary
