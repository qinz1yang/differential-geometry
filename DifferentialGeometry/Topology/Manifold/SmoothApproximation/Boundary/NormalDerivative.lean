import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Positive inward normal derivative of a diffeomorphism of manifolds with boundary (A3-b)

`pos_mfderiv_comp_of_diffeomorph`: let `h : A ≃ₘ^k⟮𝓡∂ (n+1), 𝓡∂ (n+1)⟯ B` be a `C^k`
diffeomorphism (`1 ≤ k`) and `r : B → ℝ` a `C¹` defining function of `∂B` (`r ≥ 0`, `r = 0` on
`∂B`, `dr ≠ 0` on `∂B`). Then at every boundary point `p` of `A`, the differential of `r ∘ h` is
positive on every strictly inward tangent vector (positive `0`-th coordinate in the chart at `p`).

Proof: in the chart at `p` the coordinate expression of `r ∘ h` is `≥ 0` and vanishes at the
chart image of `p`, a point of the boundary hyperplane; hence its derivative within the half-space
is `≥ 0` on the tangent cone `{w | 0 ≤ w 0}` (`IsLocalMinOn.hasFDerivWithinAt_nonneg`). It is
nonzero by the chain rule (`dr ≠ 0` on `∂B`, `dh` invertible, `h` preserves the boundary). A
nonzero functional that is `≥ 0` on a closed half-space is `> 0` on the open half-space.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

/-- A nonzero linear functional that is `≥ 0` on the closed half-space `{w | 0 ≤ w 0}` is
positive on the open half-space. -/
theorem pos_of_nonneg_on_halfSpace {n : ℕ} {Λ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ}
    (hΛ : ∀ w : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ w 0 → 0 ≤ Λ w) (hne : Λ ≠ 0)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : 0 < v 0) : 0 < Λ v := by
  set e₀ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he₀
  have he₀0 : e₀ 0 = 1 := by simp [he₀]
  have hdecomp : ∀ w : EuclideanSpace ℝ (Fin (n + 1)), Λ w = w 0 * Λ e₀ := by
    intro w
    have hz : (w - w 0 • e₀) 0 = 0 := by simp [he₀0]
    have h1 : 0 ≤ Λ (w - w 0 • e₀) := hΛ _ hz.ge
    have h2 : 0 ≤ Λ (-(w - w 0 • e₀)) := hΛ _ (by simp only [PiLp.neg_apply, hz, neg_zero]; rfl)
    rw [map_neg] at h2
    have h0 : Λ (w - w 0 • e₀) = 0 := le_antisymm (by linarith) h1
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
    exact h0
  have hpos : 0 < Λ e₀ := by
    refine lt_of_le_of_ne (hΛ e₀ (by rw [he₀0]; exact zero_le_one)) ?_
    intro h0
    apply hne
    ext w
    rw [hdecomp w, ← h0, mul_zero]
    rfl
  rw [hdecomp v]
  exact mul_pos hv hpos

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]

/-- **A3-b (positive inward normal derivative).** For a `C^k` diffeomorphism (`1 ≤ k`) of
manifolds with boundary and a `C¹` defining function `r` of `∂B`, the differential of `r ∘ h` at
a boundary point `p` of `A` is positive on every strictly inward vector. -/
theorem pos_mfderiv_comp_of_diffeomorph {k : ℕ∞ω} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) {r : B → ℝ}
    (hr : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) 1 r) (hrn : ∀ y, 0 ≤ r y)
    (hr0 : ∀ y, (𝓡∂ (n + 1)).IsBoundaryPoint y → r y = 0)
    (hrd : ∀ y, (𝓡∂ (n + 1)).IsBoundaryPoint y → mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r y ≠ 0)
    {p : A} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p) (v : TangentSpace (𝓡∂ (n + 1)) p)
    (hv : 0 < EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) v) :
    (0 : ℝ) < (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (r ∘ h) p v : ℝ) := by
  have hk0 : k ≠ 0 := (lt_of_lt_of_le zero_lt_one hk).ne'
  have hhp : (𝓡∂ (n + 1)).IsBoundaryPoint (h p) := ((h.isLocalDiffeomorph p).isBoundaryPoint_iff hk0).mp hp
  have hmdh : MDifferentiableAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) h p := h.contMDiff.mdifferentiableAt hk0
  have hmdr : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (h p) := hr.mdifferentiableAt one_ne_zero
  have hmdg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (r ∘ h) p := hmdr.comp p hmdh
  have hcomp : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (r ∘ h) p =
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (h p)).comp (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) h p) := mfderiv_comp p hmdr hmdh
  have hne : (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (r ∘ h) p : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) ≠ 0 := by
    intro hΛ
    apply hrd (h p) hhp
    have hsurj := (h.isInvertible_mfderiv hk0 (x := p)).surjective
    ext w
    obtain ⟨u, rfl⟩ := hsurj w
    have := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ => L u) (hcomp.symm.trans hΛ)
    exact this
  have hφ0 : (extChartAt (𝓡∂ (n + 1)) p p) 0 = 0 := by
    have hfr := (𝓡∂ (n + 1)).isBoundaryPoint_iff.mp hp
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hfr
    exact hfr.symm
  have hnonneg : ∀ w : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ w 0 →
      (0 : ℝ) ≤ ((mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (r ∘ h) p :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) w : ℝ) := by
    intro w hw
    have hD := hmdg.hasMFDerivAt.2
    have hmin : IsLocalMinOn (writtenInExtChartAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) p (r ∘ h)) (range (𝓡∂ (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) p p) := by
      refine Filter.Eventually.of_forall fun z => ?_
      simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        comp_apply, id_eq, extChartAt_to_inv]
      rw [hr0 _ hhp]
      exact hrn _
    have hcone : w ∈ posTangentConeAt (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) p p) := by
      apply mem_posTangentConeAt_of_segment_subset
      refine (𝓡∂ (n + 1)).convex_range.segment_subset
        (extChartAt_target_subset_range p (mem_extChartAt_target p)) ?_
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ (extChartAt (𝓡∂ (n + 1)) p p + w) 0
      rw [PiLp.add_apply, hφ0, zero_add]
      exact hw
    exact hmin.hasFDerivWithinAt_nonneg hD hcone
  exact pos_of_nonneg_on_halfSpace hnonneg hne (by simpa using hv)

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
