import DifferentialGeometry.Analysis.ODE.InvariantSet
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.ODE.Gronwall

open Filter Set
open scoped Topology NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Convex.real_inner_sub_nonpos_of_norm_eq_iInf_of_mem_posTangentConeAt
    {C : Set E} (hC : Convex ℝ C) {x p v : E} (hp : p ∈ C)
    (hmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖) (hv : v ∈ posTangentConeAt C p) :
    inner ℝ (x - p) v ≤ 0 := by
  have hnormal : ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC hp).mp hmin
  have hmax : IsMaxOn (fun y : E ↦ inner ℝ (x - p) y) C p := by
    intro y hy
    have := hnormal y hy
    rw [inner_sub_right] at this
    exact sub_nonpos.mp this
  have hderiv : HasFDerivAt (fun y : E ↦ inner ℝ (x - p) y) (innerSL ℝ (x - p)) p := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ (x - p)).hasFDerivAt
  exact hmax.localize.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt hv

theorem frequently_slope_lt_of_le_of_eq_of_hasDerivWithinAt_right
    {g q : ℝ → ℝ} {t q' : ℝ} (hgq : ∀ s, g s ≤ q s) (heq : g t = q t)
    (hq : HasDerivWithinAt q q' (Ici t) t) :
    ∀ r, q' < r → ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (g z - g t) < r := by
  intro r hr
  refine ((hq.liminf_right_slope_le hr).and_eventually self_mem_nhdsWithin).mono ?_
  intro z hz
  rw [slope, vsub_eq_sub] at hz
  have hzt : 0 < z - t := sub_pos.mpr hz.2
  have hdiff : g z - g t ≤ q z - q t := by rw [heq]; linarith [hgq z]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hzt.le)) hz.1

theorem nagumo_mapsTo_of_lipschitz [CompleteSpace E]
    {f : ℝ → E → E} {C : Set E} {a b : ℝ} {γ : ℝ → E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (htangent : VectorFieldTangentTo f C) (L : ℝ≥0)
    (hL : ∀ t ∈ Ico a b, LipschitzWith L (f t))
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (ha : γ a ∈ C) :
    MapsTo γ (Icc a b) C := by
  intro t ht
  let g : ℝ → ℝ := fun s ↦ Metric.infDist (γ s) C ^ 2
  have hgcont : ContinuousOn g (Icc a b) := by
    exact ((Metric.continuous_infDist_pt C).comp_continuousOn hγ.continuousOn).pow 2
  have hgslope :
      ∀ x ∈ Ico a b, ∀ r,
        2 * (L : ℝ) * g x < r →
          ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (g z - g x) < r := by
    intro x hx
    obtain ⟨p, hp, hmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex (γ x)
    let q : ℝ → ℝ := fun s ↦ ‖γ s - p‖ ^ 2
    have hγright : HasDerivWithinAt γ (f x (γ x)) (Ici x) x :=
      (hγ x (mem_Icc_of_Ico hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
    have hq : HasDerivWithinAt q (2 * inner ℝ (γ x - p) (f x (γ x))) (Ici x) x := by
      simpa [q] using (hγright.sub_const p).norm_sq
    have hgq : ∀ s, g s ≤ q s := by
      intro s
      have hle : Metric.infDist (γ s) C ≤ ‖γ s - p‖ := by
        simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := γ s) hp
      exact (sq_le_sq₀ Metric.infDist_nonneg (norm_nonneg _)).mpr hle
    have hdist : Metric.infDist (γ x) C = ‖γ x - p‖ := by
      rw [Metric.infDist_eq_iInf]
      simpa [dist_eq_norm] using hmin.symm
    have heq : g x = q x := by simp [g, q, hdist]
    have hnormal : inner ℝ (γ x - p) (f x p) ≤ 0 :=
      Convex.real_inner_sub_nonpos_of_norm_eq_iInf_of_mem_posTangentConeAt
        hconvex hp hmin (htangent x p hp)
    have hLip : ‖f x (γ x) - f x p‖ ≤ (L : ℝ) * ‖γ x - p‖ :=
      (hL x hx).norm_sub_le _ _
    have hinner :
        inner ℝ (γ x - p) (f x (γ x) - f x p) ≤
          ‖γ x - p‖ * ‖f x (γ x) - f x p‖ :=
      real_inner_le_norm _ _
    have hqbound :
        2 * inner ℝ (γ x - p) (f x (γ x)) ≤ 2 * (L : ℝ) * g x := by
      change
        2 * inner ℝ (γ x - p) (f x (γ x)) ≤
          2 * (L : ℝ) * Metric.infDist (γ x) C ^ 2
      rw [hdist]
      have hnorm : 0 ≤ ‖γ x - p‖ := norm_nonneg _
      have hLnonneg : 0 ≤ (L : ℝ) := L.coe_nonneg
      rw [inner_sub_right] at hinner
      nlinarith [sq_nonneg ‖γ x - p‖]
    intro r hr
    exact frequently_slope_lt_of_le_of_eq_of_hasDerivWithinAt_right hgq heq hq r
      (lt_of_le_of_lt hqbound hr)
  have hga : g a ≤ 0 := by simp [g, Metric.infDist_zero_of_mem ha]
  have hbound : ∀ x ∈ Ico a b, 2 * (L : ℝ) * g x ≤ (2 * (L : ℝ)) * g x + 0 := by
    intro x _
    ring_nf
    exact le_rfl
  have hgronwall :=
    le_gronwallBound_of_liminf_deriv_right_le hgcont hgslope hga hbound t ht
  have hgle : g t ≤ 0 := by
    simpa [gronwallBound_ε0_δ0] using hgronwall
  have hge : 0 ≤ g t := by simp [g, sq_nonneg]
  have hgt : g t = 0 := le_antisymm hgle hge
  have hinf : Metric.infDist (γ t) C = 0 := by
    have : Metric.infDist (γ t) C ^ 2 = 0 := by simpa [g] using hgt
    exact sq_eq_zero_iff.mp this
  exact (hclosed.mem_iff_infDist_zero hne).mpr hinf

theorem nagumo_isForwardInvariantForODE_of_lipschitz [CompleteSpace E]
    {f : ℝ → E → E} {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (htangent : VectorFieldTangentTo f C) (L : ℝ≥0)
    (hL : ∀ t, LipschitzWith L (f t)) :
    IsForwardInvariantForODE f C := by
  intro a b _ γ hγ ha
  exact nagumo_mapsTo_of_lipschitz hne hclosed hconvex htangent L
    (fun t _ ↦ hL t) hγ ha

theorem nagumo_convexCone_isForwardInvariantForODE_of_mapsTo [CompleteSpace E]
    (C : ConvexCone ℝ E) (hne : (C : Set E).Nonempty) (hclosed : IsClosed (C : Set E))
    {f : ℝ → E → E} (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (f t))
    (hf : ∀ t, MapsTo (f t) C C) :
    IsForwardInvariantForODE f C :=
  nagumo_isForwardInvariantForODE_of_lipschitz
    hne hclosed C.convex
      (ConvexCone.vectorFieldTangentTo_of_mapsTo C hf) L hL

theorem nagumo_properCone_isForwardInvariantForODE_of_mapsTo [CompleteSpace E]
    (C : ProperCone ℝ E) {f : ℝ → E → E} (L : ℝ≥0)
    (hL : ∀ t, LipschitzWith L (f t)) (hf : ∀ t, MapsTo (f t) C C) :
    IsForwardInvariantForODE f C :=
  nagumo_isForwardInvariantForODE_of_lipschitz
    C.nonempty C.isClosed C.convex
      (ProperCone.vectorFieldTangentTo_of_mapsTo C hf) L hL

end DifferentialGeometry.Analysis.ODE
