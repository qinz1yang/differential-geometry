import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint regularity on `ℝ × E` from a time-slice PDE (bootstrap direction)

Bootstrap-direction companions to `TimeJetCommute` (which goes the other way, from joint
smoothness to commuting derivatives).  Here we BUILD joint regularity of a two-variable
family `G : ℝ → E → F` on an open `U ⊆ ℝ × E` from separated data:

* a pointwise evolution equation in the time direction, `∂ₜ G = R` (`HasDerivAt` at every
  point of `U`), with `R` merely continuous — no joint differentiability assumed a priori;
* spatial differentiability of each time slice.

Main statements:
* `hasFDerivAt_of_slice` — the kernel: joint (Fréchet) differentiability at a point from
  the time-direction `HasDerivAt` (with derivative continuous at the point) plus slice
  differentiability.  This is the "continuous partials ⟹ differentiable" principle in the
  one-time-variable form needed for parabolic bootstrap arguments; the time direction is
  handled by the mean-value inequality, so no joint hypothesis is required.
* `contDiffOn_succ_of_pde` — the induction step: if the time derivative `R` and the spatial
  derivative family `W` are jointly `C^q` on `U`, then `G` is jointly `C^{q+1}` on `U`.
* `contDiffOn_one_of_pde` — first bootstrap step (`q = 0`): continuous `R` and `W` give
  joint `C¹`.
* `contDiffOn_inf_of_pde` — the `C^∞` endpoint: jointly `C^∞` inputs `R`, `W` give jointly
  `C^∞` `G` (no induction needed: instantiate the step at every finite order).

Intended consumer: joint spacetime regularity of Ricci-flow limit metrics
(`∂ₜ g = -2 Ric(g)` bootstraps time regularity from spatial regularity); see
`DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/FlowLimitRegularity.md`.
-/

noncomputable section

open scoped ContDiff Topology
open Asymptotics Set

namespace DifferentialGeometry
namespace Analysis

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Joint differentiability from a time-slice PDE (kernel).**  If `G` satisfies
`∂ₜ G = R` at every point of an open `U ⊆ ℝ × E` with `R` continuous (within `U`) at `p₀`,
and the time slice `G p₀.1` is differentiable at `p₀.2`, then the joint map
`p ↦ G p.1 p.2` is differentiable at `p₀`, with derivative assembled from the two partial
derivatives.  The time direction is controlled by the mean-value inequality on the segment
`[[p₀.1, p.1]] × {p.2}`, which stays in `U` for `p` close to `p₀`. -/
theorem hasFDerivAt_of_slice {G : ℝ → E → F} {R : ℝ × E → F} {W : E →L[ℝ] F}
    {U : Set (ℝ × E)} (hU : IsOpen U) {p₀ : ℝ × E} (hp₀ : p₀ ∈ U)
    (hpde : ∀ p ∈ U, HasDerivAt (fun s : ℝ => G s p.2) (R p) p.1)
    (hRc : ContinuousWithinAt R U p₀)
    (hslice : HasFDerivAt (fun y : E => G p₀.1 y) W p₀.2) :
    HasFDerivAt (fun p : ℝ × E => G p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (R p₀)
        + W.comp (ContinuousLinearMap.snd ℝ ℝ E)) p₀ := by
  -- spatial part: lift the slice derivative along the second projection
  have h₁ : HasFDerivAt (fun p : ℝ × E => G p₀.1 p.2)
      (W.comp (ContinuousLinearMap.snd ℝ ℝ E)) p₀ :=
    hslice.comp p₀ hasFDerivAt_snd
  -- time part: the increment `G p.1 p.2 - G p₀.1 p.2` is `p.1`-differentiable via the MVT
  have h₂ : HasFDerivAt (fun p : ℝ × E => G p.1 p.2 - G p₀.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (R p₀)) p₀ := by
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    -- a ball around `p₀` inside `U` on which `‖R - R p₀‖ ≤ ε`
    have hRatt : ContinuousAt R p₀ := hRc.continuousAt (hU.mem_nhds hp₀)
    have hev : ∀ᶠ q in 𝓝 p₀, ‖R q - R p₀‖ ≤ ε ∧ q ∈ U := by
      have h1 : ∀ᶠ q in 𝓝 p₀, ‖R q - R p₀‖ ≤ ε := by
        filter_upwards [hRatt (Metric.closedBall_mem_nhds (R p₀) hε)] with q hq
        simpa [dist_eq_norm] using hq
      filter_upwards [h1, hU.mem_nhds hp₀] with q hq1 hq2 using ⟨hq1, hq2⟩
    obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    filter_upwards [Metric.ball_mem_nhds p₀ hr0] with p hp
    -- the time segment `[[p₀.1, p.1]] × {p.2}` stays inside the ball
    have hseg : ∀ s ∈ uIcc p₀.1 p.1, (s, p.2) ∈ Metric.ball p₀ r := by
      intro s hs
      have h1 : |s - p₀.1| ≤ |p.1 - p₀.1| := abs_sub_left_of_mem_uIcc hs
      have h2 : dist (s, p.2) p₀ ≤ dist p p₀ := by
        rw [Prod.dist_eq, Prod.dist_eq]
        exact max_le_max (by simpa [Real.dist_eq] using h1) le_rfl
      exact lt_of_le_of_lt h2 hp
    -- mean-value inequality for `s ↦ G s p.2 - (s - p₀.1) • R p₀` on the segment
    have hder : ∀ s ∈ uIcc p₀.1 p.1,
        HasDerivWithinAt (fun s' : ℝ => G s' p.2 - (s' - p₀.1) • R p₀)
          (R (s, p.2) - R p₀) (uIcc p₀.1 p.1) s := by
      intro s hs
      have hd := hpde (s, p.2) (hball _ (hseg s hs)).2
      have hlin : HasDerivAt (fun s' : ℝ => (s' - p₀.1) • R p₀) (R p₀) s := by
        simpa using ((hasDerivAt_id s).sub_const p₀.1).smul_const (R p₀)
      exact (hd.sub hlin).hasDerivWithinAt
    have hbound : ∀ s ∈ uIcc p₀.1 p.1, ‖R (s, p.2) - R p₀‖ ≤ ε := fun s hs =>
      (hball _ (hseg s hs)).1
    have hMVT := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
      (convex_uIcc p₀.1 p.1) left_mem_uIcc right_mem_uIcc
    -- rearrange to the little-o inequality
    calc ‖(fun p : ℝ × E => G p.1 p.2 - G p₀.1 p.2) p
            - (fun p : ℝ × E => G p.1 p.2 - G p₀.1 p.2) p₀
            - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (R p₀)) (p - p₀)‖
        = ‖(G p.1 p.2 - (p.1 - p₀.1) • R p₀)
            - (G p₀.1 p.2 - (p₀.1 - p₀.1) • R p₀)‖ := by
          simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
            Prod.fst_sub, sub_self, zero_smul, sub_zero]
          congr 1
          abel
      _ ≤ ε * ‖p.1 - p₀.1‖ := hMVT
      _ ≤ ε * ‖p - p₀‖ := by
          have : ‖p.1 - p₀.1‖ ≤ ‖p - p₀‖ := by
            simpa [Prod.fst_sub] using norm_fst_le (p - p₀)
          exact mul_le_mul_of_nonneg_left this hε.le
  -- assemble: `G p.1 p.2 = (G p.1 p.2 - G p₀.1 p.2) + G p₀.1 p.2`
  have h₃ := h₂.add h₁
  refine h₃.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun p => (sub_add_cancel _ _).symm

/-- **Bootstrap induction step.**  If `∂ₜ G = R` pointwise on the open `U` and each time
slice of `G` has spatial derivative `W`, with `R` and `W` jointly `C^q`, then `G` is
jointly `C^{q+1}` on `U`.  (The joint derivative of `G` is assembled from `R` and `W` by
continuous-linear algebra, so it is jointly `C^q`.) -/
theorem contDiffOn_succ_of_pde {q : ℕ}
    {G : ℝ → E → F} {R : ℝ × E → F} {W : ℝ × E → E →L[ℝ] F} {U : Set (ℝ × E)}
    (hU : IsOpen U)
    (hpde : ∀ p ∈ U, HasDerivAt (fun s : ℝ => G s p.2) (R p) p.1)
    (hslice : ∀ p ∈ U, HasFDerivAt (fun y : E => G p.1 y) (W p) p.2)
    (hR : ContDiffOn ℝ q R U) (hW : ContDiffOn ℝ q W U) :
    ContDiffOn ℝ (q + 1) (fun p : ℝ × E => G p.1 p.2) U := by
  have hL : ∀ p ∈ U, HasFDerivAt (fun p : ℝ × E => G p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (R p)
        + (W p).comp (ContinuousLinearMap.snd ℝ ℝ E)) p := fun p hp =>
    hasFDerivAt_of_slice hU hp hpde (hR.continuousOn.continuousWithinAt hp) (hslice p hp)
  have hdiff : DifferentiableOn ℝ (fun p : ℝ × E => G p.1 p.2) U := fun p hp =>
    ((hL p hp).differentiableAt).differentiableWithinAt
  have hfderiv : ContDiffOn ℝ q (fderiv ℝ (fun p : ℝ × E => G p.1 p.2)) U := by
    have hpart1 : ContDiffOn ℝ q (fun p : ℝ × E =>
        (ContinuousLinearMap.fst ℝ ℝ E).smulRight (R p)) U := by
      have hclm : ContDiff ℝ q (fun c : F =>
          (ContinuousLinearMap.fst ℝ ℝ E).smulRight c) :=
        (ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
          (ContinuousLinearMap.fst ℝ ℝ E)).contDiff
      exact hclm.comp_contDiffOn hR
    have hpart2 : ContDiffOn ℝ q (fun p : ℝ × E =>
        (W p).comp (ContinuousLinearMap.snd ℝ ℝ E)) U :=
      hW.clm_comp contDiffOn_const
    exact (hpart1.add hpart2).congr fun p hp => (hL p hp).fderiv
  exact (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
    ⟨hdiff, by simp, hfderiv⟩

/-- **First bootstrap step (joint `C¹`).**  Continuous time derivative (the PDE right-hand
side) plus continuous spatial derivative give joint `C¹` on the open `U`. -/
theorem contDiffOn_one_of_pde
    {G : ℝ → E → F} {R : ℝ × E → F} {W : ℝ × E → E →L[ℝ] F} {U : Set (ℝ × E)}
    (hU : IsOpen U)
    (hpde : ∀ p ∈ U, HasDerivAt (fun s : ℝ => G s p.2) (R p) p.1)
    (hslice : ∀ p ∈ U, HasFDerivAt (fun y : E => G p.1 y) (W p) p.2)
    (hR : ContinuousOn R U) (hW : ContinuousOn W U) :
    ContDiffOn ℝ 1 (fun p : ℝ × E => G p.1 p.2) U := by
  have h := contDiffOn_succ_of_pde (q := 0) hU hpde hslice
    (contDiffOn_zero.2 hR) (contDiffOn_zero.2 hW)
  simpa using h

/-- **`C^∞` endpoint of the bootstrap.**  If `∂ₜ G = R` pointwise on the open `U`, each
time slice is spatially differentiable with derivative family `W`, and `R`, `W` are jointly
`C^∞`, then `G` is jointly `C^∞`.  (Instantiate the induction step at every finite order —
the inputs already carry all orders.) -/
theorem contDiffOn_inf_of_pde
    {G : ℝ → E → F} {R : ℝ × E → F} {W : ℝ × E → E →L[ℝ] F} {U : Set (ℝ × E)}
    (hU : IsOpen U)
    (hpde : ∀ p ∈ U, HasDerivAt (fun s : ℝ => G s p.2) (R p) p.1)
    (hslice : ∀ p ∈ U, HasFDerivAt (fun y : E => G p.1 y) (W p) p.2)
    (hR : ContDiffOn ℝ ∞ R U) (hW : ContDiffOn ℝ ∞ W U) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => G p.1 p.2) U := by
  rw [contDiffOn_infty]
  intro n
  cases n with
  | zero =>
    exact (contDiffOn_one_of_pde hU hpde hslice hR.continuousOn hW.continuousOn).of_le
      (by exact_mod_cast Nat.zero_le 1)
  | succ q =>
    have h := contDiffOn_succ_of_pde (q := q) hU hpde hslice
      (hR.of_le (mod_cast le_top)) (hW.of_le (mod_cast le_top))
    exact_mod_cast h

end Analysis
end DifferentialGeometry
