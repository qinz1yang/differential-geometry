import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# CH12-S15, H1 group D (calculus core)

Pure normed-space statement behind the immersion/injectivity of the transfer isotopy: if
`ψ(x,0) = x` then `x ↦ ψ(x, μ c(x))` has derivative within `1/2` of the identity (and is hence
bi-Lipschitz with constant `2` on a ball) as soon as `c` is small in `C^1` on that ball.
-/

set_option autoImplicit false
open scoped Topology
open Set Metric Filter
noncomputable section
namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem calc_C1_small_S15 {N : Set (E × E)} {T' : Set E} (hN : IsOpen N) (hT : IsOpen T')
    {x0 : E} {r : ℝ} {ψ : E × E → E}
    (hψ : ContDiffOn ℝ 1 ψ N) (hBT : closedBall x0 r ⊆ T')
    (hid : ∀ x ∈ T', ψ (x, 0) = x) (hBN : ∀ x ∈ T', (x, (0 : E)) ∈ N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : E → E, ContDiffOn ℝ 1 c T' →
      (∀ x ∈ closedBall x0 r, ‖c x‖ ≤ ε ∧ ‖fderiv ℝ c x‖ ≤ ε) → ∀ μ : ℝ, |μ| ≤ 2 →
      (∀ x ∈ closedBall x0 r, (x, μ • c x) ∈ N) ∧
      (∀ x ∈ closedBall x0 r, ∃ L : E →L[ℝ] E,
        HasFDerivAt (fun y => ψ (y, μ • c y)) L x ∧ ‖L - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) ∧
      (∀ x ∈ closedBall x0 r, ∀ y ∈ closedBall x0 r,
        ‖x - y‖ ≤ 2 * ‖ψ (x, μ • c x) - ψ (y, μ • c y)‖) := by
  have hdiff : ∀ z ∈ N, DifferentiableAt ℝ ψ z := fun z hz =>
    (hψ.contDiffAt (hN.mem_nhds hz)).differentiableAt one_ne_zero
  have hfc : ContinuousOn (fderiv ℝ ψ) N := hψ.continuousOn_fderiv_of_isOpen hN le_rfl
  let D1 : E × E → (E →L[ℝ] E) := fun z => (fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ E E)
  let D2 : E × E → (E →L[ℝ] E) := fun z => (fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ E E)
  have hD1c : ContinuousOn D1 N := by
    have : Continuous (fun A : (E × E →L[ℝ] E) => A.comp (ContinuousLinearMap.inl ℝ E E)) :=
      ((ContinuousLinearMap.compL ℝ E (E × E) E).flip (ContinuousLinearMap.inl ℝ E E)).continuous
    exact this.comp_continuousOn hfc
  have hD2c : ContinuousOn D2 N := by
    have : Continuous (fun A : (E × E →L[ℝ] E) => A.comp (ContinuousLinearMap.inr ℝ E E)) :=
      ((ContinuousLinearMap.compL ℝ E (E × E) E).flip (ContinuousLinearMap.inr ℝ E E)).continuous
    exact this.comp_continuousOn hfc
  have hD1 : ∀ x ∈ T', D1 (x, 0) = ContinuousLinearMap.id ℝ E := by
    intro x hx
    have h1 : HasFDerivAt (fun y : E => ψ (y, (0 : E))) (D1 (x, 0)) x :=
      (hdiff _ (hBN x hx)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x (0 : E))
    have h2 : HasFDerivAt (fun y : E => ψ (y, (0 : E))) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hT.mem_nhds hx) (fun y hy => hid y hy))
    exact h1.unique h2
  have hBc : IsCompact (closedBall x0 r) := isCompact_closedBall x0 r
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, ∀ x ∈ closedBall x0 r, ‖D2 (x, 0)‖ ≤ C0 := by
    apply hBc.exists_bound_of_continuousOn
    exact (hD2c.comp (continuousOn_id.prodMk continuousOn_const)
      (fun x hx => hBN x (hBT hx)))
  set C : ℝ := max C0 0 with hC
  have hCle : ∀ x ∈ closedBall x0 r, ‖D2 (x, 0)‖ ≤ C := fun x hx => (hC0 x hx).trans (le_max_left _ _)
  have hC0' : 0 ≤ C := le_max_right _ _
  let Gd : Set (E × E) := N ∩ (fun z => ‖D1 z - ContinuousLinearMap.id ℝ E‖) ⁻¹' Iio (1 / 4) ∩
    (fun z => ‖D2 z‖) ⁻¹' Iio (C + 1)
  have hGd : IsOpen Gd := by
    have h1 : ContinuousOn (fun z => ‖D1 z - ContinuousLinearMap.id ℝ E‖) N :=
      (hD1c.sub continuousOn_const).norm
    have h2 : ContinuousOn (fun z => ‖D2 z‖) N := hD2c.norm
    have h1o : IsOpen (N ∩ (fun z => ‖D1 z - ContinuousLinearMap.id ℝ E‖) ⁻¹' Iio (1 / 4)) :=
      h1.isOpen_inter_preimage hN isOpen_Iio
    have h2' : ContinuousOn (fun z => ‖D2 z‖)
        (N ∩ (fun z => ‖D1 z - ContinuousLinearMap.id ℝ E‖) ⁻¹' Iio (1 / 4)) :=
      h2.mono inter_subset_left
    exact h2'.isOpen_inter_preimage h1o isOpen_Iio
  have hBG : closedBall x0 r ×ˢ ({0} : Set E) ⊆ Gd := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    have hw0 : w = 0 := hw
    subst hw0
    refine ⟨⟨hBN x (hBT hx), ?_⟩, ?_⟩
    · show ‖D1 (x, 0) - ContinuousLinearMap.id ℝ E‖ < 1 / 4
      rw [hD1 x (hBT hx)]; simp
    · show ‖D2 (x, 0)‖ < C + 1
      linarith [hCle x hx]
  obtain ⟨u, v, hu, hv, hBu, h0v, huv⟩ :=
    generalized_tube_lemma hBc isCompact_singleton hGd hBG
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hv 0 (h0v rfl)
  refine ⟨min (δ / 4) (1 / (8 * (C + 1))), lt_min (by linarith) (by positivity), ?_⟩
  intro c hc hcb μ hμ
  set ε := min (δ / 4) (1 / (8 * (C + 1))) with hε
  have hε1 : ε ≤ δ / 4 := min_le_left _ _
  have hε2 : ε ≤ 1 / (8 * (C + 1)) := min_le_right _ _
  have hmem : ∀ x ∈ closedBall x0 r, (x, μ • c x) ∈ Gd := by
    intro x hx
    apply huv
    refine ⟨hBu hx, hball ?_⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |μ| * ‖c x‖ ≤ 2 * ε := mul_le_mul hμ (hcb x hx).1 (norm_nonneg _) (by norm_num)
      _ < δ := by linarith
  have hderiv : ∀ x ∈ closedBall x0 r, ∃ L : E →L[ℝ] E,
      HasFDerivAt (fun y => ψ (y, μ • c y)) L x ∧ ‖L - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
    intro x hx
    have hxT := hBT hx
    have hcd : HasFDerivAt c (fderiv ℝ c x) x :=
      ((hc.contDiffAt (hT.mem_nhds hxT)).differentiableAt one_ne_zero).hasFDerivAt
    have hz := (hmem x hx).1.1
    have hψd := (hdiff _ hz).hasFDerivAt
    have hpair : HasFDerivAt (fun y => (y, μ • c y))
        ((ContinuousLinearMap.id ℝ E).prod (μ • fderiv ℝ c x)) x :=
      (hasFDerivAt_id x).prodMk (hcd.const_smul μ)
    refine ⟨_, hψd.comp x hpair, ?_⟩
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    have hsplit : (fderiv ℝ ψ (x, μ • c x)).comp ((ContinuousLinearMap.id ℝ E).prod (μ • fderiv ℝ c x)) v
        = D1 (x, μ • c x) v + D2 (x, μ • c x) (μ • fderiv ℝ c x v) := by
      simp only [D1, D2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.id_apply,
        smul_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
    have hG := hmem x hx
    have h1 : ‖D1 (x, μ • c x) - ContinuousLinearMap.id ℝ E‖ < 1 / 4 := hG.1.2
    have h2 : ‖D2 (x, μ • c x)‖ < C + 1 := hG.2
    have e1 : ((fderiv ℝ ψ (x, μ • c x)).comp ((ContinuousLinearMap.id ℝ E).prod (μ • fderiv ℝ c x))
        - ContinuousLinearMap.id ℝ E) v =
        (D1 (x, μ • c x) - ContinuousLinearMap.id ℝ E) v + D2 (x, μ • c x) (μ • fderiv ℝ c x v) := by
      rw [ContinuousLinearMap.sub_apply, hsplit, ContinuousLinearMap.sub_apply]; abel
    rw [e1]
    have b1 : ‖(D1 (x, μ • c x) - ContinuousLinearMap.id ℝ E) v‖ ≤ 1 / 4 * ‖v‖ :=
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)))
    have b2a : ‖μ • fderiv ℝ c x v‖ ≤ 2 * (ε * ‖v‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      have h5 : ‖fderiv ℝ c x v‖ ≤ ε * ‖v‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hcb x hx).2 (norm_nonneg _))
      exact mul_le_mul hμ h5 (norm_nonneg _) (by norm_num)
    have b2 : ‖D2 (x, μ • c x) (μ • fderiv ℝ c x v)‖ ≤ (C + 1) * (2 * ε) * ‖v‖ := by
      have h6 := (ContinuousLinearMap.le_opNorm (D2 (x, μ • c x)) (μ • fderiv ℝ c x v)).trans
        (mul_le_mul h2.le b2a (norm_nonneg _) (by linarith))
      calc _ ≤ (C + 1) * (2 * (ε * ‖v‖)) := h6
        _ = (C + 1) * (2 * ε) * ‖v‖ := by ring
    have hb3 : (C + 1) * (2 * ε) ≤ 1 / 4 := by
      have : (C + 1) * ε ≤ 1 / 8 := by
        calc (C + 1) * ε ≤ (C + 1) * (1 / (8 * (C + 1))) := mul_le_mul_of_nonneg_left hε2 (by linarith)
          _ = 1 / 8 := by field_simp
      nlinarith
    calc _ ≤ ‖(D1 (x, μ • c x) - ContinuousLinearMap.id ℝ E) v‖ + ‖D2 (x, μ • c x) (μ • fderiv ℝ c x v)‖ :=
          norm_add_le _ _
      _ ≤ 1 / 4 * ‖v‖ + (C + 1) * (2 * ε) * ‖v‖ := add_le_add b1 b2
      _ ≤ 1 / 2 * ‖v‖ := by nlinarith [norm_nonneg v]
  refine ⟨fun x hx => (hmem x hx).1.1, hderiv, ?_⟩
  choose! L hL hLb using hderiv
  intro x hx y hy
  have hmv := (convex_closedBall x0 r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => ψ (z, μ • c z) - z) (f' := fun z => L z - ContinuousLinearMap.id ℝ E)
    (fun z hz => ((hL z hz).sub (hasFDerivAt_id z)).hasFDerivWithinAt) (fun z hz => hLb z hz) hy hx
  have h3 : ‖(ψ (x, μ • c x) - x) - (ψ (y, μ • c y) - y)‖ ≤ 1 / 2 * ‖x - y‖ := by
    have := hmv
    rw [norm_sub_rev] at this
    simpa [norm_sub_rev] using this
  have h4 : ‖x - y‖ ≤ ‖ψ (x, μ • c x) - ψ (y, μ • c y)‖ + ‖(ψ (x, μ • c x) - x) - (ψ (y, μ • c y) - y)‖ := by
    calc ‖x - y‖ = ‖(ψ (x, μ • c x) - ψ (y, μ • c y)) - ((ψ (x, μ • c x) - x) - (ψ (y, μ • c y) - y))‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

end GC.LongTime.Ch12
