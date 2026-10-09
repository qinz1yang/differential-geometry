import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.UniformConvergence

/-!
# Almost-lower curvature bounds pass to `C²`-close coefficient fields (general level `κ`)

Lane CM-A (CM5.a). `eventually_coefficientRm04_lower` (B7) transfers the bound `Rm ≥ 0` of a
limit coefficient field to `Rm ≥ -δ · Gram` for the approximating fields. Here the limit bound is
`Rm ≥ κ · Gram` for an arbitrary real `κ`, and the transferred bound is `Rm ≥ (κ - δ) · Gram`.
The Gram term `c(v,v) c(w,w) - c(v,w)²` converges uniformly on `L` times unit balls
(`tendstoUniformlyOn_coefficientGramDet`), which absorbs the change of the Gram factor.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ContDiff
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn tendstoUniformlyOn_of_cPConvergence)
namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U L : Set E} {c : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {c₀ : E → E →L[ℝ] E →L[ℝ] ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The Gram determinant `B(v,v) B(w,w) - B(v,w)²` of a bilinear form. -/
private theorem continuous_gramDet [NormedSpace ℝ E] :
    Continuous fun P : (E →L[ℝ] E →L[ℝ] ℝ) × E × E =>
      P.1 P.2.1 P.2.1 * P.1 P.2.2 P.2.2 - (P.1 P.2.1 P.2.2) ^ 2 := by
  have hev : Continuous fun P : (E →L[ℝ] E →L[ℝ] ℝ) × E × E => fun (u v : E) => P.1 u v := by
    fun_prop
  have h2 (f g : (E →L[ℝ] E →L[ℝ] ℝ) × E × E → E) (hf : Continuous f) (hg : Continuous g) :
      Continuous fun P : (E →L[ℝ] E →L[ℝ] ℝ) × E × E => P.1 (f P) (g P) :=
    ((continuous_fst.clm_apply hf).clm_apply hg)
  exact ((h2 _ _ (by fun_prop) (by fun_prop)).mul (h2 _ _ (by fun_prop) (by fun_prop))).sub
    ((h2 _ _ (by fun_prop) (by fun_prop)).pow 2)

/-- Uniform convergence of the Gram determinants on `L` times unit balls, from uniform convergence
of the coefficient fields on the compact set `L` where the limit is continuous. -/
theorem tendstoUniformlyOn_coefficientGramDet (hL : IsCompact L) (hc₀ : ContinuousOn c₀ L)
    (hconv : TendstoUniformlyOn c c₀ atTop L) :
    TendstoUniformlyOn (fun k (q : E × E × E) =>
        c k q.1 q.2.1 q.2.1 * c k q.1 q.2.2 q.2.2 - (c k q.1 q.2.1 q.2.2) ^ 2)
      (fun q => c₀ q.1 q.2.1 q.2.1 * c₀ q.1 q.2.2 q.2.2 - (c₀ q.1 q.2.1 q.2.2) ^ 2) atTop
      (L ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ Metric.closedBall (0 : E) 1)) := by
  set D : Set (E × E × E) := L ×ˢ (Metric.closedBall (0 : E) 1 ×ˢ Metric.closedBall (0 : E) 1)
  let G₀ : E × E × E → (E →L[ℝ] E →L[ℝ] ℝ) × E × E := fun q => (c₀ q.1, q.2)
  let Φ : (E →L[ℝ] E →L[ℝ] ℝ) × E × E → ℝ :=
    fun P => P.1 P.2.1 P.2.1 * P.1 P.2.2 P.2.2 - (P.1 P.2.1 P.2.2) ^ 2
  have hD : IsCompact D := hL.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hG₀ : ContinuousOn G₀ D :=
    (hc₀.comp continuousOn_fst fun q hq => hq.1).prodMk continuousOn_snd
  have hK : IsCompact (G₀ '' D) := hD.image_of_continuousOn hG₀
  have hΦ : ∀ P ∈ G₀ '' D, ContinuousAt Φ P := fun P _ => continuous_gramDet.continuousAt
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  have hr := hK.uniformContinuousAt_of_continuousAt Φ hΦ (Metric.dist_mem_uniformity hε)
  obtain ⟨η, hη, hηr⟩ :=
    (Metric.mem_uniformity_dist (α := (E →L[ℝ] E →L[ℝ] ℝ) × E × E)).1 hr
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv η hη] with k hk q hq
  have hdist : dist (G₀ q) ((c k q.1, q.2) : (E →L[ℝ] E →L[ℝ] ℝ) × E × E) < η := by
    simp only [G₀, Prod.dist_eq, dist_self]
    exact max_lt (hk q.1 hq.1) hη
  have key := hηr hdist (mem_image_of_mem G₀ hq)
  rw [mem_ofPred_eq] at key
  exact key

private theorem lower_transfer_level {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) {μ : ℝ}
    {V W : E} (h : μ * (b x V V * b x W W - (b x V W) ^ 2) ≤ coefficientRm04 b x V W W V)
    {v w : E} (α β γ η : ℝ) (hv : α • V + β • W = v) (hw : γ • V + η • W = w) :
    μ * (b x v v * b x w w - (b x v w) ^ 2) ≤ coefficientRm04 b x v w w v := by
  subst hv hw
  rw [bilin_gram_change_of_basis hsymm.self_of_nhds,
    coefficientRm04_change_of_basis hb hsymm hco, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Almost-lower curvature bound at level `κ`.** If the limit coefficient field satisfies
`Rm ≥ κ · Gram` on the compact set `L`, then for every `δ > 0` the approximating fields eventually
satisfy `Rm ≥ (κ - δ) · Gram` on `L`. -/
theorem eventually_coefficientRm04_lower_of_level (hU : IsOpen U) (hL : IsCompact L)
    (hLU : L ⊆ U) (hc : ∀ k, ContDiffOn ℝ 2 (c k) U) (hc₀ : ContDiffOn ℝ 2 c₀ U)
    (hsymm : ∀ k, ∀ y ∈ U, ∀ v w : E, c k y v w = c k y w v)
    (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < c₀ y v v) (hconv : MapCPConvergenceOn L 2 c c₀)
    {κ : ℝ}
    (hlow : ∀ y ∈ L, ∀ v w : E,
      κ * (c₀ y v v * c₀ y w w - (c₀ y v w) ^ 2) ≤ coefficientRm04 c₀ y v w w v) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ y ∈ L, ∀ v w : E,
      (κ - δ) * (c k y v v * c k y w w - (c k y v w) ^ 2) ≤ coefficientRm04 (c k) y v w w v := by
  intro δ hδ
  obtain ⟨lam, hlam, -, hco⟩ := exists_eventually_coercive hL hLU hc₀ hconv hpos
  have hR := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_coefficientRm04 hU hL hLU hc hc₀ hconv hpos) (δ * lam ^ 2 / 2)
    (by positivity)
  have hG := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_coefficientGramDet hL (hc₀.continuousOn.mono hLU)
      (tendstoUniformlyOn_of_cPConvergence (hconv.mono_order (Nat.zero_le 2))))
    (δ * lam ^ 2 / (2 * (|κ| + 1))) (by positivity)
  filter_upwards [hco, hR, hG] with k hk1 hk2 hk3 y hy v w
  have hyU : U ∈ 𝓝 y := hU.mem_nhds (hLU hy)
  have hb : ContDiffAt ℝ 2 (c k) y := (hc k).contDiffAt hyU
  have hs : ∀ᶠ z in 𝓝 y, ∀ u t : E, c k z u t = c k z t u :=
    Filter.eventually_of_mem hyU fun z hz => hsymm k z hz
  have hcoer : IsCoercive (c k y) := ⟨lam, hlam, fun u => by linarith [hk1 y hy u]⟩
  have hdeg : ∀ V : E, (κ - δ) * (c k y V V * c k y V V - (c k y V V) ^ 2) ≤
      coefficientRm04 (c k) y V V V V := by
    intro V
    have h := coefficientRm04_swap_left (c k) y V V V V
    have h0 : c k y V V * c k y V V - (c k y V V) ^ 2 = 0 := by ring
    rw [h0, mul_zero]
    linarith
  have horth : ∀ V W : E, ‖V‖ = 1 → ‖W‖ = 1 → inner ℝ V W = 0 →
      (κ - δ) * (c k y V V * c k y W W - (c k y V W) ^ 2) ≤
        coefficientRm04 (c k) y V W W V := by
    intro V W hV hW hVW
    have hWV : c k y W V = c k y V W := hsymm k y (hLU hy) W V
    have ha := hk1 y hy V
    rw [hV, one_pow, mul_one] at ha
    have hq := hk1 y hy (c k y V W • V - c k y V V • W)
    have hn : ‖c k y V W • V - c k y V V • W‖ ^ 2 = (c k y V W) ^ 2 + (c k y V V) ^ 2 := by
      simp only [norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right, hVW,
        hV, hW, Real.norm_eq_abs, mul_one, mul_zero, sq_abs]
      ring
    have hexp : c k y (c k y V W • V - c k y V V • W) (c k y V W • V - c k y V V • W) =
        c k y V V * (c k y V V * c k y W W - (c k y V W) ^ 2) := by
      simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply, smul_eq_mul, hWV]
      ring
    rw [hn, hexp] at hq
    have hapos : 0 < c k y V V := lt_of_lt_of_le hlam ha
    have hX : lam * c k y V V ≤ c k y V V * c k y W W - (c k y V W) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hapos
      nlinarith [mul_nonneg hlam.le (sq_nonneg (c k y V W))]
    have hGk : lam ^ 2 ≤ c k y V V * c k y W W - (c k y V W) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ha hlam.le]
    have hVb : V ∈ Metric.closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hV.le
    have hWb : W ∈ Metric.closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hW.le
    have h1 := hk2 (y, V, W, W, V) ⟨hy, hVb, hWb, hWb, hVb⟩
    have h0 := hlow y hy V W
    have h3 := hk3 (y, V, W) ⟨hy, hVb, hWb⟩
    rw [Real.dist_eq] at h1 h3
    have h2 := (abs_lt.mp h1).2
    set G₀ := c₀ y V V * c₀ y W W - (c₀ y V W) ^ 2 with hG₀
    set Gk := c k y V V * c k y W W - (c k y V W) ^ 2 with hGkdef
    change |G₀ - Gk| < δ * lam ^ 2 / (2 * (|κ| + 1)) at h3
    have hκG : κ * G₀ - κ * Gk ≥ -(δ * lam ^ 2 / 2) := by
      have habs : |κ * G₀ - κ * Gk| ≤ |κ| * (δ * lam ^ 2 / (2 * (|κ| + 1))) := by
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left h3.le (abs_nonneg κ)
      have hfrac : |κ| * (δ * lam ^ 2 / (2 * (|κ| + 1))) ≤ δ * lam ^ 2 / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [abs_nonneg κ, mul_pos hδ (pow_pos hlam 2)]
      linarith [neg_abs_le (κ * G₀ - κ * Gk)]
    nlinarith [mul_le_mul_of_nonneg_left hGk hδ.le]
  by_cases hv0 : v = 0
  · exact lower_transfer_level hb hs hcoer (hdeg w) 0 0 1 0 (by simp [hv0]) (by simp)
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    set V : E := ‖v‖⁻¹ • v with hVdef
    have hV1 : ‖V‖ = 1 := by rw [hVdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
    have hvV : ‖v‖ • V + (0 : ℝ) • V = v := by
      rw [zero_smul, add_zero, hVdef, smul_inv_smul₀ hnv]
    set w' : E := w - inner ℝ V w • V with hw'def
    by_cases hw0 : w' = 0
    · refine lower_transfer_level hb hs hcoer (hdeg V) ‖v‖ 0 (inner ℝ V w) 0 hvV ?_
      rw [zero_smul, add_zero]
      exact (sub_eq_zero.1 hw0).symm
    · have hnw : ‖w'‖ ≠ 0 := norm_ne_zero_iff.2 hw0
      set W : E := ‖w'‖⁻¹ • w' with hWdef
      have hW1 : ‖W‖ = 1 := by rw [hWdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw]
      have hVW : inner ℝ V W = 0 := by
        rw [hWdef, real_inner_smul_right, hw'def, inner_sub_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hV1]
        ring
      refine lower_transfer_level hb hs hcoer (horth V W hV1 hW1 hVW) ‖v‖ 0 (inner ℝ V w) ‖w'‖
        (by rw [zero_smul, add_zero, hVdef, smul_inv_smul₀ hnv]) ?_
      rw [hWdef, smul_inv_smul₀ hnw, hw'def, add_sub_cancel]

end DifferentialGeometry.Analysis
