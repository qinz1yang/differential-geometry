import DifferentialGeometry.Analysis.Elliptic.Barrier.SupportComparison
import DifferentialGeometry.Analysis.Parabolic.Energy.CutoffEnergy

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradient_product_local (g : SmoothRiemannianMetric I M)
    (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g f)) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g h)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => f y * h y))) x := by
  have hr := mdifferentiableAt_add_section
    (hf.self_of_nhds.smul_section hgh) (hh.self_of_nhds.smul_section hgf)
  apply hr.congr_of_eventuallyEq
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) (gradientFun_mul g hfy hhy)

private theorem cutoff_square_dissipation
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T ε t : ℝ)
    (χ q : ℝ → M → ℝ) (x : M) (F : ShiCutoffLowerSupportAt G T ε χ t x)
    (B a w : ℝ) (hε : 0 ≤ ε) (hχ : χ t x ∈ Icc 0 1)
    (hB : 0 ≤ B) (hw : 0 ≤ w) (hq : 0 ≤ q t x) (hqB : q t x ≤ B)
    (htime : DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 T) t)
    (hspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y)
    (hgrad : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) (G.metric t) (q t))) x)
    (hgradSq : (G.metric t).inner x (gradientFun (I := I) (G.metric t) (q t) x)
      (gradientFun (I := I) (G.metric t) (q t) x) ≤ 4 * B * w)
    (hP : parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ -2 * w + a * q t x) :
    parabolicOperatorWithDrift G T (fun _ _ => 0) (fun s y => F.phi s y ^ 2 * q s y) t x ≤
      a * (F.phi t x ^ 2 * q t x) + 18 * ε * B := by
  let φ := F.phi
  let ψ := fun s y => φ s y * φ s y
  have hφ : φ t x ∈ Icc 0 1 := by simpa only [φ, F.eq_at] using hχ
  have hφ0 := hφ.1
  have hψtime := F.time_diff.mul F.time_diff
  have hψspace := F.space_diff_nhds.mono fun y hy => hy.mul hy
  have hψgrad := gradient_product_local (G.metric t) (φ t) (φ t) x
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hψ := parabolic_mul_local G T (fun _ _ => 0) φ φ t x F.time_diff F.time_diff
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hψq := parabolic_mul_local G T (fun _ _ => 0) ψ q t x hψtime htime
    hψspace hspace hψgrad hgrad
  have hvec : gradientFun (I := I) (G.metric t) (ψ t) x =
      (2 * φ t x) • gradientFun (I := I) (G.metric t) (φ t) x :=
    gradientFun_mul_self (G.metric t) F.space_diff_nhds.self_of_nhds
  have hnorm : (G.metric t).inner x (gradientFun (I := I) (G.metric t) (ψ t) x)
      (gradientFun (I := I) (G.metric t) (ψ t) x) ≤ (4 * ε * φ t x) * (φ t x ^ 2) := by
    rw [hvec]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left F.grad_sq_le (sq_nonneg (2 * φ t x))
    nlinarith only [hh]
  have hcross := cutoff_gradient_cross_le (G.metric t) x
    (gradientFun (I := I) (G.metric t) (ψ t) x) (gradientFun (I := I) (G.metric t) (q t) x)
    (4 * ε * φ t x) (φ t x ^ 2) B w (by positivity) (sq_nonneg _) hB hw hnorm hgradSq
  have hψP : parabolicOperatorWithDrift G T (fun _ _ => 0) ψ t x ≤ 2 * ε * φ t x := by
    have hg0 := metric_inner_self_nonneg (G.metric t) x (gradientFun (I := I) (G.metric t) (φ t) x)
    have hp := mul_le_mul_of_nonneg_left F.parabolic_le hφ.1
    simp only [gradientAt] at hψ
    dsimp only [ψ]
    nlinarith only [hψ, hp, hg0]
  have hp1 := mul_le_mul_of_nonneg_left hP (sq_nonneg (φ t x))
  have hp2 := mul_le_mul_of_nonneg_left hψP hq
  have hqterm := mul_le_mul_of_nonneg_left hqB (show 0 ≤ 2 * ε * φ t x by positivity)
  have hφterm := mul_le_mul_of_nonneg_left hφ.2 (show 0 ≤ 18 * ε * B by positivity)
  have hwterm := mul_nonneg (sq_nonneg (φ t x)) hw
  simp only [gradientAt] at hψq
  dsimp only [ψ, φ] at hψq hp1 hp2 hcross hqterm hφterm hwterm ⊢
  simp only [pow_two]
  nlinarith only [hψq, hp1, hp2, hcross, hqterm, hφterm, hwterm]

variable [I.Boundaryless]

theorem nonpositive_of_dissipation_and_cutoffs
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 < T)
    (q w : ℝ → M → ℝ) (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hcont : ContinuousOn (fun p : ℝ × M => q p.1 p.2) (Icc 0 T ×ˢ univ))
    (htime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (q t))
    (hinit : ∀ x : M, q 0 x ≤ 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ B)
    (hw : ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ w t x)
    (hgrad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < q t x →
      (G.metric t).inner x (gradientFun (I := I) (G.metric t) (q t) x)
        (gradientFun (I := I) (G.metric t) (q t) x) ≤ 4 * B * w t x)
    (hheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < q t x →
      parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ -2 * w t x + a * q t x)
    (hcut : ∀ O : M, Nonempty (ShiBarrierCutoffData G T O)) :
    ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ 0 := by
  intro t ht O
  obtain ⟨cut⟩ := hcut O
  have hb (n : ℕ) : ∀ s ∈ Icc 0 T, ∀ x : M,
      cut.chi n s x ^ 2 * q s x ≤ Real.exp (a * s) * (0 + (18 * cut.err n * B) * s) := by
    let Q := fun s x => cut.chi n s x ^ 2 * q s x
    apply scalar_linear_reaction_bound_support G T hT (fun _ _ => 0) Q
      (cut.support n) (cut.support_compact n) a (18 * cut.err n * B) 0 ha
      (mul_nonneg (mul_nonneg (by norm_num) (cut.err_nonneg n)) hB) le_rfl
    · exact ((cut.joint_cont n).pow 2).mul (hcont.mono (prod_mono subset_rfl (subset_univ _)))
    · intro s hs x hx
      simp only [Q, cut.support_zero n s hs x hx, zero_pow (by norm_num : 2 ≠ 0), zero_mul, le_refl]
    · intro x
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hinit x)
    · intro s hs hp x hpos
      have hχpos : 0 < cut.chi n s x := by
        by_contra hn
        have hz : cut.chi n s x = 0 := le_antisymm (le_of_not_gt hn) (cut.range n s x hs).1
        simp only [Q, hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul, lt_self_iff_false] at hpos
      have hqpos : 0 < q s x := by
        by_contra hn
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt hn))) hpos
      let F := cut.lowerSupport n s hs hp x hχpos
      have hsp : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (q s) y :=
        Eventually.of_forall fun y => (hspace s hs hp).mdifferentiableAt (by simp)
      have hg := gradientFun_mdiffAt (G.metric s) (hspace s hs hp) x
      have hFsp := F.space_diff_nhds.mono fun y hy => hy.mul hy
      have hFg := gradient_product_local (G.metric s) (F.phi s) (F.phi s) x
        F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
      refine ⟨fun r y => (F.phi r y * F.phi r y) * q r y, ?_, ?_,
        (F.time_diff.mul F.time_diff).mul (htime s hs hp x),
        hFsp.and hsp |>.mono (fun y hy => hy.1.mul hy.2),
        gradient_product_local (G.metric s) (fun y => F.phi s y * F.phi s y) (q s) x hFsp hsp hFg hg, ?_⟩
      · simp only [F.eq_at, Q, pow_two]
      · have hpositive : ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (s, x), 0 < q p.1 p.2 :=
          Tendsto.eventually_const_lt hqpos (hcont (s, x) ⟨hs, mem_univ x⟩)
        filter_upwards [F.lower_nhds, hpositive] with p hF hq
        dsimp only [Q]
        rw [← pow_two]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hF.1 hF.2 2) hq.le
      · simpa only [pow_two] using cutoff_square_dissipation G T (cut.err n) s (cut.chi n) q x F
          B a (w s x) (cut.err_nonneg n) (cut.range n s x hs) hB (hw s hs x) hqpos.le
          (hbound s hs x) (htime s hs hp x) hsp hg (hgrad s hs hp x hqpos) (hheat s hs hp x hqpos)
  have hlim : Tendsto (fun n => Real.exp (a * t) * (0 + (18 * cut.err n * B) * t)) atTop (𝓝 0) := by
    convert Tendsto.const_mul (Real.exp (a * t))
      (Tendsto.mul_const t (Tendsto.mul_const B (Tendsto.const_mul 18 cut.err_tendsto))) using 1 <;> simp
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [cut.center_exhausts t ht] with n hn
  simpa only [hn, one_pow, one_mul] using hb n t ht O

theorem scalar_quadratic_reaction_bound_cutoffs
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 < T)
    (u w : ℝ → M → ℝ) (c A B : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : c * (A + 1) * T ≤ 1 / 2)
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ univ))
    (htime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun r => u r x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hbound : ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ B)
    (hw : ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ w t x)
    (hgrad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      (G.metric t).inner x (gradientFun (I := I) (G.metric t) (u t) x)
        (gradientFun (I := I) (G.metric t) (u t) x) ≤ 4 * u t x * w t x)
    (hheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift G T (fun _ _ => 0) u t x ≤ -2 * w t x + c * (u t x + 1) ^ 2)
    (hinit : ∀ x : M, u 0 x ≤ A)
    (hcut : ∀ O : M, Nonempty (ShiBarrierCutoffData G T O)) :
    ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ 2 * A + 1 := by
  let v := fun t : ℝ => (A + 1) / (1 - c * (A + 1) * t) - 1
  have hden (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 - c * (A + 1) * t := by
    have hh := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hc (by linarith : 0 ≤ A + 1))
    linarith
  have hv : ContinuousOn v (Icc 0 T) :=
    (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun t ht => (hden t ht).ne')).sub continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt v (c * (v t + 1) ^ 2) (Icc 0 T) t := by
    have hlinear : HasDerivAt (fun r : ℝ => 1 - c * (A + 1) * r) (-(c * (A + 1))) t := by
      have hh := (hasDerivAt_const t (1 : ℝ)).sub
        ((hasDerivAt_id t).const_mul (c * (A + 1)))
      simp only [zero_sub, mul_one] at hh
      convert hh using 1
      all_goals rfl
    have hh := ((hasDerivAt_const t (A + 1)).div hlinear (hden t ht).ne').sub_const 1
    have he : (0 * (1 - c * (A + 1) * t) - (A + 1) * -(c * (A + 1))) /
        (1 - c * (A + 1) * t) ^ 2 = c * (v t + 1) ^ 2 := by
      dsimp only [v]
      rw [sub_add_cancel, div_pow]
      ring
    rw [he] at hh
    exact hh.hasDerivWithinAt
  have hv0 (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ v t := by
    dsimp only [v]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ (hden t ht)).mpr
    have hh := mul_nonneg (mul_nonneg hc (show 0 ≤ A + 1 by linarith)) ht.1
    nlinarith
  have hvbound (t : ℝ) (ht : t ∈ Icc 0 T) : v t ≤ 2 * A + 1 := by
    have hs : c * (A + 1) * t ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hc (by linarith : 0 ≤ A + 1))).trans hsmall
    have hvb : (A + 1) / (1 - c * (A + 1) * t) ≤ 2 * (A + 1) := by
      apply (div_le_iff₀ (hden t ht)).mpr
      nlinarith
    dsimp only [v]
    linarith
  let q := fun t x => u t x - v t
  let a := c * (B + 2 * A + 3)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hqc : ContinuousOn (fun p : ℝ × M => q p.1 p.2) (Icc 0 T ×ˢ univ) :=
    hu.sub (hv.comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hqb (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) : q t x ≤ B := by
    dsimp only [q]
    linarith [hbound t ht x, hv0 t ht]
  have hqP (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : M) (hqpos : 0 < q t x) :
      parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ -2 * w t x + a * q t x := by
    dsimp only [q]
    rw [parabolic_sub_time_curve_identity G T (fun _ _ => 0) u v t
      (fun y => (hspace t ht hp).mdifferentiableAt (by simp)) x (htime t ht hp x)
      (hd t ht).differentiableWithinAt, (hd t ht).derivWithin ((uniqueDiffOn_Icc hT) t ht)]
    have hcoef : c * (u t x + v t + 2) ≤ a := by
      apply mul_le_mul_of_nonneg_left _ hc
      linarith [hbound t ht x, hvbound t ht]
    have hm := mul_le_mul_of_nonneg_right hcoef hqpos.le
    dsimp only [q] at hm
    nlinarith only [hheat t ht hp x, hm]
  have hqg (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : M) (_hqpos : 0 < q t x) :
      (G.metric t).inner x (gradientFun (I := I) (G.metric t) (q t) x)
        (gradientFun (I := I) (G.metric t) (q t) x) ≤ 4 * B * w t x := by
    have he : gradientFun (I := I) (G.metric t) (q t) x =
        gradientFun (I := I) (G.metric t) (u t) x := by
      dsimp only [q]
      rw [gradientFun_sub (G.metric t) ((hspace t ht hp).mdifferentiableAt (by simp))
        mdifferentiableAt_const, gradientFun_const, sub_zero]
    rw [he]
    exact (hgrad t ht hp x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound t ht x) (by norm_num : (0 : ℝ) ≤ 4)) (hw t ht x))
  have hb := nonpositive_of_dissipation_and_cutoffs G T hT q w a B ha hB hqc
    (fun t ht hp x => (htime t ht hp x).sub (hd t ht).differentiableWithinAt)
    (fun t ht hp => (hspace t ht hp).sub contMDiff_const)
    (by simpa only [q, v, mul_zero, sub_zero, div_one, add_sub_cancel_right,
      sub_nonpos] using hinit) hqb hw hqg hqP hcut
  intro t ht x
  exact (sub_nonpos.mp (hb t ht x)).trans (hvbound t ht)
end DifferentialGeometry.Analysis
