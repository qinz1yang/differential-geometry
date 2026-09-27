import DifferentialGeometry.Analysis.Elliptic.Barrier.SupportComparison
import DifferentialGeometry.Analysis.Parabolic.Energy.CutoffEnergy
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradient_product_local
    (g : SmoothRiemannianMetric I M)
    (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g f)) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g h)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => f y * h y))) x := by
  have hr := mdifferentiableAt_add_section
    (hf.self_of_nhds.smul_section hgh)
    (hh.self_of_nhds.smul_section hgf)
  apply hr.congr_of_eventuallyEq
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg
    (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    (gradientFun_mul g hfy hhy)

private theorem cutoff_square_dissipation
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T ε t : ℝ) (χ q : ℝ → M → ℝ) (x : M)
    (F : ShiCutoffLowerSupportAt G T ε χ t x)
    (B a w : ℝ)
    (hε : 0 ≤ ε) (hχ : χ t x ∈ Icc 0 1)
    (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hq : 0 ≤ q t x) (hqB : q t x ≤ B)
    (htime : DifferentiableWithinAt ℝ
      (fun s => q s x) (Icc 0 T) t)
    (hspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y)
    (hgrad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (q t))) x)
    (hgradSq :
      (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (q t) x)
        (gradientFun (I := I) (G.metric t) (q t) x) ≤
          4 * B * w)
    (hP :
      parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤
        -2 * w + a * q t x) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
        (fun s y => F.phi s y ^ 2 * q s y) t x ≤
      a * (F.phi t x ^ 2 * q t x) + 18 * ε * B := by
  let φ := F.phi
  let ψ := fun s y => φ s y * φ s y
  have hφ : φ t x ∈ Icc 0 1 := by
    simpa only [φ, F.eq_at] using hχ
  have hφ0 := hφ.1
  have hψtime := F.time_diff.mul F.time_diff
  have hψspace := F.space_diff_nhds.mono fun y hy => hy.mul hy
  have hψgrad := gradient_product_local (G.metric t) (φ t) (φ t) x
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hψ := parabolic_mul_local G T (fun _ _ => 0) φ φ t x
    F.time_diff F.time_diff F.space_diff_nhds F.space_diff_nhds
    F.grad_diff F.grad_diff
  have hψq := parabolic_mul_local G T (fun _ _ => 0) ψ q t x
    hψtime htime hψspace hspace hψgrad hgrad
  have hvec :
      gradientFun (I := I) (G.metric t) (ψ t) x =
        (2 * φ t x) •
          gradientFun (I := I) (G.metric t) (φ t) x :=
    gradientFun_mul_self (G.metric t) F.space_diff_nhds.self_of_nhds
  have hnorm :
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (ψ t) x)
          (gradientFun (I := I) (G.metric t) (ψ t) x) ≤
        (4 * ε * φ t x) * (φ t x ^ 2) := by
    rw [hvec]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left F.grad_sq_le
      (sq_nonneg (2 * φ t x))
    nlinarith only [hh]
  have hcross := cutoff_gradient_cross_le (G.metric t) x
    (gradientFun (I := I) (G.metric t) (ψ t) x)
    (gradientFun (I := I) (G.metric t) (q t) x)
    (4 * ε * φ t x) (φ t x ^ 2) B w
    (by positivity) (sq_nonneg _) hB hw hnorm hgradSq
  have hψP :
      parabolicOperatorWithDrift G T (fun _ _ => 0) ψ t x ≤
        2 * ε * φ t x := by
    have hg0 := metric_inner_self_nonneg (G.metric t) x
      (gradientFun (I := I) (G.metric t) (φ t) x)
    have hp := mul_le_mul_of_nonneg_left F.parabolic_le hφ.1
    simp only [gradientAt] at hψ
    dsimp only [ψ]
    nlinarith only [hψ, hp, hg0]
  have hp1 := mul_le_mul_of_nonneg_left hP (sq_nonneg (φ t x))
  have hp2 := mul_le_mul_of_nonneg_left hψP hq
  have hqterm := mul_le_mul_of_nonneg_left hqB
    (show 0 ≤ 2 * ε * φ t x by positivity)
  have hφterm := mul_le_mul_of_nonneg_left hφ.2
    (show 0 ≤ 18 * ε * B by positivity)
  have hwterm := mul_nonneg (sq_nonneg (φ t x)) hw
  simp only [gradientAt] at hψq
  dsimp only [ψ, φ] at hψq hp1 hp2 hcross hqterm hφterm hwterm ⊢
  simp only [pow_two]
  nlinarith only [hψq, hp1, hp2, hcross, hqterm, hφterm, hwterm]

variable [I.Boundaryless]

private theorem nonpositive_of_dissipative_lower_supports
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (hT : 0 < T)
    (q : ℝ → M → ℝ) (a B : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hcont : ContinuousOn (fun p : ℝ × M => q p.1 p.2)
      (Icc 0 T ×ˢ univ))
    (hinit : ∀ x : M, q 0 x ≤ 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ B)
    (hsupport : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < q t x →
      ∃ v : ℝ → M → ℝ, ∃ w : ℝ,
        v t x = q t x ∧
        (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
          v p.1 p.2 ≤ q p.1 p.2) ∧
        ContinuousWithinAt (fun p : ℝ × M => v p.1 p.2)
          (spacetimeSlab (M := M) T) (t, x) ∧
        DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y) ∧
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (gradientFun (I := I) (G.metric t) (v t))) x ∧
        0 ≤ w ∧
        (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (v t) x)
          (gradientFun (I := I) (G.metric t) (v t) x) ≤
            4 * B * w ∧
        parabolicOperatorWithDrift G T (fun _ _ => 0) v t x ≤
          -2 * w + a * v t x)
    (hcut : ∀ O : M, Nonempty (ShiBarrierCutoffData G T O)) :
    ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ 0 := by
  intro t ht O
  obtain ⟨cut⟩ := hcut O
  have hb (n : ℕ) : ∀ s ∈ Icc 0 T, ∀ x : M,
      cut.chi n s x ^ 2 * q s x ≤
        Real.exp (a * s) * (0 + (18 * cut.err n * B) * s) := by
    let Q := fun s x => cut.chi n s x ^ 2 * q s x
    apply scalar_linear_reaction_bound_support G T hT
      (fun _ _ => 0) Q (cut.support n) (cut.support_compact n)
      a (18 * cut.err n * B) 0 ha
      (mul_nonneg (mul_nonneg (by norm_num) (cut.err_nonneg n)) hB)
      le_rfl
    · exact ((cut.joint_cont n).pow 2).mul
        (hcont.mono (prod_mono subset_rfl (subset_univ _)))
    · intro s hs x hx
      simp only [Q, cut.support_zero n s hs x hx,
        zero_pow (by norm_num : 2 ≠ 0), zero_mul, le_refl]
    · intro x
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hinit x)
    · intro s hs hp x hpos
      have hχpos : 0 < cut.chi n s x := by
        by_contra hn
        have hz : cut.chi n s x = 0 :=
          le_antisymm (le_of_not_gt hn) (cut.range n s x hs).1
        simp only [Q, hz, zero_pow (by norm_num : 2 ≠ 0),
          zero_mul, lt_self_iff_false] at hpos
      have hqpos : 0 < q s x := by
        by_contra hn
        exact (not_lt_of_ge
          (mul_nonpos_of_nonneg_of_nonpos
            (sq_nonneg _) (le_of_not_gt hn))) hpos
      obtain ⟨v, w, heq, hle, hvc, htime, hspace, hgrad,
        hw, hvg, hP⟩ := hsupport s hs hp x hqpos
      have hvpos : 0 < v s x := by
        rw [heq]
        exact hqpos
      let F := cut.lowerSupport n s hs hp x hχpos
      have hFsp := F.space_diff_nhds.mono fun y hy => hy.mul hy
      have hFg := gradient_product_local (G.metric s) (F.phi s) (F.phi s) x
        F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
      refine ⟨fun r y => (F.phi r y * F.phi r y) * v r y, ?_, ?_,
        (F.time_diff.mul F.time_diff).mul htime,
        hFsp.and hspace |>.mono (fun y hy => hy.1.mul hy.2),
        gradient_product_local (G.metric s)
          (fun y => F.phi s y * F.phi s y) (v s) x
          hFsp hspace hFg hgrad, ?_⟩
      · simp only [F.eq_at, heq, Q, pow_two]
      · have hpositive :
            ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (s, x),
              0 < v p.1 p.2 :=
          Tendsto.eventually_const_lt hvpos hvc
        filter_upwards [F.lower_nhds, hle, hpositive] with p hF hvle hvpos
        dsimp only [Q]
        rw [← pow_two]
        exact mul_le_mul
          (pow_le_pow_left₀ hF.1 hF.2 2)
          hvle hvpos.le (sq_nonneg _)
      · simpa only [pow_two] using
          cutoff_square_dissipation G T (cut.err n) s
            (cut.chi n) v x F B a w
            (cut.err_nonneg n) (cut.range n s x hs)
            hB hw hvpos.le
            (by rw [heq]; exact hbound s hs x)
            htime hspace hgrad hvg hP
  have hlim :
      Tendsto
        (fun n => Real.exp (a * t) * (0 + (18 * cut.err n * B) * t))
        atTop (𝓝 0) := by
    convert Tendsto.const_mul (Real.exp (a * t))
      (Tendsto.mul_const t
        (Tendsto.mul_const B (Tendsto.const_mul 18 cut.err_tendsto)))
      using 1 <;> simp
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [cut.center_exhausts t ht] with n hn
  simpa only [hn, one_pow, one_mul] using hb n t ht O

theorem nonpositive_of_linear_reaction_lower_supports_and_cutoffs
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (hT : 0 < T)
    (q : ℝ → M → ℝ) (a C : ℝ) (ha : 0 ≤ a)
    (hcont : ContinuousOn (fun p : ℝ × M => q p.1 p.2)
      (Icc 0 T ×ˢ univ))
    (hinit : ∀ x : M, q 0 x ≤ 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ C)
    (hsupport : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < q t x →
      ∃ v : ℝ → M → ℝ,
        v t x = q t x ∧
        (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
          v p.1 p.2 ≤ q p.1 p.2) ∧
        ContinuousWithinAt (fun p : ℝ × M => v p.1 p.2)
          (spacetimeSlab (M := M) T) (t, x) ∧
        DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y) ∧
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (gradientFun (I := I) (G.metric t) (v t))) x ∧
        parabolicOperatorWithDrift G T (fun _ _ => 0) v t x ≤
          a * v t x)
    (hcut : ∀ O : M, Nonempty (ShiBarrierCutoffData G T O)) :
    ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ 0 := by
  let φ : ℝ → ℝ := fun r => Real.exp r - 1
  let u : ℝ → M → ℝ := fun t x => φ (q t x)
  let B : ℝ := Real.exp C
  have hB : 0 ≤ B := (Real.exp_pos C).le
  have hφdiff : Differentiable ℝ φ := by
    simpa only [φ] using Real.differentiable_exp.sub_const 1
  have hφderiv : deriv φ = Real.exp := by
    funext r
    exact ((Real.hasDerivAt_exp r).sub_const 1).deriv
  have hucont :
      ContinuousOn (fun p : ℝ × M => u p.1 p.2)
        (Icc 0 T ×ˢ univ) := by
    have hh := (Real.continuous_exp.comp_continuousOn hcont).sub
      (continuousOn_const (c := (1 : ℝ)))
    convert hh using 1
    rfl
  have huinit : ∀ x : M, u 0 x ≤ 0 := by
    intro x
    change Real.exp (q 0 x) - 1 ≤ 0
    exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (hinit x))
  have hubound : ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ B := by
    intro t ht x
    have he := Real.exp_le_exp.mpr (hbound t ht x)
    change Real.exp (q t x) - 1 ≤ Real.exp C
    linarith only [he]
  have husupport :
      ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < u t x →
      ∃ V : ℝ → M → ℝ, ∃ w : ℝ,
        V t x = u t x ∧
        (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
          V p.1 p.2 ≤ u p.1 p.2) ∧
        ContinuousWithinAt (fun p : ℝ × M => V p.1 p.2)
          (spacetimeSlab (M := M) T) (t, x) ∧
        DifferentiableWithinAt ℝ (fun s => V s x) (Icc 0 T) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (V t) y) ∧
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (gradientFun (I := I) (G.metric t) (V t))) x ∧
        0 ≤ w ∧
        (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (V t) x)
          (gradientFun (I := I) (G.metric t) (V t) x) ≤
            4 * B * w ∧
        parabolicOperatorWithDrift G T (fun _ _ => 0) V t x ≤
          -2 * w + (a * B) * V t x := by
    intro t ht hp x hupos
    have hqpos : 0 < q t x := by
      by_contra hn
      have he := Real.exp_le_one_iff.mpr (le_of_not_gt hn)
      change 0 < Real.exp (q t x) - 1 at hupos
      linarith only [he, hupos]
    obtain ⟨v, heq, hle, hvc, htime, hspace, hgrad, hP⟩ :=
      hsupport t ht hp x hqpos
    let V : ℝ → M → ℝ := fun s y => φ (v s y)
    let N : ℝ :=
      (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (v t) x)
        (gradientFun (I := I) (G.metric t) (v t) x)
    let w : ℝ := Real.exp (v t x) / 2 * N
    have hN : 0 ≤ N := metric_inner_self_nonneg (G.metric t) x _
    have hw : 0 ≤ w :=
      mul_nonneg
        (div_nonneg (Real.exp_pos (v t x)).le (by norm_num)) hN
    have he : Real.exp (v t x) ≤ B := by
      rw [heq]
      exact Real.exp_le_exp.mpr (hbound t ht x)
    have hv0 : 0 ≤ v t x := by
      rw [heq]
      exact hqpos.le
    have hφ' : DifferentiableAt ℝ (deriv φ) (v t x) := by
      rw [hφderiv]
      exact Real.differentiable_exp _
    have hVtime :
        DifferentiableWithinAt ℝ (fun s => V s x) (Icc 0 T) t := by
      simpa only [V, φ] using htime.exp.sub_const 1
    have hVspace :
        ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (V t) y :=
      hspace.mono fun y hy =>
        (hφdiff (v t y)).mdifferentiableAt.comp y hy
    have hVgrad :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (gradientFun (I := I) (G.metric t) (V t))) x :=
      grad_comp_mdiffAt (I := I) (G.metric t)
        hφdiff hφ' hspace hgrad
    have hVg :
        (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (V t) x)
          (gradientFun (I := I) (G.metric t) (V t) x) ≤
            4 * B * w := by
      have hg :
          gradientFun (I := I) (G.metric t) (V t) x =
            Real.exp (v t x) •
              gradientFun (I := I) (G.metric t) (v t) x := by
        simpa only [V, hφderiv] using
          (gradientFun_comp (I := I) (G.metric t)
            (φ := φ) (f := v t)
            (hφdiff (v t x)) hspace.self_of_nhds)
      have heN : 0 ≤ Real.exp (v t x) * N :=
        mul_nonneg (Real.exp_pos (v t x)).le hN
      calc
        (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) (V t) x)
            (gradientFun (I := I) (G.metric t) (V t) x) =
            Real.exp (v t x) * (Real.exp (v t x) * N) := by
          rw [hg]
          simp only [map_smul, smul_apply, smul_eq_mul]
          rfl
        _ ≤ B * (Real.exp (v t x) * N) :=
          mul_le_mul_of_nonneg_right he heN
        _ = 2 * B * w := by
          dsimp only [w]
          ring
        _ ≤ 4 * B * w := by
          nlinarith only [mul_nonneg hB hw]
    have hVP :
        parabolicOperatorWithDrift G T (fun _ _ => 0) V t x ≤
          -2 * w + (a * B) * V t x := by
      have hc :
          parabolicOperatorWithDrift G T (fun _ _ => 0) V t x =
            Real.exp (v t x) *
                parabolicOperatorWithDrift G T (fun _ _ => 0) v t x -
              Real.exp (v t x) * N := by
        simpa only [V, hφderiv, Real.deriv_exp, gradientAt, N] using
          (parabolic_comp_nhds (I := I) G T (fun _ _ => 0)
            (φ := φ) v t x hφdiff hφ' htime hspace hgrad)
      have hvexp : v t x ≤ V t x := by
        have hh := Real.add_one_le_exp (v t x)
        change v t x ≤ Real.exp (v t x) - 1
        linarith only [hh]
      have hp1 := mul_le_mul_of_nonneg_left hP
        (Real.exp_pos (v t x)).le
      have hp2 :
          Real.exp (v t x) * (a * v t x) ≤
            (a * B) * V t x := by
        calc
          Real.exp (v t x) * (a * v t x) =
              a * (Real.exp (v t x) * v t x) := by ring
          _ ≤ a * (B * v t x) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right he hv0) ha
          _ = (a * B) * v t x := by ring
          _ ≤ (a * B) * V t x :=
            mul_le_mul_of_nonneg_left hvexp (mul_nonneg ha hB)
      rw [hc]
      dsimp only [w]
      nlinarith only [hp1, hp2]
    refine ⟨V, w, ?_, ?_, ?_,
      hVtime, hVspace, hVgrad, hw, hVg, hVP⟩
    · change Real.exp (v t x) - 1 = Real.exp (q t x) - 1
      rw [heq]
    · filter_upwards [hle] with p hp
      exact sub_le_sub_right (Real.exp_le_exp.mpr hp) 1
    · have hh :=
        (Real.continuous_exp.continuousAt.comp_continuousWithinAt hvc).sub
          (continuousWithinAt_const (b := (1 : ℝ)))
      convert hh using 1
      rfl
  have hu := nonpositive_of_dissipative_lower_supports G T hT
    u (a * B) B (mul_nonneg ha hB) hB
    hucont huinit hubound husupport hcut
  intro t ht x
  have hh := hu t ht x
  change Real.exp (q t x) - 1 ≤ 0 at hh
  exact Real.exp_le_one_iff.mp (by linarith only [hh])

end DifferentialGeometry.Analysis
