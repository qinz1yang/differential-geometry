import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.TravelingBallComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem traveling_phase_laplacian
    (G : MetricConnectionFamily (I := 𝓡 3) (M := E3) ℝ)
    (T : ℝ) (x₀ : E3) (r s : ℝ) (x : E3) :
    laplacianAt G s (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x =
      -laplacianAt G s (fun y : E3 => ‖y‖ ^ 2) x +
        (2 * (s / T)) *
          laplacianAt G s (fun y : E3 => ⟪y, x₀⟫_ℝ) x := by
  let f₀ : E3 → ℝ := fun y => ‖y‖ ^ 2
  let f₁ : E3 → ℝ := fun y => ⟪y, x₀⟫_ℝ
  have h₀ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f₀ :=
    (contDiff_norm_sq ℝ).contMDiff
  have h₁ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f₁ :=
    ((contDiff_id (E := E3)).inner ℝ contDiff_const).contMDiff
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ((-1 : ℝ) • f₀) :=
    show ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => (-1 : ℝ) * f₀ y) from
      contMDiff_const.mul h₀
  have hl : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ((2 * (s / T)) • f₁) :=
    show ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => (2 * (s / T)) * f₁ y) from
      contMDiff_const.mul h₁
  have hh := hn.add hl
  have heq :
      DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s =
        fun y => (r ^ 2 - ‖(s / T) • x₀‖ ^ 2) +
          (((-1 : ℝ) • f₀ + (2 * (s / T)) • f₁) y) := by
    funext y
    dsimp only [DifferentialGeometry.Analysis.travelingBallPhase, f₀, f₁,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [norm_sub_sq_real, real_inner_smul_right]
    ring
  rw [heq]
  have hc := laplacian_add_const (G.connection s) (G.metric s)
    (r ^ 2 - ‖(s / T) • x₀‖ ^ 2)
    (Eventually.of_forall fun y => hh.mdifferentiableAt (by simp))
    (gradientFun_mdiffAt (G.metric s) hh x)
  change laplacianAt G s
      (fun y => (r ^ 2 - ‖(s / T) • x₀‖ ^ 2) +
        (((-1 : ℝ) • f₀ + (2 * (s / T)) • f₁) y)) x =
    laplacianAt G s ((-1 : ℝ) • f₀ + (2 * (s / T)) • f₁) x at hc
  rw [hc]
  have hadd : laplacianAt G s ((-1 : ℝ) • f₀ + (2 * (s / T)) • f₁) x =
      laplacianAt G s ((-1 : ℝ) • f₀) x +
        laplacianAt G s ((2 * (s / T)) • f₁) x :=
    laplacianAt_add G s
      (fun y => hn.mdifferentiableAt (by simp))
      (fun y => hl.mdifferentiableAt (by simp))
      (gradientFun_mdiffAt (G.metric s) hn x)
      (gradientFun_mdiffAt (G.metric s) hl x)
  have hnLap : laplacianAt G s ((-1 : ℝ) • f₀) x =
      (-1 : ℝ) * laplacianAt G s f₀ x :=
    laplacianAt_smul G s (-1 : ℝ)
      (fun y => h₀.mdifferentiableAt (by simp))
      (gradientFun_mdiffAt (G.metric s) h₀ x)
  have hlLap : laplacianAt G s ((2 * (s / T)) • f₁) x =
      (2 * (s / T)) * laplacianAt G s f₁ x :=
    laplacianAt_smul G s (2 * (s / T))
      (fun y => h₁.mdifferentiableAt (by simp))
      (gradientFun_mdiffAt (G.metric s) h₁ x)
  rw [hadd, hnLap, hlLap]
  change (-1 : ℝ) * laplacianAt G s f₀ x +
      (2 * (s / T)) * laplacianAt G s f₁ x =
    -laplacianAt G s f₀ x +
      (2 * (s / T)) * laplacianAt G s f₁ x
  ring

private theorem traveling_phase_time_derivative
    (T : ℝ) (x₀ : E3) (r s : ℝ) (x : E3) :
    HasDerivAt
      (fun t => DifferentialGeometry.Analysis.travelingBallPhase T x₀ r t x)
      ((2 / T) * ⟪x - (s / T) • x₀, x₀⟫_ℝ) s := by
  have hz := (hasDerivAt_const (x := s) (c := x)).sub
    (((hasDerivAt_id s).div_const T).smul_const x₀)
  have hh := (hasDerivAt_const (x := s) (c := r ^ 2)).sub hz.norm_sq
  change HasDerivAt
    (fun t => r ^ 2 - ‖x - (t / T) • x₀‖ ^ 2) _ s
  have he : (2 / T) * ⟪x - (s / T) • x₀, x₀⟫_ℝ =
      0 - 2 * ⟪x - (s / T) • x₀, (0 : E3) - (1 / T) • x₀⟫_ℝ := by
    simp only [zero_sub, inner_neg_right, real_inner_smul_right]
    ring
  rw [he]
  exact hh

private theorem traveling_phase_operator
    (G : MetricConnectionFamily (I := 𝓡 3) (M := E3) ℝ)
    (T : ℝ) (hT : 0 < T) (x₀ : E3) (r s : ℝ)
    (hs : s ∈ Icc 0 T) (x : E3) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
      (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r) s x =
      (2 / T) * ⟪x - (s / T) • x₀, x₀⟫_ℝ +
        laplacianAt G s (fun y : E3 => ‖y‖ ^ 2) x -
        (2 * (s / T)) *
          laplacianAt G s (fun y : E3 => ⟪y, x₀⟫_ℝ) x := by
  rw [parabolicOperatorWithDrift_eq,
    (traveling_phase_time_derivative T x₀ r s x).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hT) s hs),
    heatOperatorWithDrift_zero_drift]
  change (2 / T) * ⟪x - (s / T) • x₀, x₀⟫_ℝ -
      laplacianAt G s (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x = _
  rw [traveling_phase_laplacian]
  ring

private theorem traveling_phase_gradient_lower
    (g : SmoothRiemannianMetric (𝓡 3) E3)
    (T : ℝ) (x₀ : E3) (r s : ℝ) (x : E3)
    (M : ℝ) (hM : 0 < M)
    (hmetric : ∀ v : E3, g.inner x v v ≤ M * ‖v‖ ^ 2) :
    (4 / M) * ‖x - (s / T) • x₀‖ ^ 2 ≤
      g.inner x
        (gradientFun g (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x)
        (gradientFun g (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x) := by
  let z : E3 := x - (s / T) • x₀
  let V := gradientFun g (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x
  let q : ℝ := g.inner x V V
  have hq : 0 ≤ q := metric_inner_self_nonneg g x V
  have hpair : g.inner x V z = -2 * ‖z‖ ^ 2 := by
    have hd :=
      (((hasFDerivAt_id x).sub_const ((s / T) • x₀)).norm_sq).const_sub (r ^ 2)
    calc
      g.inner x V z =
          mvfderiv (I := 𝓡 3)
            (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x z :=
        inner_gradientFun g _ x z
      _ = fderiv ℝ
          (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x z := by
        change (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) x) z = _
        exact congrArg (fun L : E3 →L[ℝ] ℝ => L z)
          (mfderiv_eq_fderiv (𝕜 := ℝ)
            (f := DifferentialGeometry.Analysis.travelingBallPhase T x₀ r s) (x := x))
      _ = -2 * ‖z‖ ^ 2 := by
        change fderiv ℝ
          (fun y : E3 => r ^ 2 - ‖y - (s / T) • x₀‖ ^ 2) x z = _
        calc
          _ = (-(2 • (innerSL ℝ z)).comp (ContinuousLinearMap.id ℝ E3)) z :=
            congrArg (fun L : E3 →L[ℝ] ℝ => L z) hd.fderiv
          _ = -(2 * ⟪z, z⟫_ℝ) := by simp
          _ = -2 * ‖z‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]; ring
  by_cases hz : z = 0
  · change (4 / M) * ‖z‖ ^ 2 ≤ q
    simpa only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hq
  · have hzsq : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g x V z
    rw [hpair] at hcs
    have hprod : (4 * ‖z‖ ^ 2) * ‖z‖ ^ 2 ≤ (q * M) * ‖z‖ ^ 2 := by
      calc
        (4 * ‖z‖ ^ 2) * ‖z‖ ^ 2 = (-2 * ‖z‖ ^ 2) ^ 2 := by ring
        _ ≤ q * g.inner x z z := hcs
        _ ≤ q * (M * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hmetric z) hq
        _ = (q * M) * ‖z‖ ^ 2 := by ring
    have hcancel : 4 * ‖z‖ ^ 2 ≤ q * M :=
      (mul_le_mul_iff_left₀ hzsq).mp hprod
    change (4 / M) * ‖z‖ ^ 2 ≤ q
    calc
      (4 / M) * ‖z‖ ^ 2 = (4 * ‖z‖ ^ 2) / M := by ring
      _ ≤ q := (div_le_iff₀ hM).mpr hcancel

theorem PartialStandardSolution.exists_traveling_phase_coefficients
    (S : PartialStandardSolution)
    (a t₀ : ℝ) (ha : 0 < a) (hat : a < t₀)
    (hTl : ENNReal.ofReal t₀ < S.lifetime)
    (x₀ : E3) (r : ℝ) (hr : 0 < r) :
    let Q := S.toSolutionOn.timeShift a
    let G := flowG Q
    let τ := t₀ - a
    (∀ s : ℝ, G.metric s = S.metric (s + a)) ∧
    (∀ s ∈ Icc 0 τ, s + a ∈ S.domain) ∧
    (Icc 0 τ ⊆
      ((lifetimeInterval S.lifetime S.lifetime_pos).timeShift a).regular) ∧
    ∃ C c : ℝ, 0 < c ∧
      (∀ s ∈ Icc 0 τ, ∀ x : E3,
        0 < DifferentialGeometry.Analysis.travelingBallPhase τ x₀ r s x →
          parabolicOperatorWithDrift G τ (fun _ _ => 0)
            (DifferentialGeometry.Analysis.travelingBallPhase τ x₀ r) s x ≤ C) ∧
      (∀ s ∈ Icc 0 τ, ∀ x : E3,
        c * ‖x - (s / τ) • x₀‖ ^ 2 ≤
          (G.metric s).inner x
            (gradientAt G s (DifferentialGeometry.Analysis.travelingBallPhase τ x₀ r s) x)
            (gradientAt G s (DifferentialGeometry.Analysis.travelingBallPhase τ x₀ r s) x)) := by
  let Q := S.toSolutionOn.timeShift a
  let G := flowG Q
  let τ : ℝ := t₀ - a
  have hτ : 0 < τ := sub_pos.mpr hat
  have ht₀ : 0 < t₀ := ha.trans hat
  have hshift (s : ℝ) (hs : s ∈ Icc 0 τ) : s + a ∈ Icc a t₀ := by
    refine ⟨by linarith only [hs.1], ?_⟩
    have hu := hs.2
    change s ≤ t₀ - a at hu
    linarith only [hu]
  have hreg :
      Icc 0 τ ⊆
        ((lifetimeInterval S.lifetime S.lifetime_pos).timeShift a).regular := by
    intro s hs
    have hh := hshift s hs
    change s + a ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos (s + a)).mpr
      ⟨ha.trans_le hh.1, (ENNReal.ofReal_le_ofReal hh.2).trans_lt hTl⟩
  have hcarrier : ∀ s ∈ Icc 0 τ, s + a ∈ S.domain := by
    intro s hs
    exact (lifetimeInterval S.lifetime S.lifetime_pos).regular_subset (hreg hs)
  have hQ : IsSolutionOn Q := isSolutionOn_timeShift S.isSolutionOn a
  have hf₀ :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : E3 => ‖y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).contMDiff
  have hf₁ :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : E3 => ⟪y, x₀⟫_ℝ) :=
    ((contDiff_id (E := E3)).inner ℝ contDiff_const).contMDiff
  have hL₀ :
      ContinuousOn
        (fun p : ℝ × E3 => laplacianAt G p.1 (fun y : E3 => ‖y‖ ^ 2) p.2)
        (Icc 0 τ ×ˢ (univ : Set E3)) :=
    G.laplacianAt_continuousOn hQ.smoothMetric hreg
      (uniqueDiffOn_Icc hτ) (fun _ _ => rfl) hf₀
  have hL₁ :
      ContinuousOn
        (fun p : ℝ × E3 => laplacianAt G p.1 (fun y : E3 => ⟪y, x₀⟫_ℝ) p.2)
        (Icc 0 τ ×ˢ (univ : Set E3)) :=
    G.laplacianAt_continuousOn hQ.smoothMetric hreg
      (uniqueDiffOn_Icc hτ) (fun _ _ => rfl) hf₁
  have htime :
      Continuous (fun p : ℝ × E3 =>
        (2 / τ) * ⟪p.2 - (p.1 / τ) • x₀, x₀⟫_ℝ) :=
    continuous_const.mul
      ((continuous_snd.sub
        ((continuous_fst.div_const τ).smul continuous_const)).inner continuous_const)
  have hcoef :
      Continuous (fun p : ℝ × E3 => 2 * (p.1 / τ)) :=
    continuous_const.mul (continuous_fst.div_const τ)
  have hP :
      ContinuousOn
        (fun p : ℝ × E3 =>
          parabolicOperatorWithDrift G τ (fun _ _ => 0)
            (DifferentialGeometry.Analysis.travelingBallPhase τ x₀ r) p.1 p.2)
        (Icc 0 τ ×ˢ (univ : Set E3)) := by
    apply ((htime.continuousOn.add hL₀).sub
      (hcoef.continuousOn.mul hL₁)).congr
    intro p hp
    exact traveling_phase_operator G τ hτ x₀ r p.1 hp.1 p.2
  let U : Set E3 := Metric.closedBall (0 : E3) (r + ‖x₀‖)
  have hcompact : IsCompact (Icc 0 τ ×ˢ U) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn
    (hP.mono (prod_mono subset_rfl (subset_univ U)))
  obtain ⟨K, hK, hRm⟩ := S.curvature_bound t₀ ht₀.le hTl
  let M : ℝ := Real.exp (18 * K * t₀)
  have hM : 0 < M := Real.exp_pos _
  have hmetric (s : ℝ) (hs : s ∈ Icc 0 τ) (x v : E3) :
      (G.metric s).inner x v v ≤ M * ‖v‖ ^ 2 := by
    have hh := hshift s hs
    have hcompare := (S.metric_comparison_closed hTl hK hRm
      (s + a) ⟨ha.le.trans hh.1, hh.2⟩ x v).2
    change (G.metric s).inner x v v ≤
      Real.exp (18 * K * (s + a)) *
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v at hcompare
    have hexp : Real.exp (18 * K * (s + a)) ≤ M :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hh.2 (mul_nonneg (by norm_num) hK))
    have hcap :
        0 ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v :=
      metric_inner_self_nonneg DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x v
    exact hcompare.trans
      ((mul_le_mul_of_nonneg_right hexp hcap).trans
        (mul_le_mul_of_nonneg_left
          (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_le x v) hM.le))
  refine ⟨fun _ => rfl, hcarrier, hreg, B, 4 / M,
    div_pos (by norm_num) hM, ?_, ?_⟩
  · intro s hs x hf
    have hdist : ‖x - (s / τ) • x₀‖ < r := by
      apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
      dsimp only [DifferentialGeometry.Analysis.travelingBallPhase] at hf
      linarith only [hf]
    have hu₀ : 0 ≤ s / τ := div_nonneg hs.1 hτ.le
    have hu₁ : s / τ ≤ 1 := (div_le_one hτ).mpr hs.2
    have hpath : ‖(s / τ) • x₀‖ ≤ ‖x₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu₀]
      calc
        (s / τ) * ‖x₀‖ ≤ 1 * ‖x₀‖ :=
          mul_le_mul_of_nonneg_right hu₁ (norm_nonneg x₀)
        _ = ‖x₀‖ := one_mul _
    have htriangle :
        ‖x‖ ≤ ‖x - (s / τ) • x₀‖ + ‖(s / τ) • x₀‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (x - (s / τ) • x₀) ((s / τ) • x₀)
    have hxnorm : ‖x‖ ≤ r + ‖x₀‖ := by
      linarith only [htriangle, hdist, hpath]
    have hxU : x ∈ U := by
      simpa only [U, Metric.mem_closedBall, dist_zero_right] using hxnorm
    have hb := hB (s, x) ⟨hs, hxU⟩
    exact (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hb)
  · intro s hs x
    simpa only [gradientAt] using
      traveling_phase_gradient_lower
        (G.metric s) τ x₀ r s x M hM (hmetric s hs x)

end DifferentialGeometry.PDE.RicciFlow
