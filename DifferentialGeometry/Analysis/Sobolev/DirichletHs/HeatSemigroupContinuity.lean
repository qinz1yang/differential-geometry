import DifferentialGeometry.Analysis.Sobolev.DirichletHs.HeatSemigroupExt
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.FiniteSupport

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

private lemma norm_dirichletHeatSemigroupHsExt_sub_le_diff
    {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}
    {t t₀ : ℝ} (ht : 0 ≤ t) (ht₀ : 0 ≤ t₀)
    (u : dirichletHs g σ) :
    ‖dirichletHeatSemigroupHsExt g σ t u -
        dirichletHeatSemigroupHsExt g σ t₀ u‖ ≤
      ‖dirichletHeatSemigroupHsExt g σ |t - t₀| u - u‖ := by
  rcases le_or_gt t₀ t with hle | hlt
  · have h_diff_nn : 0 ≤ t - t₀ := sub_nonneg.mpr hle
    have h_abs : |t - t₀| = t - t₀ := abs_of_nonneg h_diff_nn
    have h_law :
        dirichletHeatSemigroupHsExt g σ t =
          (dirichletHeatSemigroupHsExt g σ t₀).comp
            (dirichletHeatSemigroupHsExt g σ (t - t₀)) := by
      have h_add :=
        dirichletHeatSemigroupHsExt_add
          (g := g) (σ := σ) ht₀ h_diff_nn
      have h_eq : t₀ + (t - t₀) = t := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        dirichletHeatSemigroupHsExt g σ t u =
          dirichletHeatSemigroupHsExt g σ t₀
            (dirichletHeatSemigroupHsExt
              g σ (t - t₀) u) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        dirichletHeatSemigroupHsExt g σ t₀
            (dirichletHeatSemigroupHsExt
              g σ (t - t₀) u) -
          dirichletHeatSemigroupHsExt g σ t₀ u =
        dirichletHeatSemigroupHsExt g σ t₀
          (dirichletHeatSemigroupHsExt
            g σ (t - t₀) u - u) := by
      rw [← (dirichletHeatSemigroupHsExt g σ t₀).map_sub]
    rw [h_sub_eq]
    have h_op_le :=
      ContinuousLinearMap.le_opNorm
        (dirichletHeatSemigroupHsExt g σ t₀)
        (dirichletHeatSemigroupHsExt g σ (t - t₀) u - u)
    have h_op_le_one :
        ‖dirichletHeatSemigroupHsExt g σ t₀‖ ≤ 1 :=
      dirichletHeatSemigroupHsExt_opNorm_le_one
        (g := g) (σ := σ) ht₀
    have h_norm_nn :
        0 ≤ ‖dirichletHeatSemigroupHsExt
            g σ (t - t₀) u - u‖ := norm_nonneg _
    calc ‖dirichletHeatSemigroupHsExt g σ t₀
              (dirichletHeatSemigroupHsExt
                g σ (t - t₀) u - u)‖
        ≤ ‖dirichletHeatSemigroupHsExt g σ t₀‖ *
            ‖dirichletHeatSemigroupHsExt
              g σ (t - t₀) u - u‖ := h_op_le
      _ ≤ 1 * ‖dirichletHeatSemigroupHsExt
              g σ (t - t₀) u - u‖ :=
            mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖dirichletHeatSemigroupHsExt
              g σ (t - t₀) u - u‖ := one_mul _
      _ = ‖dirichletHeatSemigroupHsExt
              g σ |t - t₀| u - u‖ := by rw [h_abs]
  · have h_diff_nn : 0 ≤ t₀ - t := sub_nonneg.mpr hlt.le
    have h_abs : |t - t₀| = t₀ - t := by
      rw [abs_sub_comm, abs_of_nonneg h_diff_nn]
    have h_law :
        dirichletHeatSemigroupHsExt g σ t₀ =
          (dirichletHeatSemigroupHsExt g σ t).comp
            (dirichletHeatSemigroupHsExt
              g σ (t₀ - t)) := by
      have h_add :=
        dirichletHeatSemigroupHsExt_add
          (g := g) (σ := σ) ht h_diff_nn
      have h_eq : t + (t₀ - t) = t₀ := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        dirichletHeatSemigroupHsExt g σ t₀ u =
          dirichletHeatSemigroupHsExt g σ t
            (dirichletHeatSemigroupHsExt
              g σ (t₀ - t) u) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        dirichletHeatSemigroupHsExt g σ t u -
          dirichletHeatSemigroupHsExt g σ t
            (dirichletHeatSemigroupHsExt
              g σ (t₀ - t) u) =
        dirichletHeatSemigroupHsExt g σ t
          (u - dirichletHeatSemigroupHsExt
            g σ (t₀ - t) u) := by
      rw [← (dirichletHeatSemigroupHsExt g σ t).map_sub]
    rw [h_sub_eq]
    have h_op_le :=
      ContinuousLinearMap.le_opNorm
        (dirichletHeatSemigroupHsExt g σ t)
        (u - dirichletHeatSemigroupHsExt
          g σ (t₀ - t) u)
    have h_op_le_one :
        ‖dirichletHeatSemigroupHsExt g σ t‖ ≤ 1 :=
      dirichletHeatSemigroupHsExt_opNorm_le_one
        (g := g) (σ := σ) ht
    have h_norm_nn :
        0 ≤ ‖u - dirichletHeatSemigroupHsExt
            g σ (t₀ - t) u‖ := norm_nonneg _
    have h_norm_swap :
        ‖u - dirichletHeatSemigroupHsExt
            g σ (t₀ - t) u‖ =
          ‖dirichletHeatSemigroupHsExt
            g σ (t₀ - t) u - u‖ := by
      rw [norm_sub_rev]
    calc ‖dirichletHeatSemigroupHsExt g σ t
              (u - dirichletHeatSemigroupHsExt
                g σ (t₀ - t) u)‖
        ≤ ‖dirichletHeatSemigroupHsExt g σ t‖ *
            ‖u - dirichletHeatSemigroupHsExt
              g σ (t₀ - t) u‖ := h_op_le
      _ ≤ 1 * ‖u - dirichletHeatSemigroupHsExt
              g σ (t₀ - t) u‖ :=
            mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖dirichletHeatSemigroupHsExt
              g σ (t₀ - t) u - u‖ := by
            rw [one_mul, h_norm_swap]
      _ = ‖dirichletHeatSemigroupHsExt
              g σ |t - t₀| u - u‖ := by rw [h_abs]

private lemma sq_norm_dirichletHeatSemigroupHsExt_sub_self_of_finite
    {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}
    {τ : ℝ} (hτ : 0 ≤ τ)
    {u' : dirichletHs g σ}
    (hu' : u' ∈ dirichletHs.finiteSupportSubmodule
      g σ) :
    ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ ^ 2 =
      ∑ i ∈ ((dirichletHs.mem_finiteSupportSubmodule
          u').mp hu').toFinset,
        dirichletSobolevWeight i σ *
          ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
            u'.coeff i) ^ 2 := by
  classical
  set hu'fin := (dirichletHs.mem_finiteSupportSubmodule
    u').mp hu'
  set F := hu'fin.toFinset
  have h_norm_sq := dirichletHs.norm_sq_eq_tsum
    (dirichletHeatSemigroupHsExt g σ τ u' - u')
  have h_diff_coeff : ∀ i,
      (dirichletHeatSemigroupHsExt g σ τ u' - u').coeff i =
        (Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
          u'.coeff i := by
    intro i
    have h_sub : (dirichletHeatSemigroupHsExt g σ τ u' - u').coeff i =
        (dirichletHeatSemigroupHsExt g σ τ u').coeff i - u'.coeff i := by
      change (fun j => (dirichletHeatSemigroupHsExt
            g σ τ u').coeff j - u'.coeff j) i = _
      rfl
    rw [h_sub, dirichletHeatSemigroupHsExt_coeff
      (g := g) (σ := σ) hτ u' i]
    ring
  have h_tsum_eq :
      ∑' i, dirichletSobolevWeight i σ *
          ((dirichletHeatSemigroupHsExt g σ τ u' - u').coeff i) ^ 2 =
      ∑' i, dirichletSobolevWeight i σ *
          ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
            u'.coeff i) ^ 2 := by
    refine tsum_congr (fun i => ?_)
    rw [h_diff_coeff]
  rw [h_norm_sq, h_tsum_eq]
  apply tsum_eq_sum
  intro i hi
  have h_zero : u'.coeff i = 0 := by
    by_contra h
    exact hi (hu'fin.mem_toFinset.mpr (Function.mem_support.mpr h))
  rw [h_zero]
  ring

private lemma tendsto_dirichletHeatSemigroupHsExt_of_finite
    {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}
    {u' : dirichletHs g σ}
    (hu' : u' ∈ dirichletHs.finiteSupportSubmodule
      g σ) :
    Tendsto (fun τ : ℝ =>
        dirichletHeatSemigroupHsExt g σ τ u')
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 u') := by
  classical
  set hu'fin := (dirichletHs.mem_finiteSupportSubmodule
    u').mp hu'
  set F := hu'fin.toFinset with hF_def
  suffices h_norm_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) by
    have h_diff_to_zero :
        Tendsto (fun τ : ℝ =>
            dirichletHeatSemigroupHsExt g σ τ u' - u')
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero
        (f := fun τ : ℝ =>
          dirichletHeatSemigroupHsExt g σ τ u' - u')).mpr h_norm_to_zero
    have h_added :=
      h_diff_to_zero.add (tendsto_const_nhds (x := u'))
    simpa using h_added
  have h_sq_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ ^ 2)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    have h_rewrite :
        (fun τ : ℝ =>
          ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ ^ 2) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0]
        (fun τ : ℝ =>
          ∑ i ∈ F, dirichletSobolevWeight i σ *
            ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
              u'.coeff i) ^ 2) := by
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ_nn : 0 ≤ τ := Set.mem_Ici.mp hτ
      simpa [hF_def] using
        sq_norm_dirichletHeatSemigroupHsExt_sub_self_of_finite
          (g := g) (σ := σ) hτ_nn hu'
    have h_each_to_zero :
        ∀ i ∈ F,
          Tendsto (fun τ : ℝ =>
              dirichletSobolevWeight i σ *
                ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
                  u'.coeff i) ^ 2)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
      intro i _
      have h_exp_cont :
          Continuous (fun τ : ℝ =>
            Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) := by
        exact (Real.continuous_exp.comp
          ((continuous_const (y := -(dirichletLaplacianEigenvalue i))).mul
            continuous_id)).sub continuous_const
      have h_at_zero :
          Real.exp (-(dirichletLaplacianEigenvalue i) * (0 : ℝ)) - 1 = 0 := by
        rw [mul_zero, Real.exp_zero]; ring
      have h_exp_to_zero :
          Tendsto (fun τ : ℝ =>
              Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1)
            (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h_at := h_exp_cont.continuousAt (x := (0 : ℝ))
        change Tendsto _ (𝓝 0)
          (𝓝 (Real.exp (-(dirichletLaplacianEigenvalue i) * (0 : ℝ)) - 1))
          at h_at
        rw [h_at_zero] at h_at
        exact h_at
      have h_exp_to_zero_within :
          Tendsto (fun τ : ℝ =>
              Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) :=
        h_exp_to_zero.mono_left nhdsWithin_le_nhds
      have h_mul_to_zero :
          Tendsto (fun τ : ℝ =>
              (Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
                u'.coeff i)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
        have := h_exp_to_zero_within.mul
          (tendsto_const_nhds (x := u'.coeff i))
        simpa using this
      have h_sq_to_zero :
          Tendsto (fun τ : ℝ =>
              ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
                u'.coeff i) ^ 2)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
        have := h_mul_to_zero.pow 2
        simpa using this
      have := h_sq_to_zero.const_mul
        (dirichletSobolevWeight i σ)
      simpa using this
    have h_sum_to_zero :
        Tendsto (fun τ : ℝ =>
            ∑ i ∈ F, dirichletSobolevWeight i σ *
              ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
                u'.coeff i) ^ 2)
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
      have h := tendsto_finsetSum (f := fun i τ =>
        dirichletSobolevWeight i σ *
          ((Real.exp (-(dirichletLaplacianEigenvalue i) * τ) - 1) *
            u'.coeff i) ^ 2) F h_each_to_zero
      simpa using h
    exact h_sum_to_zero.congr' h_rewrite.symm
  have h_norm_eq_sqrt :
      ∀ τ : ℝ,
        ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ =
          Real.sqrt
            (‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ ^ 2) := by
    intro τ
    rw [Real.sqrt_sq (norm_nonneg _)]
  have h_sqrt_cont : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt
    rw [Real.sqrt_zero] at h
    exact h
  have h_sqrt_to_zero :
      Tendsto (fun τ : ℝ =>
          Real.sqrt
            (‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ ^ 2))
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := h_sqrt_cont.comp h_sq_to_zero
  exact (Filter.tendsto_congr (fun τ => h_norm_eq_sqrt τ)).mpr
    h_sqrt_to_zero

private lemma tendsto_dirichletHeatSemigroupHsExt_at_zero
    (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ)
    (u : dirichletHs g σ) :
    Tendsto (fun τ : ℝ =>
        dirichletHeatSemigroupHsExt g σ τ u)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 u) := by
  classical
  suffices h_norm_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖dirichletHeatSemigroupHsExt g σ τ u - u‖)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) by
    have h_diff_to_zero :
        Tendsto (fun τ : ℝ =>
            dirichletHeatSemigroupHsExt g σ τ u - u)
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero
        (f := fun τ : ℝ =>
          dirichletHeatSemigroupHsExt g σ τ u - u)).mpr h_norm_to_zero
    have h_added :=
      h_diff_to_zero.add (tendsto_const_nhds (x := u))
    simpa using h_added
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h_eps3_pos : 0 < ε / 3 := by linarith
  have h_close :=
    Metric.mem_closure_iff.mp
      (dirichletHs.mem_closure_finiteSupportSubmodule u)
      (ε / 3) h_eps3_pos
  obtain ⟨u', hu'_mem, hu'_close⟩ := h_close
  have hu'_tendsto :=
    tendsto_dirichletHeatSemigroupHsExt_of_finite
      (g := g) (σ := σ) hu'_mem
  have hu'_diff_to_zero :
      Tendsto (fun τ : ℝ =>
          dirichletHeatSemigroupHsExt g σ τ u' - u')
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    have := hu'_tendsto.sub (tendsto_const_nhds (x := u'))
    simpa using this
  have hu'_norm_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    have := hu'_diff_to_zero.norm
    simpa using this
  have h_eventually :
      ∀ᶠ τ in 𝓝[Set.Ici (0 : ℝ)] 0,
        ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ < ε / 3 := by
    have h := hu'_norm_to_zero (Metric.ball_mem_nhds 0 h_eps3_pos)
    filter_upwards [h] with τ hτ
    simpa [Real.dist_eq, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      using hτ
  filter_upwards [h_eventually, self_mem_nhdsWithin]
    with τ h_eps3 hτ_mem
  have hτ_nn : 0 ≤ τ := Set.mem_Ici.mp hτ_mem
  have h_decomp :
      dirichletHeatSemigroupHsExt g σ τ u - u =
        dirichletHeatSemigroupHsExt g σ τ (u - u') +
          (dirichletHeatSemigroupHsExt g σ τ u' - u') +
            (u' - u) := by
    rw [(dirichletHeatSemigroupHsExt g σ τ).map_sub]
    abel
  have h_first_norm :
      ‖dirichletHeatSemigroupHsExt g σ τ (u - u')‖ ≤
        ‖u - u'‖ := by
    have h_le :=
      ContinuousLinearMap.le_opNorm
        (dirichletHeatSemigroupHsExt g σ τ) (u - u')
    have h_op :
        ‖dirichletHeatSemigroupHsExt g σ τ‖ ≤ 1 :=
      dirichletHeatSemigroupHsExt_opNorm_le_one
        (g := g) (σ := σ) hτ_nn
    have h_nn : 0 ≤ ‖u - u'‖ := norm_nonneg _
    calc ‖dirichletHeatSemigroupHsExt g σ τ (u - u')‖
        ≤ ‖dirichletHeatSemigroupHsExt g σ τ‖ * ‖u - u'‖ := h_le
      _ ≤ 1 * ‖u - u'‖ := mul_le_mul_of_nonneg_right h_op h_nn
      _ = ‖u - u'‖ := one_mul _
  have h_uu' : ‖u - u'‖ < ε / 3 := by
    have : dist u u' < ε / 3 := hu'_close
    rwa [dist_eq_norm] at this
  have h_u'u : ‖u' - u‖ < ε / 3 := by
    rw [norm_sub_rev]; exact h_uu'
  have h_first_lt : ‖dirichletHeatSemigroupHsExt g σ τ (u - u')‖
      < ε / 3 := lt_of_le_of_lt h_first_norm h_uu'
  have h_total_norm :
      ‖dirichletHeatSemigroupHsExt g σ τ u - u‖ ≤
        ‖dirichletHeatSemigroupHsExt g σ τ (u - u')‖ +
          ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ +
            ‖u' - u‖ := by
    rw [h_decomp]
    calc ‖dirichletHeatSemigroupHsExt g σ τ (u - u') +
            (dirichletHeatSemigroupHsExt g σ τ u' - u') +
              (u' - u)‖
        ≤ ‖dirichletHeatSemigroupHsExt g σ τ (u - u') +
              (dirichletHeatSemigroupHsExt g σ τ u' - u')‖ +
            ‖u' - u‖ := norm_add_le _ _
      _ ≤ ‖dirichletHeatSemigroupHsExt g σ τ (u - u')‖ +
              ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ +
            ‖u' - u‖ := by
          gcongr
          exact norm_add_le _ _
  have h_lt :
      ‖dirichletHeatSemigroupHsExt g σ τ u - u‖ <
        ε / 3 + ε / 3 + ε / 3 := by
    calc ‖dirichletHeatSemigroupHsExt g σ τ u - u‖
        ≤ ‖dirichletHeatSemigroupHsExt g σ τ (u - u')‖ +
            ‖dirichletHeatSemigroupHsExt g σ τ u' - u'‖ +
              ‖u' - u‖ := h_total_norm
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have h1 := h_first_lt
          have h2 := h_eps3
          have h3 := h_u'u
          linarith
  have h_sum_eq : ε / 3 + ε / 3 + ε / 3 = ε := by ring
  rw [h_sum_eq] at h_lt
  simpa [Real.dist_eq, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h_lt

theorem dirichletHeatSemigroupHsExt_continuousOn (g : SmoothRiemannianMetric (I_half n) M)
    (σ : ℝ) (u : dirichletHs g σ) :
    ContinuousOn (fun t : ℝ =>
        dirichletHeatSemigroupHsExt g σ t u) (Set.Ici 0) := by
  intro t₀ ht₀
  have ht₀_nn : 0 ≤ t₀ := Set.mem_Ici.mp ht₀
  rcases lt_or_eq_of_le ht₀_nn with ht₀_pos | ht₀_eq
  · rw [ContinuousWithinAt]
    rw [show (𝓝 (dirichletHeatSemigroupHsExt g σ t₀ u)) =
        𝓝 (0 +
          dirichletHeatSemigroupHsExt g σ t₀ u) by rw [zero_add]]
    have h_diff_to_zero :
        Tendsto (fun t : ℝ =>
            dirichletHeatSemigroupHsExt g σ t u -
              dirichletHeatSemigroupHsExt g σ t₀ u)
          (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
      have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t₀ := Ioi_mem_nhds ht₀_pos
      have h_pos_within : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ici (0 : ℝ)] t₀ :=
        mem_nhdsWithin_of_mem_nhds h_pos_nhds
      have h_bound_event : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] t₀,
          ‖dirichletHeatSemigroupHsExt g σ t u -
              dirichletHeatSemigroupHsExt g σ t₀ u‖ ≤
            ‖dirichletHeatSemigroupHsExt g σ |t - t₀| u - u‖ := by
        filter_upwards [h_pos_within] with t ht_pos
        exact norm_dirichletHeatSemigroupHsExt_sub_le_diff
          (g := g) (σ := σ)
          (le_of_lt ht_pos) ht₀_nn u
      have h_abs_to_zero :
          Tendsto (fun t : ℝ => |t - t₀|)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
        have h_sub : Tendsto (fun t : ℝ => t - t₀)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 (0 : ℝ)) := by
          have h_amb : Tendsto (fun t : ℝ => t - t₀)
              (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
            Filter.Tendsto.sub tendsto_id tendsto_const_nhds
          have h_simp : Tendsto (fun t : ℝ => t - t₀)
              (𝓝 t₀) (𝓝 (0 : ℝ)) := by simpa using h_amb
          exact h_simp.mono_left nhdsWithin_le_nhds
        have := h_sub.abs
        simpa using this
      have h_abs_to_zero_within :
          Tendsto (fun t : ℝ => |t - t₀|)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨h_abs_to_zero, ?_⟩
        exact Eventually.of_forall (fun _ => Set.mem_Ici.mpr (abs_nonneg _))
      have h_strong :=
        tendsto_dirichletHeatSemigroupHsExt_at_zero
          g σ u
      have h_compose :
          Tendsto (fun t : ℝ =>
              dirichletHeatSemigroupHsExt g σ |t - t₀| u)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 u) :=
        h_strong.comp h_abs_to_zero_within
      have h_diff_to_zero' :
          Tendsto (fun t : ℝ =>
              dirichletHeatSemigroupHsExt g σ |t - t₀| u - u)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
        have := h_compose.sub (tendsto_const_nhds (x := u))
        simpa using this
      have h_norm_to_zero :
          Tendsto (fun t : ℝ =>
              ‖dirichletHeatSemigroupHsExt g σ |t - t₀| u - u‖)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
        have := h_diff_to_zero'.norm
        simpa using this
      exact squeeze_zero_norm' h_bound_event h_norm_to_zero
    have h_added :=
      h_diff_to_zero.add (tendsto_const_nhds
        (x := dirichletHeatSemigroupHsExt g σ t₀ u))
    simpa using h_added
  · subst ht₀_eq
    rw [ContinuousWithinAt]
    have h_at_zero :
        dirichletHeatSemigroupHsExt g σ 0 u = u := by
      rw [dirichletHeatSemigroupHsExt_zero]; rfl
    rw [h_at_zero]
    exact tendsto_dirichletHeatSemigroupHsExt_at_zero
      g σ u

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
