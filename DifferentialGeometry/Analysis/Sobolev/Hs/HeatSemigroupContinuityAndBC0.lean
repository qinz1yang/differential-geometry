import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupHsExt
import DifferentialGeometry.Analysis.Sobolev.Hs.FiniteSupport
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.AbstractSemigroup

/-!
# Strong continuity of the scalar spectral heat semigroup on `[0, ∞)`

For a closed Riemannian manifold `(M, g)` and a spectral Sobolev exponent
`σ`, the extended heat semigroup
`heatSemigroupHsExt g σ : ℝ → scalarHs g σ →L[ℝ] scalarHs g σ`
is strongly continuous on the non-negative half-line: for every
`u : scalarHs g σ`, the map `t ↦ heatSemigroupHsExt g σ t u` is
continuous on `Set.Ici 0`. This is the last structural property needed to
package the semigroup as a `BoundedC0Semigroup (scalarHs g σ)`.

## Strategy

The proof follows the standard contractive-comparison pattern. The key
ingredients are:

* the operator-norm contraction
  `‖heatSemigroupHsExt g σ t‖ ≤ 1` for `t ≥ 0`
  (`heatSemigroupHsExt_opNorm_le_one`), and
* the semigroup law on `t, s ≥ 0`
  (`heatSemigroupHsExt_add`),

which together yield, for any `t, t₀ ≥ 0`,

  `‖heatSemigroupHsExt g σ t u − heatSemigroupHsExt g σ t₀ u‖`
  `  ≤ ‖heatSemigroupHsExt g σ |t − t₀| u − u‖`.

Hence strong continuity at every `t₀ ≥ 0` reduces to right-continuity at
`0`, i.e. `heatSemigroupHsExt g σ τ u → u` as `τ ↓ 0`. Right-continuity
at `0` is proved by a three-term `ε/3` argument:

1. approximate `u` by a finitely-supported `u'` (using density of
   `finiteSupportSubmodule`),
2. control the residual `u − u'` by contractivity,
3. handle the finite-rank piece `heatSemigroupHsExt g σ τ u' − u'`
   directly: its coordinates are a finite linear combination of
   `(exp(−λᵢ τ) − 1) · u'.coeff i` weighted by the spectral basis, each
   factor tending to `0` as `τ → 0`.

## Main results

* `heatSemigroupHsExt_continuousOn` — strong continuity of the heat
  semigroup on `[0, ∞)`.
* `scalarHsBoundedC0Semigroup` — the heat semigroup packaged as a
  `BoundedC0Semigroup (scalarHs g σ)`.
* `HkScalar g k`, `hkScalarBoundedC0Semigroup g k` — the integer-exponent
  alias and its packaged semigroup.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.Spectral

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Contractive comparison

For `t, t₀ ≥ 0`, the difference
`heatSemigroupHsExt g σ t u − heatSemigroupHsExt g σ t₀ u`
has norm bounded by `‖heatSemigroupHsExt g σ |t − t₀| u − u‖`. The proof
writes the larger of `t, t₀` as the sum of the smaller and `|t − t₀|`,
applies the semigroup law `heatSemigroupHsExt_add`, and finishes by
contractivity `heatSemigroupHsExt_opNorm_le_one`. -/

private lemma norm_heatSemigroupHsExt_sub_le_diff
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t t₀ : ℝ} (ht : 0 ≤ t) (ht₀ : 0 ≤ t₀)
    (u : scalarHs (I := I) (M := M) g σ) :
    ‖heatSemigroupHsExt (I := I) (M := M) g σ t u -
        heatSemigroupHsExt (I := I) (M := M) g σ t₀ u‖ ≤
      ‖heatSemigroupHsExt (I := I) (M := M) g σ |t - t₀| u - u‖ := by
  rcases le_or_gt t₀ t with hle | hlt
  · -- `t ≥ t₀`. Write `t = t₀ + (t − t₀)`.
    have h_diff_nn : 0 ≤ t - t₀ := sub_nonneg.mpr hle
    have h_abs : |t - t₀| = t - t₀ := abs_of_nonneg h_diff_nn
    have h_law :
        heatSemigroupHsExt (I := I) (M := M) g σ t =
          (heatSemigroupHsExt (I := I) (M := M) g σ t₀).comp
            (heatSemigroupHsExt (I := I) (M := M) g σ (t - t₀)) := by
      have h_add :=
        heatSemigroupHsExt_add (I := I) (M := M)
          (g := g) (σ := σ) ht₀ h_diff_nn
      have h_eq : t₀ + (t - t₀) = t := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        heatSemigroupHsExt (I := I) (M := M) g σ t u =
          heatSemigroupHsExt (I := I) (M := M) g σ t₀
            (heatSemigroupHsExt
              (I := I) (M := M) g σ (t - t₀) u) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        heatSemigroupHsExt (I := I) (M := M) g σ t₀
            (heatSemigroupHsExt
              (I := I) (M := M) g σ (t - t₀) u) -
          heatSemigroupHsExt (I := I) (M := M) g σ t₀ u =
        heatSemigroupHsExt (I := I) (M := M) g σ t₀
          (heatSemigroupHsExt
            (I := I) (M := M) g σ (t - t₀) u - u) := by
      rw [← (heatSemigroupHsExt (I := I) (M := M) g σ t₀).map_sub]
    rw [h_sub_eq]
    have h_op_le :=
      ContinuousLinearMap.le_opNorm
        (heatSemigroupHsExt (I := I) (M := M) g σ t₀)
        (heatSemigroupHsExt (I := I) (M := M) g σ (t - t₀) u - u)
    have h_op_le_one :
        ‖heatSemigroupHsExt (I := I) (M := M) g σ t₀‖ ≤ 1 :=
      heatSemigroupHsExt_opNorm_le_one
        (I := I) (M := M) (g := g) (σ := σ) ht₀
    have h_norm_nn :
        0 ≤ ‖heatSemigroupHsExt
            (I := I) (M := M) g σ (t - t₀) u - u‖ := norm_nonneg _
    calc ‖heatSemigroupHsExt (I := I) (M := M) g σ t₀
              (heatSemigroupHsExt
                (I := I) (M := M) g σ (t - t₀) u - u)‖
        ≤ ‖heatSemigroupHsExt (I := I) (M := M) g σ t₀‖ *
            ‖heatSemigroupHsExt
              (I := I) (M := M) g σ (t - t₀) u - u‖ := h_op_le
      _ ≤ 1 * ‖heatSemigroupHsExt
              (I := I) (M := M) g σ (t - t₀) u - u‖ :=
            mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖heatSemigroupHsExt
              (I := I) (M := M) g σ (t - t₀) u - u‖ := one_mul _
      _ = ‖heatSemigroupHsExt
              (I := I) (M := M) g σ |t - t₀| u - u‖ := by rw [h_abs]
  · -- `t < t₀`. Write `t₀ = t + (t₀ − t)`.
    have h_diff_nn : 0 ≤ t₀ - t := sub_nonneg.mpr hlt.le
    have h_abs : |t - t₀| = t₀ - t := by
      rw [abs_sub_comm, abs_of_nonneg h_diff_nn]
    have h_law :
        heatSemigroupHsExt (I := I) (M := M) g σ t₀ =
          (heatSemigroupHsExt (I := I) (M := M) g σ t).comp
            (heatSemigroupHsExt
              (I := I) (M := M) g σ (t₀ - t)) := by
      have h_add :=
        heatSemigroupHsExt_add (I := I) (M := M)
          (g := g) (σ := σ) ht h_diff_nn
      have h_eq : t + (t₀ - t) = t₀ := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        heatSemigroupHsExt (I := I) (M := M) g σ t₀ u =
          heatSemigroupHsExt (I := I) (M := M) g σ t
            (heatSemigroupHsExt
              (I := I) (M := M) g σ (t₀ - t) u) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        heatSemigroupHsExt (I := I) (M := M) g σ t u -
          heatSemigroupHsExt (I := I) (M := M) g σ t
            (heatSemigroupHsExt
              (I := I) (M := M) g σ (t₀ - t) u) =
        heatSemigroupHsExt (I := I) (M := M) g σ t
          (u - heatSemigroupHsExt
            (I := I) (M := M) g σ (t₀ - t) u) := by
      rw [← (heatSemigroupHsExt (I := I) (M := M) g σ t).map_sub]
    rw [h_sub_eq]
    have h_op_le :=
      ContinuousLinearMap.le_opNorm
        (heatSemigroupHsExt (I := I) (M := M) g σ t)
        (u - heatSemigroupHsExt
          (I := I) (M := M) g σ (t₀ - t) u)
    have h_op_le_one :
        ‖heatSemigroupHsExt (I := I) (M := M) g σ t‖ ≤ 1 :=
      heatSemigroupHsExt_opNorm_le_one
        (I := I) (M := M) (g := g) (σ := σ) ht
    have h_norm_nn :
        0 ≤ ‖u - heatSemigroupHsExt
            (I := I) (M := M) g σ (t₀ - t) u‖ := norm_nonneg _
    have h_norm_swap :
        ‖u - heatSemigroupHsExt
            (I := I) (M := M) g σ (t₀ - t) u‖ =
          ‖heatSemigroupHsExt
            (I := I) (M := M) g σ (t₀ - t) u - u‖ := by
      rw [norm_sub_rev]
    calc ‖heatSemigroupHsExt (I := I) (M := M) g σ t
              (u - heatSemigroupHsExt
                (I := I) (M := M) g σ (t₀ - t) u)‖
        ≤ ‖heatSemigroupHsExt (I := I) (M := M) g σ t‖ *
            ‖u - heatSemigroupHsExt
              (I := I) (M := M) g σ (t₀ - t) u‖ := h_op_le
      _ ≤ 1 * ‖u - heatSemigroupHsExt
              (I := I) (M := M) g σ (t₀ - t) u‖ :=
            mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖heatSemigroupHsExt
              (I := I) (M := M) g σ (t₀ - t) u - u‖ := by
            rw [one_mul, h_norm_swap]
      _ = ‖heatSemigroupHsExt
              (I := I) (M := M) g σ |t - t₀| u - u‖ := by rw [h_abs]

/-! ## Right-continuity at `0` on finitely-supported elements

For `u'` with finite eigenbasis support, the difference
`heatSemigroupHsExt g σ τ u' − u'` has coordinates
`(exp(−λᵢ τ) − 1) · u'.coeff i`, supported on the finite set
`hu'.toFinset`. Its squared norm is the finite sum

  `∑_{i ∈ F} (1 + λᵢ)^σ · ((exp(−λᵢ τ) − 1) · u'.coeff i)²`,

each summand of which is continuous in `τ` and vanishes at `τ = 0`. The
finite sum therefore tends to `0` as `τ → 0`. -/

/-- For a finitely-supported `u'`, the squared norm of the difference
`heatSemigroupHsExt g σ τ u' − u'` is a finite sum of squared spectral
terms. -/
private lemma sq_norm_heatSemigroupHsExt_sub_self_of_finite
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {τ : ℝ} (hτ : 0 ≤ τ)
    {u' : scalarHs (I := I) (M := M) g σ}
    (hu' : u' ∈ scalarHs.finiteSupportSubmodule
      (I := I) (M := M) g σ) :
    ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ ^ 2 =
      ∑ i ∈ ((scalarHs.mem_finiteSupportSubmodule
          (I := I) (M := M) u').mp hu').toFinset,
        scalarSobolevWeight (I := I) (M := M) i σ *
          ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
            u'.coeff i) ^ 2 := by
  classical
  set hu'fin := (scalarHs.mem_finiteSupportSubmodule
    (I := I) (M := M) u').mp hu'
  set F := hu'fin.toFinset
  -- Squared norm via the weighted-tsum formula on `scalarHs`.
  have h_norm_sq := scalarHs.norm_sq_eq_tsum
    (I := I) (M := M)
    (heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u')
  -- Coefficient of the difference at index `i`.
  have h_diff_coeff : ∀ i,
      (heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u').coeff i =
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
          u'.coeff i := by
    intro i
    have h_sub : (heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u').coeff i =
        (heatSemigroupHsExt (I := I) (M := M) g σ τ u').coeff i - u'.coeff i := by
      change (fun j => (heatSemigroupHsExt
            (I := I) (M := M) g σ τ u').coeff j - u'.coeff j) i = _
      rfl
    rw [h_sub, heatSemigroupHsExt_coeff (I := I) (M := M)
      (g := g) (σ := σ) hτ u' i]
    ring
  -- Rewrite the tsum summand using the explicit difference coefficient.
  have h_tsum_eq :
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
          ((heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u').coeff i) ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
          ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
            u'.coeff i) ^ 2 := by
    refine tsum_congr (fun i => ?_)
    rw [h_diff_coeff]
  rw [h_norm_sq, h_tsum_eq]
  -- Outside the support `F`, `u'.coeff i = 0`, so the summand vanishes.
  apply tsum_eq_sum
  intro i hi
  have h_zero : u'.coeff i = 0 := by
    by_contra h
    exact hi (hu'fin.mem_toFinset.mpr (Function.mem_support.mpr h))
  rw [h_zero]
  ring

/-- For a finitely-supported `u'`, the map
`τ ↦ heatSemigroupHsExt g σ τ u'` is continuous at `0` within `Ici 0`. -/
private lemma tendsto_heatSemigroupHsExt_of_finite
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {u' : scalarHs (I := I) (M := M) g σ}
    (hu' : u' ∈ scalarHs.finiteSupportSubmodule
      (I := I) (M := M) g σ) :
    Tendsto (fun τ : ℝ =>
        heatSemigroupHsExt (I := I) (M := M) g σ τ u')
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 u') := by
  classical
  set hu'fin := (scalarHs.mem_finiteSupportSubmodule
    (I := I) (M := M) u').mp hu'
  set F := hu'fin.toFinset with hF_def
  -- Rephrase as `‖difference‖ → 0`.
  suffices h_norm_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) by
    -- Translate `norm → 0` into the actual `Tendsto` we need.
    have h_diff_to_zero :
        Tendsto (fun τ : ℝ =>
            heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u')
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero
        (f := fun τ : ℝ =>
          heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u')).mpr h_norm_to_zero
    have h_added :=
      h_diff_to_zero.add (tendsto_const_nhds (x := u'))
    simpa using h_added
  -- It suffices to show the squared norm tends to `0`.
  have h_sq_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ ^ 2)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    -- Rewrite using the finite-sum identity on `[0, ∞)`.
    have h_rewrite :
        (fun τ : ℝ =>
          ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ ^ 2) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0]
        (fun τ : ℝ =>
          ∑ i ∈ F, scalarSobolevWeight (I := I) (M := M) i σ *
            ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
              u'.coeff i) ^ 2) := by
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ_nn : 0 ≤ τ := Set.mem_Ici.mp hτ
      simpa [hF_def] using
        sq_norm_heatSemigroupHsExt_sub_self_of_finite
          (I := I) (M := M) (g := g) (σ := σ) hτ_nn hu'
    -- Show the RHS finite sum tends to `0` at `τ = 0`.
    have h_each_to_zero :
        ∀ i ∈ F,
          Tendsto (fun τ : ℝ =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
                  u'.coeff i) ^ 2)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
      intro i _
      -- The continuous map `τ ↦ exp(-λ τ) - 1` vanishes at `τ = 0`.
      have h_exp_cont :
          Continuous (fun τ : ℝ =>
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) := by
        exact (Real.continuous_exp.comp
          ((continuous_const (y := -(EigenIdx.lambda (I := I) (M := M) i))).mul
            continuous_id)).sub continuous_const
      have h_at_zero :
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (0 : ℝ)) - 1 = 0 := by
        rw [mul_zero, Real.exp_zero]; ring
      have h_exp_to_zero :
          Tendsto (fun τ : ℝ =>
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1)
            (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h_at := h_exp_cont.continuousAt (x := (0 : ℝ))
        change Tendsto _ (𝓝 0)
          (𝓝 (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (0 : ℝ)) - 1))
          at h_at
        rw [h_at_zero] at h_at
        exact h_at
      have h_exp_to_zero_within :
          Tendsto (fun τ : ℝ =>
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) :=
        h_exp_to_zero.mono_left nhdsWithin_le_nhds
      have h_mul_to_zero :
          Tendsto (fun τ : ℝ =>
              (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
                u'.coeff i)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
        have := h_exp_to_zero_within.mul
          (tendsto_const_nhds (x := u'.coeff i))
        simpa using this
      have h_sq_to_zero :
          Tendsto (fun τ : ℝ =>
              ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
                u'.coeff i) ^ 2)
            (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
        have := h_mul_to_zero.pow 2
        simpa using this
      have := h_sq_to_zero.const_mul
        (scalarSobolevWeight (I := I) (M := M) i σ)
      simpa using this
    have h_sum_to_zero :
        Tendsto (fun τ : ℝ =>
            ∑ i ∈ F, scalarSobolevWeight (I := I) (M := M) i σ *
              ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
                u'.coeff i) ^ 2)
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
      have h := tendsto_finset_sum (f := fun i τ =>
        scalarSobolevWeight (I := I) (M := M) i σ *
          ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * τ) - 1) *
            u'.coeff i) ^ 2) F h_each_to_zero
      simpa using h
    exact h_sum_to_zero.congr' h_rewrite.symm
  -- `norm → 0` from `norm² → 0` and continuity of `√`.
  have h_norm_eq_sqrt :
      ∀ τ : ℝ,
        ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ =
          Real.sqrt
            (‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ ^ 2) := by
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
            (‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ ^ 2))
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := h_sqrt_cont.comp h_sq_to_zero
  exact (Filter.tendsto_congr (fun τ => h_norm_eq_sqrt τ)).mpr
    h_sqrt_to_zero

/-! ## Right-continuity at `0` on all of `scalarHs g σ`

The full right-continuity at `0` follows by a three-term `ε/3` argument:
approximate `u` by a finitely-supported `u'`, use the finite-rank
right-continuity above on `u'`, and control the residual `u − u'` by
contractivity. -/

private lemma tendsto_heatSemigroupHsExt_at_zero
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u : scalarHs (I := I) (M := M) g σ) :
    Tendsto (fun τ : ℝ =>
        heatSemigroupHsExt (I := I) (M := M) g σ τ u)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 u) := by
  classical
  -- Reduce to `‖heatSemigroupHsExt g σ τ u - u‖ → 0`.
  suffices h_norm_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u - u‖)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) by
    have h_diff_to_zero :
        Tendsto (fun τ : ℝ =>
            heatSemigroupHsExt (I := I) (M := M) g σ τ u - u)
          (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero
        (f := fun τ : ℝ =>
          heatSemigroupHsExt (I := I) (M := M) g σ τ u - u)).mpr h_norm_to_zero
    have h_added :=
      h_diff_to_zero.add (tendsto_const_nhds (x := u))
    simpa using h_added
  -- ε-δ formulation via `Metric.tendsto_nhds`.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Pick `u'` finitely supported with `‖u - u'‖ < ε / 3`.
  have h_eps3_pos : 0 < ε / 3 := by linarith
  have h_close :=
    Metric.mem_closure_iff.mp
      (scalarHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) u)
      (ε / 3) h_eps3_pos
  obtain ⟨u', hu'_mem, hu'_close⟩ := h_close
  -- `u'` has finite support; right-continuity at `0` for `u'`.
  have hu'_tendsto :=
    tendsto_heatSemigroupHsExt_of_finite
      (I := I) (M := M) (g := g) (σ := σ) hu'_mem
  -- Reformulate `hu'_tendsto` as a norm-to-zero.
  have hu'_diff_to_zero :
      Tendsto (fun τ : ℝ =>
          heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u')
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    have := hu'_tendsto.sub (tendsto_const_nhds (x := u'))
    simpa using this
  have hu'_norm_to_zero :
      Tendsto (fun τ : ℝ =>
          ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖)
        (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    have := hu'_diff_to_zero.norm
    simpa using this
  -- From `‖S τ u' - u'‖ → 0`: eventually `< ε / 3`.
  have h_eventually :
      ∀ᶠ τ in 𝓝[Set.Ici (0 : ℝ)] 0,
        ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ < ε / 3 := by
    have h := hu'_norm_to_zero (Metric.ball_mem_nhds 0 h_eps3_pos)
    filter_upwards [h] with τ hτ
    simpa [Real.dist_eq, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      using hτ
  -- Combine with `‖u - u'‖ < ε / 3` and contractivity.
  filter_upwards [h_eventually, self_mem_nhdsWithin]
    with τ h_eps3 hτ_mem
  have hτ_nn : 0 ≤ τ := Set.mem_Ici.mp hτ_mem
  -- `dist (S τ u) u = ‖S τ u - u‖`.
  -- Triangle: ‖S τ u - u‖ ≤ ‖S τ (u - u')‖ + ‖S τ u' - u'‖ + ‖u' - u‖.
  have h_decomp :
      heatSemigroupHsExt (I := I) (M := M) g σ τ u - u =
        heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u') +
          (heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u') +
            (u' - u) := by
    rw [(heatSemigroupHsExt (I := I) (M := M) g σ τ).map_sub]
    abel
  have h_first_norm :
      ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u')‖ ≤
        ‖u - u'‖ := by
    have h_le :=
      ContinuousLinearMap.le_opNorm
        (heatSemigroupHsExt (I := I) (M := M) g σ τ) (u - u')
    have h_op :
        ‖heatSemigroupHsExt (I := I) (M := M) g σ τ‖ ≤ 1 :=
      heatSemigroupHsExt_opNorm_le_one
        (I := I) (M := M) (g := g) (σ := σ) hτ_nn
    have h_nn : 0 ≤ ‖u - u'‖ := norm_nonneg _
    calc ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u')‖
        ≤ ‖heatSemigroupHsExt (I := I) (M := M) g σ τ‖ * ‖u - u'‖ := h_le
      _ ≤ 1 * ‖u - u'‖ := mul_le_mul_of_nonneg_right h_op h_nn
      _ = ‖u - u'‖ := one_mul _
  -- The residual `‖u - u'‖ = dist u' u < ε/3`.
  have h_uu' : ‖u - u'‖ < ε / 3 := by
    have : dist u u' < ε / 3 := hu'_close
    rwa [dist_eq_norm] at this
  have h_u'u : ‖u' - u‖ < ε / 3 := by
    rw [norm_sub_rev]; exact h_uu'
  have h_first_lt : ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u')‖
      < ε / 3 := lt_of_le_of_lt h_first_norm h_uu'
  -- Final triangle estimate.
  have h_total_norm :
      ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u - u‖ ≤
        ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u')‖ +
          ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ +
            ‖u' - u‖ := by
    rw [h_decomp]
    calc ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u') +
            (heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u') +
              (u' - u)‖
        ≤ ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u') +
              (heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u')‖ +
            ‖u' - u‖ := norm_add_le _ _
      _ ≤ ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u')‖ +
              ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ +
            ‖u' - u‖ := by
          gcongr
          exact norm_add_le _ _
  have h_lt :
      ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u - u‖ <
        ε / 3 + ε / 3 + ε / 3 := by
    calc ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u - u‖
        ≤ ‖heatSemigroupHsExt (I := I) (M := M) g σ τ (u - u')‖ +
            ‖heatSemigroupHsExt (I := I) (M := M) g σ τ u' - u'‖ +
              ‖u' - u‖ := h_total_norm
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have h1 := h_first_lt
          have h2 := h_eps3
          have h3 := h_u'u
          linarith
  have h_sum_eq : ε / 3 + ε / 3 + ε / 3 = ε := by ring
  rw [h_sum_eq] at h_lt
  -- Convert `‖x‖ < ε` to `dist x 0 < ε`.
  simpa [Real.dist_eq, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h_lt

/-! ## Strong continuity on `[0, ∞)`

For `t₀ > 0`, two-sided continuity follows from the contractive
comparison combined with right-continuity at `0`. For `t₀ = 0`, the
result is exactly the right-continuity established above. -/

/-- **Strong continuity of the scalar spectral heat semigroup on
`[0, ∞)`.** For every `u : scalarHs g σ`, the map
`t ↦ heatSemigroupHsExt g σ t u` is continuous on `Set.Ici 0`. -/
theorem heatSemigroupHsExt_continuousOn (g : SmoothRiemannianMetric I M)
    (σ : ℝ) (u : scalarHs (I := I) (M := M) g σ) :
    ContinuousOn (fun t : ℝ =>
        heatSemigroupHsExt (I := I) (M := M) g σ t u) (Set.Ici 0) := by
  intro t₀ ht₀
  have ht₀_nn : 0 ≤ t₀ := Set.mem_Ici.mp ht₀
  rcases lt_or_eq_of_le ht₀_nn with ht₀_pos | ht₀_eq
  · -- `t₀ > 0`: two-sided continuity via the contractive comparison.
    rw [ContinuousWithinAt]
    -- Reduce to convergence of the difference to `0`.
    rw [show (𝓝 (heatSemigroupHsExt (I := I) (M := M) g σ t₀ u)) =
        𝓝 (0 +
          heatSemigroupHsExt (I := I) (M := M) g σ t₀ u) by rw [zero_add]]
    have h_diff_to_zero :
        Tendsto (fun t : ℝ =>
            heatSemigroupHsExt (I := I) (M := M) g σ t u -
              heatSemigroupHsExt (I := I) (M := M) g σ t₀ u)
          (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
      -- Bound: norm ≤ ‖S |t - t₀| u - u‖.
      have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t₀ := Ioi_mem_nhds ht₀_pos
      have h_pos_within : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ici (0 : ℝ)] t₀ :=
        mem_nhdsWithin_of_mem_nhds h_pos_nhds
      have h_bound_event : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] t₀,
          ‖heatSemigroupHsExt (I := I) (M := M) g σ t u -
              heatSemigroupHsExt (I := I) (M := M) g σ t₀ u‖ ≤
            ‖heatSemigroupHsExt (I := I) (M := M) g σ |t - t₀| u - u‖ := by
        filter_upwards [h_pos_within] with t ht_pos
        exact norm_heatSemigroupHsExt_sub_le_diff
          (I := I) (M := M) (g := g) (σ := σ)
          (le_of_lt ht_pos) ht₀_nn u
      -- `|t - t₀| → 0` in `𝓝[Ici 0] t₀`, and takes nonneg values.
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
      -- Compose with right-continuity at 0.
      have h_strong :=
        tendsto_heatSemigroupHsExt_at_zero
          (I := I) (M := M) g σ u
      have h_compose :
          Tendsto (fun t : ℝ =>
              heatSemigroupHsExt (I := I) (M := M) g σ |t - t₀| u)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 u) :=
        h_strong.comp h_abs_to_zero_within
      have h_diff_to_zero' :
          Tendsto (fun t : ℝ =>
              heatSemigroupHsExt (I := I) (M := M) g σ |t - t₀| u - u)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
        have := h_compose.sub (tendsto_const_nhds (x := u))
        simpa using this
      have h_norm_to_zero :
          Tendsto (fun t : ℝ =>
              ‖heatSemigroupHsExt (I := I) (M := M) g σ |t - t₀| u - u‖)
            (𝓝[Set.Ici (0 : ℝ)] t₀) (𝓝 0) := by
        have := h_diff_to_zero'.norm
        simpa using this
      exact squeeze_zero_norm' h_bound_event h_norm_to_zero
    -- Add back the constant value at `t₀`.
    have h_added :=
      h_diff_to_zero.add (tendsto_const_nhds
        (x := heatSemigroupHsExt (I := I) (M := M) g σ t₀ u))
    simpa using h_added
  · -- `t₀ = 0`: use right-continuity at `0`.
    subst ht₀_eq
    rw [ContinuousWithinAt]
    have h_at_zero :
        heatSemigroupHsExt (I := I) (M := M) g σ 0 u = u := by
      rw [heatSemigroupHsExt_zero]; rfl
    rw [h_at_zero]
    exact tendsto_heatSemigroupHsExt_at_zero
      (I := I) (M := M) g σ u

/-! ## Packaging as a `BoundedC0Semigroup` -/

/-- The scalar spectral heat semigroup `e^{t Δ_g}` on `scalarHs g σ`
packaged as a bounded strongly continuous one-parameter contraction
semigroup. -/
noncomputable def scalarHsBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    DifferentialGeometry.Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup
      (scalarHs (I := I) (M := M) g σ) where
  toFun := fun t => heatSemigroupHsExt (I := I) (M := M) g σ t
  apply_zero := heatSemigroupHsExt_zero (I := I) (M := M) g σ
  apply_add := fun _ _ ht hs =>
    heatSemigroupHsExt_add (I := I) (M := M) (g := g) (σ := σ) ht hs
  opNorm_le_one := fun _ ht =>
    heatSemigroupHsExt_opNorm_le_one (I := I) (M := M)
      (g := g) (σ := σ) ht
  continuousOn_apply := fun u =>
    heatSemigroupHsExt_continuousOn (I := I) (M := M) g σ u

/-- The underlying one-parameter family of `scalarHsBoundedC0Semigroup`
is the extended scalar heat semigroup. -/
@[simp]
theorem scalarHsBoundedC0Semigroup_apply
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (t : ℝ) :
    scalarHsBoundedC0Semigroup (I := I) (M := M) g σ t =
      heatSemigroupHsExt (I := I) (M := M) g σ t := rfl

/-! ## Integer-exponent alias

For integer `k`, `HkScalar g k` abbreviates `scalarHs g k` (the
spectral-`Hᵏ` Sobolev space), and `hkScalarBoundedC0Semigroup g k` is the
corresponding bounded `C₀`-semigroup. -/

/-- The integer-exponent alias for the spectral Sobolev space on scalars:
`HkScalar g k := scalarHs g (k : ℝ)`. -/
abbrev HkScalar (g : SmoothRiemannianMetric I M) (k : ℕ) : Type _ :=
  scalarHs (I := I) (M := M) g (k : ℝ)

/-- The scalar spectral heat semigroup on `HkScalar g k`, packaged as a
bounded strongly continuous one-parameter contraction semigroup. -/
noncomputable abbrev hkScalarBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    DifferentialGeometry.Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup
      (HkScalar (I := I) (M := M) g k) :=
  scalarHsBoundedC0Semigroup (I := I) (M := M) g (k : ℝ)

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
