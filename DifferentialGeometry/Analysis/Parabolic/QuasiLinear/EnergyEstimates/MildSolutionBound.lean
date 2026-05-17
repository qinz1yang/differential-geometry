import DifferentialGeometry.Analysis.ODE.IntegralGronwall
import DifferentialGeometry.Analysis.Sobolev.Hk.HeatSemigroupHkExt
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A-priori `Hˢ`-norm bound for continuous mild solutions

For a closed Riemannian manifold `(M, g)`, a Sobolev exponent `σ`, an
initial datum `u₀ : Hˢ`, and a Lipschitz nonlinearity
`N : Hˢ → Hˢ`, any continuous map `u : [0, T] → Hˢ` that satisfies the
Duhamel mild-solution formula

  `u(t) = e^{t Δ} u₀ + ∫₀ᵗ e^{(t-τ) Δ} (N (u τ)) dτ`

is bounded in `Hˢ` by `(‖u₀‖ + ‖N 0‖ · t) · exp(L · t)`. The estimate is
obtained by applying the affine integral Grönwall inequality to the norm
function `f(t) := ‖u t‖`, after bounding the Duhamel integrand pointwise
via the contractivity of the heat semigroup and the Lipschitz hypothesis
on `N`.

## Main results

* `mild_solution_norm_le` — the a-priori `Hˢ` bound for continuous mild
  solutions to the scalar quasi-linear heat equation.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear
namespace EnergyEstimates

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hk
open DifferentialGeometry.Analysis.Laplacian.Spectral
open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **A-priori `Hˢ` bound for continuous mild solutions.** Let `(M, g)` be
a closed Riemannian manifold, `σ ∈ ℝ`, and `N : Hˢ → Hˢ` an `L`-Lipschitz
map. Any continuous `u : [0, T] → Hˢ` satisfying the Duhamel mild-solution
formula `u(t) = e^{t Δ} u₀ + ∫₀ᵗ e^{(t-τ) Δ} (N (u τ)) dτ` on `[0, T]`
obeys `‖u t‖ ≤ (‖u₀‖ + ‖N 0‖ · t) · exp(L · t)` for every `t ∈ [0, T]`.

The bound is obtained by applying the affine integral Grönwall inequality
to `f(t) := ‖u t‖`, using contractivity of the heat semigroup on `t ≥ 0`
and the Lipschitz bound `‖N x‖ ≤ L · ‖x‖ + ‖N 0‖`. -/
theorem mild_solution_norm_le
    {g : SmoothRiemannianMetric I M} {σ : ℝ} (u₀ : scalarHs (I := I) (M := M) g σ)
    {N : scalarHs (I := I) (M := M) g σ → scalarHs (I := I) (M := M) g σ}
    {L : NNReal} (hN : LipschitzWith L N)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → scalarHs (I := I) (M := M) g σ}
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatSemigroupHkExt (I := I) (M := M) g σ t u₀ +
        ∫ τ in (0:ℝ)..t,
          heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖u t‖ ≤ (‖u₀‖ + ‖N 0‖ * t) * Real.exp ((L : ℝ) * t) := by
  -- Abbreviations.
  set f : ℝ → ℝ := fun t => ‖u t‖ with hf_def
  -- `f` is continuous on `Icc 0 T` and non-negative everywhere.
  have hf_cont : ContinuousOn f (Set.Icc 0 T) := hu_cont.norm
  have hf_nn : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ f t := fun t _ => norm_nonneg _
  -- Non-negativity bookkeeping.
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hu₀_nn : (0 : ℝ) ≤ ‖u₀‖ := norm_nonneg _
  have hN0_nn : (0 : ℝ) ≤ ‖N 0‖ := norm_nonneg _
  -- The pointwise bound `‖N x‖ ≤ L · ‖x‖ + ‖N 0‖` for every `x : Hˢ`.
  have hN_bound : ∀ x : scalarHs (I := I) (M := M) g σ,
      ‖N x‖ ≤ (L : ℝ) * ‖x‖ + ‖N 0‖ := by
    intro x
    have h_dist := hN.dist_le_mul x 0
    -- `dist (N x) (N 0) ≤ L · dist x 0`
    have h_normNxN0 : ‖N x - N 0‖ ≤ (L : ℝ) * ‖x‖ := by
      have hd : dist (N x) (N 0) = ‖N x - N 0‖ := dist_eq_norm _ _
      have hxd : dist x (0 : scalarHs (I := I) (M := M) g σ) = ‖x‖ := by
        rw [dist_zero_right]
      rw [hd, hxd] at h_dist
      exact h_dist
    calc
      ‖N x‖ = ‖(N x - N 0) + N 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖N x - N 0‖ + ‖N 0‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖x‖ + ‖N 0‖ := by linarith
  -- The auxiliary integrand bound `g_int(τ) := L · f τ + ‖N 0‖` is
  -- continuous on `Icc 0 T`.
  set g_int : ℝ → ℝ := fun τ => (L : ℝ) * f τ + ‖N 0‖ with hg_int_def
  have hg_int_cont : ContinuousOn g_int (Set.Icc 0 T) := by
    refine ContinuousOn.add ?_ continuousOn_const
    exact continuousOn_const.mul hf_cont
  -- The key step: bound `f t` by `‖u₀‖ + ‖N 0‖ · t + L · ∫₀ᵗ f`.
  have hf_int :
      ∀ t ∈ Set.Icc (0:ℝ) T,
        f t ≤ ‖u₀‖ + ‖N 0‖ * t + (L : ℝ) * ∫ τ in (0:ℝ)..t, f τ := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htT : t ≤ T := ht.2
    -- Restrict continuity of `f` and `g_int` to `Icc 0 t ⊆ Icc 0 T`.
    have hIcc_sub : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) T :=
      Set.Icc_subset_Icc le_rfl htT
    have hf_cont_t : ContinuousOn f (Set.Icc 0 t) := hf_cont.mono hIcc_sub
    have hg_cont_t : ContinuousOn g_int (Set.Icc 0 t) := hg_int_cont.mono hIcc_sub
    have hf_ii : IntervalIntegrable f MeasureTheory.volume 0 t :=
      hf_cont_t.intervalIntegrable_of_Icc ht0
    have hg_ii : IntervalIntegrable g_int MeasureTheory.volume 0 t :=
      hg_cont_t.intervalIntegrable_of_Icc ht0
    -- Apply the Duhamel identity, then split into the homogeneous and
    -- Duhamel-integral terms.
    have hu_t := hu_eq t ht
    have hf_le_split :
        f t ≤ ‖heatSemigroupHkExt (I := I) (M := M) g σ t u₀‖ +
          ‖∫ τ in (0:ℝ)..t,
            heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ := by
      change ‖u t‖ ≤ _
      rw [hu_t]
      exact norm_add_le _ _
    -- Homogeneous term bound: `‖e^{tΔ} u₀‖ ≤ ‖u₀‖` since the semigroup is a
    -- contraction on `Hˢ` for `t ≥ 0`.
    have hhom_le : ‖heatSemigroupHkExt (I := I) (M := M) g σ t u₀‖ ≤ ‖u₀‖ := by
      have h_op := heatSemigroupHkExt_opNorm_le_one
        (I := I) (M := M) (g := g) (σ := σ) ht0
      have h_apply :
          ‖heatSemigroupHkExt (I := I) (M := M) g σ t u₀‖ ≤
            ‖heatSemigroupHkExt (I := I) (M := M) g σ t‖ * ‖u₀‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h_step : ‖heatSemigroupHkExt (I := I) (M := M) g σ t‖ * ‖u₀‖ ≤
          1 * ‖u₀‖ := by gcongr
      linarith
    -- Pointwise bound for the Duhamel integrand on `Ioc 0 t`.
    have h_ptw : ∀ τ ∈ Set.Ioc (0:ℝ) t,
        ‖heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ ≤
          g_int τ := by
      intro τ hτ
      have hτ_le_t : τ ≤ t := hτ.2
      have h_sub_nn : 0 ≤ t - τ := sub_nonneg.mpr hτ_le_t
      -- Contraction of the heat semigroup on `t - τ ≥ 0`.
      have h_op_sub := heatSemigroupHkExt_opNorm_le_one
        (I := I) (M := M) (g := g) (σ := σ) h_sub_nn
      have h_apply :
          ‖heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ ≤
            ‖heatSemigroupHkExt (I := I) (M := M) g σ (t - τ)‖ * ‖N (u τ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h_step :
          ‖heatSemigroupHkExt (I := I) (M := M) g σ (t - τ)‖ * ‖N (u τ)‖ ≤
            1 * ‖N (u τ)‖ := by gcongr
      have h_op_one :
          ‖heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ ≤
            ‖N (u τ)‖ := by linarith
      -- Lipschitz bound on `N (u τ)`.
      have h_lip : ‖N (u τ)‖ ≤ (L : ℝ) * ‖u τ‖ + ‖N 0‖ := hN_bound (u τ)
      change ‖heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ ≤
        (L : ℝ) * f τ + ‖N 0‖
      linarith
    -- Bound the Duhamel-integral norm.
    have h_int_le :
        ‖∫ τ in (0:ℝ)..t,
            heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ ≤
          ∫ τ in (0:ℝ)..t, g_int τ := by
      refine intervalIntegral.norm_integral_le_of_norm_le (hab := ht0) ?_ hg_ii
      exact Filter.Eventually.of_forall h_ptw
    -- Compute `∫₀ᵗ g_int = L · ∫₀ᵗ f + ‖N 0‖ · t`.
    have h_int_split :
        ∫ τ in (0:ℝ)..t, g_int τ =
          (L : ℝ) * (∫ τ in (0:ℝ)..t, f τ) + ‖N 0‖ * t := by
      have h_split_add :
          ∫ τ in (0:ℝ)..t, g_int τ =
            (∫ τ in (0:ℝ)..t, (L : ℝ) * f τ) +
              ∫ τ in (0:ℝ)..t, (‖N 0‖ : ℝ) := by
        change ∫ τ in (0:ℝ)..t, ((L : ℝ) * f τ + ‖N 0‖) =
          (∫ τ in (0:ℝ)..t, (L : ℝ) * f τ) +
            ∫ τ in (0:ℝ)..t, (‖N 0‖ : ℝ)
        exact intervalIntegral.integral_add (hf_ii.const_mul (L : ℝ))
          (intervalIntegrable_const)
      have h_const_mul :
          ∫ τ in (0:ℝ)..t, (L : ℝ) * f τ =
            (L : ℝ) * ∫ τ in (0:ℝ)..t, f τ :=
        intervalIntegral.integral_const_mul _ _
      have h_const :
          ∫ τ in (0:ℝ)..t, (‖N 0‖ : ℝ) = ‖N 0‖ * t := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
      rw [h_split_add, h_const_mul, h_const]
    -- Assemble the final inequality.
    calc
      f t ≤ ‖heatSemigroupHkExt (I := I) (M := M) g σ t u₀‖ +
            ‖∫ τ in (0:ℝ)..t,
              heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))‖ :=
            hf_le_split
      _ ≤ ‖u₀‖ + ∫ τ in (0:ℝ)..t, g_int τ := by linarith
      _ = ‖u₀‖ + ((L : ℝ) * (∫ τ in (0:ℝ)..t, f τ) + ‖N 0‖ * t) := by
            rw [h_int_split]
      _ = ‖u₀‖ + ‖N 0‖ * t + (L : ℝ) * ∫ τ in (0:ℝ)..t, f τ := by ring
  -- Apply the affine integral Grönwall inequality with
  -- `A := ‖u₀‖, B := ‖N 0‖, K := L`.
  intro t ht
  exact integral_gronwall_le_affine (T := T) (A := ‖u₀‖) (B := ‖N 0‖) (K := (L : ℝ))
    hT hu₀_nn hN0_nn hL_nn (f := f) hf_cont hf_nn hf_int t ht

end EnergyEstimates
end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
