import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity
import DifferentialGeometry.Analysis.Sobolev.Solutions.FriedrichsCommutator
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollification operator on Euclidean space.

This module sets up the mollification operator
`mollifyEps hε u := mollifierEps hε ⋆ u` on
`EuclideanSpace ℝ (Fin d)`, used downstream for approximating non-smooth
`L²` / `H¹` functions by smooth ones.

## Main results

* `mollifyEps_contDiff`: for `0 < ε`, the mollified function is smooth on
  the whole space when `u : E → ℝ` is locally integrable.
* `mollifyEps_continuous`: continuity of the mollified function.
* `mollifyEps_apply`: pointwise integral formula.
* `mollifyEps_hasCompactSupport`: compact support of the mollified function
  when `u` has compact support.
* `mollifyEps_memLp_two_of_hasCompactSupport`: when `u` is in `L²` with
  compact support, the mollified function is in `L²` (by smoothness +
  compact support).
* `tendsto_mollifyEps_of_continuous`: pointwise convergence of the
  mollified function to a continuous function as `ε → 0⁺`.
* `ae_tendsto_mollifyEps_of_locallyIntegrable`: a.e. pointwise convergence
  of the mollified function to a locally integrable function.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The ε-mollified version of a function `u : E → ℝ`:
`mollifyEps hε u := mollifierEps hε ⋆ u`. The convolution uses the standard
`lsmul ℝ ℝ` bilinear pairing on real-valued functions. -/
def mollifyEps {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) : E → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.mollifierEps (d := d) hε ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u

/-- For `0 < ε` and a locally integrable `u : E → ℝ`, the mollified function
is smooth on the whole space. -/
theorem mollifyEps_contDiff {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_loc : LocallyIntegrable u (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) := by
  unfold mollifyEps
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport hε)
    (DifferentialGeometry.Analysis.Sobolev.mollifierEps_smooth hε)
    hu_loc

/-- Continuity of the mollified function. -/
theorem mollifyEps_continuous {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_loc : LocallyIntegrable u (volume : Measure E)) :
    Continuous (mollifyEps (d := d) hε u) :=
  (mollifyEps_contDiff (d := d) hε hu_loc).continuous

/-- The mollified value at `x` is the integral of `mollifierEps(t) · u(x - t)`. -/
lemma mollifyEps_apply {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      ∫ t,
        DifferentialGeometry.Analysis.Sobolev.mollifierEps (d := d) hε t * u (x - t)
        ∂(volume : Measure E) := by
  simp [mollifyEps, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- If `u` has compact support, so does `mollifyEps hε u`. -/
theorem mollifyEps_hasCompactSupport {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_supp : HasCompactSupport u) :
    HasCompactSupport (mollifyEps (d := d) hε u) :=
  HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure E))
    (DifferentialGeometry.Analysis.Sobolev.mollifierEps_compactSupport hε)
    hu_supp

/-- For `u ∈ L²` with compact support, the mollified function is in `L²`.
Combination of smoothness (hence continuity) and compact support of the
result, both established above. -/
theorem mollifyEps_memLp_two_of_hasCompactSupport {ε : ℝ} (hε : 0 < ε)
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    (hu_supp : HasCompactSupport u) :
    MemLp (mollifyEps (d := d) hε u) 2 (volume : Measure E) := by
  have hu_loc : LocallyIntegrable u (volume : Measure E) :=
    hu_l2.locallyIntegrable (by norm_num)
  have h_cont : Continuous (mollifyEps (d := d) hε u) :=
    mollifyEps_continuous (d := d) hε hu_loc
  have h_supp : HasCompactSupport (mollifyEps (d := d) hε u) :=
    mollifyEps_hasCompactSupport (d := d) hε hu_supp
  exact h_cont.memLp_of_hasCompactSupport h_supp

/-- Pointwise convergence of the mollified function to a continuous function
at every point: for `u : E → ℝ` continuous and any `x₀ : E`,
`mollifyEps εₙ u x₀ → u x₀` along any sequence `εₙ → 0⁺`. -/
theorem tendsto_mollifyEps_of_continuous {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu : Continuous u) (x₀ : E) :
    Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_rOut_tendsto :
      Tendsto
        (fun i => (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps
            (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_conv_tendsto :
      Tendsto
        (fun i =>
          ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
              (hε i)).normed (volume : Measure E) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀)
        l (𝓝 (u x₀)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure E))
      h_rOut_tendsto hu x₀
  have h_fn_eq : ∀ i,
      ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
            (hε i)).normed (volume : Measure E) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
            (hε i)).normed (volume : Measure E) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine h_conv_tendsto.congr ?_
  intro i; exact h_fn_eq i

/-- Almost-everywhere pointwise convergence of the mollified function to a
locally integrable function. -/
theorem ae_tendsto_mollifyEps_of_locallyIntegrable {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu_loc : LocallyIntegrable u (volume : Measure E)) :
    ∀ᵐ x₀ ∂(volume : Measure E),
      Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_bump_rIn : ∀ i,
      (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2 := by
    intro i
    show (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2
    rfl
  have h_rOut_tendsto :
      Tendsto
        (fun i =>
          (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_ratio :
      ∀ᶠ i in l,
        (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
          ≤ 2 *
            (DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
              (hε i)).rIn := by
    refine Filter.Eventually.of_forall fun i => ?_
    rw [h_bump_rOut, h_bump_rIn]
    have : ε i = 2 * (ε i / 2) := by ring
    linarith
  have h_ae :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure E)) h_rOut_tendsto h_ratio hu_loc
  filter_upwards [h_ae] with x₀ hx₀
  have h_eq : ∀ i,
      ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (volume : Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((DifferentialGeometry.Analysis.Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (volume : Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine hx₀.congr ?_
  intro i; exact h_eq i

end DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect
