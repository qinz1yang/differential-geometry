import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticLowerSemicontinuity
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Filter MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_sum_norm_sq_weak_gradient_le_liminf_on_subset
    {Ω S : Set E} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (f : ℕ → E → F) (v : E → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (K : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (K n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp E 2 (volume.restrict Ω)),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z))) :
    (∫ x in S, ∑ j : Fin d, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2) ≤
      liminf (fun n => ∫ x in S, ∑ j : Fin d,
        ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) atTop := by
  classical
  let B : E → F →L[ℝ] F →L[ℝ] ℝ := S.indicator (fun _ => innerSL ℝ)
  have hm : AEStronglyMeasurable B (volume.restrict Ω) :=
    aestronglyMeasurable_const.indicator hS
  have hb : ∀ᵐ x ∂volume.restrict Ω, ‖B x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    by_cases hx : x ∈ S
    · simpa only [B, indicator_of_mem hx] using
        (show ‖(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)‖ ≤ 1 from norm_innerSL_le ℝ)
    · rw [show B x = 0 by simp only [B, indicator_of_notMem hx]]
      rw [ContinuousLinearMap.opNorm_zero]
      exact zero_le_one
  have hp : ∀ᵐ x ∂volume.restrict Ω, ∀ z : F, 0 ≤ B x z z := by
    filter_upwards [] with x
    intro z
    by_cases hx : x ∈ S
    · rw [show B x = (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) by
        simp only [B, indicator_of_mem hx]]
      change 0 ≤ inner ℝ z z
      exact real_inner_self_nonneg
    · simp only [B, indicator_of_notMem hx, zero_apply, le_refl]
  have heq (w : E → F) :
      (∫ x in Ω, B x (w x) (w x)) = ∫ x in S, ‖w x‖ ^ 2 := by
    have hi : (fun x => B x (w x) (w x)) = S.indicator (fun x => ‖w x‖ ^ 2) := by
      funext x
      by_cases hx : x ∈ S
      · rw [show B x = (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) by
          simp only [B, indicator_of_mem hx], indicator_of_mem hx]
        change inner ℝ (w x) (w x) = ‖w x‖ ^ 2
        exact real_inner_self_eq_norm_sq _
      · simp only [B, indicator_of_notMem hx, zero_apply]
    rw [hi, setIntegral_indicator hS, inter_eq_right.mpr hSΩ]
  have hbase := sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    f v hs hv K hf hrep hweak (fun _ => B) B (fun _ => hm) 1 (fun _ => hb)
    (Eventually.of_forall fun _ => tendsto_const_nhds) (fun _ => hp)
  simp_rw [heq] at hbase
  obtain ⟨A, A₀, hA, hA₀, _⟩ := exists_lp_gradient_columns_of_tendsto_inner
    f v hs hv K hf hrep hweak
  have hvi (j : Fin d) : Integrable (fun x =>
      ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2) (volume.restrict S) := by
    have hmem : MemLp (fun x => WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        2 (volume.restrict Ω) := (Lp.memLp (A₀ j)).ae_eq (hA₀ j)
    exact (hmem.mono_measure (Measure.restrict_mono_set volume hSΩ)).norm.integrable_sq
  have hfi (n : ℕ) (j : Fin d) : Integrable (fun x =>
      ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) (volume.restrict S) := by
    have hmem : MemLp (fun x => fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        2 (volume.restrict Ω) := (Lp.memLp (A j n)).ae_eq (hA j n)
    exact (hmem.mono_measure (Measure.restrict_mono_set volume hSΩ)).norm.integrable_sq
  have hvsum : (∫ x in S, ∑ j : Fin d,
      ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2) =
        ∑ j : Fin d, ∫ x in S, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad x j)‖ ^ 2 :=
    integral_finsetSum Finset.univ (fun j _ => hvi j)
  have hfsum (n : ℕ) : (∫ x in S, ∑ j : Fin d,
      ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) =
        ∑ j : Fin d, ∫ x in S, ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2 :=
    integral_finsetSum Finset.univ (fun j _ => hfi n j)
  simpa only [hvsum, hfsum] using hbase

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
