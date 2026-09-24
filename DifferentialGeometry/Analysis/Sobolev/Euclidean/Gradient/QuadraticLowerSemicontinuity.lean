import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Columns
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import DifferentialGeometry.Topology.Order.LiminfSum

noncomputable section

open Filter MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    {Ω : Set E} (f : ℕ → E → F) (v : E → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (K : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (K n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp E 2 (volume.restrict Ω)),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)))
    (B : ℕ → E → F →L[ℝ] F →L[ℝ] ℝ) (B₀ : E → F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ∀ n, AEStronglyMeasurable (B n) (volume.restrict Ω))
    (C : ℝ) (hC : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖B n x‖ ≤ C)
    (hconv : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => B n x) atTop (𝓝 (B₀ x)))
    (hpos : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ∀ z, 0 ≤ B n x z z)
    (j : Fin d) :
    (∫ x in Ω, B₀ x (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤
      liminf (fun n => ∫ x in Ω,
        B n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) atTop := by
  obtain ⟨A, A₀, hA, hA₀, hAweak⟩ :=
    exists_lp_gradient_columns_of_tendsto_inner f v hs hv K hf hrep hweak
  have h := integral_quadratic_le_liminf_of_weak_of_ae_tendsto
    B B₀ hB C hC hconv hpos (A j) (A₀ j) (hAweak j)
  have heq (n : ℕ) :
      (∫ x in Ω, B n x (A j n x) (A j n x)) =
        ∫ x in Ω, B n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1)) := by
    apply integral_congr_ae
    filter_upwards [hA j n] with x hx
    rw [hx]
  have heq₀ :
      (∫ x in Ω, B₀ x (A₀ j x) (A₀ j x)) =
        ∫ x in Ω, B₀ x (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)) := by
    apply integral_congr_ae
    filter_upwards [hA₀ j] with x hx
    rw [hx]
  simpa only [heq, heq₀] using h

theorem sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    {Ω : Set E} (f : ℕ → E → F) (v : E → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (K : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (K n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp E 2 (volume.restrict Ω)),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)))
    (B : ℕ → E → F →L[ℝ] F →L[ℝ] ℝ) (B₀ : E → F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ∀ n, AEStronglyMeasurable (B n) (volume.restrict Ω))
    (C : ℝ) (hC : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖B n x‖ ≤ C)
    (hconv : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => B n x) atTop (𝓝 (B₀ x)))
    (hpos : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ∀ z, 0 ≤ B n x z z) :
    (∑ j : Fin d, ∫ x in Ω, B₀ x (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤
      liminf (fun n => ∑ j : Fin d, ∫ x in Ω,
        B n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) atTop := by
  let q (j : Fin d) (n : ℕ) := ∫ x in Ω,
    B n x (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
      (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
  obtain ⟨A, A₀, hA, _, hAweak⟩ :=
    exists_lp_gradient_columns_of_tendsto_inner f v hs hv K hf hrep hweak
  have heq (j : Fin d) (n : ℕ) :
      (∫ x in Ω, B n x (A j n x) (A j n x)) = q j n := by
    apply integral_congr_ae
    filter_upwards [hA j n] with x hx
    rw [hx]
  have hlo (j : Fin d) : IsBoundedUnder (· ≥ ·) atTop (q j) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q j n
    apply Eventually.of_forall
    intro n
    exact integral_nonneg_of_ae ((hpos n).mono fun x hx => hx _)
  have hhi (j : Fin d) : IsBoundedUnder (· ≤ ·) atTop (q j) := by
    obtain ⟨D, hD⟩ := isBoundedUnder_integral_quadratic_of_weak B
      (fun n x y => ((hB n).apply_continuousLinearMap x).apply_continuousLinearMap y)
      (Eventually.of_forall hC) (A j) (A₀ j) (hAweak j)
    change ∀ᶠ n in atTop, ‖∫ x in Ω, B n x (A j n x) (A j n x)‖ ≤ D at hD
    refine ⟨D, ?_⟩
    change ∀ᶠ n in atTop, q j n ≤ D
    filter_upwards [hD] with n hn
    exact (le_abs_self (q j n)).trans (by simpa only [heq, Real.norm_eq_abs] using hn)
  have hlsc (j : Fin d) :
      (∫ x in Ω, B₀ x (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ≤ liminf (q j) atTop :=
    integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
      f v hs hv K hf hrep hweak B B₀ hB C hC hconv hpos j
  have hsum := sum_liminf_le Finset.univ q (fun j _ => hlo j) (fun j _ => hhi j)
  have heqsum : (∑ j, q j) = (fun n => ∑ j, q j n) := by
    funext n
    exact Finset.sum_apply n Finset.univ q
  rw [heqsum] at hsum
  exact (Finset.sum_le_sum fun j _ => hlsc j).trans hsum

end DifferentialGeometry.Analysis.Sobolev.Euclidean
