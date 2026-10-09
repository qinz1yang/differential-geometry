import DifferentialGeometry.Analysis.InnerProductSpace.RealSpectralProjectionPerturbation

set_option autoImplicit false
noncomputable section
open Metric ContinuousLinearMap
open scoped NNReal Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sum_smul_sub_le_of_active_close
    {ι : Type*} (S : Finset ι) {U : Set E} (hU : IsOpen U) {w : ι → E → ℝ} {m : ℕ}
    (hw : ∀ i ∈ S, ContDiffOn ℝ m (w i) U)
    (hw0 : ∀ y ∈ U, ∀ i ∈ S, 0 ≤ w i y)
    (hw1 : ∀ y ∈ U, ∑ i ∈ S, w i y = 1)
    (A : ι → H →L[ℝ] H) (hA : ∀ i ∈ S, (A i).toLinearMap.IsSymmetric)
    (P : Submodule ℝ H) {δ σ : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4) (hσ : 0 ≤ σ)
    (hclose : ∀ i ∈ S, (∃ y ∈ U, w i y ≠ 0) → ‖A i - P.starProjection‖ ≤ δ)
    {x : E} (hx : x ∈ U) (B : ℝ≥0)
    (hD : ∀ j, 1 ≤ j → j ≤ m →
      (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) ≤ B * σ ^ j) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n (fun y =>
        (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
          Module.End.eigenspace (∑ i ∈ S, w i y • A i).toLinearMap μ).starProjection -
            P.starProjection) x‖ ≤
        max 4 ((resolventDerivativeBound 4 B n : ℝ) / 2) * δ * σ ^ n := by
  classical
  let J : Finset ι := S.filter (fun i => ∃ y ∈ U, w i y ≠ 0)
  have hJS : J ⊆ S := Finset.filter_subset _ _
  have hzero (i : ι) (hi : i ∈ S) (hnot : i ∉ J) (y : E) (hy : y ∈ U) :
      w i y = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hi, y, hy, hne⟩)
  have hsum (y : E) (hy : y ∈ U) : (∑ i ∈ S, w i y) = ∑ i ∈ J, w i y := by
    exact (Finset.sum_subset hJS (fun i hi hnot => hzero i hi hnot y hy)).symm
  have hoperator (y : E) (hy : y ∈ U) :
      (∑ i ∈ S, w i y • A i) = ∑ i ∈ J, w i y • A i := by
    exact (Finset.sum_subset hJS (fun i hi hnot => by
      rw [hzero i hi hnot y hy, zero_smul])).symm
  have hjetzero (j : ℕ) (i : ι) (hi : i ∈ S) (hnot : i ∉ J) :
      iteratedFDeriv ℝ j (w i) x = 0 := by
    have heq : w i =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hzero i hi hnot y hy
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (heq.iteratedFDeriv ℝ j).self_of_nhds
  have hDJ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      (∑ i ∈ J, ‖iteratedFDeriv ℝ j (w i) x‖) ≤ B * σ ^ j := by
    have heq : (∑ i ∈ J, ‖iteratedFDeriv ℝ j (w i) x‖) =
        ∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖ := by
      exact Finset.sum_subset hJS (fun i hi hnot => by
        rw [hjetzero j i hi hnot, norm_zero])
    rw [heq]
    exact hD j hj hjm
  have hlocal := norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sum_smul_sub_le
    J hU (fun i hi => hw i (hJS hi))
    (fun y hy i hi => hw0 y hy i (hJS hi))
    (fun y hy => (hsum y hy).symm.trans (hw1 y hy))
    A (fun i hi => hA i (hJS hi)) P hδ hδsmall hσ
    (fun i hi => hclose i (hJS hi) (Finset.mem_filter.mp hi).2) hx B hDJ
  have heq : (fun y =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
        Module.End.eigenspace (∑ i ∈ S, w i y • A i).toLinearMap μ).starProjection -
          P.starProjection) =ᶠ[𝓝 x] (fun y =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
        Module.End.eigenspace (∑ i ∈ J, w i y • A i).toLinearMap μ).starProjection -
          P.starProjection) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hoperator y hy]
  intro n hnm
  rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
  exact hlocal n hnm
