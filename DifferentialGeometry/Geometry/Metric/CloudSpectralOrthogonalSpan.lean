import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# CFS04's span clause: the spectral projector is the identity off the local span

Blueprint `master207B.tex`, CFS04 (`lem:fibration-cloud-neighborhood-spectral`, lines 1922–1965),
last display: on each CFS02 neighbourhood `B(v, λ r₀)` the single space
`V = span{x_i − x₀, L_{x_i} : i ∈ J}` satisfies `Q|_{V⊥} = I` and
`proj_{V⊥} η(z) = proj_{V⊥}(z − x₀)`. The (SE) and (DE) clauses of CFS04 are the existing kernel
`GC.MetricGeometry.exists_uniform_cloud_displacement_jets`; this module adds the span clause for the
SAME weights, average and spectral projector (the cluster of eigenvalues in `B(1, 1/2)`).

* `orthogonal_le_spectralCluster` (kernel): if the weights sum to one and every plane with a
  nonzero weight lies in `V`, then `V⊥` lies in the eigenvalue-one space of
  `O = Σ w_i (L_i)⊥-projection`, hence in the spectral cluster `Q`.
* `starProjection_orthogonal_comp_of_le` (kernel): `V⊥ ≤ Q` gives `π_{V⊥} π_Q = π_{V⊥}`.
* `cfs04_orthogonal_span_clause` (row clause): for the cutoff weights
  `w_i = φ_i / Σ_a φ_a`, `φ_i = ballCutoff x_i (10 λ r_i) (20 λ r_i)`, every `z ∈ B(v, λ r₀)`
  (`v ∈ B(x₀, 5 λ r₀)`, `x₀` selected) satisfies `π_Q y = y` for `y ∈ V⊥` and
  `π_{V⊥}(π_Q(z − μ(z))) = π_{V⊥}(z − x₀)`, `μ = Σ w_i x_i`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Module
open scoped BigOperators

namespace GC.MetricGeometry

open DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Weighted normal projectors fix `V⊥` when every active plane lies in `V`: `V⊥` lies in the
spectral cluster of eigenvalues in `B(1, 1/2)`. -/
theorem orthogonal_le_spectralCluster {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) (L : ι → Submodule ℝ H) (V : Submodule ℝ H)
    (hLV : ∀ i ∈ s, w i ≠ 0 → L i ≤ V) :
    Vᗮ ≤ ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
      End.eigenspace (∑ i ∈ s, w i • (L i)ᗮ.starProjection).toLinearMap μ := by
  intro y hy
  have hfix : (∑ i ∈ s, w i • (L i)ᗮ.starProjection) y = y := by
    rw [sum_apply]
    calc ∑ i ∈ s, (w i • (L i)ᗮ.starProjection) y = ∑ i ∈ s, w i • y := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [smul_apply]
          by_cases hwi : w i = 0
          · rw [hwi, zero_smul, zero_smul]
          · congr 1
            exact Submodule.starProjection_eq_self_iff.mpr
              (Submodule.orthogonal_le (hLV i hi hwi) hy)
      _ = y := by rw [← Finset.sum_smul, hw, one_smul]
  have hmem : y ∈ End.eigenspace (∑ i ∈ s, w i • (L i)ᗮ.starProjection).toLinearMap 1 := by
    rw [End.mem_eigenspace_iff, one_smul]
    exact hfix
  exact Submodule.mem_iSup_of_mem (1 : ℝ) (Submodule.mem_iSup_of_mem (mem_ball_self (by norm_num))
    hmem)

/-- `V⊥ ≤ Q` gives `π_{V⊥} ∘ π_Q = π_{V⊥}`. -/
theorem starProjection_orthogonal_comp_of_le {V Q : Submodule ℝ H} (hVQ : Vᗮ ≤ Q) (u : H) :
    Vᗮ.starProjection (Q.starProjection u) = Vᗮ.starProjection u := by
  have h := congrArg (fun A : H →L[ℝ] H => A u) (Submodule.starProjection_comp_starProjection_of_le
    hVQ)
  simpa using h

/-- CFS04's span clause for the cutoff weights, average and spectral cluster of the selection. -/
theorem cfs04_orthogonal_span_clause (I : Finset H) (r : H → ℝ) (hr : ∀ i ∈ I, 0 < r i)
    (P : H → Submodule ℝ H) {ℓ : ℝ} (hℓ : 0 < ℓ) {x₀ : H} (hx₀ : x₀ ∈ I) {v : H}
    (hv : v ∈ ball x₀ (5 * ℓ * r x₀)) :
    let V : Submodule ℝ H := ⨆ (i ∈ I) (_ : (closedBall i (20 * ℓ * r i) ∩
      ball v (ℓ * r x₀)).Nonempty), (ℝ ∙ (i - x₀)) ⊔ P i
    let w : H → H → ℝ := fun i y => ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
      ∑ a ∈ I, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y
    let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
      End.eigenspace (∑ i ∈ I, w i y • (P i)ᗮ.starProjection).toLinearMap μ
    ∀ z ∈ ball v (ℓ * r x₀), (∀ y ∈ Vᗮ, (Q z).starProjection y = y) ∧
      Vᗮ.starProjection ((Q z).starProjection (z - ∑ i ∈ I, w i z • i)) =
        Vᗮ.starProjection (z - x₀) := by
  intro V w Q z hz
  have hr₀ := hr x₀ hx₀
  -- the reference cutoff is one at `z`, so the denominator is positive
  have hzx₀ : dist z x₀ ≤ 10 * ℓ * r x₀ := by
    have h1 := mem_ball.mp hz
    have h2 := mem_ball.mp hv
    have := dist_triangle z v x₀
    nlinarith
  have hone : ballCutoff x₀ (10 * ℓ * r x₀) (2 * (10 * ℓ * r x₀)) z = 1 :=
    ballCutoff_eq_one_of_mem_closedBall (by positivity) (by nlinarith)
      (mem_closedBall.mpr hzx₀)
  have hden : 0 < ∑ a ∈ I, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) z := by
    have hle := Finset.single_le_sum (f := fun a => ballCutoff a (10 * ℓ * r a)
      (2 * (10 * ℓ * r a)) z) (fun a _ => (ballCutoff_mem_Icc _ _ _ _).1) hx₀
    simp only [hone] at hle
    linarith
  have hw : ∑ i ∈ I, w i z = 1 := by
    simp only [w]
    rw [← Finset.sum_div, div_self hden.ne']
  -- an active weight forces the index into `J`
  have hactive : ∀ i ∈ I, w i z ≠ 0 →
      (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x₀)).Nonempty := by
    intro i hi hwi
    have hcut : ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) z ≠ 0 := by
      intro h0
      exact hwi (by simp only [w, h0, zero_div])
    have hri := hr i hi
    have hzi : z ∈ ball i (2 * (10 * ℓ * r i)) := by
      by_contra hn
      exact hcut (ballCutoff_eq_zero_of_not_mem_ball (by positivity) (by nlinarith) hn)
    refine ⟨z, mem_closedBall.mpr ?_, hz⟩
    have := mem_ball.mp hzi
    linarith
  have hJV : ∀ i ∈ I, (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x₀)).Nonempty →
      (ℝ ∙ (i - x₀)) ⊔ P i ≤ V := fun i hi hJ =>
    le_iSup₂_of_le (f := fun (j : H) (_ : j ∈ I) => ⨆ (_ : (closedBall j (20 * ℓ * r j) ∩
      ball v (ℓ * r x₀)).Nonempty), (ℝ ∙ (j - x₀)) ⊔ P j) i hi (le_iSup_of_le hJ le_rfl)
  have hVQ : Vᗮ ≤ Q z :=
    orthogonal_le_spectralCluster I (fun i => w i z) hw P V fun i hi hwi =>
      le_sup_right.trans (hJV i hi (hactive i hi hwi))
  refine ⟨fun y hy => Submodule.starProjection_eq_self_iff.mpr (hVQ hy), ?_⟩
  rw [starProjection_orthogonal_comp_of_le hVQ]
  -- the average differs from `x₀` by a vector of `V`
  have hmean : z - ∑ i ∈ I, w i z • i = (z - x₀) - ∑ i ∈ I, w i z • (i - x₀) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]
    abel
  have hmemV : ∑ i ∈ I, w i z • (i - x₀) ∈ V := by
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hwi : w i z = 0
    · rw [hwi, zero_smul]
      exact V.zero_mem
    · exact Submodule.smul_mem _ _ (le_sup_left.trans (hJV i hi (hactive i hi hwi))
        (Submodule.mem_span_singleton_self _))
  rw [hmean, map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hmemV, sub_zero]

end GC.MetricGeometry
