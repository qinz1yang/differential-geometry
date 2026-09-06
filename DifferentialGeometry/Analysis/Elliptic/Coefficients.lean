import DifferentialGeometry.Analysis.Schauder.CompactEllipticity
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients
import Mathlib.Topology.Instances.Matrix

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

def ellipticCoeffOfPointwiseBounds
    {d : ℕ} [NeZero d]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ)
    (hmeas : ∀ i j, Measurable (fun x => a x i j))
    (hcoer : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
      lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (a x) ξ⟫_ℝ)
    (hcoer_inv : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
      Λ⁻¹ * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE ((a x)⁻¹) ξ⟫_ℝ) :
    DeGiorgi.EllipticCoeff d Ω := by
  refine {
    a := a
    lam := lam
    Λ := Λ
    measurable_comp := hmeas
    hlam := hlam
    hΛ := hΛ
    coercive := ?_
    coercive_inv := ?_ }
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hcoer x hx
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hcoer_inv x hx

theorem exists_uniform_matrix_and_inverse_quadratic_lower_bound
    {X : Type*} [TopologicalSpace X]
    {d : ℕ}
    {K : Set X} (hKc : IsCompact K)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hAcont : ∀ i j, ContinuousOn (fun x => A x i j) K)
    (hApos : ∀ x ∈ K, (A x).PosDef) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin d),
        c₁ * ‖v‖ ^ 2 ≤ ⟪v, DeGiorgi.matMulE (A x) v⟫_ℝ) ∧
      (∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin d),
        c₂ * ‖v‖ ^ 2 ≤ ⟪v, DeGiorgi.matMulE ((A x)⁻¹) v⟫_ℝ) := by
  obtain ⟨c, hc, hcbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound
    hKc A hAcont hApos
  have hAcont_inv : ∀ i j, ContinuousOn (fun x => (A x)⁻¹ i j) K := by
    intro i j x hx
    have hA : ContinuousOn A K := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      exact hAcont i j
    have hdet : (A x).det ≠ 0 := ne_of_gt (hApos x hx).det_pos
    have hinv : ContinuousAt Ring.inverse (A x).det := by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
    have hc' := (continuousAt_matrix_inv (A x) hinv).comp_continuousWithinAt
      (hA x hx)
    exact (continuous_apply j).continuousAt.comp_continuousWithinAt
      ((continuous_apply i).continuousAt.comp_continuousWithinAt hc')
  obtain ⟨c₂, hc₂, hc₂bound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound
    hKc (fun x => (A x)⁻¹) hAcont_inv (fun x hx => (hApos x hx).inv)
  refine ⟨c, c₂, hc, hc₂, ?_, ?_⟩
  · intro x hx v
    change c * ‖v‖ ^ 2 ≤ (DeGiorgi.matMulE _ v).ofLp ⬝ᵥ star v.ofLp
    rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
    exact hcbound x hx v
  · intro x hx v
    change c₂ * ‖v‖ ^ 2 ≤ (DeGiorgi.matMulE _ v).ofLp ⬝ᵥ star v.ofLp
    rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
    exact hc₂bound x hx v

theorem ellipticCoeff_of_continuous_posDef_on_compact
    {d : ℕ} [NeZero d] {Ω K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hΩK : Ω ⊆ K) (hKc : IsCompact K)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hAmeas : ∀ i j, Measurable (fun x => A x i j))
    (hAcont : ∀ i j, ContinuousOn (fun x => A x i j) K)
    (hApos : ∀ x ∈ K, (A x).PosDef) :
    ∃ C : DeGiorgi.EllipticCoeff d Ω, C.a = A := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hcoer, hcoer_inv⟩ :=
    exists_uniform_matrix_and_inverse_quadratic_lower_bound hKc A hAcont hApos
  let Λ : ℝ := max c₁ c₂⁻¹
  have hΛ : c₁ ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le hc₁ hΛ
  have hc₂ne : c₂ ≠ 0 := ne_of_gt hc₂
  have hcoerΩ : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
      c₁ * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (A x) ξ⟫_ℝ := by
    intro x hx ξ
    exact hcoer x (hΩK hx) ξ
  have hcoerInvΩ : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
      Λ⁻¹ * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE ((A x)⁻¹) ξ⟫_ℝ := by
    intro x hx ξ
    have hmax : c₂⁻¹ ≤ Λ := le_max_right _ _
    have hscale : Λ⁻¹ ≤ c₂ := by
      have hi := (inv_le_inv₀ hΛpos (inv_pos.mpr hc₂)).2 hmax
      simpa [hc₂ne] using hi
    exact (mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖ξ‖)).trans
      (hcoer_inv x (hΩK hx) ξ)
  exact ⟨ellipticCoeffOfPointwiseBounds hΩm A c₁ Λ hc₁ hΛ hAmeas
    hcoerΩ hcoerInvΩ, rfl⟩

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
