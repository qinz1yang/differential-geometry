import DifferentialGeometry.Geometry.Metric.CloudGateTubeRow

/-!
# Consumer of CFS19

* `cfs19_row_univ`: CFS19 with the ambient domain `O = H` (the slim case of CFS22, whose cutoff
  is smooth on all of `H`): the closed support of `ψ` along `f` lies over the original core `A`
  and inside the projection tube of the original centres.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open scoped ContDiff

namespace GC.MetricGeometry

/-- CFS19 with `O = H`. -/
theorem cfs19_row_univ {M H Hq I : Type*} [TopologicalSpace M] [CompactSpace M]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Hq] [NormedSpace ℝ Hq]
    (F : M → H) (hF : Continuous F) (ρ : M → ℝ) (hρ : Continuous ρ) (hρpos : ∀ p, 0 < ρ p)
    (A : Set M) (hA : IsOpen A) (G ψ : H → ℝ) (hG : Continuous G) (hψ : ContDiff ℝ ∞ ψ)
    (hgate : tsupport ψ ⊆ {z | (1 / 2 : ℝ) ≤ G z}) (houtside : ∀ p ∉ A, G (F p) = 0)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (marker : I → Hq → ℝ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (hsupport : ∀ i p, 0 < marker i (π (F p)) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (hfull : ∀ p ∈ A, ∃ i, marker i (π (F p)) = R i)
    (sel : M → M) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 * σ / 10 ∧ ∀ f : M → H, (∀ p, ‖f p - F p‖ ≤ κ * ρ p) →
      ∀ p, f p ∈ tsupport ψ → p ∈ A ∧ π (f p) ∈ ball (π (F p)) (σ * ρ (sel p)) := by
  let hdec_C14KA : ∀ z, Decidable (z ∈ cfsProjectedTube π F A (fun p => σ * ρ (sel p))) :=
    fun _ => Classical.propDecidable _
  have hgate' : closure (support ψ ∩ univ) ∩ univ ⊆ {z | (1 / 2 : ℝ) ≤ G z} := by
    rw [inter_univ, inter_univ]
    exact hgate
  obtain ⟨κ, hκ, hκc, hrow⟩ := cfs19_row univ isOpen_univ F (fun _ => mem_univ _) hF ρ hρ hρpos
    A hA G ψ hG.continuousOn hψ.contDiffOn hgate' houtside π hπ marker R hR hsupport hfull sel
    hsel hσ
  refine ⟨κ, hκ, hκc, fun f hf p hp => ?_⟩
  obtain ⟨-, hloc, -, -⟩ := hrow f hf
  obtain ⟨hpA, hd, -⟩ := hloc p (by rw [inter_univ]; exact hp)
  have hr : 0 < σ * ρ (sel p) := mul_pos hσ (hρpos (sel p))
  refine ⟨hpA, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

end GC.MetricGeometry
