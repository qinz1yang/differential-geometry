import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputLocalityBLOC
import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentLocalityBLOC

/-!
# The blend step of BCG04 / BCG05 on native stage outputs

Blueprint `master207B.tex`, BCG04 (B:9132) and BCG05 (B:9202); external draft 61 §3.3–3.5,
disposition D61-8. One stage of (CHAIN) with an active slot is
`Ψ z = z + ψ z • (π_Q (a (π_Q z)) − π_Q z)` with `a = O.ambient` the ambient nearest map of ONE
`Cfs15StageOutput O`. The stage hypothesis is exactly "points of the cutoff's closed support satisfy
the locality premise": if `z ∈ tsupport ψ`, then the original core point `x` is in the cloud, the
projected (perturbed) input `π_Q z` lies in `B(x, r_x)` (tube membership), and every contributor `i`
of the whole window at `x` has `J i = c`, `P i ≤ ker J`.

* `Cfs15StageOutput.stage_value_BLOC`: then `ψ z ≠ 0 → J (a (π_Q z)) = c`.
* `Cfs15StageOutput.adjustment_level_BLOC` / `adjustment_eq_BLOC`: with `(Q)ᗮ ≤ ker J` and
  `J z = c`, `J (Ψ z) = c = J z` (exact); `adjustment_scalar_BLOC`: `v (Ψ z) = 1`.
* `cfs15_chain3_level_BLOC`: the three stages `g₁, g₂, g₃` on three outputs `O₁, O₂, O₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace Cfs15StageOutput

variable {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **The stage value at the perturbed input**: if every point of the closed support of `ψ`
satisfies the locality premise at `x` (cloud membership, tube membership `π_Q z ∈ B(x, r_x)`, the
whole contributor window), then `ψ z ≠ 0 → J (a (π_Q z)) = c`. -/
theorem stage_value_BLOC (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (ψ : H → ℝ) (J : H →L[ℝ] F) {x z : H} {c : F}
    (hstage : z ∈ tsupport ψ → x ∈ S ∧ Q.starProjection z ∈ ball x (r x) ∧
      ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
        J i = c ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    ψ z ≠ 0 → J (O.ambient (Q.starProjection z)) = c := fun hψ => by
  obtain ⟨hx, hzx, hcontrib⟩ := hstage (subset_tsupport ψ hψ)
  exact (O.affine_locality_BLOC hx J c hcontrib).2.2.1 _ hzx

/-- **One active blend step keeps the level** (BCG04 with `c = 0`, BCG05 with `c = 1`): if `Q`
retains the block (`Qᗮ ≤ ker J`), `J z = c`, and the closed support of `ψ` satisfies the locality
premise at `x`, then `J (Ψ z) = c`. -/
theorem adjustment_level_BLOC (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (J : H →L[ℝ] F) (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (ψ : H → ℝ) {x z : H} {c : F}
    (hz : J z = c)
    (hstage : z ∈ tsupport ψ → x ∈ S ∧ Q.starProjection z ∈ ball x (r x) ∧
      ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
        J i = c ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    J (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = c :=
  adjustmentMap_level_BLOC Q J hQ O.ambient ψ hz (O.stage_value_BLOC Q ψ J hstage)

/-- **Exactness of one active blend step**: under the hypotheses of `adjustment_level_BLOC`,
`J (Ψ z) = J z`. -/
theorem adjustment_eq_BLOC (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (J : H →L[ℝ] F) (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (ψ : H → ℝ) {x z : H} {c : F}
    (hz : J z = c)
    (hstage : z ∈ tsupport ψ → x ∈ S ∧ Q.starProjection z ∈ ball x (r x) ∧
      ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
        J i = c ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    J (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = J z := by
  rw [O.adjustment_level_BLOC Q J hQ ψ hz hstage, hz]

/-- **BCG05's scalar blend step**: `v z = 1` and every contributor of the window at `x` with
`v i = 1`, `P i ≤ ker v` on the closed support of `ψ` give `v (Ψ z) = 1`. -/
theorem adjustment_scalar_BLOC (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (v : H →L[ℝ] ℝ) (hQ : Qᗮ ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) (ψ : H → ℝ) {x z : H}
    (hz : v z = 1)
    (hstage : z ∈ tsupport ψ → x ∈ S ∧ Q.starProjection z ∈ ball x (r x) ∧
      ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
        v i = 1 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) :
    v (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = 1 :=
  O.adjustment_level_BLOC Q v hQ ψ hz hstage

end Cfs15StageOutput

/-- **The three active stages of (CHAIN)** on three native outputs `O₁, O₂, O₃`:
`g₁ = Ψ₁ u`, `g₂ = Ψ₂ g₁`, `g₃ = Ψ₃ g₂` (`u = F(p)`). If every `Q_j` retains the block, `J u = c`,
and at each stage the cutoff's closed support satisfies the locality premise at the stage's
original core point `x_j`, then `J g₁ = J g₂ = J g₃ = c`. -/
theorem cfs15_chain3_level_BLOC {k₁ k₂ k₃ K₁ K₂ K₃ : ℕ} {ε₁ ε₂ ε₃ cw₁ cw₂ cw₃ : ℝ}
    {S₁ S₂ S₃ T₁ T₂ T₃ : Set H} {r₁ r₂ r₃ : H → ℝ} {P₁ P₂ P₃ : H → Submodule ℝ H}
    (O₁ : Cfs15StageOutput k₁ K₁ ε₁ cw₁ S₁ T₁ r₁ P₁)
    (O₂ : Cfs15StageOutput k₂ K₂ ε₂ cw₂ S₂ T₂ r₂ P₂)
    (O₃ : Cfs15StageOutput k₃ K₃ ε₃ cw₃ S₃ T₃ r₃ P₃) (Q₁ Q₂ Q₃ : Submodule ℝ H) (J : H →L[ℝ] F)
    (hQ₁ : Q₁ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (hQ₂ : Q₂ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F))
    (hQ₃ : Q₃ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (ψ₁ ψ₂ ψ₃ : H → ℝ) (u x₁ x₂ x₃ : H) {c : F}
    (hu : J u = c)
    (h₁ : u ∈ tsupport ψ₁ → x₁ ∈ S₁ ∧ Q₁.starProjection u ∈ ball x₁ (r₁ x₁) ∧
      ∀ i ∈ O₁.I, (closedBall i (80 * ε₁⁻¹ * r₁ i) ∩ ball x₁ (8 * ε₁⁻¹ * r₁ x₁)).Nonempty →
        J i = c ∧ P₁ i ≤ LinearMap.ker (J : H →ₗ[ℝ] F))
    (h₂ : adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y)) ψ₁ u ∈ tsupport ψ₂ →
      x₂ ∈ S₂ ∧ Q₂.starProjection (adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y))
        ψ₁ u) ∈ ball x₂ (r₂ x₂) ∧
      ∀ i ∈ O₂.I, (closedBall i (80 * ε₂⁻¹ * r₂ i) ∩ ball x₂ (8 * ε₂⁻¹ * r₂ x₂)).Nonempty →
        J i = c ∧ P₂ i ≤ LinearMap.ker (J : H →ₗ[ℝ] F))
    (h₃ : adjustmentMap Q₂ (fun y => Q₂.starProjection (O₂.ambient y)) ψ₂
        (adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y)) ψ₁ u) ∈ tsupport ψ₃ →
      x₃ ∈ S₃ ∧ Q₃.starProjection (adjustmentMap Q₂ (fun y => Q₂.starProjection (O₂.ambient y))
        ψ₂ (adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y)) ψ₁ u)) ∈
          ball x₃ (r₃ x₃) ∧
      ∀ i ∈ O₃.I, (closedBall i (80 * ε₃⁻¹ * r₃ i) ∩ ball x₃ (8 * ε₃⁻¹ * r₃ x₃)).Nonempty →
        J i = c ∧ P₃ i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    J (adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y)) ψ₁ u) = c ∧
    J (adjustmentMap Q₂ (fun y => Q₂.starProjection (O₂.ambient y)) ψ₂
      (adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y)) ψ₁ u)) = c ∧
    J (adjustmentMap Q₃ (fun y => Q₃.starProjection (O₃.ambient y)) ψ₃
      (adjustmentMap Q₂ (fun y => Q₂.starProjection (O₂.ambient y)) ψ₂
        (adjustmentMap Q₁ (fun y => Q₁.starProjection (O₁.ambient y)) ψ₁ u))) = c :=
  chain3_level_BLOC Q₁ Q₂ Q₃ J hQ₁ hQ₂ hQ₃ O₁.ambient O₂.ambient O₃.ambient ψ₁ ψ₂ ψ₃ u hu
    (O₁.stage_value_BLOC Q₁ ψ₁ J h₁) (fun _ => O₂.stage_value_BLOC Q₂ ψ₂ J h₂)
    (fun _ => O₃.stage_value_BLOC Q₃ ψ₃ J h₃)

end GC.MetricGeometry
