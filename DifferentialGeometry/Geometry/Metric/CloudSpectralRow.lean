import DifferentialGeometry.Geometry.Metric.CloudSpectralOrthogonalSpan
import DifferentialGeometry.Geometry.Metric.CloudDisplacementJets

/-!
# CFS04 complete: (SE), (DE) and the span clause for the same selection

Blueprint `master207B.tex`, CFS04 (`lem:fibration-cloud-neighborhood-spectral`, lines 1922–1965).
`cfs04_row` is the existing kernel `exists_uniform_cloud_displacement_jets` (weights, spectral
projector `Q`, displacement `η = Q(z)(z − μ(z))` with their (SE) and (DE) jet bounds on every CFS02
neighbourhood `B(v, λ r₀)`) together with the last display of the row for the SAME selection,
weights and projector: with `V = span{x_i − x₀, L_{x_i} : i ∈ J}`, `Q|_{V⊥} = I` and
`proj_{V⊥} η(z) = proj_{V⊥}(z − x₀)` (`cfs04_orthogonal_span_clause`). The bound
`dim V ≤ N(k + 1)` of the row is not restated (it is the count `|J| ≤ N` of CFS02 times `k + 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff

namespace GC.MetricGeometry

universe u

/-- CFS04 (`lem:fibration-cloud-neighborhood-spectral`), all clauses for one selection. -/
theorem cfs04_row
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B E : ℕ → ℝ≥0,
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))) →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          (∀ m : ℕ, ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            ∀ j ≤ m, ∀ z ∈ ball v (ℓ * r x₀),
              (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j
                (fun y => ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
                  (∑ a ∈ hI.toFinset,
                    ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)) z‖) ≤
                      (B m : ℝ) / (r x₀) ^ j) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω ∧
          (∀ z ∈ Ω, Module.finrank ℝ (Q z) = Module.finrank ℝ H - k) ∧
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)) Ω ∧
          ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball v (ℓ * r x₀)) ∧
            (∀ z ∈ ball v (ℓ * r x₀),
              Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
              ‖(Q z).starProjection - (P x₀)ᗮ.starProjection‖ ≤
                24 * (2 * (C + 1) + 1) * δ) ∧
            (∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball v (ℓ * r x₀),
              (‖iteratedFDeriv ℝ j (fun y =>
                (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                  Module.End.eigenspace
                    (∑ i ∈ hI.toFinset,
                      w i y • (P i)ᗮ.starProjection).toLinearMap μ).starProjection -
                    (P x₀)ᗮ.starProjection) z‖ ≤
                max 4 ((resolventDerivativeBound 4 (B m) j : ℝ) / 2) *
                  (6 * (2 * (C + 1) + 1)) * δ / (r x₀) ^ j) ∧
              ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection
                (y - ∑ i ∈ hI.toFinset, w i y • i) -
                  (P x₀)ᗮ.starProjection (y - x₀)) z‖ ≤
                    (E m : ℝ) * δ * r x₀ * ((r x₀)⁻¹) ^ j) ∧
            (let V : Submodule ℝ H := ⨆ (i ∈ hI.toFinset) (_ : (closedBall i (20 * ℓ * r i) ∩
                ball v (ℓ * r x₀)).Nonempty), (ℝ ∙ (i - x₀)) ⊔ P i
              ∀ z ∈ ball v (ℓ * r x₀), (∀ y ∈ Vᗮ, (Q z).starProjection y = y) ∧
                Vᗮ.starProjection ((Q z).starProjection (z - ∑ i ∈ hI.toFinset, w i z • i)) =
                  Vᗮ.starProjection (z - x₀)) := by
  obtain ⟨B, E, hker⟩ := exists_uniform_cloud_displacement_jets.{u} k C hC
  refine ⟨B, E, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδs hscale hcloud ℓ
  obtain ⟨I, hI, hIS, hdisj, hcov, hwts, hrest⟩ :=
    hker H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδs hscale hcloud
  refine ⟨I, hI, hIS, hdisj, hcov, hwts, ?_⟩
  intro w Q Ω
  obtain ⟨h1, h2, h3, h4⟩ := hrest
  refine ⟨h1, h2, h3, fun x₀ hx₀ v hv => ⟨(h4 x₀ hx₀ v hv).1, (h4 x₀ hx₀ v hv).2.1,
    (h4 x₀ hx₀ v hv).2.2, ?_⟩⟩
  have hℓ : (0 : ℝ) < ℓ := by positivity
  exact cfs04_orthogonal_span_clause hI.toFinset r
    (fun i hi => hrmin.trans_le (hlower i (hIS (hI.mem_toFinset.mp hi)))) P hℓ
    (hI.mem_toFinset.mpr hx₀) hv

end GC.MetricGeometry
