import DifferentialGeometry.Geometry.Fibration.ActualStageMeanShared

/-!
# GAF01's stage nearest maps on the shared modulus (one `Ξ` for GAF02 and FC39's register)

`gaf01_row_nearest_mean_abstract_GAFS4` with its moduli chosen from `cfs15_shared_modulus_GAFS4`
at the stage dimension `k_st` and a jet order `K`: the stage clause additionally carries
`Cfs15ModulusAtV2 (gafStageDim st) K (5 / 3) (Ξ st) Γ` (FC39's field `Ξ_range` form); every other
conjunct verbatim, same proof.

* `gaf01_row_nearest_shared_abstract_GAFS4 K`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **GAF01 on the shared modulus.** For the jet order `K`, moduli `θ, Ξ` such that for every
stage `st` and quality `0 < Γ < θ_st` (`0 < Ξ_st(Γ) ≤ 1`, CFS15's full conclusion
`Cfs15ModulusAtV2 k_st K (5/3) Ξ_st Γ` and CFS12's interior condition
`Γ((80B + 31)Ξ_st(Γ)⁻¹ + 2) < 1`) there is `c_w ≥ 0` with: every
cloud `S ⊆ T` with CFS15's hypotheses at quality `Γ` (buffer `128Ξ⁻¹`, ratio `5/3`, planes of
dimension `k_st`) has a map `a` with every conclusion of `gaf01_row_nearest_abstract_GAF3` and
(SMV); and GAF01's choice clause verbatim (`b_cut`, `κ`, `L₀` of `gaf01_row`). -/
theorem gaf01_row_nearest_shared_abstract_GAFS4 (K : ℕ) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ),
      (∀ st : Fin 3, 0 < θ st ∧ Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
        ∀ Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ ∧ Ξ st Γ ≤ 1 ∧
          Cfs15ModulusAtV2 (gafStageDim st) K (5 / 3) (Ξ st) Γ ∧
          Γ * ((80 * (5 / 3) + 31) * (Ξ st Γ)⁻¹ + 2) < 1 ∧ ∃ cw : ℝ, 0 ≤ cw ∧
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
            (S T : Set H), S ⊆ T → TotallyBounded S →
            ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
            (∀ x ∈ S, Module.finrank ℝ (P x) = gafStageDim st) →
            ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
            (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ st Γ)⁻¹ * max (r y) (r x) →
              r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
            (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / Γ))
              ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / Γ)) ≤
                ENNReal.ofReal (Γ * r x)) →
            ∃ a : H → H, ContDiffOn ℝ ∞ a (⋃ x ∈ S, ball x (r x)) ∧
              ∀ x ∈ S, ∀ z ∈ ball x (r x),
                ‖a z - (x + (P x).starProjection (z - x))‖ ≤ Ξ st Γ * r x ∧
                DifferentiableAt ℝ a z ∧
                ‖fderiv ℝ a z - (P x).starProjection‖ ≤ Ξ st Γ ∧
                (∀ (Kk : Submodule ℝ H) (c : H),
                  (∀ i ∈ S, (closedBall i (80 * (Ξ st Γ)⁻¹ * r i) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * r x)).Nonempty →
                    Kk.starProjection i = c ∧ P i ≤ Kkᗮ) →
                  Kk.starProjection (a z) = c) ∧
                ∀ ℓ : H →L[ℝ] ℝ,
                  (∀ i ∈ S, (closedBall i (80 * (Ξ st Γ)⁻¹ * r i) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * r x)).Nonempty →
                    P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) →
                  ∀ R₀ β : ℝ,
                  (∀ i ∈ S, (closedBall i (80 * (Ξ st Γ)⁻¹ * r i) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * r x)).Nonempty → |ℓ i - R₀| ≤ β) →
                  |ℓ (a z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / r x) ∧
      ∀ (C : Fin 3 → ℝ), (∀ j, 0 < C j) → ∀ cadj : ℝ, 0 < cadj →
      ∃ c Γ S e : Fin 3 → ℝ,
        let Ω : ℝ := max 1 (max (C 0) (max (C 1) (C 2)))
        let α : Fin 3 → ℝ := fun j =>
          min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
            ((1 / 2) / (8 * (1 + gafDerivativeBound)))
        let t : Fin 3 → ℝ := fun j => min (3 * S j / 10) (min (α j) 1)
        (c 2 < cadj ∧ c 2 < 1 / 1000 ∧ c 2 < 1 / 512) ∧
        (c 1 ≤ c 2 ∧ c 1 ≤ t 2 ∧ c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 1 / 1000 ∧ c 1 ≤ 1 / 512) ∧
        (c 0 ≤ c 1 ∧ c 0 ≤ t 1 ∧ c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 1 / 1000 ∧ c 0 ≤ 1 / 512) ∧
        ∀ j, (Γ j < θ j ∧ 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) < 1 / 10 ∧
            Ξ j (Γ j) < α j ∧ Ξ j (Γ j) < 1 / (1000 * (Ω + 1)) ∧
            0 < S j ∧ S j < 1 / 2 ∧ S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧
            S j < Γ j ^ 3 / (100 * C j) ∧
            0 < e j ∧ e j < 1 / 100 ∧ e j < Γ j * S j / 100 ∧ e j < S j / 1000 ∧
            2 * e j < 1 / (48 * Ω)) ∧
          (∀ E H ν σ : ℝ, 0 ≤ E → E ≤ t j → 0 ≤ H → H ≤ t j → ν ≤ Γ j → σ ≤ 1 / 2 →
            let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
            E + a < c j ∧ a * gafCutoffConstant * (gafDerivativeBound + H) +
                Ξ j (Γ j) * (gafDerivativeBound + H) + ν + 2 * H < c j ∧
              Ξ j (Γ j) * (gafDerivativeBound + H) + H < 1 / 2) ∧
          (∀ ν : ℝ, ν ≤ e j → ν + e j ≤ 1 / (48 * Ω)) ∧
          (∀ R rx : ℝ, 0 < R → 9 / 20 * S j * R ≤ rx →
            (2 * e j + 25 / 12 * (1 + Ω) * Ξ j (Γ j) * S j) * R < S j * R / 100 ∧
              S j * R / 100 < rx / 4 ∧ Ξ j (Γ j) < 1 / (2 * Ω)) := by
  choose θ hθ Ξ hΞ using fun st : Fin 3 => cfs15_shared_modulus_GAFS4 (gafStageDim st) K
  have hpos : ∀ st Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ := fun st Γ hΓ hθΓ => by
    obtain ⟨m, hm⟩ := ((hΞ st).2 Γ hΓ hθΓ).1
    rw [hm]
    positivity
  have hle : ∀ st Γ, 0 < Γ → Γ < θ st → Ξ st Γ ≤ 1 := fun st Γ hΓ hθΓ => by
    obtain ⟨m, hm⟩ := ((hΞ st).2 Γ hΓ hθΓ).1
    rw [hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨θ, Ξ, fun st => ⟨hθ st, (hΞ st).1, fun Γ hΓ hθΓ =>
    ⟨hpos st Γ hΓ hθΓ, hle st Γ hΓ hθΓ, ((hΞ st).2 Γ hΓ hθΓ).2⟩⟩, fun C hC cadj hcadj => ?_⟩
  have hΩ : (1 : ℝ) ≤ max 1 (max (C 0) (max (C 1) (C 2))) := le_max_left _ _
  obtain ⟨c, Γ, S, e, h⟩ := exists_three_stage_adjustment_choice_below Ξ θ hθ hpos
    (fun st => (hΞ st).1) C hcadj gafCutoffConstant_nonneg gafKappa_pos
    (zero_le_one.trans one_le_gafDerivativeBound) hΩ hC
  obtain ⟨h2, h1, h0, hstage⟩ := h
  refine ⟨c, Γ, S, e, h2, h1, h0, fun j => ?_⟩
  obtain ⟨hfacts, hbud⟩ := hstage j
  obtain ⟨hθj, -, -, hΓ, -, -, -, hΞΩ, hS, -, -, -, -, -, -, -, he, h2e⟩ := id hfacts
  refine ⟨hfacts, hbud, fun ν hν => by linarith, fun R rx hR hrx => ?_⟩
  exact one_sheet_proximity_budget hΩ hS hR he.le (hpos j (Γ j) hΓ hθj).le hΞΩ.le hrx

end DifferentialGeometry.Geometry.Collapse
