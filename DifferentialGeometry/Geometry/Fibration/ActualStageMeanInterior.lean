import DifferentialGeometry.Geometry.Fibration.ActualStageNearest
import DifferentialGeometry.Geometry.Metric.LargeCloudStageMean
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestBindings

/-!
# CFS15's mean modulus with CFS12's interior condition exported (one shared modulus)

`cfs15_mean_modulus_GAFS2` proves, inside its proof, that its quality `Γ` and accuracy `Ξ(Γ)`
satisfy CFS12's interior condition `Γ((80B + 31)Ξ(Γ)⁻¹ + 2) < 1` (`B = 5/3`, threshold
`min δ₀ (1/(2A))`), but does not state it. This file re-states the modulus and GAF01's abstract
row with this conjunct exported (same proofs; every other conjunct verbatim), so that GAF02 (which
smooths at the buffer `b = Ξ(Γ)⁻¹`) and FC39's register use ONE modulus, and
`nb_cw_stage_selection_GAFS3` applies at `b = Ξ(Γ)⁻¹` with no further hypothesis.

* `cfs15_mean_modulus_GAFS4`: `cfs15_mean_modulus_GAFS2` + the conjunct
  `Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1` for `0 < Γ < θ₁`.
* `gaf01_row_nearest_mean_abstract_GAFS4`: `gaf01_row_nearest_mean_abstract_GAFS2` + the conjunct
  `Γ * ((80 * (5 / 3) + 31) * (Ξ st Γ)⁻¹ + 2) < 1` at every stage `st` and `0 < Γ < θ_st`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **CFS15's modulus with EDP01's weighted mean and CFS12's interior condition.** For the stage
dimension `k` (ratio `B = 5/3`) there are `θ₁ > 0` and `Ξ(Γ) = (1/2)^(m+4) → 0` such that for
`0 < Γ < θ₁`: CFS12's interior condition `Γ((80B + 31)Ξ(Γ)⁻¹ + 2) < 1` holds, and there is
`c_w ≥ 0` with: every cloud `S ⊆ T` of quality `Γ` with CFS15's hypotheses at the buffer
`128Ξ⁻¹` has a map `a`, smooth on `⋃_{x ∈ S} B(x, r_x)`, with CFS14 (3)'s value and derivative
bounds at accuracy `Ξ`, GAF03's locality, and (SMV) with this `c_w` on every `B(x, r_x)`. -/
theorem cfs15_mean_modulus_GAFS4 (k : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
        Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1 ∧
        ∃ cw : ℝ, 0 ≤ cw ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
          (S T : Set H), S ⊆ T → TotallyBounded S →
          ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
          (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
          ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
          (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ Γ)⁻¹ * max (r y) (r x) →
            r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
          (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / Γ))
            ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / Γ)) ≤
              ENNReal.ofReal (Γ * r x)) →
          ∃ a : H → H, ContDiffOn ℝ ∞ a (⋃ x ∈ S, ball x (r x)) ∧
            ∀ x ∈ S, ∀ z ∈ ball x (r x),
              ‖a z - (x + (P x).starProjection (z - x))‖ ≤ Ξ Γ * r x ∧
              DifferentiableAt ℝ a z ∧
              ‖fderiv ℝ a z - (P x).starProjection‖ ≤ Ξ Γ ∧
              (∀ (Kk : Submodule ℝ H) (c : H),
                (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                    ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty →
                  Kk.starProjection i = c ∧ P i ≤ Kkᗮ) →
                Kk.starProjection (a z) = c) ∧
              ∀ ℓ : H →L[ℝ] ℝ,
                (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                    ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty →
                  P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) →
                ∀ R₀ β : ℝ,
                (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                    ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty → |ℓ i - R₀| ≤ β) →
                |ℓ (a z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / r x := by
  refine ParameterSelection.exists_modulus_of_thresholds
    (P := fun ε Γ => Γ * ((80 * (5 / 3) + 31) * ε⁻¹ + 2) < 1 ∧ ∃ cw : ℝ, 0 ≤ cw ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
          (S T : Set H), S ⊆ T → TotallyBounded S →
          ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
          (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
          ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
          (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * ε⁻¹ * max (r y) (r x) →
            r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
          (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / Γ))
            ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / Γ)) ≤
              ENNReal.ofReal (Γ * r x)) →
          ∃ a : H → H, ContDiffOn ℝ ∞ a (⋃ x ∈ S, ball x (r x)) ∧
            ∀ x ∈ S, ∀ z ∈ ball x (r x),
              ‖a z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
              DifferentiableAt ℝ a z ∧
              ‖fderiv ℝ a z - (P x).starProjection‖ ≤ ε ∧
              (∀ (Kk : Submodule ℝ H) (c : H),
                (∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩
                    ball x (8 * ε⁻¹ * r x)).Nonempty →
                  Kk.starProjection i = c ∧ P i ≤ Kkᗮ) →
                Kk.starProjection (a z) = c) ∧
              ∀ ℓ : H →L[ℝ] ℝ,
                (∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩
                    ball x (8 * ε⁻¹ * r x)).Nonempty →
                  P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) →
                ∀ R₀ β : ℝ,
                (∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩
                    ball x (8 * ε⁻¹ * r x)).Nonempty → |ℓ i - R₀| ≤ β) →
                |ℓ (a z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / r x)
    (fun m => ?_)
  have hε : (0 : ℝ) < (1 / 2 : ℝ) ^ (m + 4) := by positivity
  have hε1 : (1 / 2 : ℝ) ^ (m + 4) ≤ 1 / 10 := by
    calc (1 / 2 : ℝ) ^ (m + 4) ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 10 := by norm_num
  set ε : ℝ := (1 / 2 : ℝ) ^ (m + 4) with hεdef
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr (by linarith)
  obtain ⟨F, -, C, -, δ₀, hδ₀, -, hrest⟩ :=
    exists_uniform_large_cloud_nearest_blueprint_budget.{0} k 0 (5 / 3) ε (by norm_num) hε hε1
  obtain ⟨cw, hcw, hwb⟩ := exists_selection_weight_deriv_bound_GAFS2.{0} k ε⁻¹ (5 / 3) hinv
    (by norm_num)
  set A : ℝ := (80 * (5 / 3 : ℝ) + 31) * ε⁻¹ + 2 with hA
  have hApos : 0 < A := by positivity
  refine ⟨min δ₀ (1 / (2 * A)), lt_min hδ₀ (by positivity), fun Γ hΓ hΓd => ?_⟩
  have hΓA : Γ * A < 1 := by
    have hs : Γ ≤ 1 / (2 * A) := hΓd.trans (min_le_right _ _)
    have hm : Γ * (2 * A) ≤ 1 := (le_div_iff₀ (by positivity)).mp hs
    nlinarith
  refine ⟨hΓA, cw, hcw, ?_⟩
  intro H _ _ _ S T hST htb r P hdim rmin R hrmin hlo hhi hmcb hcloud
  have hr : ∀ x ∈ S, 0 < r x := fun x hx => hrmin.trans_le (hlo x hx)
  have happ := hrest H S T hST htb r P hdim rmin R Γ hrmin hlo hhi hΓ
    (hΓd.trans (min_le_left _ _)) hmcb hcloud
  obtain ⟨I, hI, hIS, hdisj, -, htube, hrest'⟩ := happ
  obtain ⟨⟨-, cs, hcs⟩, -⟩ := hrest'
  obtain ⟨-, hemb, p, -, -, hval, -⟩ := hcs
  obtain ⟨a, hext, hcd, hfd⟩ := exists_nearestAmbientExtension_GAF3 _ p hemb
  have hΩ : ∀ x ∈ S, ∀ z ∈ ball x (r x), z ∈ ⋃ x : ↥S, ball (x : H) (r x) :=
    fun x hx z hz => mem_iUnion.mpr ⟨⟨x, hx⟩, hz⟩
  have hwb' := hwb H S T hST r P hdim hr Γ hΓ hΓA
    (fun x hx y hy hd => hmcb x (hST hx) y (hST hy) hd) hcloud I hI hIS hdisj htube
  have hval' : ∀ x ∈ S, ∀ z ∈ ball x (r x),
      ‖a z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
      DifferentiableAt ℝ a z ∧ ‖fderiv ℝ a z - (P x).starProjection‖ ≤ ε := by
    intro x hx z hz
    have hzΩ := hΩ x hx z hz
    have hvx := hval ⟨x, hx⟩ ⟨z, hz⟩
    have haz := hext z hzΩ
    exact ⟨haz ▸ hvx.1, (hcd z hzΩ).differentiableAt (by simp), (hfd z hzΩ) ▸ hvx.2⟩
  have hmean := nearest_mean_of_zero_set_GAFS2 S r P I hI hIS hr hε (by linarith) htube _ rfl
    hwb' a hval' (fun x hx z hz => (hext z (hΩ x hx z hz)) ▸ (p ⟨z, hΩ x hx z hz⟩).2.2)
  refine ⟨a, ?_, fun x hx z hz => ⟨(hval' x hx z hz).1, (hval' x hx z hz).2.1,
    (hval' x hx z hz).2.2, hmean x hx z hz⟩⟩
  intro y hy
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
  exact (hcd y (hΩ x hx y hyx)).contDiffWithinAt

/-- **GAF01 with stage nearest maps carrying EDP01's weighted mean, interior condition exported.**
Moduli `θ, Ξ` such that for every stage `st` and quality `0 < Γ < θ_st` (`0 < Ξ_st(Γ) ≤ 1` and
CFS12's interior condition `Γ((80B + 31)Ξ_st(Γ)⁻¹ + 2) < 1`) there is `c_w ≥ 0` with: every
cloud `S ⊆ T` with CFS15's hypotheses at quality `Γ` (buffer `128Ξ⁻¹`, ratio `5/3`, planes of
dimension `k_st`) has a map `a` with every conclusion of `gaf01_row_nearest_abstract_GAF3` and
(SMV); and GAF01's choice clause verbatim (`b_cut`, `κ`, `L₀` of `gaf01_row`). -/
theorem gaf01_row_nearest_mean_abstract_GAFS4 :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ),
      (∀ st : Fin 3, 0 < θ st ∧ Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
        ∀ Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ ∧ Ξ st Γ ≤ 1 ∧
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
  choose θ hθ Ξ hΞ using fun st : Fin 3 => cfs15_mean_modulus_GAFS4 (gafStageDim st)
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
