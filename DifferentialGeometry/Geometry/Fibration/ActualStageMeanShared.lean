import DifferentialGeometry.Geometry.Fibration.ActualStageMeanInterior
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2Validity

/-!
# One modulus for GAF02 and FC39's register: CFS15 at jet order `K` + interior condition + mean

FC39's register requires of its modulus `D.Ξ j` CFS15's full conclusion at jet order `K`
(`Cfs15ModulusOut` / `Cfs15ModulusAtV2`, the fields `Ξ_cfs15`, `Ξ_range`), while GAF02's stage maps
need CFS15's modulus at jet order `0` with EDP01's weighted mean and CFS12's interior condition
(`cfs15_mean_modulus_GAFS4`). Both are threshold moduli over the same kernel
`exists_uniform_large_cloud_nearest_blueprint_budget`, so one modulus carries both: the threshold
predicate is the conjunction, the threshold the minimum.

* `cfs15_shared_modulus_GAFS4 k K`: `θ₁, Ξ` with, for `0 < Γ < θ₁`,
  `Cfs15ModulusAtV2 k K (5/3) Ξ Γ`, the interior condition and every conclusion of
  `cfs15_mean_modulus_GAFS4` (verbatim).
* `cfs15_shared_modulus_out_GAFS4 k K`: consumer — the same `Ξ` satisfies the register's
  `Cfs15ModulusOut (k) K (5/3) Ξ` (the field `Ξ_cfs15`) and the conclusion of
  `cfs15_mean_modulus_GAFS4`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **The shared stage modulus (CFS15 at jet order `K`, interior condition, EDP01's mean).** For the
stage dimension `k`, jet order `K` and ratio `B = 5/3` there are `θ₁ > 0` and `Ξ → 0` such that
for `0 < Γ < θ₁`: CFS15's full conclusion `Cfs15ModulusAtV2 k K (5/3) Ξ Γ` (the register's `Ξ_range`
form of `cfs15_modulus_row`), CFS12's interior condition `Γ((80B + 31)Ξ(Γ)⁻¹ + 2) < 1`, and every
conclusion of `cfs15_mean_modulus_GAFS4` (a constant `c_w ≥ 0`, the stage nearest map with value,
derivative, GAF03's locality and (SMV)) for the same `Ξ`. -/
theorem cfs15_shared_modulus_GAFS4 (k K : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
        Cfs15ModulusAtV2 k K (5 / 3) Ξ Γ ∧
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
    (P := fun ε Γ => Cfs15ModulusAtV2 k K (5 / 3) (fun _ => ε) Γ ∧
        Γ * ((80 * (5 / 3) + 31) * ε⁻¹ + 2) < 1 ∧ ∃ cw : ℝ, 0 ≤ cw ∧
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
  obtain ⟨FK, hFK, CK, hCK, δK, hδK, hδKle, hrestK⟩ :=
    exists_uniform_large_cloud_nearest_blueprint_budget.{0} k K (5 / 3) ((1 / 2 : ℝ) ^ (m + 4))
      (by norm_num) hε hε1
  have hK : ∀ Γ, Γ ≤ δK →
      Cfs15ModulusAtV2 k K (5 / 3) (fun _ => (1 / 2 : ℝ) ^ (m + 4)) Γ := fun Γ hΓ => by
    unfold Cfs15ModulusAtV2
    exact ⟨⟨m, rfl⟩, FK, hFK, CK, hCK, δK, hδK, hδKle, hΓ, hrestK⟩
  set ε : ℝ := (1 / 2 : ℝ) ^ (m + 4) with hεdef
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr (by linarith)
  obtain ⟨F, -, C, -, δ₀, hδ₀, -, hrest⟩ :=
    exists_uniform_large_cloud_nearest_blueprint_budget.{0} k 0 (5 / 3) ε (by norm_num) hε hε1
  obtain ⟨cw, hcw, hwb⟩ := exists_selection_weight_deriv_bound_GAFS2.{0} k ε⁻¹ (5 / 3) hinv
    (by norm_num)
  set A : ℝ := (80 * (5 / 3 : ℝ) + 31) * ε⁻¹ + 2 with hA
  have hApos : 0 < A := by positivity
  refine ⟨min δK (min δ₀ (1 / (2 * A))), lt_min hδK (lt_min hδ₀ (by positivity)),
    fun Γ hΓ hΓdd => ?_⟩
  have hΓd : Γ ≤ min δ₀ (1 / (2 * A)) := hΓdd.trans (min_le_right _ _)
  have hΓA : Γ * A < 1 := by
    have hs : Γ ≤ 1 / (2 * A) := hΓd.trans (min_le_right _ _)
    have hm : Γ * (2 * A) ≤ 1 := (le_div_iff₀ (by positivity)).mp hs
    nlinarith
  refine ⟨hK Γ (hΓdd.trans (min_le_left _ _)), hΓA, cw, hcw, ?_⟩
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

/-- **The shared modulus fills FC39's `Ξ` fields.** The modulus of `cfs15_shared_modulus_GAFS4 k K`
satisfies the register's field type `Cfs15ModulusOut k K (5/3) Ξ` (`Ξ_cfs15`), and on its range
`(0, θ₁)` both `Cfs15ModulusAtV2 k K (5/3) Ξ Γ` (`Ξ_range`) and CFS12's interior condition at the
buffer `Ξ(Γ)⁻¹`. -/
theorem cfs15_shared_modulus_out_GAFS4 (k K : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Cfs15ModulusOut k K (5 / 3) Ξ ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → Cfs15ModulusAtV2 k K (5 / 3) Ξ Γ ∧
        Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1 := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_shared_modulus_GAFS4 k K
  have hout : Cfs15ModulusOut k K (5 / 3) Ξ := by
    unfold Cfs15ModulusOut
    exact ⟨θ₁, hθ₁, hΞ, fun Γ hΓ hθΓ => (h Γ hΓ hθΓ).2.1⟩
  exact ⟨θ₁, hθ₁, Ξ, hout, fun Γ hΓ hθΓ => ⟨(h Γ hΓ hθΓ).2.1, (h Γ hΓ hθΓ).2.2.1⟩⟩

end DifferentialGeometry.Geometry.Collapse
