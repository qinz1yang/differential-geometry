import DifferentialGeometry.Analysis.ParameterSelection.ThreeStageAdjustmentChoiceBelow
import DifferentialGeometry.Geometry.Metric.CloudSmoothingModulusRow
import DifferentialGeometry.Geometry.Collapse.OneSheetBudget
import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacket
import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets

/-!
# GAF01 on the actual constants: one choice for the three adjustments

Blueprint `master207B.tex`, GAF01 (`prop:fibration-actual-adjustment-choices`, B:5704–5795),
bound to the ACTUAL early constants of the closed-carrier construction:

* `gafMultiplicity` `N = ⌊fc07ActiveBound⌋₊` (FC07's pointwise count of active supports, which
  bounds every active-tag count of `𝓔⁰`, `cgp_active_tags_ncard_le_fc07`), the profile bound
  `P = cgpProfileBound` (CGP02's `P₀`), `gafCutoffConstant` `b_cut = 10⁴ (N+1)² P⁴`, `gafKappa`
  `κ = 1/(1000 (N+1) P²)`, `gafDerivativeBound` `L₀ = 1000 (N+2) P₀²` (CGP02's literal constant,
  `cgp02_row`);
* the smoothing moduli `Ξ_j` of CFS15 (`cfs15_modulus_row` at the stage dimension `k_j = 2, 1, 1`,
  jet order `K` and the CFS07 ratio `B = 5/3`), with their thresholds `θ_j` and CFS15's full
  conclusion; they are chosen first (they depend only on `k_j`, `K`, `B`).

`gaf01_row`: such moduli exist, and then for every `c_adjust > 0` and all positive graph moduli
`C_j` (`Ω = max{1, C_j}`) one choice `c_j, Γ_j, Σ_j, e_j` in the retained order with (JA), (JB),
`Γ_j` below CFS15's threshold, CFS31's (MB) order constraints (`c₂ ≤ t₃`, `c₁ ≤ t₂`,
`c_j ≤ 4κ/5`, `c_j ≤ 1/512`), CFS20's three strict budgets with `b = b_cut`, `L = L₀`, `μ = 1/2`,
and CGP07's (OS) and (SN) bounds at every stage.
The ACTUAL cloud clause of GAF01 (the producers TCP05/06, EGP06/07, SGP04–06 deliver clouds with
rough error `e_j` and normal error `≤ e_j < Γ_j`) is not part of this theorem. Strengthenings: any
positive `C_j` (the TCP05 / EGP06 / SGP04 moduli are particular values) and any jet order `K`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter DifferentialGeometry.Analysis GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped BigOperators NNReal ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

section Constants

/-- The stage dimensions `k_j = 2, 1, 1` (circle, edge and slim stages). -/
def gafStageDim : Fin 3 → ℕ := ![2, 1, 1]

/-- GAF01's early multiplicity `N = ⌊fc07ActiveBound⌋₊`. -/
def gafMultiplicity : ℕ := ⌊fc07ActiveBound⌋₊

/-- GAF01's cutoff constant `b_cut = 10⁴ (N+1)² P⁴` (CFS31's derivative constant). -/
def gafCutoffConstant : ℝ := 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4

/-- GAF01's `κ = 1/(1000 (N+1) P²)`. -/
def gafKappa : ℝ := 1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2)

/-- CGP02's early derivative constant `L₀ = 1000 (N+2) P₀²` of the actual `𝓔⁰`. -/
def gafDerivativeBound : ℝ := 1000 * (fc07ActiveBound + 2) * cgpProfileBound ^ 2

theorem one_le_fc07ActiveBound : 1 ≤ fc07ActiveBound := by
  have hv : ∀ r : ℝ, 0 < r → 0 < modelVolume (-(1 ^ 2)) 3 r := fun r hr =>
    modelVolume_pos (by norm_num) hr ⟨hr.le, fun h => absurd h (by norm_num)⟩
  have h1 := div_pos (hv (4 * (10 + 2 * 200 + 1 / 3)) (by norm_num)) (hv (1 / 3) (by norm_num))
  have h2 := div_pos (hv (4 * (10 + 2 * 2000000 + 1 / 3)) (by norm_num)) (hv (1 / 3) (by norm_num))
  have h3 := div_pos (hv (4 * (10 + 2 * 100 + 1 / 3)) (by norm_num)) (hv (1 / 3) (by norm_num))
  rw [fc07ActiveBound]
  linarith

theorem gafCutoffConstant_nonneg : 0 ≤ gafCutoffConstant := by
  rw [gafCutoffConstant]
  positivity

theorem gafKappa_pos : 0 < gafKappa := by
  have hP : 0 < cgpProfileBound := zero_lt_one.trans_le cgpProfileBound_spec.1
  rw [gafKappa]
  positivity

theorem one_le_gafDerivativeBound : 1 ≤ gafDerivativeBound := by
  have hP : 1 ≤ cgpProfileBound := cgpProfileBound_spec.1
  have hN := one_le_fc07ActiveBound
  have hP2 : 1 ≤ cgpProfileBound ^ 2 := one_le_pow₀ hP
  rw [gafDerivativeBound]
  nlinarith

end Constants

section Choice

theorem gaf_cfs15_ratio : (1 : ℝ) ≤ 5 / 3 := by norm_num

/-- **GAF01** (`prop:fibration-actual-adjustment-choices`) on the actual constants. First the
smoothing moduli `Ξ_j` of CFS15 at the stage dimensions `k_j = 2, 1, 1` (thresholds `θ_j`, CFS15's
full conclusion below `θ_j`); then for every `c_adjust > 0` and positive graph moduli `C_j` one
choice in the retained order `c₃ ; Γ₃, Σ₃, e₃ ; c₂ ; … ; c₁ ; …` with (JA), (JB), `Γ_j < θ_j`,
CFS31's (MB) order constraints, CFS20's budgets with `b_cut`, `L₀`, `μ = 1/2`, and CGP07's (OS) and
(SN) at every stage. -/
theorem gaf01_row (K : ℕ) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ),
      (∀ st : Fin 3, 0 < θ st ∧ Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
        ∀ Γ, 0 < Γ → Γ < θ st → (∃ m : ℕ, Ξ st Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
          ((∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
              ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
              δ₀ ≤ (Ξ st Γ) / (3 * finiteCloudJetBudget F C K) ∧ Γ ≤ δ₀ ∧
              ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
                [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
                ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
                (∀ x ∈ S, Module.finrank ℝ (P x) = (gafStageDim st)) →
                ∀ rmin R δ : ℝ, 0 < rmin →
                (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
                0 < δ → δ ≤ δ₀ →
                (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ st Γ)⁻¹ * max (r y) (r x) →
                  r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
                (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
                  ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
                    ENNReal.ofReal (δ * r x)) →
                ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
                  I.PairwiseDisjoint (fun i => ball i (r i)) ∧
                  (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
                  ((⋃ x ∈ S, ball x (8 * (Ξ st Γ)⁻¹ * r x)) ⊆
                    ⋃ i ∈ I, ball i (20 * (Ξ st Γ)⁻¹ * r i)) ∧
                  let w : H → H → ℝ := fun i y =>
                      ballCutoff i (40 * (Ξ st Γ)⁻¹ * r i) (2 * (40 * (Ξ st Γ)⁻¹ * r i)) y /
                      (∑ a ∈ hI.toFinset,
                        ballCutoff a (40 * (Ξ st Γ)⁻¹ * r a) (2 * (40 * (Ξ st Γ)⁻¹ * r a)) y)
                  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                      Module.End.eigenspace
                      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
                  let η : H → H := fun y => (Q y).starProjection
                    (y - ∑ i ∈ hI.toFinset, w i y • i)
                  let U : Set H := ⋃ i ∈ I, ball i (20 * (Ξ st Γ)⁻¹ * r i)
                  let Z : Set H := {z | z ∈ U ∧ η z = 0}
                  (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
                    ∃ cs : ChartedSpace (Fin (gafStageDim st) → ℝ) Z,
                      let _ := cs
                      IsManifold 𝓘(ℝ, Fin (gafStageDim st) → ℝ) ∞ Z ∧
                      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (gafStageDim st) → ℝ) 𝓘(ℝ, H) ∞
                        (Subtype.val : Z → H) ∧
                      let V : S → TopologicalSpace.Opens H :=
                        fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
                      let Ω : TopologicalSpace.Opens H :=
                        ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
                      ∃ p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin (gafStageDim st) → ℝ), Z⟯,
                        _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin (gafStageDim st) → ℝ) ∞ p ∧
                        (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H) ∧
                          (∀ y ∈ Z, IsMinOn (fun w => dist (z : H) w) Z y → y = (p z : H))) ∧
                        (∀ x : S, ∀ z : V x,
                          ‖(p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                            ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ (Ξ st Γ) * r x ∧
                          (let D : H →L[ℝ] H :=
                            mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H))
                              ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
                          ‖D - (P x).starProjection‖ ≤ (Ξ st Γ))) ∧
                        (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                         ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j : ℕ,
                           ‖iteratedFDeriv ℝ j
                             (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                               C j * δ * r x * ((r x)⁻¹) ^ j) ∧
                        (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                         ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j ≤ K,
                           ‖iteratedFDeriv ℝ j
                             (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                               ((Ξ st Γ) / 3) * r x * ((r x)⁻¹) ^ j) ∧
                        (∀ z : Z, ∀ hz : (z : H) ∈ Ω, p ⟨(z : H), hz⟩ = z) ∧
                        (∀ x : S, ∀ z : Z, (z : H) ∈ ball (x : H) (r x) →
                          ‖actualZeroSetNormalProjector (gafStageDim st) Z z -
                            (P x)ᗮ.starProjection‖ ≤ (Ξ st Γ))) ∧
                  (let N : Set H := ⋃ x ∈ S, ball x (r x);
                    IsProperMap (Subtype.val : {z : N | (z : H) ∈ Z} → N)) ∧
                  (Z ⊆ ⋃ q ∈ T, ball q ((Ξ st Γ) * r q)) ∧
                  (∀ x ∈ S,
                    hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 (Ξ st Γ)⁻¹)
                        (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ closedBall 0 (Ξ st Γ)⁻¹) ≤
                        ENNReal.ofReal (7 * (Ξ st Γ) / 16) ∧
                      hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 (Ξ st Γ)⁻¹)
                        (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ ball 0 (Ξ st Γ)⁻¹) ≤
                        ENNReal.ofReal (7 * (Ξ st Γ) / 16)) ∧
                  ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
                    ContDiffOn ℝ ∞ (g x) (ball 0 (4 * (Ξ st Γ)⁻¹ * r x)) ∧
                    (∀ t ∈ ball (0 : P x) (4 * (Ξ st Γ)⁻¹ * r x), ‖g x t‖ ≤ r x / 4 ∧
                      (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
                    (∀ t ∈ ball (0 : P x) (4 * (Ξ st Γ)⁻¹ * r x),
                      ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
                      η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
                    (∀ m t, t ∈ ball (0 : P x) (4 * (Ξ st Γ)⁻¹ * r x) → ∀ j, j ≤ m →
                      ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
                    Z ∩ ball (x : H) (3 * (Ξ st Γ)⁻¹ * r x) =
                      {z : H | ∃ t ∈ ball (0 : P x) (4 * (Ξ st Γ)⁻¹ * r x),
                        z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                          ball (x : H) (3 * (Ξ st Γ)⁻¹ * r x) ∧
                    (∀ t ∈ ball (0 : P x) (4 * (Ξ st Γ)⁻¹ * r x), ∀ j ≤ K + 1,
                      ‖iteratedFDeriv ℝ j (g x) t‖ ≤ ((Ξ st Γ) / 3) * r x * ((r x)⁻¹) ^ j)))) ∧
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
  choose θ hθ Ξ hΞ using fun st : Fin 3 =>
    cfs15_modulus_row.{0} (gafStageDim st) K (5 / 3) gaf_cfs15_ratio
  have hpos : ∀ st Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ := fun st Γ hΓ hθΓ => by
    obtain ⟨m, hm⟩ := ((hΞ st).2 Γ hΓ hθΓ).1
    rw [hm]
    positivity
  refine ⟨θ, Ξ, fun st => ⟨hθ st, hΞ st⟩, fun C hC cadj hcadj => ?_⟩
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

end Choice

end DifferentialGeometry.Geometry.Collapse
