import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2ValidityRows
import DifferentialGeometry.Geometry.Metric.CloudSmoothingModulusRow
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

/-!
# Closed realization, the parts bindable now: constants, member models, orientation (FC39-VAL3)

External review 52, "What can be bound now" and "Order of work" step 3 (closed realization): the
early constants of the register are the ACTUAL constants of the native rows (constant provenance),
and the closed members carry the standing data and the orientation that the final producer
`eventually_nonempty_localChartPacketsC14` requires of its model sequence.

* `closedEarlyDataV3 K`: `N = gafMultiplicity` (GAF01), `P = max{1, P_cgp, P_sgp, P_zero}` (CGP02,
  SGP04/EGP06/TCP05, zero blocks), `C = gafGraphConst` (TCP05, EGP06, SGP04), `L₀ = max{1, L_gaf}`
  (CGP02's derivative bound), `Ξ_j` = CFS15's modulus at `(k_j, K, 5/3)` below CFS15's threshold
  `θ₁` and `1` above it (so that every admissible stage value `Γ_j` lies in CFS15's native range).
* `closedEarlyDataV3_fields_VAL3`: the early fields of `PartialClosedThresholdValidityV2Rows`
  (`N_ge`, `P_ge`, `P_ge_sgp`, `P_ge_zero`, `L₀_ge`, `Ξ_cfs15`, `Ξ_range`, `C_ge`) hold for it.
* `ClosedModel.nonempty_orientation_VAL3`: every normalized member model carries an orientation in
  the model `𝓡 3` (from `W.orientation`, pulled back along `ψ`) — the producer's hypothesis
  `∀ i, ManifoldOrientation (𝓡 3) (X i) 3`.
* `exists_closedModel_sequence_VAL3`: on the closed standing sequence (`closedCollapseHypotheses` at
  the ratios `w_{m+2}`), one model per member with the producer's `hstand` and `hder` at
  `α m = m + 2` (with `A' = boundaryDerivativeConstant A K`) and an orientation.
* Consumer `closedEarlyDataV3_stage_ranges_VAL3`: every stage of `closedEarlyDataV3 K` meets the
  cloud ranges of the three branch ends.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Constant provenance -/

/-- CFS15 (`cfs15_modulus_row`) gives a modulus carrying `Cfs15ModulusOut`. -/
theorem exists_cfs15ModulusOut_VAL3 (k K : ℕ) : ∃ Ξ : ℝ → ℝ, Cfs15ModulusOut k K (5 / 3) Ξ := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_modulus_row k K (5 / 3) (by norm_num)
  exact ⟨Ξ, θ₁, hθ₁, hΞ, h⟩

/-- CFS15's modulus at `(k, K, 5/3)`. -/
def cfs15Modulus_VAL3 (k K : ℕ) : ℝ → ℝ := Classical.choose (exists_cfs15ModulusOut_VAL3 k K)

theorem cfs15Modulus_spec_VAL3 (k K : ℕ) : Cfs15ModulusOut k K (5 / 3) (cfs15Modulus_VAL3 k K) :=
  Classical.choose_spec (exists_cfs15ModulusOut_VAL3 k K)

/-- CFS15's threshold `θ₁` for the chosen modulus. -/
def cfs15Range_VAL3 (k K : ℕ) : ℝ := Classical.choose (cfs15Modulus_spec_VAL3 k K)

theorem cfs15Range_spec_VAL3 (k K : ℕ) : 0 < cfs15Range_VAL3 k K ∧
    Tendsto (cfs15Modulus_VAL3 k K) (𝓝[>] 0) (𝓝 0) ∧
    ∀ Γ, 0 < Γ → Γ < cfs15Range_VAL3 k K →
      Cfs15ModulusAtV2 k K (5 / 3) (cfs15Modulus_VAL3 k K) Γ :=
  Classical.choose_spec (cfs15Modulus_spec_VAL3 k K)

/-- The register's modulus `Ξ_j`: CFS15's modulus below CFS15's threshold, `1` above it. -/
def closedModulusV3 (K : ℕ) (j : Fin 3) (Γ : ℝ) : ℝ :=
  if Γ < cfs15Range_VAL3 (gafStageDim j) K then cfs15Modulus_VAL3 (gafStageDim j) K Γ else 1

/-- CFS15's conclusion at one value depends only on the value of the modulus there. -/
theorem cfs15ModulusAtV2_congr_VAL3 {k K : ℕ} {B Γ : ℝ} {Ξ Ξ' : ℝ → ℝ} (h : Ξ Γ = Ξ' Γ)
    (hΞ : Cfs15ModulusAtV2 k K B Ξ Γ) : Cfs15ModulusAtV2 k K B Ξ' Γ := by
  have e : Cfs15ModulusAtV2 k K B (fun _ => Ξ Γ) Γ := hΞ
  rw [h] at e
  exact e

theorem closedModulusV3_atV2_VAL3 (K : ℕ) (j : Fin 3) {Γ : ℝ} (hΓ : 0 < Γ)
    (hΓ1 : Γ < cfs15Range_VAL3 (gafStageDim j) K) :
    Cfs15ModulusAtV2 (gafStageDim j) K (5 / 3) (closedModulusV3 K j) Γ :=
  cfs15ModulusAtV2_congr_VAL3 (by simp only [closedModulusV3, hΓ1, ↓reduceIte])
    ((cfs15Range_spec_VAL3 _ K).2.2 Γ hΓ hΓ1)

theorem closedModulusV3_pos_VAL3 (K : ℕ) (j : Fin 3) {Γ : ℝ} (hΓ : 0 < Γ) :
    0 < closedModulusV3 K j Γ := by
  by_cases h : Γ < cfs15Range_VAL3 (gafStageDim j) K
  · obtain ⟨m, hm⟩ := (closedModulusV3_atV2_VAL3 K j hΓ h).1
    rw [hm]
    positivity
  · simp only [closedModulusV3, h, ↓reduceIte]
    exact one_pos

theorem closedModulusV3_tendsto_VAL3 (K : ℕ) (j : Fin 3) :
    Tendsto (closedModulusV3 K j) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hθ, hT, -⟩ := cfs15Range_spec_VAL3 (gafStageDim j) K
  refine hT.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hθ)] with Γ hΓ
  have hΓ' : Γ < cfs15Range_VAL3 (gafStageDim j) K := hΓ
  simp only [closedModulusV3, hΓ', ↓reduceIte]

theorem gafGraphConst_pos_VAL3 (j : Fin 3) : 0 < gafGraphConst j := by
  fin_cases j
  · exact zero_lt_one.trans_le one_le_tcpGraphConst
  · exact egpGraphConst_pos_KC4
  · exact (by norm_num : (0 : ℝ) < 4000).trans_le four_le_sgpGraphBound_SGP4

/-- **Constant provenance** (PR01–PR03): the early constants of the closed register are those of
the native rows. -/
def closedEarlyDataV3 (K : ℕ) : ClosedEarlyData where
  N := gafMultiplicity
  P := max 1 (max cgpProfileBound (max sgpProfileBound zeroProfileBound))
  one_le_P := le_max_left _ _
  C := gafGraphConst
  C_pos := gafGraphConst_pos_VAL3
  L₀ := max 1 gafDerivativeBound
  one_le_L₀ := le_max_left _ _
  Ξ := closedModulusV3 K
  Ξ_pos := fun j _ hΓ => closedModulusV3_pos_VAL3 K j hΓ
  Ξ_tendsto := closedModulusV3_tendsto_VAL3 K

/-- Every admissible stage value `Γ_j` of `closedEarlyDataV3 K` lies below CFS15's threshold. -/
theorem ClosedStage.Γ_lt_cfs15Range_VAL3 {K : ℕ} (st : ClosedStage (closedEarlyDataV3 K))
    (j : Fin 3) : st.Γ j < cfs15Range_VAL3 (gafStageDim j) K := by
  by_contra h
  have hlt := st.Ξ_lt j
  have hb : closedAccuracyBound (closedEarlyDataV3 K) (st.c j) ≤ 1 / 10 := min_le_left _ _
  have h1 : (closedEarlyDataV3 K).Ξ j (st.Γ j) = 1 := by
    change closedModulusV3 K j (st.Γ j) = 1
    simp only [closedModulusV3, h, ↓reduceIte]
  rw [h1] at hlt
  linarith

/-- **The early fields hold for the provenance data**: `N_ge`, `P_ge`, `P_ge_sgp`, `P_ge_zero`,
`L₀_ge`, `Ξ_cfs15`, `Ξ_range` (every actual `Γ_j` in CFS15's native range) and `C_ge`. -/
theorem closedEarlyDataV3_fields_VAL3 (K : ℕ) :
    gafMultiplicity ≤ (closedEarlyDataV3 K).N ∧ cgpProfileBound ≤ (closedEarlyDataV3 K).P ∧
      sgpProfileBound ≤ (closedEarlyDataV3 K).P ∧ zeroProfileBound ≤ (closedEarlyDataV3 K).P ∧
      gafDerivativeBound ≤ (closedEarlyDataV3 K).L₀ ∧
      (∀ j, Cfs15ModulusOut (gafStageDim j) K (5 / 3) ((closedEarlyDataV3 K).Ξ j)) ∧
      (∀ (st : ClosedStage (closedEarlyDataV3 K)) j,
        Cfs15ModulusAtV2 (gafStageDim j) K (5 / 3) ((closedEarlyDataV3 K).Ξ j) (st.Γ j)) ∧
      ∀ j, gafGraphConst j ≤ (closedEarlyDataV3 K).C j := by
  refine ⟨le_rfl, (le_max_left _ _).trans (le_max_right _ _),
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _), le_max_right _ _,
    fun j => ?_, fun st j => closedModulusV3_atV2_VAL3 K j (st.Γ_pos j)
      (st.Γ_lt_cfs15Range_VAL3 j), fun j => le_rfl⟩
  obtain ⟨hθ, -, -⟩ := cfs15Range_spec_VAL3 (gafStageDim j) K
  exact ⟨_, hθ, closedModulusV3_tendsto_VAL3 K j,
    fun Γ hΓ hΓ1 => closedModulusV3_atV2_VAL3 K j hΓ hΓ1⟩

/-- **Consumer**: every stage of `closedEarlyDataV3 K` meets the cloud ranges (TP), (EP), (CP) of
TCP06, EGP07 and SGP06 at its own stage values. -/
theorem closedEarlyDataV3_stage_ranges_VAL3 {K : ℕ} (st : ClosedStage (closedEarlyDataV3 K)) :
    (0 < st.Γ 0 ∧ st.Γ 0 < 1 ∧ 0 < st.Sig 0 ∧ st.Sig 0 < st.Γ 0 / 200 ∧
      st.Sig 0 < st.Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ 0 < st.e 0 ∧ st.e 0 < 1 / 100 ∧
      st.e 0 < st.Γ 0 * st.Sig 0 / 100) ∧
    (st.Γ 1 ∈ Ioo (0 : ℝ) 1 ∧ 0 < st.Sig 1 ∧
      st.Sig 1 < min (st.Γ 1 / 200) (st.Γ 1 ^ 3 / (100 * egpGraphConst)) ∧ 0 < st.e 1 ∧
      st.e 1 < min (1 / 100) (min (st.Γ 1 * st.Sig 1 / 100) (st.Sig 1 / 1000))) ∧
    (0 < st.Γ 2 ∧ st.Γ 2 < 1 ∧ 0 < st.Sig 2 ∧ st.Sig 2 < st.Γ 2 / 200 ∧
      st.Sig 2 < st.Γ 2 ^ 3 / (100 * sgpGraphBound) ∧ 0 < st.e 2 ∧ st.e 2 < 1 / 100 ∧
      st.e 2 < st.Γ 2 * st.Sig 2 / 100) :=
  ⟨st.tcp06_range_VAL3 (fun _ => le_rfl), st.egp07_range_VAL3 (fun _ => le_rfl),
    st.sgp06_range_VAL3 (fun _ => le_rfl)⟩

/-! ### Member models: orientation and standing data -/

/-- **The normalized model of a closed member is oriented** in the model `𝓡 3`: the member's
orientation `W.orientation`, pulled back along the diffeomorphism `ψ`. -/
theorem ClosedModel.nonempty_orientation_VAL3 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) :
    Nonempty (ManifoldOrientation (𝓡 3) M.X 3) := by
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  let o₁ : ManifoldOrientation W.model W.Carrier (Module.finrank ℝ E3) :=
    OrientationAssembly.reindexManifoldOrientation W.model (finCongr hdim.symm) W.orientation
  let so := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation
    W.model o₁
  let so' := DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation (𝓡 3) W.model M.ψ
    M.ψ.contMDiff (fun x => (M.ψ.mfderivToContinuousLinearEquiv (by simp) x).bijective) so
  obtain ⟨O, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) so'
  exact ⟨OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr hdim) O⟩

/-- **The closed member sequence meets the final producer's sequence hypotheses**: on the closed
standing sequence there is one normalized model per member with LPA01's `hstand` and `hder` at
`α m = m + 2` (constant `A' = boundaryDerivativeConstant A K`) and an orientation in `𝓡 3`. -/
theorem exists_closedModel_sequence_VAL3 (K : ℕ) (A : ℝ → ℝ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ M : ∀ m, ClosedModel (Wseq m) (gseq m),
      (∀ m (p : (M m).X), ENNReal.ofReal (((m : ℝ) + 2) *
          firstVolumeScale (M m).gX p ((m : ℝ) + 2)⁻¹) ≤ curvatureRadius (M m).gX p) ∧
      (∀ m (p : (M m).X) v, 0 < v → v < 4 * Real.pi / 3 → ((m : ℝ) + 2)⁻¹ ≤ v →
        ∀ C, 0 < C → C < (m : ℝ) + 2 → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (M m).gX p (C * firstVolumeScale (M m).gX p v),
          curvatureDerivativeNorm (M m).gX k y ≤
            boundaryDerivativeConstant A K C v * (firstVolumeScale (M m).gX p v ^ (k + 2))⁻¹) ∧
      ∀ m, Nonempty (ManifoldOrientation (𝓡 3) (M m).X 3) := by
  let M : ∀ m, ClosedModel (Wseq m) (gseq m) := fun m =>
    Classical.choice (nonempty_closedModel_VAL (Wseq m) (gseq m) (hf m))
  refine ⟨M, fun m p => ?_, fun m p v hv hvc hvH C hC hCH k hk y hy => ?_,
    fun m => (M m).nonempty_orientation_VAL3⟩
  · have h := (closed_standing_clauses_VAL K A Wseq gseq hg m ((M m).ψ p)).1
    rwa [← (M m).firstVolumeScale_eq, ← (M m).curvatureRadius_eq] at h
  · have h := (closed_standing_clauses_VAL K A Wseq gseq hg m ((M m).ψ p)).2 v hv hvc hvH C hC
      hCH k hk ((M m).ψ y)
    rw [(M m).ball_eq_preimage, (M m).firstVolumeScale_eq] at hy
    rw [(M m).curvatureDerivativeNorm_eq, (M m).firstVolumeScale_eq]
    exact h hy

end DifferentialGeometry.Geometry.Collapse
