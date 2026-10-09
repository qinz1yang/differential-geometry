import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4NbCw
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCollarCircleApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14StagedSTG

/-!
# Register V4 and the staged collar request: EDP06's collar → circle step at every register
(lane FC39-VAL6)

Lane C14-STG added the clause `3βc ≤ β 2` to the staged contract
(`exists_c14d_staged_assignment_STG`) for lane C14-EDP6's collar → circle step
(`edp06_collar_circle_C14`). Register V4 (`StaticRegisterV4.lean`: `βc` chosen right after `β₂`)
carries the same clause at EVERY register (`ClosedRegisterV4.three_mul_βc_le_β_two_VAL6`). This file
discharges EDP06's step on the register's own final family:

* `ClosedRegisterV4.edp06_side_VAL6`: EDP06's numerical side conditions at every register V4:
  `3βc ≤ β 2`, `β 2 < 1`, `0 ≤ γ`, `1 ≤ Δ`;
* `ClosedFamilyInstanceV4.no_three_VAL6`: on an instance carrying LC18's exclusion
  (`Lc18ExclusionOutV4`, part of the validity record's family package), the row's no-three input
  holds at EVERY point at the instance's scale (the scale lies in LPA01's window);
* `ClosedFamilyInstanceV4.edp06_collar_circle_VAL6`: EDP06's conclusion on the instance's family at
  the register's values (kernel `edp06_collar_circle_C14`, with no hypothesis beyond the band);
* `PartialClosedThresholdValidityV4.edp06_on_tail_VAL6`: from the validity record, at every
  register, every member of the register's tail carries an instance on which EDP06's step holds;
* `exists_partialClosedThresholdValidityV4Rows_edp06_VAL6`: at `earlyDataSharedV4 K` on every closed
  standing sequence, ONE strategy with the whole partial record, PR10's `N_b, c_w`, and EDP06's
  step on the tail of every register.

Two of the staged requests lane C14-STG lists as missing records are met on register V4 by a
strategy cap (no new slot):

* TCP04's `β₂ < γc/1000` (B:5483): `ClosedThresholdsV4.withCollarβ₂_VAL6` (`β₂`'s slot reads `γc`
  in the circle prefix), `ClosedRegisterV4.β₂_lt_γc_of_below_VAL6`;
* the boundary route's `v_s < ϑ₃/4` (BCG02 / R17; `ϑ₃ = ϑ 2`, the register's `v_s` is the error
  `ve`): `BoundaryThresholdsV4.withVsCap_VAL6`, `BoundaryRegisterV4.ve_lt_ϑ_VAL6`.

The third (the Δ-stage short-buffer radii of TCP01–TCP04, FC22, LFR35–LFR38) has its slot `ΔLow`
but no supplier, as in the staged contract.

**What the register does NOT give** (recorded, not assumed; compiled as
`ClosedRegisterV4.β_ne_c14PreFinal_VAL6`): `exists_c14d_staged_assignment_STG`
cannot be instantiated at a register's values. Its prefix `C14PreBeta` has the field
`β_three : β 3 = threeSplittingExclusionThreshold` (an equality), while every register V4 has
`β 3 = β₃ < lc18` and the realization's `lc18 ≤ threeSplittingExclusionThreshold`, so
`β 3 < threeSplittingExclusionThreshold` strictly; the prefix `C14PreFinal` also carries the staged
producer's outputs (`a₂, β₀, σ₀, Δ₀, τ₀, bc₀, a₀, b₁, w₀, bd₀, b₀, εr, δ', Λz`), whereas the
realization runs FC39-WIT's witness-exporting producer with Skolem thresholds. EDP06 itself only
needs `β 3 ≤ threeSplittingExclusionThreshold` (binding) or the no-three input (kernel), which the
register meets.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **EDP06's numerical side conditions at every register V4**: the collar request `3βc ≤ β 2`
(lane C14-STG), `β 2 < 1`, `0 ≤ γ` and `1 ≤ Δ`. -/
theorem ClosedRegisterV4.edp06_side_VAL6 {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) :
    3 * R.later.circle.βc ≤ R.β 2 ∧ R.β 2 < 1 ∧ 0 ≤ R.later.circle.γ ∧ 1 ≤ R.later.excl.Δ := by
  refine ⟨R.three_mul_βc_le_β_two_VAL6, ?_, R.later.γ_pos.le, ?_⟩
  · rw [R.β_two_VAL6]
    have := R.later.β₂_lt_audit_VAL6
    linarith
  · have := R.later.hundred_lt_Δ_VAL6
    linarith

/-- **The row's no-three input on an instance**: with LC18's exclusion on the model, at every point
`x` the rescaled member at the instance's scale `ρ(x)` has no three-splitting of quality `β 3`. -/
theorem ClosedFamilyInstanceV4.no_three_VAL6 {K : ℕ} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV4 K R M δ εr Λz) (hex : Lc18ExclusionOutV4 R M) (x : M.X) :
    ¬ @HasEuclideanSplitting.{0, 0} M.X (M.mX.rescale (F.ρ x)⁻¹ (inv_pos.mpr (F.ρ_pos x))) x 3
      (R.β 3) := by
  rw [ClosedRegisterV4.β_three_VAL6]
  exact hex x (F.ρ x) (F.ρ_pos x) (F.ρ_bounds x).1.le (F.ρ_bounds x).2.le

/-- **EDP06's collar → circle step on an instance at a register V4** (B:7103–7108): with LC18's
exclusion on the model, a point of EDP06's band at an edge centre `j` of the family
(`d(x, j) < 100Δρ(j)`, `|η_j(x)| < 4.01Δ`, `|F(x)/ρ(x) − 4Δ| < h ≤ 1/1000`) is two-stratum and lies
at distance `< 2ρ(a)` from a circle centre `a` with `‖η_a(x)‖ < 2(1 + γ)` — at the register's
values, with `3βc ≤ β 2` from register V4. -/
theorem ClosedFamilyInstanceV4.edp06_collar_circle_VAL6 {K : ℕ} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV4 K R M δ εr Λz) (hex : Lc18ExclusionOutV4 R M) {h : ℝ}
    (hh : h ≤ 1 / 1000) {j : M.X} (hj : j ∈ F.family.edge.centres) {x : M.X}
    (hx : dist x j < 100 * R.later.excl.Δ * F.ρ j)
    (hη : let c := F.family.edge.chart j hj
      let hMc : CompleteSpace M.X := complete_of_compact
      letI := M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
      letI := radialScaledBundle M.gX (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
      letI : IsContinuousRiemannianBundle E3 (fun x : M.X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous M.gX (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) M.X :=
        radialScaledManifold (m := M.mX) M.gX M.hmetric (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
      letI : CompleteSpace M.X :=
        (M.mX.rescale_completeSpace_iff (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))).mpr hMc
      |c.coord x| < 401 / 100 * R.later.excl.Δ)
    (ht : |F.family.edge.smoothing x / F.ρ x - 4 * R.later.excl.Δ| < h) :
    x ∈ scaledSplittingStratum.{0, 0} F.ρ F.ρ_pos R.β 2 ∧
      ∃ a, ∃ ha : a ∈ F.family.circle.centres, dist x a < 2 * F.ρ a ∧
        (let c := F.family.circle.chart a ha
         letI := M.mX.rescale (F.ρ a)⁻¹ (inv_pos.mpr (F.ρ_pos a))
         ‖c.coord x‖ < 2 * (1 + R.later.circle.γ)) := by
  obtain ⟨h3βc, hβ2, hγ, hΔ⟩ := R.edp06_side_VAL6
  exact edp06_collar_circle_C14 F.family h3βc hβ2 hγ hΔ hh hj hx hη ht (F.no_three_VAL6 hex x)

namespace PartialClosedThresholdValidityV4

variable {K : ℕ} {A : ℝ → ℝ} {Wseq : ℕ → CompactCarrier.{u}}
  {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier}
  {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}

/-- **EDP06's collar → circle step on the tail of every register V4, from the validity record**:
on every member of the register's tail there is a normalized model and one instance of the final
family at the register's values on which every point of EDP06's band at an edge centre is
two-stratum and lies in a circle chart with `‖η_a(x)‖ < 2(1 + γ)`. -/
theorem edp06_on_tail_VAL6 (hv : PartialClosedThresholdValidityV4 K A Wseq gseq D T)
    (hf : ∀ m, ClosedMemberFacts (Wseq m)) (R : ClosedRegisterV4 D T) :
    ∃ δ εr Λz : ℝ, ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
      ∃ F : ClosedFamilyInstanceV4 K R M δ εr Λz,
      ∀ h : ℝ, h ≤ 1 / 1000 → ∀ j (hj : j ∈ F.family.edge.centres) (x : M.X),
        dist x j < 100 * R.later.excl.Δ * F.ρ j →
        (let c := F.family.edge.chart j hj
         let hMc : CompleteSpace M.X := complete_of_compact
         letI := M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
         letI := radialScaledBundle M.gX (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
         letI : IsContinuousRiemannianBundle E3 (fun x : M.X => TangentSpace 𝓘(ℝ, E3) x) :=
           radialScaledContinuous M.gX (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
         letI : IsRiemannianManifold 𝓘(ℝ, E3) M.X :=
           radialScaledManifold (m := M.mX) M.gX M.hmetric (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
         letI : CompleteSpace M.X :=
           (M.mX.rescale_completeSpace_iff (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))).mpr hMc
         |c.coord x| < 401 / 100 * R.later.excl.Δ) →
        |F.family.edge.smoothing x / F.ρ x - 4 * R.later.excl.Δ| < h →
        x ∈ scaledSplittingStratum.{0, 0} F.ρ F.ρ_pos R.β 2 ∧
          ∃ a, ∃ ha : a ∈ F.family.circle.centres, dist x a < 2 * F.ρ a ∧
            (let c := F.family.circle.chart a ha
             letI := M.mX.rescale (F.ρ a)⁻¹ (inv_pos.mpr (F.ρ_pos a))
             ‖c.coord x‖ < 2 * (1 + R.later.circle.γ)) := by
  obtain ⟨εrF, δ'F, ΛzF, hfam⟩ := hv.family hf
  obtain ⟨-, -, -, -, -, -, δ, -, -, ht⟩ := hfam R
  refine ⟨δ, εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, hex⟩ := ht m hm
  exact ⟨M, F, fun h hh j hj x hx hη hsm => F.edp06_collar_circle_VAL6 hex hh hj hx hη hsm⟩

end PartialClosedThresholdValidityV4

/-- **The inhabited partial record on register V4 with EDP06's collar step** (consumer of G1–G3):
at the early data `earlyDataSharedV4 K` (the ONE shared CFS15 modulus), on every closed standing
sequence, one strategy `T` at which the whole record `PartialClosedThresholdValidityV4Rows` holds,
the `N_b, c_w` slots are PR10's values, every register carries the collar request `3βc ≤ β 2` and
`β 3 ≤` LC18's threshold, and on the tail of every register EDP06's collar → circle step holds on an
instance of the final family at the register's values. -/
theorem exists_partialClosedThresholdValidityV4Rows_edp06_VAL6 (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = sharedNb_VAL6 ∧ T.cw = sharedCw_VAL6 ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        3 * R.later.circle.βc ≤ R.β 2 ∧ R.β 3 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
        ∃ δ εr Λz : ℝ, ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
          ∃ F : ClosedFamilyInstanceV4 K R M δ εr Λz,
          ∀ h : ℝ, h ≤ 1 / 1000 → ∀ j (hj : j ∈ F.family.edge.centres) (x : M.X),
            dist x j < 100 * R.later.excl.Δ * F.ρ j →
            (let c := F.family.edge.chart j hj
             let hMc : CompleteSpace M.X := complete_of_compact
             letI := M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
             letI := radialScaledBundle M.gX (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
             letI : IsContinuousRiemannianBundle E3 (fun x : M.X => TangentSpace 𝓘(ℝ, E3) x) :=
               radialScaledContinuous M.gX (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))
             letI : IsRiemannianManifold 𝓘(ℝ, E3) M.X :=
               radialScaledManifold (m := M.mX) M.gX M.hmetric (F.ρ j)⁻¹
                 (inv_pos.mpr (F.ρ_pos j))
             letI : CompleteSpace M.X :=
               (M.mX.rescale_completeSpace_iff (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))).mpr hMc
             |c.coord x| < 401 / 100 * R.later.excl.Δ) →
            |F.family.edge.smoothing x / F.ρ x - 4 * R.later.excl.Δ| < h →
            x ∈ scaledSplittingStratum.{0, 0} F.ρ F.ρ_pos R.β 2 ∧
              ∃ a, ∃ ha : a ∈ F.family.circle.centres, dist x a < 2 * F.ρ a ∧
                (let c := F.family.circle.chart a ha
                 letI := M.mX.rescale (F.ρ a)⁻¹ (inv_pos.mpr (F.ρ_pos a))
                 ‖c.coord x‖ < 2 * (1 + R.later.circle.γ)) := by
  obtain ⟨T, hv, hNb, hcw⟩ :=
    exists_partialClosedThresholdValidityV4Rows_nbcw_VAL6 K hK A hA Wseq gseq hf hg
  exact ⟨T, hv, hNb, hcw, fun R => ⟨R.three_mul_βc_le_β_two_VAL6,
    hv.toPartialClosedThresholdValidityV4.β_three_le_VAL6 R,
    hv.toPartialClosedThresholdValidityV4.edp06_on_tail_VAL6 hf R⟩⟩

/-! ### The staged contract's requests on register V4 -/

/-- **The staged prefix never carries a register's splitting vector** (why
`exists_c14d_staged_assignment_STG` is not instantiated at a register's values): for a strategy with
`lc18 ≤` LC18's threshold (every realization strategy), `R.β 3 = β₃ < lc18`, while every
`C14PreFinal` has `β 3 =` LC18's threshold (field `C14PreBeta.β_three`). -/
theorem ClosedRegisterV4.β_ne_c14PreFinal_VAL6 {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (hT : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) (R : ClosedRegisterV4 D T)
    (P : C14PreFinal) : P.β ≠ R.β := by
  intro h
  have h1 := P.β_three
  have h2 : R.β 3 < threeSplittingExclusionThreshold.{0, 0} := by
    rw [R.β_three_VAL6]
    exact R.later.β₃_lt.trans_le hT
  rw [h] at h1
  linarith

/-- **TCP04's request `β₂ < γc/1000` as a strategy cap** (B:5483; a missing request record of lane
C14-STG): `U` with `β₂`'s slot capped by `γc/1000`, read at the circle prefix (before `βc`). -/
def ClosedThresholdsV4.withCollarβ₂_VAL6 {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedThresholdsV4 D :=
  { U with
    β₂Up := fun st cp β₃ => min (U.β₂Up st cp β₃) (posOr_VAL3 (cp.γc / 1000))
    β₂Up_pos := fun st cp β₃ => lt_min (U.β₂Up_pos st cp β₃) (posOr_pos_VAL3 _) }

/-- **TCP04's `β₂ < γc/1000` at every register of a strategy below the cap.** -/
theorem ClosedRegisterV4.β₂_lt_γc_of_below_VAL6 {D : ClosedEarlyData} {T U : ClosedThresholdsV4 D}
    (h : ClosedStrategyBelowV4 T U.withCollarβ₂_VAL6) (R : ClosedRegisterV4 D T) :
    R.later.excl.β₂ < R.later.circle.γc / 1000 := by
  have h1 := (R.later.β₂_lt.trans_le (min_le_left _ _)).trans_le (h.β₂Up_le _ _ _)
  have hγc := R.later.γc_pos
  have h2 : U.withCollarβ₂_VAL6.β₂Up R.stage R.later.circle.toPrefixV4 R.later.excl.β₃ ≤
      R.later.circle.γc / 1000 := by
    change min _ (posOr_VAL3 (R.later.circle.γc / 1000)) ≤ _
    rw [posOr_eq_VAL3 (by positivity)]
    exact min_le_right _ _
  exact h1.trans_le h2

/-- **The boundary route's request `v_s < ϑ₃/4` as a boundary strategy cap** (BCG02 / R17; a
missing request record of lane C14-STG): the interior error slot of every boundary request is
capped by `ϑ₃/4` (`ϑ₃ = ϑ 2`, fixed at BR11 before PR14). -/
def BoundaryThresholdsV4.withVsCap_VAL6 {D : BoundaryEarlyData} (Tb : BoundaryThresholdsV4 D) :
    BoundaryThresholdsV4 D :=
  { Tb with
    interior := fun ϑ sh bc =>
      { Tb.interior ϑ sh bc with
        errorsUp := fun st ci ex =>
          min ((Tb.interior ϑ sh bc).errorsUp st ci ex) (posOr_VAL3 (ϑ 2 / 4))
        errorsUp_pos := fun st ci ex =>
          lt_min ((Tb.interior ϑ sh bc).errorsUp_pos st ci ex) (posOr_pos_VAL3 _) } }

/-- **`v_s < ϑ₃/4` at every boundary register V4 of the capped strategy** (the register's `v_s` is
the error `ve`, the family's slim value tolerance). -/
theorem BoundaryRegisterV4.ve_lt_ϑ_VAL6 {D : BoundaryEarlyData} {Tb : BoundaryThresholdsV4 D}
    (R : BoundaryRegisterV4 D Tb.withVsCap_VAL6) : R.later.err.co.ve < R.ϑ 2 / 4 := by
  have h := R.later.ve_lt.trans_le (min_le_right _ _)
  have hϑ := R.ϑ_pos 2
  have h2 : (Tb.withVsCap_VAL6.toClosed R.ϑ R.shortErr R.bcgErr).errorsUp R.stage R.later.circle
      R.later.excl ≤ R.ϑ 2 / 4 := by
    change min _ (posOr_VAL3 (R.ϑ 2 / 4)) ≤ _
    rw [posOr_eq_VAL3 (by positivity)]
    exact min_le_right _ _
  exact h.trans_le h2

/-- TCP04's `β₂ < γc/1000` at every register of the capped strategy itself. -/
theorem ClosedRegisterV4.β₂_lt_γc_VAL6 {D : ClosedEarlyData} {U : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D U.withCollarβ₂_VAL6) :
    R.later.excl.β₂ < R.later.circle.γc / 1000 := by
  have h1 := R.later.β₂_lt.trans_le (min_le_left _ _)
  have hγc := R.later.γc_pos
  have h2 : U.withCollarβ₂_VAL6.β₂Up R.stage R.later.circle.toPrefixV4 R.later.excl.β₃ ≤
      R.later.circle.γc / 1000 := by
    change min _ (posOr_VAL3 (R.later.circle.γc / 1000)) ≤ _
    rw [posOr_eq_VAL3 (by positivity)]
    exact min_le_right _ _
  exact h1.trans_le h2

/-- **Inhabitants of the two caps at the concrete data**: a register V4 of
`unitClosedThresholdsV4.withCollarβ₂_VAL6` with `β₂ < γc/1000` and `3βc ≤ β 2`, and a boundary
register V4 of `unitBoundaryThresholdsV4.withVsCap_VAL6` with `v_s < ϑ₃/4`. -/
theorem unit_staged_caps_VAL6 :
    (∃ R : ClosedRegisterV4 unitClosedEarlyData unitClosedThresholdsV4.withCollarβ₂_VAL6,
      R.later.excl.β₂ < R.later.circle.γc / 1000 ∧ 3 * R.later.circle.βc ≤ R.β 2) ∧
    ∃ R : BoundaryRegisterV4 unitBoundaryEarlyDataV2 unitBoundaryThresholdsV4.withVsCap_VAL6,
      R.later.err.co.ve < R.ϑ 2 / 4 := by
  obtain ⟨R⟩ := exists_closedRegisterV4 unitClosedEarlyData unitClosedThresholdsV4.withCollarβ₂_VAL6
  obtain ⟨Rb⟩ := exists_boundaryRegisterV4 unitBoundaryEarlyDataV2
    unitBoundaryThresholdsV4.withVsCap_VAL6
  exact ⟨⟨R, R.β₂_lt_γc_VAL6, R.three_mul_βc_le_β_two_VAL6⟩, Rb, Rb.ve_lt_ϑ_VAL6⟩

end DifferentialGeometry.Geometry.Collapse
