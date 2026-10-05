import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV2SequenceValidity
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindings

/-!
# The validity bridge of the per-sequence boundary supply (lane FC39-BQ2; review 54 §6.2)

External review 54, §6.2 (dispositions row 6): the realization must return the partial validity
for the SAME early data `D` and the SAME strategy `T` as the family on the tail, and `D` must be
early data WITH SOURCES — PR01–PR03's `N, P, L₀, Ξ` (and `C`) and BSA01's numerical `δ⋆, C₀`
(BBR01's BR00–BR03, B:10370–10371) — not an arbitrary `D` with `D.δStar = δStar`.

* `PartialBoundaryThresholdValidityV3_BQ2 K D T` extends `PartialBoundaryThresholdValidityV2_BQ`
  (the early sources `N, P, L₀, Ξ` on `D.toClosedEarlyData`, LC18's obstruction and `I(1)` for
  every boundary request) by the remaining early sources: PR01's graph constants `C_ge`, BSA01's
  `C₀ = 1000` (B:7593), and `δ⋆` as BSA01's threshold — BSA01.b (`Vol B(p, r) ≤ C₀ δ² r` on the
  collar part `z ≤ 96`) and BSA01.c (finite curvature scale, `R_p ≤ d + 3`, the use of `δ⋆` in
  BBR03, B:10621–10622) at every ratio `δ ≤ D.δStar`, on universe-`0` carriers (the producer's).
* `boundaryEarlyDataSrc_BQ2 K δ hδ`: the early data with sources (`closedEarlyDataV3 K`,
  `δ⋆ := δ`, `C₀ := 1000`); `boundaryThresholdsSrc_BQ2 D`: a strategy with LC18's obstruction and
  the actual `I(1)`; `exists_sourced_boundaryEarlyData_BQ2`: the validity holds there for every
  `δ` below BSA01's threshold (inhabitant).
* THE BRIDGE `PartialBoundaryThresholdValidityV3_BQ2.of_refines_BQ2`: for the same `D`, every
  strategy refining a valid one is valid (the early sources depend on `D` only; LC18's slot only
  decreases and `I(1)` is kept along `BoundaryStrategyRefinesV2_BQ`). So the strategy `T` that
  realizes the family on a sequence carries the validity on the SAME `D` (review 54 §6.2, second
  repair: sourced early data first, then the same refinement keeps the validity).
* Consumers: `ballVolume_le_BQ2` (BSA01.b at a member of the boundary standing sequence at
  `δ_{n+1}`), `curvatureRadius_le_BQ2` (BSA01.c there).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology ENNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

/-- **The member-free boundary validity with ALL early sources** (PARTIAL: boundary-slot `Out`s
are open, as for its parent). -/
structure PartialBoundaryThresholdValidityV3_BQ2 (K : ℕ) (D : BoundaryEarlyData)
    (T : BoundaryThresholdsV2 D) : Prop
    extends PartialBoundaryThresholdValidityV2_BQ K D T where
  /-- PR01 `C`: the early graph constants of TCP05, EGP06, SGP04 are below `C_j`. -/
  C_ge : ∀ j, gafGraphConst j ≤ D.C j
  /-- BR00 (B:10370): BSA01's numerical `C₀ = 1000` (B:7593). -/
  C₀_eq : D.C₀ = 1000
  /-- BR00 (B:10370): `δ⋆` is BSA01's threshold — BSA01.b with the constant `C₀` at every ratio
  `δ ≤ δ⋆` (B:7605–7610). -/
  bsa01_volume : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier)
    (K' : ℕ) (δ : ℝ), 2 ≤ K' → 0 ≤ δ → δ ≤ D.δStar → ∀ B : NearlyCuspidalBoundary W g K' δ,
    ∀ (i : Fin B.count) (p : CuspHalfSpace), p.2.val 0 ≤ 96 → ∀ r : ℝ, r ≤ 1 →
      ballVolume g ((B.collar i).toFun p) r ≤ ENNReal.ofReal (D.C₀ * δ ^ 2 * r)
  /-- BBR03 (B:10621–10622): below `δ⋆` every curvature scale is finite — BSA01.c (B:7614–7616). -/
  bsa01_scale : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier)
    (K' : ℕ) (δ : ℝ), 2 ≤ K' → 0 ≤ δ → δ ≤ D.δStar → NearlyCuspidalBoundary W g K' δ →
    ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
      curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3

/-- **The early data with sources**: PR01–PR03's constants of the native rows
(`closedEarlyDataV3 K`), `δ⋆ := δ` and BSA01's `C₀ = 1000`. -/
def boundaryEarlyDataSrc_BQ2 (K : ℕ) (δ : ℝ) (hδ : 0 < δ) : BoundaryEarlyData :=
  { closedEarlyDataV3 K with δStar := δ, δStar_pos := hδ, C₀ := 1000, C₀_pos := by norm_num }

/-- A boundary strategy at `D` whose interior is the rows' strategy with LC18's obstruction and
the actual `I(1)`. -/
def boundaryThresholdsSrc_BQ2 (D : BoundaryEarlyData) : BoundaryThresholdsV2 D where
  ϑUp := fun _ => 1
  ϑUp_pos := fun _ => one_pos
  shortUp := fun _ _ => 1
  shortUp_pos := fun _ _ => one_pos
  bcgUp := fun _ _ => 1
  bcgUp_pos := fun _ _ => one_pos
  interior := fun _ _ _ =>
    { partialRowsStrategyV2 D.toClosedEarlyData with
      lc18 := threeSplittingExclusionThreshold.{0, 0}
      lc18_pos := threeSplittingExclusionThreshold_pos
      I₁ := ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2
      I₁_pos := integral_sinh_sq_pos_BQ }
  cuspUp := fun _ _ _ _ _ => 1
  cuspUp_pos := fun _ _ _ _ _ => one_pos
  cuspRadii := fun _ _ _ _ _ _ => 0
  productUp := fun _ _ _ _ _ _ _ => 1
  productUp_pos := fun _ _ _ _ _ _ _ => one_pos
  tailLow := fun _ _ _ _ _ _ _ _ => 0
  fixedConstants := ∅

/-- **Inhabitant (sourced early data)**: below BSA01's threshold the early data with sources
carries the whole member-free validity, at the strategy `boundaryThresholdsSrc_BQ2`. -/
theorem exists_sourced_boundaryEarlyData_BQ2 (K : ℕ) :
    ∃ δB : ℝ, 0 < δB ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δB →
      PartialBoundaryThresholdValidityV3_BQ2 K (boundaryEarlyDataSrc_BQ2 K δ hδ)
        (boundaryThresholdsSrc_BQ2 (boundaryEarlyDataSrc_BQ2 K δ hδ)) := by
  obtain ⟨δS, hδS, h⟩ := bsa01_clauses_except_II.{0}
  obtain ⟨hN, hP, hPs, hPz, hL, hΞ, hΞr, hC⟩ := closedEarlyDataV3_fields_VAL3 K
  refine ⟨δS, hδS, fun δ hδ hle => ?_⟩
  exact
    { N_ge := hN, P_ge := hP, P_ge_sgp := hPs, P_ge_zero := hPz, L₀_ge := hL, Ξ_cfs15 := hΞ
      Ξ_range := hΞr
      lc18_le := fun _ _ _ => le_rfl
      I₁_eq := fun _ _ _ => rfl
      C_ge := hC
      C₀_eq := rfl
      bsa01_volume := fun W g K' δ' hK hδ0 hδ' B i p hp r hr =>
        ((h W g K' δ' hK hδ0 (hδ'.trans hle) B).2.2.1 i p hp).2.1 r hr
      bsa01_scale := fun W g K' δ' hK hδ0 hδ' B hc =>
        (h W g K' δ' hK hδ0 (hδ'.trans hle) B).2.2.2.2.1 hc }

namespace PartialBoundaryThresholdValidityV3_BQ2

variable {K : ℕ} {D : BoundaryEarlyData}

/-- **THE VALIDITY BRIDGE** (review 54 §6.2): for the SAME early data, a strategy refining a valid
strategy is valid. -/
theorem of_refines_BQ2 {T U : BoundaryThresholdsV2 D}
    (hv : PartialBoundaryThresholdValidityV3_BQ2 K D U) (h : BoundaryStrategyRefinesV2_BQ T U) :
    PartialBoundaryThresholdValidityV3_BQ2 K D T :=
  { N_ge := hv.N_ge, P_ge := hv.P_ge, P_ge_sgp := hv.P_ge_sgp, P_ge_zero := hv.P_ge_zero
    L₀_ge := hv.L₀_ge, Ξ_cfs15 := hv.Ξ_cfs15, Ξ_range := hv.Ξ_range
    lc18_le := fun ϑ sh bc => (h.interior_refines ϑ sh bc).lc18_le.trans (hv.lc18_le ϑ sh bc)
    I₁_eq := fun ϑ sh bc => (h.interior_refines ϑ sh bc).I₁_eq.trans (hv.I₁_eq ϑ sh bc)
    C_ge := hv.C_ge, C₀_eq := hv.C₀_eq, bsa01_volume := hv.bsa01_volume
    bsa01_scale := hv.bsa01_scale }

variable {T : BoundaryThresholdsV2 D}

/-- **Consumer (BSA01.b on the standing sequence)**: at a member of the boundary standing sequence
(ratio `δ_{n+1}`, `n ≥ 0`), the collar balls have volume at most `C₀ δ_{n+1}² r`. -/
theorem ballVolume_le_BQ2 (hv : PartialBoundaryThresholdValidityV3_BQ2 K D T)
    {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier} {K' : ℕ}
    (hK : 2 ≤ K') (n : ℕ)
    (B : NearlyCuspidalBoundary W g K' (boundaryCounterexampleRatio D.δStar (n + 1)))
    (i : Fin B.count) (p : CuspHalfSpace) (hp : p.2.val 0 ≤ 96) (r : ℝ) (hr : r ≤ 1) :
    ballVolume g ((B.collar i).toFun p) r ≤
      ENNReal.ofReal (1000 * boundaryCounterexampleRatio D.δStar (n + 1) ^ 2 * r) := by
  rw [← hv.C₀_eq]
  exact hv.bsa01_volume W g K' _ hK
    (boundaryCounterexampleRatio_pos D.δStar_pos (Nat.le_add_left 1 n)).le
    (boundaryCounterexampleRatio_le _ _) B i p hp r hr

/-- **Consumer (BSA01.c on the standing sequence)**: at a member of the boundary standing sequence,
every curvature scale is finite and `R_p ≤ d(p, ∂W) + 3`. -/
theorem curvatureRadius_le_BQ2 (hv : PartialBoundaryThresholdValidityV3_BQ2 K D T)
    {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {K' : ℕ} (hK : 2 ≤ K') (n : ℕ)
    (B : NearlyCuspidalBoundary W g K' (boundaryCounterexampleRatio D.δStar (n + 1)))
    (p : W.Carrier) :
    curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3 :=
  (hv.bsa01_scale W g K' _ hK
    (boundaryCounterexampleRatio_pos D.δStar_pos (Nat.le_add_left 1 n)).le
    (boundaryCounterexampleRatio_le _ _) B inferInstance p).2

end PartialBoundaryThresholdValidityV3_BQ2

end DifferentialGeometry.Geometry.Collapse
