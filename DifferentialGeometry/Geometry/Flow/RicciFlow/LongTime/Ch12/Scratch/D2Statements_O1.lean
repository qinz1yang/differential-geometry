import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows

/-!
# CH12-O1 scratch: D2 / M02 / D3 frozen statements

Design note: `docs/geometrization/chapter12/design-D2-D3-M02-20261006.md`.

* Everything named `…Statement_O1` / `…Target_O1` / `…Proposal_O1` is a `def … : Prop`
  (a statement under discussion), never used as an assumption of a theorem below except as an
  explicit hypothesis of a trivial implication.
* Proved here (no sorry):
  - `neck_order_eventually_ge_O1`: `hdec` forces the *incoming neck* order of every late cutoff
    record to be eventually `≥ m`, for every `m` (this is all that `hdec` buys for D2).
  - `A13Statement_twenty_of_allK_O1`: the all-K A13 implies the K = 20 fallback.
  - `LateCutFamily.eventually_thin_geometry_O1`: D3, any `L` — `alternatives w` turns
    `L.thin` into `hasThinVolumeGeometry … K w` eventually (constructors exclude the other cases).
  - `linkedCanonicalWindow_hasCanonicalWindow_O1`: the proposed profile strengthening is a
    strengthening of the existing `hasCanonicalWindow`.
  - `linked_window_order_eventually_ge_O1`: under the proposed link, `hdec` makes the cap-window
    datum order eventually `≥ m` for every `m` (the missing D2 input).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck
open Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-! ## D2: what `hdec` gives — incoming neck order grows -/

/-- [V-proved] For every `m`, after some time `B` every incoming neck of every cutoff record
of the profile has order `≥ m`.  Uses only `order_lower`, `delta_le`, `delta_pos`,
`accuracy_eq` and `hdec`.  The *outgoing cap window* order (`parameters.modelOrder`) is NOT
affected; see the design note §1. -/
theorem neck_order_eventually_ge_O1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) (m : ℕ) :
    ∃ B : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount)
      (α : ((F.tower.history n).toHistory.event i).transition.trace.tubes.Index),
      B < (F.tower.history n).toHistory.time i.succ → m ≤ (Hp.records n i).order α := by
  obtain ⟨B, hB⟩ := hdec (1 / ((m : ℝ) + 1)) (by positivity)
  refine ⟨B, fun n i α ht => ?_⟩
  have hle := (Hp.records n i).delta_le α
  have hpos := (Hp.records n i).delta_pos α
  have hlow := (Hp.records n i).order_lower α
  rw [Hp.accuracy_eq] at hle
  have hlt : (Hp.records n i).delta α < 1 / ((m : ℝ) + 1) := hle.trans_lt (hB _ ht)
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hinv : (m : ℝ) + 1 < ((Hp.records n i).delta α)⁻¹ := by
    have h1 : (m : ℝ) + 1 = (1 / ((m : ℝ) + 1))⁻¹ := by field_simp
    rw [h1]
    exact (inv_lt_inv₀ (by positivity) hpos).mpr hlt
  have hfloor : m + 1 ≤ ⌊((Hp.records n i).delta α)⁻¹⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact hinv.le
  have h2 : 2 * ⌊((Hp.records n i).delta α)⁻¹⌋₊ + 4 ≤ (Hp.records n i).order α :=
    (le_max_right _ _).trans hlow
  omega

/-! ## D2: statements (Prop definitions only) -/

/-- A13 at a fixed order `K`, as a proposition (the K = 20 fallback is `A13Statement_O1 20`). -/
def A13Statement_O1 (K : ℕ) : Prop :=
  ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ),
    GC.LongTime.hasAnalyticAdmissibility F δ →
    (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) →
    ∀ (slices : ℕ → GC.LongTime.RegularSlice F.observation),
      (∀ j : ℕ, (j : ℝ) < (slices j).time) →
      (∀ j : ℕ, Nonempty (slices j).stage.Carrier) →
      ∀ L : GC.LongTime.LateCutFamily F K slices, L.hasEventualDerivativeBounds

/-- The current all-K A13 (`LateCutGeometry.lean:158`), as a proposition. -/
def A13AllKStatement_O1 : Prop :=
  ∀ K : ℕ, GC.LongTime.lateDerivativeOrder ≤ K → A13Statement_O1.{u} K

/-- [V-proved] The all-K form implies the K = 20 fallback (so the fallback is a weakening). -/
theorem A13Statement_twenty_of_allK_O1 (h : A13AllKStatement_O1.{u}) :
    A13Statement_O1.{u} GC.LongTime.lateDerivativeOrder :=
  h _ le_rfl

/-- M04 target at order `K` (D-WBD §9.3 generalised): uniform late scale-invariant jets at
every canonical-scale point, including newly inserted cap cores. -/
def capJetsTarget_O1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (K : ℕ) : Prop :=
  ∃ T C : ℝ, 0 < T ∧ 0 < C ∧
    ∀ t : ℝ, T ≤ t → ∀ x : (GC.LongTime.postStage F.observation t).Carrier,
      (Hp.parameters.neckRadius t ^ 2)⁻¹ <
          metricScalarAt (GC.LongTime.postMetric F.observation t) x →
      ∀ k : ℕ, k ≤ K →
        curvatureDerivativeNorm (GC.LongTime.postMetric F.observation t) k x ≤
          C * (Real.sqrt (metricScalarAt (GC.LongTime.postMetric F.observation t) x)) ^ (k + 2)

/-! ## D2: proposed profile strengthening (A12 statement change; for the user's decision) -/

section LinkedWindow

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- `hasCanonicalWindow` (`CanonicalCapWindows.lean:22`) with the insertion datum `(δ', k)`
tied to the static neck: `δ' ≤ S.delta` and `2⌊δ'⁻¹⌋ ≤ k`.  In the existing predicate
`δ'` and `k` are bare existentials, which is exactly why the cap-window jets of order > `m`
are uncontrolled (design note §1.3). -/
def linkedCanonicalWindowProposal_O1 (S : E.PresentedStaticCap fixed D m ε b) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ' : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ' k)
    (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
      fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x z)) ∧
    (∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
      S.window x = S.inclusion (S.witness.cap z)) ∧
    δ' ≤ S.delta ∧ 2 * ⌊δ'⁻¹⌋₊ ≤ k

/-- [V-proved] The proposal strengthens the existing field. -/
theorem linkedCanonicalWindow_hasCanonicalWindow_O1 (S : E.PresentedStaticCap fixed D m ε b)
    (h : linkedCanonicalWindowProposal_O1 S) : S.hasCanonicalWindow := by
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, -, -⟩ := h
  exact ⟨x₀, δ', k, d, w, h1, h2, h3⟩

/-- [V-proved] Under the link, a small static-neck precision forces a large datum order. -/
theorem linked_window_order_ge_O1 (S : E.PresentedStaticCap fixed D m ε b)
    (h : linkedCanonicalWindowProposal_O1 S) (n : ℕ) (hS : S.delta < 1 / ((n : ℝ) + 1)) :
    ∃ (x₀ : E.incoming.terminalRegularOpen) (δ' : ℝ) (k : ℕ)
      (_ : normalizedDatum E.terminal.metric x₀ δ' k), 2 * (n + 1) ≤ k := by
  obtain ⟨x₀, δ', k, d, -, -, -, -, hδ, hk⟩ := h
  refine ⟨x₀, δ', k, d, ?_⟩
  have hpos : 0 < δ' := d.precision_pos
  have hlt : δ' < 1 / ((n : ℝ) + 1) := hδ.trans_lt hS
  have hinv : (n : ℝ) + 1 < δ'⁻¹ := by
    have h1 : (n : ℝ) + 1 = (1 / ((n : ℝ) + 1))⁻¹ := by field_simp
    rw [h1]
    exact (inv_lt_inv₀ (by positivity) hpos).mpr hlt
  have hfloor : n + 1 ≤ ⌊δ'⁻¹⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact hinv.le
  omega

end LinkedWindow

/-! ## D3: arbitrary `L` — field-only steps -/

/-- [V-proved] D3 step used by TCF02/03/04: for any `L`, `alternatives w` makes every late
thin piece carry `hasThinVolumeGeometry … K w` (the `hyperbolic` and `nonnegative`
constructors carry `¬ thin`). -/
theorem LateCutFamily.eventually_thin_geometry_O1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → GC.LongTime.RegularSlice F.observation}
    (L : GC.LongTime.LateCutFamily F K slices) (w : ℝ) (hw : 0 < w)
    (hc : w < euclideanThreeUnitBallVolume) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      GC.LongTime.hasThinVolumeGeometry ((L.decomposition j C).component i)
        (L.metric j C i) K w := by
  obtain ⟨N, hN⟩ := L.alternatives w hw hc
  refine ⟨N, fun j hj C i hi => ?_⟩
  obtain ⟨pieces⟩ := hN j hj C
  cases pieces i with
  | hyperbolic not_thin _ _ => exact absurd hi not_thin
  | thin _ geometry => exact geometry
  | nonnegative not_thin _ _ => exact absurd hi not_thin

end GC.LongTime.Ch12
