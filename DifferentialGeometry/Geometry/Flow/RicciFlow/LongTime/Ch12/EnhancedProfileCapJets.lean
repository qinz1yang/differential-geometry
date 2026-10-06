import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessCoherence

/-!
# CH12-O2, group 3 (W5 / M04): all-order jets near newly inserted caps

CH12-O1 showed that with the current profile the outgoing cap window has order
`parameters.modelOrder` (an arbitrary natural number) and that the canonical-window datum
`(δ', k)` is a bare existential, so no all-K (and no K = 20) jet bound near a new cap follows.

Here, under P1 (link) + P3 (collar length / window radius) + `hdec`:

* `late_cap_window_witness_O2`: for every order `m` and accuracy `ζ > 0`, after some time every
  late cutoff record's cap window carries a `CanonicalStaticInsertionWitness` of order `m`,
  accuracy `ζ`, with the fixed collar length and the record's window radius, **whose window metric
  is the record window's pulled-back output metric** (the witness is rebuilt from the linked datum
  at lower order; `coherent_of_lowerOrder` identifies the two windows).
* `late_cap_window_jets_O2`: feeding these witnesses to the cap-window flow kernel
  `ObservedHistory.exists_uniform_prepared_incoming_cap_window_flow_with_uniform_curvature_derivative_bounds`
  (`Surgery/Topology/PreparedCapWindowGeometry.lean:668`, which accepts an arbitrary witness)
  gives, for every `N`, scale-invariant jets of order `≤ N` on the flowed cap window of every late
  cap, with constants independent of the history index, event and boundary.  The records-precision
  premise of the kernel is discharged by `hdec`; the event-slab time-derivative premise by P2.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness
open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- Two canonical static insertion witnesses built on (lower orders of) the same datum with the
same collar length and window radius have the same window metric. -/
theorem windowMetric_inner_eq_of_lowerOrder_O2 {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    {h : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ' : ℝ} {k j : ℕ}
    (d : normalizedDatum h x₀ δ' k) (hj : j ≤ k) {A : ℝ} {hA : 0 < A} {D : ℝ}
    {m₀ m₁ : ℕ} {ε₀ ε₁ : ℝ}
    (w₀ : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      (d.lowerOrder hj) A hA D m₀ ε₀)
    (w₁ : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      d A hA D m₁ ε₁)
    (x : standardCapWindow D) (v z : TangentSpace ThreeModel x) :
    w₀.windowMetric.inner x v z = w₁.windowMetric.inner x v z := by
  have hcoh :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.coherent_of_lowerOrder
      d hj (le_refl k) w₀ w₁
  obtain ⟨-, -, -, -, -, hout, -, -, -, -, -, hmap₀, hmap₁⟩ := hcoh
  have hwin : w₀.window = w₁.window := by
    ext x
    change w₀.data.windowMap x = w₁.data.windowMap x
    rw [hmap₀ x, hmap₁ x]
  rw [w₀.window_inner, w₁.window_inner, hwin, hout]

/-- **W5 static step.**  Under P1 + P3 + `hdec`: for every order `m` and accuracy `ζ`, every late
cap window carries an order-`m`, accuracy-`ζ` canonical witness with the record's window metric. -/
theorem late_cap_window_witness_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP1 : P1_O2 Hp) (hP3 : P3_O2 Hp) (m : ℕ) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ T : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      T < (F.tower.history n).time i.succ →
      ∃ (x₀ : ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen) (δ' : ℝ)
        (d : normalizedDatum ((F.tower.history n).toHistory.event i).terminal.metric
          x₀ δ' (m + 4))
        (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
          Hp.parameters.fixed.collarLength Hp.parameters.fixed.collar_pos
          Hp.parameters.modelRadius m ζ),
        metricScalarAt ((F.tower.history n).toHistory.event i).terminal.metric x₀ =
            ((Hp.records n i).static b).neck.scale ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          ((Hp.records n i).static b).neck.scale *
            ((F.tower.history n).initialMetric i.succ).inner
              (((Hp.records n i).static b).window x)
              (mfderiv ThreeModel ThreeModel ((Hp.records n i).static b).window x v)
              (mfderiv ThreeModel ThreeModel ((Hp.records n i).static b).window x z)) ∧
        (∀ z : ThreeBall, ∃ x : standardCapWindow Hp.parameters.modelRadius,
          ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
          ((Hp.records n i).static b).window x =
            ((Hp.records n i).static b).inclusion (((Hp.records n i).static b).witness.cap z)) := by
  obtain ⟨δ₀, hδ₀, hwit⟩ := hP3.1 Hp.parameters.modelRadius Hp.parameters.modelRadius_pos m ζ hζ
  obtain ⟨T, hT⟩ := late_window_datum_O2 Hp hdec hP1 (m + 4) δ₀ hδ₀
  refine ⟨T, fun n i b ht => ?_⟩
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, hδ', hk⟩ := hT n i b ht
  obtain ⟨w'⟩ := hwit δ' d.precision_pos hδ' _ x₀ (d.lowerOrder hk)
  refine ⟨x₀, δ', d.lowerOrder hk, w', h1, fun x v z => ?_, h3⟩
  rw [windowMetric_inner_eq_of_lowerOrder_O2 d hk w' w x v z, h2 x v z,
    ← (F.tower.history n).event_output i]

end GC.LongTime.Ch12
