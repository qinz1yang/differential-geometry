import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BridgeIoo_S89
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageGlue_S110

set_option autoImplicit false

/-!
# CH12-S132 / G3c (K-level): the `Ioo` datum from the `Ico` datum, keeping `K` and `b`

`ioo_of_ico_S132` is `hlift_Ioo_core_S89` at `α r := (K.stage (K.activeStage r)).Carrier` and the target
family `y r _ q := ψ_r (φ q)` of the given datum itself: the output is an `Ioo` datum `(a' < t, same b)` whose
lifts agree pointwise (`Eq`, not only `HEq`) with those of the input datum on the window `[t, 2t]`.
(The F-level bridge `hlift_Ioo_of_Ico_S89` forgets that `n` and `b` are unchanged, hence is not used.)
`defect_pt_eq_S132` : the vector-defect clause is invariant under equality of the base point.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem defect_pt_eq_S132 {A : OrientedThreeStage.{u}} (g : A.Metric) {x y : A.Carrier} (h : x = y)
    (c η : ℝ)
    (hx : ∀ V : TangentSpace ThreeModel x,
      |2 * c * ricciTensor g x V V + g.inner x V V| ≤ η * g.inner x V V) :
    ∀ V : TangentSpace ThreeModel y,
      |2 * c * ricciTensor g y V V + g.inner y V V| ≤ η * g.inner y V V := by
  subst h
  exact hx

theorem ioo_of_ico_S132 {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (K : ObservedHistory.{u}) {pp : CutoffParameters}
    (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K i pp) {t : ℝ}
    (hscale : ∀ i : Fin K.eventCount, K.time i.succ = t →
      ∀ (b : (K.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i).static b).neck.scale / 2 ≤
          metricScalarAt ((records i).static b).witness.metric
            (((records i).static b).witness.cap z))
    (hrc : ∀ i : Fin K.eventCount, K.time i.succ = t →
      pp.recenterConstant * pp.delta (K.time i.succ) ≤ 1 / 2)
    (B : Set X) (hB : B.Nonempty) (ht0 : 0 ≤ t) {first last : Fin (K.eventCount + 1)}
    {ordered : first ≤ last} {a b : ℝ} (hat : a ≤ t) (h2tb : 2 * t < b) (hb : b ≤ K.horizon)
    (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
      first ≤ K.activeStage r ∧ K.activeStage r ≤ last)
    (φ : X → K.backwardSurvivorDomain first last ordered)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ B)
    (hneg : K.time first = t → ∀ p ∈ B,
      metricScalarAt (K.initialMetric first)
        (K.backwardSurvivorMap first last ordered first le_rfl ordered (φ p)) ≤ 0) :
    ∃ (first' last' : Fin (K.eventCount + 1)) (ordered' : first' ≤ last') (a' : ℝ) (_ : a' < t)
      (stages' : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ioo a' b →
        first' ≤ K.activeStage r ∧ K.activeStage r ≤ last')
      (φ' : X → K.backwardSurvivorDomain first' last' ordered'),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ' B ∧
      ∀ (r : Icc (0 : ℝ) K.horizon) (hr : (r : ℝ) ∈ Ioo a' b) (hr0 : (r : ℝ) ∈ Ico a b),
        (r : ℝ) ∈ Icc t (2 * t) → ∀ p ∈ B,
          K.backwardSurvivorMap first' last' ordered' (K.activeStage r) (stages' r hr).1
            (stages' r hr).2 (φ' p) =
          K.backwardSurvivorMap first last ordered (K.activeStage r) (stages r hr0).1
            (stages r hr0).2 (φ p) := by
  have hmem : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Icc t (2 * t) → (r : ℝ) ∈ Ico a b :=
    fun r hr => ⟨hat.trans hr.1, by linarith [hr.2]⟩
  obtain ⟨first', last', ordered', a', ha', -, -, stages', φ', hφ', hheq'⟩ :=
    hlift_Ioo_core_S89 K records hscale hrc B hB (α := fun r => (K.stage (K.activeStage r)).Carrier)
      (Icc t (2 * t))
      (fun r hrs q => K.backwardSurvivorMap first last ordered (K.activeStage r)
        (stages r (hmem r hrs)).1 (stages r (hmem r hrs)).2 (φ q))
      ht0 hat (fun r hr => hat.trans hr.1) (by linarith) hb stages φ hφ
      (fun r hr hrs p hp => HEq.rfl) hneg
  exact ⟨first', last', ordered', a', ha', stages', φ', hφ', fun r hr hr0 hrI p hp =>
    eq_of_heq (hheq' r hr hrI p hp)⟩

end GC.LongTime.Ch12
