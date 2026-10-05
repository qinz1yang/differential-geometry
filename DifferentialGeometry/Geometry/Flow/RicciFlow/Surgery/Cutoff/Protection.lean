import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Neck.Historical
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure ProtectedIncomingWitness (D : OneStepIncoming.{u})
    (X : Set ↥D.slab.terminalRegularOpen) (x : ↥D.slab.terminalRegularOpen) where
  region : Set ↥D.slab.terminalRegularOpen
  region_open : IsOpen region
  x_mem : x ∈ region
  radius : ℝ
  radius_pos : 0 < radius
  buffer : Set ↥D.slab.terminalRegularOpen
  buffer_open : IsOpen buffer
  region_subset_buffer : region ⊆ buffer
  buffer_subset_core : buffer ⊆ interior X
  bufferRadius : ℝ
  bufferRadius_gt : 2 * radius < bufferRadius
  ball_compact : IsCompact (riemannianClosedBallOf D.terminal.metric x bufferRadius)
  ball_subset_buffer : riemannianClosedBallOf D.terminal.metric x bufferRadius ⊆ buffer
  scale_pos : 0 < metricScalarAt D.terminal.metric x
  scalar_comparable : ∀ y ∈ region,
    metricScalarAt D.terminal.metric x / 2 ≤ metricScalarAt D.terminal.metric y ∧
      metricScalarAt D.terminal.metric y ≤ 2 * metricScalarAt D.terminal.metric x
  neckCount : ℕ
  neckPrecision : Fin neckCount → ℝ
  neckOrder : Fin neckCount → ℕ
  neckChart : (i : Fin neckCount) → C(neckBuffer (neckPrecision i),
    ↥D.slab.terminalRegularOpen)
  neckChart_smooth : ∀ i, IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (neckChart i)
  neck_range_subset : ∀ i, Set.range (neckChart i) ⊆ buffer
  neck_backward : ∀ i, ∃ (θ : NeckCylinder → ↥D.slab.terminalRegularOpen) (h : ℝ),
    0 < h ∧ Set.range θ ⊆ buffer ∧
      Nonempty (AdaptedHistoricalNeck D θ (neckPrecision i) h (neckOrder i))

def precutCanonicalCoverage (D : OneStepIncoming.{u})
    (X : Set ↥D.slab.terminalRegularOpen) (rTest : ℝ)
    (ι : Type u) (collar : ι → Set ↥D.slab.terminalRegularOpen) : Prop :=
  ∀ x ∈ X, (rTest ^ 2)⁻¹ ≤ metricScalarAt D.terminal.metric x →
    (∃ i, x ∈ collar i) ∨ Nonempty (ProtectedIncomingWitness D X x)

def protectionInput (τ ε Λ : ℝ) : Prop :=
  ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
    (X : Set ↥D.slab.terminalRegularOpen) (rTest : ℝ)
    (collar : (c : ConnectedComponents ↥D.slab.terminalRegularOpen) →
      P.hornIndex c → Set ↥D.slab.terminalRegularOpen),
    τ ≤ D.endTime → 0 < rTest → IsCompact X →
    (∀ c, c ∈ P.component → P.core c ⊆ X) →
    (∀ x ∈ X, (∀ c, c ∈ P.component → x ∉ P.core c) →
      ∃ (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c),
        x ∈ collar c e) →
    (∀ c e, collar c e ⊆ P.core c) →
    precutCanonicalCoverage D X rTest
      ((c : ConnectedComponents ↥D.slab.terminalRegularOpen) × P.hornIndex c)
      (fun ie => collar ie.1 ie.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
