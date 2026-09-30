import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Terminal.Incoming
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

abbrev HalfNeckCylinder := {p : NeckCylinder // 0 ≤ p.2}

structure TerminalCorePresentation (D : OneStepIncoming.{u}) (ε Λ : ℝ) where
  epsilon_pos : 0 < ε
  Lambda_ge_one : 1 ≤ Λ
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_eq : coreRadius =
    D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  component : Set (ConnectedComponents ↥D.slab.terminalRegularOpen)
  component_finite : component.Finite
  core : ConnectedComponents ↥D.slab.terminalRegularOpen →
    Set ↥D.slab.terminalRegularOpen
  core_isCompact : ∀ c ∈ component, IsCompact (core c)
  core_isConnected : ∀ c ∈ component, IsConnected (core c)
  core_empty : ∀ c, c ∉ component → core c = ∅
  coreCharts : ∀ c, c ∈ component → ChartedSpace (EuclideanHalfSpace 3) (core c)
  core_smooth : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    IsManifold (𝓡∂ 3) ∞ (core c)
  core_induced : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (Subtype.val : core c → ↥D.slab.terminalRegularOpen)
  core_interior_eq : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    (Subtype.val : core c → ↥D.slab.terminalRegularOpen) ''
      (𝓡∂ 3).interior (core c) = interior (core c)
  core_boundary_eq : ∀ c (hc : c ∈ component),
    letI := coreCharts c hc
    (Subtype.val : core c → ↥D.slab.terminalRegularOpen) ''
      (𝓡∂ 3).boundary (core c) = frontier (core c)
  component_iff_meets_low : ∀ c : ConnectedComponents ↥D.slab.terminalRegularOpen,
    c ∈ component ↔ ∃ x : ↥D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
      metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹
  low_mem_interior_core : ∀ c ∈ component, ∀ x : ↥D.slab.terminalRegularOpen,
    ConnectedComponents.mk x = c →
    metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹ →
      x ∈ interior (core c)
  hornIndex : ConnectedComponents ↥D.slab.terminalRegularOpen → Type u
  hornIndex_finite : ∀ c, Finite (hornIndex c)
  hornIndex_empty : ∀ c, c ∉ component → IsEmpty (hornIndex c)
  horn : ∀ c, hornIndex c → NeckCylinder → ↥D.slab.terminalRegularOpen
  horn_smooth : ∀ c e, ContMDiffOn NeckCylinderModel ThreeModel ∞ (horn c e)
    (Set.univ ×ˢ Set.Ici (0 : ℝ))
  horn_interior_embedding : ∀ c e,
    let U : TopologicalSpace.Opens NeckCylinder :=
      ⟨Set.univ ×ˢ Set.Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (fun p : U => horn c e p)
  horn_injOn : ∀ c e, Set.InjOn (horn c e) (Set.univ ×ˢ Set.Ici (0 : ℝ))
  horn_proper : ∀ c e, IsProperMap fun p : HalfNeckCylinder => horn c e p.1
  horn_range_disjoint : ∀ c e e', e ≠ e' →
    Disjoint (Set.range fun p : HalfNeckCylinder => horn c e p.1)
      (Set.range fun p : HalfNeckCylinder => horn c e' p.1)
  horn_meets_core : ∀ c e,
    (Set.range fun p : HalfNeckCylinder => horn c e p.1) ∩ core c =
      Set.range fun y : Sphere 2 => horn c e (y, 0)
  horn_base_covers_boundary : ∀ c ∈ component,
    frontier (core c) = ⋃ e : hornIndex c, Set.range fun y : Sphere 2 => horn c e (y, 0)
  hornCollar : ∀ c (e : hornIndex c),
    SmoothTwoSidedCollar (𝓡 2) ThreeModel (fun y : Sphere 2 => horn c e (y, 0))
  horn_collar_core_side : ∀ c e (p : Sphere 2 × symmetricOpenInterval (hornCollar c e).radius),
    (hornCollar c e).toFun p ∈ core c ↔ (p.2 : ℝ) ≤ 0
  horn_collar_eq : ∀ c e (p : Sphere 2 × symmetricOpenInterval (hornCollar c e).radius),
    0 ≤ (p.2 : ℝ) → (hornCollar c e).toFun p = horn c e (p.1, p.2)
  horn_covers_component : ∀ c ∈ component,
    {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} =
      core c ∪ ⋃ e : hornIndex c, Set.range fun p : HalfNeckCylinder => horn c e p.1
  horn_scalar_large : ∀ c e y u, 0 ≤ u →
    (coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric (horn c e (y, u))
  horn_base_scalar : ∀ c e y,
    metricScalarAt D.terminal.metric (horn c e (y, 0)) ≤ Λ * (coreRadius ^ 2)⁻¹
  horn_scalar_diverges : ∀ (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : hornIndex c) (L : ℝ), ∃ u_L : ℝ, ∀ y u, u_L ≤ u →
    L < metricScalarAt D.terminal.metric (horn c e (y, u))
  horn_spatial_neck : ∀ (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : hornIndex c) (x : ↥D.slab.terminalRegularOpen),
    x ∈ interior (Set.range fun p : HalfNeckCylinder => horn c e p.1) →
    ∃ (δ : ℝ) (k : ℕ) (neck : NormalizedNeck D.terminal.metric δ k),
      neck.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
