import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CoOrientedNeckChainReflection

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

def cylinderAxialReflectionShift (c : ℝ) : PartialDiffeomorph IC IC Cylinder Cylinder ∞ :=
  cylinderAxialReflection.trans (cylinderAxialShift c)

theorem cylinderAxialReflectionShift_source (c : ℝ) :
    (cylinderAxialReflectionShift c).source = Set.univ := by
  rw [cylinderAxialReflectionShift, PartialDiffeomorph.trans_source]
  simp [cylinderAxialReflection, cylinderAxialShift]

@[simp]
theorem cylinderAxialReflectionShift_apply (c : ℝ) (y : Cylinder) :
    cylinderAxialReflectionShift c y = (y.1, c - y.2) := by
  rw [cylinderAxialReflectionShift, PartialDiffeomorph.trans_apply,
    cylinderAxialReflection_apply]
  simp only [cylinderAxialShift, sub_eq_add_neg, add_comm]

theorem cylinderAxialReflectionShift_symm_apply (c : ℝ) (y : Cylinder) :
    (cylinderAxialReflectionShift c).symm y = (y.1, c - y.2) := by
  have hy : (y.1, y.2 - c) ∈ (cylinderAxialShift c).source := trivial
  have h := PartialDiffeomorph.trans_symm_apply cylinderAxialReflection
    (cylinderAxialShift c) hy
  have hshift : (cylinderAxialShift c) (y.1, y.2 - c) = y := by
    apply Prod.ext
    · rfl
    · simp only [cylinderAxialShift]
      ring
  have hrefl : cylinderAxialReflection.symm (y.1, y.2 - c) = (y.1, c - y.2) := by
    rw [cylinderAxialReflection_symm_apply]
    apply Prod.ext
    · rfl
    · ring
  rw [hshift, hrefl] at h
  simpa [cylinderAxialReflectionShift] using h

theorem cylinderAxialReflectionShift_fiberPreserving (c : ℝ) :
    CylinderFiberPreserving (cylinderAxialReflectionShift c) := by
  intro y a
  rw [cylinderAxialReflectionShift_apply, cylinderAxialReflectionShift_apply]

theorem cylinderAxialReflectionShift_symm_fiberPreserving (c : ℝ) :
    CylinderFiberPreserving (cylinderAxialReflectionShift c).symm := by
  intro y a
  rw [cylinderAxialReflectionShift_symm_apply, cylinderAxialReflectionShift_symm_apply]

theorem cylinderAxialReflectionShift_axial_fderiv (c : ℝ) (y : Cylinder) :
    fderiv ℝ (fun a : ℝ => (cylinderAxialReflectionShift c (y.1, a)).2) y.2 1 = -1 := by
  have h : (fun a : ℝ => (cylinderAxialReflectionShift c (y.1, a)).2) = fun a : ℝ => c - a := by
    funext a
    rw [cylinderAxialReflectionShift_apply]
  rw [h]
  simp

theorem not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift (c : ℝ) :
    ¬ CylinderAxiallyIncreasing (cylinderAxialReflectionShift c) := by
  intro h
  have hpos := h (DifferentialGeometry.Topology.sphereTwoNorth, (0 : ℝ))
    (by rw [cylinderAxialReflectionShift_source]; exact Set.mem_univ _)
  rw [cylinderAxialReflectionShift_axial_fderiv] at hpos
  norm_num at hpos

theorem not_cylinderCoOriented_cylinderAxialReflectionShift (c : ℝ) :
    ¬ CylinderCoOriented (cylinderAxialReflectionShift c) :=
  fun h => not_cylinderAxiallyIncreasing_cylinderAxialReflectionShift c h.2.2

theorem cylinderAxialReflectionShift_trans_reflection_apply (c : ℝ) (y : Cylinder) :
    (cylinderAxialReflectionShift c).trans cylinderAxialReflection y =
      cylinderAxialShift (-c) y := by
  rw [PartialDiffeomorph.trans_apply, cylinderAxialReflectionShift_apply,
    cylinderAxialReflection_apply]
  apply Prod.ext
  · rfl
  · simp only [cylinderAxialShift]
    ring

theorem cylinderAxialReflectionShift_zero (y : Cylinder) :
    cylinderAxialReflectionShift 0 y = cylinderAxialReflection y := by
  rw [cylinderAxialReflectionShift_apply, cylinderAxialReflection_apply]
  simp

omit [T2Space M] [SigmaCompactSpace M] in
theorem LocalCap.isCompact_tube {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ} {U : Set M}
    (L : LocalCap S eps x t U) : IsCompact L.tube := by
  rw [← L.tube_eq]
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (L.tube_map.contMDiffOn_toFun.continuousOn.mono L.tube_domain)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {D : OneStepIncoming.{u}}

private theorem not_isCompact_Ici_zero : ¬ IsCompact (Set.Ici (0 : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (Metric.isCompact_iff_isClosed_bounded.mp h).2
  have h1 : |C| + 1 ≤ C := by
    have h2 := hC (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ |C| + 1))
    have h3 : dist (0 : ℝ) (|C| + 1) = |C| + 1 := by
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    rwa [h3] at h2
  have hCnonneg : 0 ≤ C := by linarith [abs_nonneg C]
  rw [abs_of_nonneg hCnonneg] at h1
  linarith

theorem not_isCompact_univ_halfNeckCylinder : ¬ IsCompact (Set.univ : Set HalfNeckCylinder) := by
  intro h
  have himage : IsCompact (Set.range fun p : HalfNeckCylinder => p.1.2) := by
    simpa [Set.image_univ] using h.image continuous_subtype_val.snd
  have hrange : Set.range (fun p : HalfNeckCylinder => p.1.2) = Set.Ici (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2
    · intro ht
      exact ⟨⟨(DifferentialGeometry.Topology.sphereTwoNorth, t), ht⟩, rfl⟩
  rw [hrange] at himage
  exact not_isCompact_Ici_zero himage

theorem TerminalCorePresentation.horn_range_not_isCompact {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    ¬ IsCompact (Set.range fun p : HalfNeckCylinder => P.horn c e p.1) := by
  intro hcomp
  have hpre := (P.horn_proper c e).isCompact_preimage hcomp
  rw [Set.preimage_range] at hpre
  exact not_isCompact_univ_halfNeckCylinder hpre

theorem AdaptedHistoricalNeck.chart_apply_reflectionShift
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen} {d h : ℝ} {k : ℕ}
    (A : AdaptedHistoricalNeck D horn d h k) (p : neckBuffer d) :
    A.chart (cylinderAxialReflectionShift A.shift p.1) = A.neck.chart p := by
  rw [cylinderAxialReflectionShift_apply]
  exact A.chart_eq_neck p

theorem TerminalCorePresentation.component_eq_empty_of_forall_not_low {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (h : ∀ x : ↥D.slab.terminalRegularOpen,
      ¬ metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹) :
    P.component = ∅ := by
  ext c
  constructor
  · intro hc
    obtain ⟨x, -, hx⟩ := (P.component_iff_meets_low c).mp hc
    exact absurd hx (h x)
  · intro hc
    exact hc.elim

theorem TerminalCorePresentation.core_eq_componentSet_of_isEmpty_hornIndex {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    (h : IsEmpty (P.hornIndex c)) :
    P.core c = {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} := by
  rw [P.horn_covers_component c hc, Set.iUnion_of_empty, Set.union_empty]

theorem TerminalCorePresentation.core_eq_componentSet_or_hornIndex_nonempty {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component) :
    P.core c = {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} ∨
      Nonempty (P.hornIndex c) := by
  by_cases h : Nonempty (P.hornIndex c)
  · exact Or.inr h
  · exact Or.inl (P.core_eq_componentSet_of_isEmpty_hornIndex hc ⟨fun a => h ⟨a⟩⟩)

theorem TerminalCorePresentation.coreRadius_inv_sq_lt_scalar_of_not_mem_core {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    {x : ↥D.slab.terminalRegularOpen} (hxc : ConnectedComponents.mk x = c)
    (hx : x ∉ P.core c) :
    (P.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x := by
  apply lt_of_not_ge
  intro h
  exact hx (interior_subset (P.low_mem_interior_core c hc x hxc h))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
