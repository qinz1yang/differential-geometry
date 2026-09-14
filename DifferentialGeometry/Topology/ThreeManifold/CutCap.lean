import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Icc (-2 : ℝ) 2

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

def sphereToClosedCell (z : S²) : ClosedCell 3 :=
  ⟨z.1, le_of_eq (by simpa only [Metric.mem_sphere, dist_zero_right] using z.2)⟩

structure SphericalTubeSystem (M : ClosedOrientedManifold.{u} 3) where
  Index : Type
  [finiteIndex : Fintype Index]
  tube : Index → C(Tube, M.Carrier)
  smooth : ∀ a, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (tube a)
  disjoint : Pairwise fun a b => Disjoint (range (tube a)) (range (tube b))

attribute [instance] SphericalTubeSystem.finiteIndex

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def removedBand (a : T.Index) : Set M.Carrier :=
  T.tube a '' {z : Tube | (-1 : ℝ) < z.2.1 ∧ z.2.1 < 1}

def core : Set M.Carrier := (⋃ a, T.removedBand a)ᶜ

def surgeryRegion : Set M.Carrier :=
  ⋃ a, T.tube a '' {z : Tube | (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2}

abbrev Boundary := T.Index × Bool

def boundaryLevel (side : Bool) : Icc (-2 : ℝ) 2 :=
  if side then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩

def boundarySphere (b : T.Boundary) : C(S², M.Carrier) :=
  (T.tube b.1).comp
    ⟨fun z => (z, boundaryLevel b.2), continuous_id.prodMk continuous_const⟩

theorem boundarySphere_mem_core (b : T.Boundary) (z : S²) :
    T.boundarySphere b z ∈ T.core := by
  intro h
  obtain ⟨a, y, hy, heq⟩ := by
    simpa only [core, mem_compl_iff, mem_iUnion, removedBand, mem_image] using h
  have ha : a = b.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne)
      (Set.mem_range_self y) ⟨(z, boundaryLevel b.2), heq.symm⟩
  subst a
  have hcoord := congrArg (fun q : Tube => (q.2 : ℝ))
    ((T.smooth b.1).isEmbedding.injective heq)
  rcases b with ⟨a, side⟩
  cases side <;> simp [boundaryLevel] at hcoord <;>
    rcases hy with ⟨hlo, hhi⟩ <;> linarith

def coreBoundarySphere (b : T.Boundary) : C(S², T.core) :=
  ⟨fun z => ⟨T.boundarySphere b z, T.boundarySphere_mem_core b z⟩,
    (T.boundarySphere b).continuous.subtype_mk _⟩

def outwardVector (b : T.Boundary) (z : S²) :
    TangentSpace (𝓡 3) (T.boundarySphere b z) :=
  mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (T.tube b.1)
    (z, boundaryLevel b.2)
    (0, (if b.2 then -1 else 1) • EuclideanSpace.single 0 (1 : ℝ))

end SphericalTubeSystem

structure SphericalCapping (M N : ClosedOrientedManifold.{u} 3)
    (T : SphericalTubeSystem M) where
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) T.core]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ T.core]
  core_induced : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.core → M.Carrier)
  core_compact : IsCompact T.core
  core_boundary : (𝓡∂ 3).boundary T.core = ⋃ b, range (T.coreBoundarySphere b)
  coreInclusion : C(T.core, N.Carrier)
  core_embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ coreInclusion
  cap : T.Boundary → C(ClosedCell 3, N.Carrier)
  cap_embedding : ∀ b, IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (cap b)
  attaching : T.Boundary → (S² ≃ₘ⟮𝓡 2, 𝓡 2⟯ S²)
  boundary_eq : ∀ b z,
    cap b (sphereToClosedCell z) = coreInclusion (T.coreBoundarySphere b (attaching b z))
  exhaustive : range coreInclusion ∪ (⋃ b, range (cap b)) = univ
  core_cap_intersection : ∀ b,
    range coreInclusion ∩ range (cap b) =
      range (coreInclusion.comp (T.coreBoundarySphere b))
  cap_disjoint : Pairwise fun b b' => Disjoint (range (cap b)) (range (cap b'))
  core_positive : ∀ x : T.core, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : T.core → M.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : T.core → M.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) coreInclusion x).toLinearMap hj))
        (M.orientation.orientation x.1) = N.orientation.orientation (coreInclusion x)
  cap_positive : ∀ b, ∀ x : ClosedCell 3, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (cap b x)
  boundary_orientation_reversing : ∀ b z (v w : TangentSpace (𝓡 2) z),
    let f : S² → M.Carrier := T.boundarySphere b ∘ attaching b
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) f z
    let e := mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S² → EuclideanSpace ℝ (Fin 3)) z
    (0 < ((M.orientation.orientation (f z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons (T.outwardVector b (attaching b z)) (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
        (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

structure SphericalCutCapTransition (M Q : ClosedOrientedManifold.{u} 3) where
  source_nonempty : Nonempty M.Carrier
  tubes : SphericalTubeSystem M
  capped : ClosedOrientedManifold.{u} 3
  capping : SphericalCapping M capped tubes
  discarded : ClosedOrientedManifold.{u} 3
  presentation : capped.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Q.Carrier ⊕ discarded.Carrier)
  presentation_positive : ∀ x : capped.Carrier,
    Orientation.map (Fin 3)
      (presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (capped.orientation.orientation x) =
        match presentation x with
        | Sum.inl q => Q.orientation.orientation q
        | Sum.inr d => discarded.orientation.orientation d
  every_component_meets_core : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : tubes.core, ∃ q : Q.Carrier,
      presentation (capping.coreInclusion x) = Sum.inl q ∧ ConnectedComponents.mk q = c
  retained_complement :
    (interior {q : Q.Carrier | ∃ x : tubes.core,
      presentation (capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : ClosedCell 3, presentation (capping.cap b z) = Sum.inl q}
  nontrivial : Nonempty tubes.Index ∨ Nonempty discarded.Carrier

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def retainedCore : Set E.tubes.core :=
  {x | ∃ q : Q.Carrier, E.presentation (E.capping.coreInclusion x) = Sum.inl q}

def retainedOutput (x : E.retainedCore) : Q.Carrier := Classical.choose x.2

theorem retainedOutput_eq (x : E.retainedCore) :
    E.presentation (E.capping.coreInclusion x.1) = Sum.inl (E.retainedOutput x) :=
  Classical.choose_spec x.2

theorem retainedCore_isEmpty_iff : IsEmpty E.retainedCore ↔ IsEmpty Q.Carrier := by
  constructor
  · intro h
    refine ⟨fun q => ?_⟩
    obtain ⟨x, r, hr, _⟩ := E.every_component_meets_core (ConnectedComponents.mk q)
    exact h.false ⟨x, r, hr⟩
  · intro h
    exact ⟨fun x => h.false (E.retainedOutput x)⟩

def controlledBy
    (D : (P : ClosedOrientedManifold.{u} 3) → ConnectedComponents P.Carrier → Prop) : Prop :=
  ∀ c : ConnectedComponents E.discarded.Carrier, D E.discarded c

end SphericalCutCapTransition

structure FiniteCutCapTrace where
  eventCount : ℕ
  eventCount_pos : 0 < eventCount
  stage : Fin (eventCount + 1) → ClosedOrientedManifold.{u} 3
  transition : (i : Fin eventCount) →
    SphericalCutCapTransition (stage i.castSucc) (stage i.succ)

namespace FiniteCutCapTrace

def controlledBy (T : FiniteCutCapTrace.{u})
    (D : (M : ClosedOrientedManifold.{u} 3) → ConnectedComponents M.Carrier → Prop) : Prop :=
  ∀ i : Fin T.eventCount, (T.transition i).controlledBy D

def extinct (T : FiniteCutCapTrace.{u}) : Prop :=
  IsEmpty (T.stage (Fin.last T.eventCount)).Carrier

abbrev InitialIdentification (T : FiniteCutCapTrace.{u})
    (M : ClosedOrientedManifold.{u} 3) :=
  ClosedOrientedManifold.OrientedDiffeomorph M (T.stage 0)

end FiniteCutCapTrace

end DifferentialGeometry.Topology
