import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapTransitionSkeleton
import DifferentialGeometry.Topology.Manifold.SphereOrientation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

private def sphereThreePoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

def sphereThreeStage : OrientedThreeStage where
  Carrier := Sphere 3
  orientation := TangentOrientationSection.ofManifoldOrientation
    (DifferentialGeometry.sphereOrientation 3 (by decide))

theorem sphereThreeStage_nonempty : Nonempty sphereThreeStage.Carrier := ⟨sphereThreePoint⟩

def standardNeckTubeIsSmoothEmbedding : Prop :=
  letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTube

theorem standardNeckTubeSystem_tube_smooth (h : standardNeckTubeIsSmoothEmbedding) :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : standardNeckTubeSystem.Index,
      IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
        (standardNeckTubeSystem.tube a) := by
  intro a
  exact h

theorem standardNeckTubeSystem_nontrivial :
    Nonempty standardNeckTubeSystem.Index ∨ Nonempty (Sphere 3) :=
  Or.inl standardNeckTubeSystem_index_nonempty

theorem standardNeckTubeSystem_boundarySpheres_disjoint :
    Disjoint (Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, false)))
      (Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, true))) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  have h' : standardNeckTubeFun (x, TubeSystem.boundaryLevel false) =
      standardNeckTubeFun (y, TubeSystem.boundaryLevel true) := hy.symm
  have h2 : (TubeSystem.boundaryLevel false : ℝ) = (TubeSystem.boundaryLevel true : ℝ) :=
    congrArg (fun z : TubeDomain => (z.2 : ℝ)) (standardNeckTubeFun_injective h')
  exact absurd h2 (by norm_num [TubeSystem.boundaryLevel])

theorem standardNeckTubeSystem_boundarySphere_ne :
    standardNeckTubeSystem.boundarySphere (PUnit.unit, false) ≠
      standardNeckTubeSystem.boundarySphere (PUnit.unit, true) := by
  intro h
  have hmem : standardNeckTubeSystem.boundarySphere (PUnit.unit, false) sphereTwoPoint ∈
      Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, true)) := by
    rw [← h]
    exact Set.mem_range_self _
  exact Set.disjoint_left.mp standardNeckTubeSystem_boundarySpheres_disjoint
    (Set.mem_range_self _) hmem

theorem standardNeckTubeSystem_core_nonempty : (standardNeckTubeSystem.core).Nonempty :=
  ⟨standardNeckTubeSystem.boundarySphere (PUnit.unit, false) sphereTwoPoint,
    TubeSystem.boundarySphere_mem_core (T := standardNeckTubeSystem) _ _⟩

theorem standardNeckTubeSystem_removedBand_ne_univ :
    standardNeckTubeSystem.removedBand PUnit.unit ≠ Set.univ := by
  intro h
  obtain ⟨x, hx⟩ := standardNeckTubeSystem_core_nonempty
  rw [TubeSystem.core, Set.mem_compl_iff] at hx
  exact hx (Set.mem_iUnion.mpr ⟨PUnit.unit, by rw [h]; exact Set.mem_univ x⟩)

local instance : ChartedSpace ThreeSpace PEmpty where
  atlas := ∅
  chartAt := fun x => PEmpty.elim x
  mem_chart_source := fun x => PEmpty.elim x
  chart_mem_atlas := fun x => PEmpty.elim x

local instance : IsManifold ThreeModel ∞ PEmpty where
  compatible := by
    intro e _ he _
    exact he.elim

private def emptyTangentOrientationSection : TangentOrientationSection PEmpty where
  orientation := fun x => PEmpty.elim x
  locally_constant := fun p => PEmpty.elim p

def emptyOrientedThreeStage : OrientedThreeStage where
  Carrier := PEmpty
  orientation := emptyTangentOrientationSection

theorem SmoothCutCapTransition.nonempty_output {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) : Nonempty N.Carrier := by
  by_cases hI : Nonempty X.trace.tubes.Index
  · obtain ⟨a⟩ := hI
    exact ⟨X.trace.capping.cap (a, false) ⟨0, by simp [ThreeBall]⟩⟩
  · have hEmpty : IsEmpty X.trace.tubes.Index := ⟨fun a => hI ⟨a⟩⟩
    have hcore : X.trace.tubes.core = Set.univ :=
      @TubeSystem.core_eq_univ_of_isEmpty _ _ X.trace.tubes hEmpty
    obtain ⟨p⟩ := X.source_nonempty
    exact ⟨X.trace.capping.coreInclusion ⟨p, by rw [hcore]; exact Set.mem_univ p⟩⟩

theorem SmoothCutCapTransition.nonempty_output_piece {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) : Nonempty Q.Carrier ∨ Nonempty D.Carrier := by
  obtain ⟨n⟩ := X.nonempty_output
  cases h : X.presentation n with
  | inl q => exact Or.inl ⟨q⟩
  | inr d => exact Or.inr ⟨d⟩

theorem not_nonempty_smoothCutCapTransition_of_isEmpty_pieces
    {P Q D N : OrientedThreeStage.{u}} (hQ : IsEmpty Q.Carrier) (hD : IsEmpty D.Carrier) :
    ¬ Nonempty (SmoothCutCapTransition P Q D N) := by
  rintro ⟨X⟩
  rcases X.nonempty_output_piece with h | h
  · exact hQ.false h.some
  · exact hD.false h.some

theorem not_nonempty_smoothCutCapTransition_empty_output (P N : OrientedThreeStage.{0}) :
    ¬ Nonempty (SmoothCutCapTransition P emptyOrientedThreeStage emptyOrientedThreeStage N) :=
  not_nonempty_smoothCutCapTransition_of_isEmpty_pieces PEmpty.instIsEmpty PEmpty.instIsEmpty

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
