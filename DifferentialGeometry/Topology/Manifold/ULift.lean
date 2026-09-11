import DifferentialGeometry.Topology.Manifold.ClosedOriented
import Mathlib.Topology.Connected.Basic

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v uE uH

@[implicit_reducible]
def uliftChartedSpace (H : Type uH) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    ChartedSpace H (ULift.{v} M) :=
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  letI : ChartedSpace M (ULift.{v} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  ChartedSpace.comp H M (ULift.{v} M)

attribute [local instance] uliftChartedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

theorem isManifold_ulift [IsManifold I ∞ M] : IsManifold I ∞ (ULift.{v} M) := by
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  let : ChartedSpace M (ULift.{v} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  let : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  let : HasGroupoid (ULift.{v} M) (@idRestrGroupoid M _) :=
    h.toOpenPartialHomeomorph.singleton_hasGroupoid (by simp [h]) (@idRestrGroupoid M _)
  let : HasGroupoid (ULift.{v} M) (contDiffGroupoid ∞ I) :=
    StructureGroupoid.HasGroupoid.comp (G₂ := @idRestrGroupoid M _) (by
      intro f hf
      have hsmooth {a : OpenPartialHomeomorph M M}
          (ha : a ∈ @idRestrGroupoid M _) : ContMDiffOn I I ∞ a a.source := by
        rcases ha with ⟨s, hs, ha⟩
        refine contMDiffOn_id.congr ?_
        intro x hx
        have hx' := OpenPartialHomeomorph.EqOnSource.eqOn ha hx
        simpa using hx'
      rw [isLocalStructomorphOn_contDiffGroupoid_iff]
      exact ⟨hsmooth hf, by
        simpa only [mfld_simps] using hsmooth ((@idRestrGroupoid M _).symm hf)⟩)
  exact IsManifold.mk' I ∞ (ULift.{v} M)

attribute [local instance] isManifold_ulift

def uliftDiffeomorph : M ≃ₘ⟮I, I⟯ ULift.{v} M := by
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  refine
    { toEquiv := h.toEquiv.symm
      contMDiff_toFun := fun x => ?_
      contMDiff_invFun := fun x => ?_ }
  · refine contMDiffWithinAt_iff'.2 ⟨h.symm.continuous.continuousWithinAt, ?_⟩
    refine contDiff_id.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Function.comp_apply]
      change extChartAt I x ((extChartAt I x).symm y) = y
      rw [(extChartAt I x).right_inv hy.1]
    · simp
  · refine contMDiffWithinAt_iff'.2 ⟨h.continuous.continuousWithinAt, ?_⟩
    refine contDiff_id.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Function.comp_apply]
      change extChartAt I x ((extChartAt I x).symm y) = y
      rw [(extChartAt I x).right_inv hy.1]
    · simp

@[simp]
theorem uliftDiffeomorph_apply (x : M) : uliftDiffeomorph I M x = ULift.up x := rfl

@[simp]
theorem uliftDiffeomorph_symm_apply (x : ULift.{v} M) :
    (uliftDiffeomorph I M).symm x = x.down := rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] {n : ℕ}

def uliftTangentOrientation (o : ManifoldOrientation I M n) (x : ULift.{v} M) :
    Orientation ℝ (TangentSpace I x) (Fin n) :=
  Orientation.map (Fin n)
    ((uliftDiffeomorph I M).mfderivToContinuousLinearEquiv (by simp) x.down).toLinearEquiv
    (o.orientation x.down)

theorem uliftTangentOrientation_locally_constant (o : ManifoldOrientation I M n) :
    ∀ p x : ULift.{v} M,
    ∀ hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set (ULift.{v} M), IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : ULift.{v} M, ∀ hy : y ∈ U,
        Orientation.map (Fin n) (tangentChartEquiv I (ULift.{v} M) p y (hU hy))
          (uliftTangentOrientation I M o y) =
        Orientation.map (Fin n) (tangentChartEquiv I (ULift.{v} M) p x hx)
          (uliftTangentOrientation I M o x) := by
  sorry

def uliftOrientation (o : ManifoldOrientation I M n) : ManifoldOrientation I (ULift.{v} M) n where
  dimension_eq := o.dimension_eq
  orientation := uliftTangentOrientation I M o
  locally_constant := uliftTangentOrientation_locally_constant I M o

theorem uliftDiffeomorph_preservesOrientation (o : ManifoldOrientation I M n) :
    (uliftDiffeomorph I M).preservesOrientation o (uliftOrientation I M o) := by
  intro x
  rfl

namespace ClosedOrientedManifold

def ulift (M : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{max u v} n where
  Carrier := ULift.{v} M.Carrier
  orientation := uliftOrientation _ _ M.orientation

@[simp]
theorem ulift_carrier (M : ClosedOrientedManifold.{u} n) :
    (ulift.{u, v} M).Carrier = ULift.{v} M.Carrier := rfl

def uliftDiffeomorph (M : ClosedOrientedManifold.{u} n) :
    M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ (ulift.{u, v} M).Carrier :=
  DifferentialGeometry.Topology.uliftDiffeomorph _ _

theorem uliftDiffeomorph_preservesOrientation (M : ClosedOrientedManifold.{u} n) :
    (uliftDiffeomorph.{u, v} M).preservesOrientation M.orientation (ulift.{u, v} M).orientation :=
  DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation _ _ M.orientation

def uliftOrientedDiffeomorph (M : ClosedOrientedManifold.{u} n) :
    OrientedDiffeomorph M (ulift.{u, v} M) :=
  ⟨uliftDiffeomorph M, uliftDiffeomorph_preservesOrientation M⟩

end ClosedOrientedManifold

namespace ConnectedClosedOrientedManifold

def ulift (M : ConnectedClosedOrientedManifold.{u} n) :
    ConnectedClosedOrientedManifold.{max u v} n where
  toClosedOrientedManifold := ClosedOrientedManifold.ulift.{u, v} M.toClosedOrientedManifold
  connected :=
    (Homeomorph.ulift : ULift.{v} M.Carrier ≃ₜ M.Carrier).connectedSpace_iff.mpr inferInstance

@[simp]
theorem ulift_carrier (M : ConnectedClosedOrientedManifold.{u} n) :
    (ulift.{u, v} M).Carrier = ULift.{v} M.Carrier := rfl

end ConnectedClosedOrientedManifold

end DifferentialGeometry.Topology
