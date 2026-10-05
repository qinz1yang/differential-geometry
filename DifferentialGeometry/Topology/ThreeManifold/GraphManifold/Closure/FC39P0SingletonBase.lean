import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySublevelPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ClosedPieces

/-!
The whole closed carrier as the constant-negative regular sublevel, with its genuine boundary
model atlas. This shared geometric helper serves the two separate X136 singleton fixtures.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

def wholeFunction (Q : ConnectedClosedOrientedManifold.{0} 3) : Q.Carrier → ℝ :=
  Function.const Q.Carrier (-1)

abbrev WholeCarrier (Q : ConnectedClosedOrientedManifold.{0} 3) :=
  {x : Q.Carrier // wholeFunction Q x ≤ 0}

theorem wholeFunction_smooth (Q : ConnectedClosedOrientedManifold.{0} 3) :
    ContMDiff (NoCuts.carrier Q).model 𝓘(ℝ, ℝ) ∞ (wholeFunction Q) :=
  contMDiff_const

theorem wholeFunction_regular (Q : ConnectedClosedOrientedManifold.{0} 3) :
    ∀ x, wholeFunction Q x = 0 →
      mfderiv (NoCuts.carrier Q).model 𝓘(ℝ, ℝ) (wholeFunction Q) x ≠ 0 := by
  intro x hx
  norm_num [wholeFunction, Function.const] at hx

theorem wholeFunction_interior (Q : ConnectedClosedOrientedManifold.{0} 3) :
    ∀ x, wholeFunction Q x = 0 → x ∈ (NoCuts.carrier Q).interior := by
  intro x hx
  norm_num [wholeFunction, Function.const] at hx

instance wholeChartedSpace (Q : ConnectedClosedOrientedManifold.{0} 3) :
    ChartedSpace (EuclideanHalfSpace 3) (WholeCarrier Q) :=
  carrierSublevelChartedSpace (NoCuts.carrier Q) (wholeFunction Q) 0
    (wholeFunction_smooth Q) (wholeFunction_regular Q) (wholeFunction_interior Q)

instance wholeIsManifold (Q : ConnectedClosedOrientedManifold.{0} 3) :
    IsManifold (𝓡∂ 3) ∞ (WholeCarrier Q) :=
  carrierSublevel_isManifold (NoCuts.carrier Q) (wholeFunction Q) 0
    (wholeFunction_smooth Q) (wholeFunction_regular Q) (wholeFunction_interior Q)

def wholeHomeomorph (Q : ConnectedClosedOrientedManifold.{0} 3) :
    WholeCarrier Q ≃ₜ Q.Carrier where
  toFun := Subtype.val
  invFun x := ⟨x, by norm_num [wholeFunction, Function.const]⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk (by simp [wholeFunction, Function.const])

instance wholeCompactSpace (Q : ConnectedClosedOrientedManifold.{0} 3) :
    CompactSpace (WholeCarrier Q) :=
  compactSpace_carrierSublevel (NoCuts.carrier Q) (wholeFunction Q) 0 continuous_const

instance wholeConnectedSpace (Q : ConnectedClosedOrientedManifold.{0} 3) :
    ConnectedSpace (WholeCarrier Q) :=
  (wholeHomeomorph Q).connectedSpace_iff.mpr inferInstance

instance wholeSecondCountable (Q : ConnectedClosedOrientedManifold.{0} 3) :
    SecondCountableTopology (WholeCarrier Q) := by
  let : SecondCountableTopology Q.Carrier := (NoCuts.carrier Q).secondCountable
  exact TopologicalSpace.Subtype.secondCountableTopology {x : Q.Carrier | wholeFunction Q x ≤ 0}

def wholePiece (Q : ConnectedClosedOrientedManifold.{0} 3) :
    PieceEmbedding (NoCuts.carrier Q) where
  Piece := WholeCarrier Q
  map := Subtype.val
  smooth := carrierSublevel_contMDiff_val (NoCuts.carrier Q) (wholeFunction Q) 0
    (wholeFunction_smooth Q) (wholeFunction_regular Q) (wholeFunction_interior Q)
  mfderiv_bijective := carrierSublevel_mfderiv_val_bijective (NoCuts.carrier Q)
    (wholeFunction Q) 0 (wholeFunction_smooth Q) (wholeFunction_regular Q)
    (wholeFunction_interior Q)
  injective := Subtype.val_injective

theorem wholePiece_range (Q : ConnectedClosedOrientedManifold.{0} 3) :
    range (wholePiece Q).map = univ := by
  apply range_eq_univ.mpr
  intro x
  exact ⟨⟨x, by norm_num [wholeFunction, Function.const]⟩, rfl⟩

theorem wholePiece_boundary (Q : ConnectedClosedOrientedManifold.{0} 3) :
    (𝓡∂ 3).boundary (wholePiece Q).Piece = ∅ := by
  apply eq_empty_of_forall_notMem
  intro x hx
  have hb := (carrierSublevel_isBoundaryPoint_iff (wholeFunction_smooth Q)
    (wholeFunction_regular Q) (wholeFunction_interior Q)).mp hx
  rcases hb with hb | hz
  · have hclosed := closedCarrier_boundary_eq_empty Q
    have hb' : x.val ∈ (NoCuts.carrier Q).model.boundary Q.Carrier := hb
    rw [hclosed] at hb'
    exact hb'.elim
  · norm_num [wholeFunction, Function.const] at hz

def wholeDiffeomorph (Q : ConnectedClosedOrientedManifold.{0} 3) :
    (wholePiece Q).Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Q.Carrier :=
  (wholePiece Q).diffeomorphOfRangeEqUniv (wholePiece_range Q)

end GC.GraphManifold.Assembly.FC39P0.X136
