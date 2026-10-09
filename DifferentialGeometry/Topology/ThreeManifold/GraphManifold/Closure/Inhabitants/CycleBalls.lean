import DifferentialGeometry.Topology.Manifold.ClosedCellChart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.StereographicClosedBall
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

/-!
Two separated actual radius-one stereographic balls in the three-sphere provide compact
smooth vertices for the explicit two-ball cycle geometry, with their native closed-cell models.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance cycleBallsDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

local instance cycleBallsConnected : ConnectedSpace (ClosedCell 3) :=
  closedCell_three_connectedSpace

def cycleBallPole : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

private def cycleBallStereo : PartialDiffeomorph (𝓡 3) (𝓡 3)
    (EuclideanSpace ℝ (Fin 3)) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞ :=
  (stereographicDiffeomorph cycleBallPole).toPartialDiffeomorph.trans
    (openSubtypePartialDiffeomorph (𝓡 3) (stereographicImage cycleBallPole)
      ⟨stereographicDiffeomorph cycleBallPole 0⟩)

def cycleBallAmbient (b : Bool) : PartialDiffeomorph (𝓡 3) (𝓡 3)
    (EuclideanSpace ℝ (Fin 3)) (NoCuts.carrier standardThreeSphereLift.{0}).Carrier ∞ :=
  (cycleBallStereo.trans (if b then sphereAntipodalDiffeomorph.toPartialDiffeomorph else
    (Diffeomorph.refl (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞)
      |>.toPartialDiffeomorph)).trans standardThreeSphereLiftDiffeomorph.toPartialDiffeomorph

theorem cycleBallAmbient_source (b : Bool) : (cycleBallAmbient b).source = univ := by
  cases b <;> apply Set.eq_univ_of_forall <;> intro x
  · exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩
  · exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩

theorem cycleBallAmbient_apply (b : Bool) (x : EuclideanSpace ℝ (Fin 3)) :
    (cycleBallAmbient b x).down =
      if b then -(stereographic' 3 cycleBallPole).symm x else
        (stereographic' 3 cycleBallPole).symm x := by
  cases b <;> rfl

private theorem cycleBallMap_eq (b : Bool) :
    closedCellChartMap (cycleBallAmbient b) 0 1 =
      fun x : ClosedCell 3 => cycleBallAmbient b x.val := by
  funext x
  change cycleBallAmbient b (0 + (1 : ℝ) • x.val) = cycleBallAmbient b x.val
  simp only [one_smul, zero_add]

private theorem cycleBallMap_smooth (b : Bool) :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (fun x : ClosedCell 3 => cycleBallAmbient b x.val) := by
  have h := contMDiff_closedCellChartMap (cycleBallAmbient b) 0 (r := 1) (by norm_num)
    (by rw [cycleBallAmbient_source]; exact subset_univ _)
  rw [cycleBallMap_eq] at h
  exact h

private theorem cycleBallMap_bijective (b : Bool) (x : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (fun y : ClosedCell 3 => cycleBallAmbient b y.val) x) := by
  have hi := injective_mfderiv_closedCellChartMap (cycleBallAmbient b) 0 (r := 1)
    (by norm_num) (by rw [cycleBallAmbient_source]; exact subset_univ _) x
  rw [cycleBallMap_eq] at hi
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

def cycleBallPiece (b : Bool) : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}) where
  Piece := ClosedCell 3
  map x := cycleBallAmbient b x.val
  smooth := cycleBallMap_smooth b
  mfderiv_bijective := cycleBallMap_bijective b
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply (cycleBallAmbient b).injOn
    · rw [cycleBallAmbient_source]
      exact mem_univ _
    · rw [cycleBallAmbient_source]
      exact mem_univ _
    · exact hxy

def cycleBallModel (b : Bool) : (cycleBallPiece b).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞

theorem cycleBallPiece_apply (b : Bool) (x : ClosedCell 3) :
    ((cycleBallPiece b).map x).down =
      if b then -(stereographic' 3 cycleBallPole).symm x.val else
        (stereographic' 3 cycleBallPole).symm x.val := cycleBallAmbient_apply b x.val

theorem cycleBall_disjoint : Disjoint (range (cycleBallPiece false).map)
    (range (cycleBallPiece true).map) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  have he := congrArg ULift.down hy
  change (cycleBallAmbient true y.val).down = (cycleBallAmbient false x.val).down at he
  rw [cycleBallAmbient_apply, cycleBallAmbient_apply] at he
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  have hm : -(stereographic' 3 cycleBallPole).symm y.val ∈
      (stereographic' 3 cycleBallPole).symm '' closedBall 0 (4 / 4) := by
    refine ⟨x.val, ?_, he.symm⟩
    simpa only [div_self (by norm_num : (4 : ℝ) ≠ 0), mem_closedBall_zero_iff] using x.property
  have hfour := (mem_antipodal_stereographic_symm_closedBall cycleBallPole
    (by norm_num : (0 : ℝ) < 4) y.val).mp hm
  linarith [y.property]

end GC.GraphManifold.Assembly
