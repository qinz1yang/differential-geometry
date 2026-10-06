import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonBase
import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CompactTypeMetric74
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause

/-!
# Draft 74, G32: the compact-model branch is a selected closed core

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. On the whole source (`A = univ`), LPA05's
`CompactModelSublevel` gives an oriented diffeomorphism `Φ : X ≃ P` onto a closed connected
oriented three-manifold of one of LFR53's four types. The closed branch of `SelectedSmoothCore74`
is then inhabited: the piece is the whole carrier `P` with the boundary charts of the constant
sublevel (`FC39P0.X136.WholeCarrier P`, empty model boundary), the map is `Φ⁻¹ ∘ val`
(a smooth embedding: the EASY cross-model kernel `diffeomorph_comp_fromHalfSpace_OCX` applied
to `wholeDiffeomorph P` and `id`), and the metric of `sec ≥ 0` is the canonical metric of the
type (`exists_nonneg_metric_of_isCompactNonnegativeType74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse
open GC.GraphManifold.Assembly.FC39P0.X136

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- The inclusion of the whole carrier with its boundary charts is a smooth embedding into the
carrier. -/
theorem wholeCarrier_val_isSmoothEmbedding74 (P : ConnectedClosedOrientedManifold.{0} 3) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : WholeCarrier P → P.Carrier) := by
  have hid : IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞ (id : WholeCarrier P → WholeCarrier P) :=
    IsSmoothEmbedding.id
  let e : WholeCarrier P ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ P.Carrier := wholeDiffeomorph P
  have h := Manifold.IsSmoothEmbedding.diffeomorph_comp_fromHalfSpace_OCX hid e
  have hfun : (⇑e ∘ id) = (Subtype.val : WholeCarrier P → P.Carrier) := funext fun y =>
    (wholePiece P).diffeomorphOfRangeEqUniv_apply (wholePiece_range P) y
  rwa [hfun] at h

/-- **The solid parametrization of a closed core**: the whole carrier of the closed type `P`,
carried back to `X` by a diffeomorphism. -/
def SolidParam74.ofClosedDiffeo74 {X : Type} [TopologicalSpace X] [ChartedSpace E3 X]
    [IsManifold I3 ∞ X] (P : ConnectedClosedOrientedManifold.{0} 3) (Φ : X ≃ₘ⟮I3, I3⟯ P.Carrier) :
    SolidParam74.{0, 0} (univ : Set X) where
  Piece := WholeCarrier P
  param := fun y => Φ.symm y.1
  embedding := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (𝓡∂ 3) (𝓡 3) (Subtype.val : WholeCarrier P → P.Carrier)
    (wholeCarrier_val_isSmoothEmbedding74 P) Φ.symm
  range_eq := by
    refine eq_univ_of_forall fun x => ⟨(wholeHomeomorph P).symm (Φ x), ?_⟩
    change Φ.symm (Φ x) = x
    exact Φ.symm_apply_apply x

/-- **The compact-model branch is a selected closed core.** -/
theorem nonempty_selectedCore74_ofCompactModel {X : Type} [TopologicalSpace X]
    [ChartedSpace E3 X] [IsManifold I3 ∞ X] {oM : ManifoldOrientation I3 X 3} {Nc : Type}
    [TopologicalSpace Nc] [ChartedSpace E3 Nc] {A : Set X} (h : CompactModelSublevel oM Nc A) :
    Nonempty (SelectedSmoothCore74.{0, 0} A) := by
  obtain ⟨hA, -, -, P, hP, Φ, -⟩ := h
  subst hA
  obtain ⟨g, hg⟩ := exists_nonneg_metric_of_isCompactNonnegativeType74 P hP
  exact ⟨.closed (SolidParam74.ofClosedDiffeo74 P Φ) P g hg (wholeDiffeomorph P)
    (wholePiece_boundary P)⟩

end GC.GraphManifold.Assembly
