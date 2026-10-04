import DifferentialGeometry.Topology.Manifold.HalfSpaceInteriorChart
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProdLeft

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.Manifold

private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)


def halfSpaceThreeSplit : E3 ≃L[ℝ] ℝ × E2 :=
  EuclideanSpace.finAddEquivProd.trans
    ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ E2))


def halfSpaceThreeInteriorChart (a : ℝ) : OpenPartialHomeomorph E3 (EuclideanHalfSpace 3) :=
  (halfSpaceThreeSplit.toHomeomorph.toOpenPartialHomeomorph.trans
    ((halfSpaceInteriorChart a).prod (OpenPartialHomeomorph.refl E2))).trans
      (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph 0 2).toOpenPartialHomeomorph

theorem halfSpaceThreeInteriorChart_mem_source (a : ℝ) (x : E3) :
    x ∈ (halfSpaceThreeInteriorChart a).source ↔ a < (halfSpaceThreeSplit x).1 := by
  simp only [halfSpaceThreeInteriorChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, preimage_univ, inter_univ, univ_inter,
    halfSpaceInteriorChart, mem_preimage, mem_prod, mem_Ioi, mem_univ, and_true]
  rfl

theorem halfSpaceThreeInteriorChart_height (a : ℝ) (x : E3)
    (hx : a < (halfSpaceThreeSplit x).1) :
    (halfSpaceThreeInteriorChart a x).val 0 = (halfSpaceThreeSplit x).1 - a := by
  change (halfSpaceInteriorChart a (halfSpaceThreeSplit x).1).val 0 = _
  exact halfSpaceInteriorChart_apply a _ hx


def halfSpaceThreeInteriorOffset (R : ℝ) : ℝ := -‖halfSpaceThreeSplit.toContinuousLinearMap‖ * R - 1

theorem halfSpaceThreeInteriorOffset_lt {R : ℝ} {x : E3} (hx : ‖x‖ ≤ R) :
    halfSpaceThreeInteriorOffset R < (halfSpaceThreeSplit x).1 := by
  have hnorm : ‖(halfSpaceThreeSplit x).1‖ ≤
      ‖halfSpaceThreeSplit.toContinuousLinearMap‖ * R :=
    (norm_fst_le _).trans (halfSpaceThreeSplit.toContinuousLinearMap.le_opNorm_of_le hx)
  have hneg := neg_abs_le (halfSpaceThreeSplit x).1
  rw [Real.norm_eq_abs] at hnorm
  unfold halfSpaceThreeInteriorOffset
  linarith

theorem halfSpaceThreeInteriorChart_bounded_height {R : ℝ} {x : E3} (hx : ‖x‖ ≤ R) :
    1 ≤ (halfSpaceThreeInteriorChart (halfSpaceThreeInteriorOffset R) x).val 0 := by
  rw [halfSpaceThreeInteriorChart_height _ _ (halfSpaceThreeInteriorOffset_lt hx)]
  have hnorm : ‖(halfSpaceThreeSplit x).1‖ ≤
      ‖halfSpaceThreeSplit.toContinuousLinearMap‖ * R :=
    (norm_fst_le _).trans (halfSpaceThreeSplit.toContinuousLinearMap.le_opNorm_of_le hx)
  have hneg := neg_abs_le (halfSpaceThreeSplit x).1
  rw [Real.norm_eq_abs] at hnorm
  unfold halfSpaceThreeInteriorOffset
  linarith


theorem halfSpaceThreeInteriorChart_trans_source {Q : Type*} [TopologicalSpace Q]
    (e : OpenPartialHomeomorph Q E3) (R : ℝ) (hR : ∀ x ∈ e.target, ‖x‖ ≤ R) :
    (e.trans (halfSpaceThreeInteriorChart (halfSpaceThreeInteriorOffset R))).source =
      e.source := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx, (halfSpaceThreeInteriorChart_mem_source _ _).mpr
      (halfSpaceThreeInteriorOffset_lt (hR _ (e.map_source hx)))⟩

end DifferentialGeometry.Topology.Manifold
