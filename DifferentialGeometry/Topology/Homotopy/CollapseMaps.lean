import DifferentialGeometry.Topology.Homotopy.OpenCollapse
import Mathlib.Topology.CompactOpen



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]


abbrev collapseConstantMaps (U : Set Y) (x : X) :=
  {f : C(Y, X) // ∀ y ∉ U, f y = x}


abbrev basedOnePointMaps (U : Set Y) (x : X) :=
  {f : C(OnePoint U, X) // f OnePoint.infty = x}


def collapseDescendValue (U : Set Y) (x : X) (f : collapseConstantMaps U x) (z : OnePoint U) : X :=
  z.elim x (fun u => f.val u)



theorem collapseDescendValue_comp (U : Set Y) (x : X) (f : collapseConstantMaps U x) (y : Y) :
    collapseDescendValue U x f (openCollapse U y) = f.val y := by
  classical
  by_cases hy : y ∈ U
  · simp only [openCollapse, dite_eq_left hy, collapseDescendValue, OnePoint.elim_some]
  · rw [openCollapse_of_notMem U hy]
    exact (f.property y hy).symm



theorem continuous_collapseDescendValue [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : X) :
    Continuous (fun z : collapseConstantMaps U x × OnePoint U =>
      collapseDescendValue U x z.1 z.2) := by
  apply (openCollapse_prod_quotient U hU hne (collapseConstantMaps U x)).continuous_iff.mpr
  have hc : Continuous (fun z : collapseConstantMaps U x × Y => z.1.val z.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  apply hc.congr
  intro z
  exact (collapseDescendValue_comp U x z.1 z.2).symm


def collapseDescend [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : X)
    (f : collapseConstantMaps U x) : basedOnePointMaps U x :=
  ⟨⟨collapseDescendValue U x f,
    (continuous_collapseDescendValue U hU hne x).comp (continuous_const.prodMk continuous_id)⟩, rfl⟩




def collapseMapsHomeomorph [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : X) :
    collapseConstantMaps U x ≃ₜ basedOnePointMaps U x where
  toFun := collapseDescend U hU hne x
  invFun f := ⟨f.val.comp ⟨openCollapse U, continuous_openCollapse U hU⟩,
    fun y hy => by
      change f.val (openCollapse U y) = x
      rw [openCollapse_of_notMem U hy, f.property]⟩
  left_inv f := by
    apply Subtype.ext
    ext y
    exact collapseDescendValue_comp U x f y
  right_inv f := by
    apply Subtype.ext
    ext z
    induction z using OnePoint.rec with
    | infty => exact f.property.symm
    | coe u =>
      change f.val (openCollapse U u) = f.val (u : OnePoint U)
      rw [openCollapse_of_mem]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_of_continuous_uncurry
    exact continuous_collapseDescendValue U hU hne x
  continuous_invFun := ((continuous_precomp
    (⟨openCollapse U, continuous_openCollapse U hU⟩ : C(Y, OnePoint U))).comp
      continuous_subtype_val).subtype_mk _

end DifferentialGeometry.Topology
