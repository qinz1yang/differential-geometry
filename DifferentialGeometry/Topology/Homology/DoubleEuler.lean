import DifferentialGeometry.Topology.Double.SideHomotopy
import DifferentialGeometry.Topology.Double.Reflection
import DifferentialGeometry.Topology.Homeomorph.HeightBand
import DifferentialGeometry.Topology.Homology.OpenCover
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace DifferentialGeometry.Homology
open DifferentialGeometry.Topology

theorem finiteHomologyType_and_eulerChar_double_of_collar
    {X : Type} [TopologicalSpace X]
    (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hn : ∀ x, 0 ≤ r x) (hz : ∀ x, r x = 0 → x ∈ B)
    {ε : ℝ} (hε : 0 < ε)
    (s : B × Ioo (-ε) ε ≃ₜ {z : Double B | |doubleHeight B r hr z| < ε})
    (hs : ∀ q, doubleHeight B r hr (s q).val = q.2.val)
    (K : Type) [Field K]
    (hfX : finiteHomologyType K (TopCat.of X))
    (hfB : finiteHomologyType K (TopCat.of B)) :
    finiteHomologyType K (TopCat.of (Double B)) ∧
      eulerChar K (TopCat.of (Double B)) =
        2 * eulerChar K (TopCat.of X) - eulerChar K (TopCat.of B) := by
  let a := ε / 2
  have ha : 0 < a := half_pos hε
  have haε : a < ε := half_lt_self hε
  let h := doubleHeight B r hr
  let D := TopCat.of (Double B)
  let U : Set D := {z | -a < h z}
  let V : Set D := {z | h z < a}
  have hU : IsOpen U := isOpen_lt continuous_const h.continuous
  have hV : IsOpen V := isOpen_lt h.continuous continuous_const
  have hcover : U ∪ V = univ := by
    apply eq_univ_of_forall
    intro z
    change -a < h z ∨ h z < a
    by_cases hz' : -a < h z
    · exact Or.inl hz'
    · exact Or.inr (by linarith)
  obtain ⟨eU⟩ := exists_doublePositive_neighborhood_homotopyEquiv B r hr hn hz ha haε s hs
  let eUV : U ≃ₜ V := (doubleReflection B).subtype (fun z => by
    change -a < h z ↔ h (doubleReflection B z) < a
    change -a < doubleHeight B r hr z ↔ doubleHeight B r hr (doubleReflection B z) < a
    rw [doubleHeight_reflection]
    constructor <;> intro hlt <;> linarith)
  let eV : ContinuousMap.HomotopyEquiv V X := eUV.symm.toHomotopyEquiv.trans eU
  have hinter : U ∩ V = {z : Double B | |h z| < a} := by
    ext z
    change (-a < h z ∧ h z < a) ↔ |h z| < a
    exact abs_lt.symm
  let band := heightBandHomeomorph h haε.le s hs
  let _ : ContractibleSpace (Ioo (-a) a) := (convex_Ioo (-a) a).contractibleSpace
    ⟨0, neg_lt_zero.mpr ha, ha⟩
  obtain ⟨eT⟩ := ContractibleSpace.hequiv_unit (Ioo (-a) a)
  let eProd : ContinuousMap.HomotopyEquiv (B × Ioo (-a) a) B :=
    ((ContinuousMap.HomotopyEquiv.refl B).prodCongr eT).trans
      (Homeomorph.prodUnique B Unit).toHomotopyEquiv
  let eI : ContinuousMap.HomotopyEquiv (U ∩ V : Set D) B :=
    ((Homeomorph.setCongr hinter).trans band.symm).toHomotopyEquiv.trans eProd
  have hfU := (finiteHomologyType_iff_of_homotopyEquiv K
    (X := TopCat.of U) (Y := TopCat.of X) eU).mpr hfX
  have hfV := (finiteHomologyType_iff_of_homotopyEquiv K
    (X := TopCat.of V) (Y := TopCat.of X) eV).mpr hfX
  have hfI := (finiteHomologyType_iff_of_homotopyEquiv K
    (X := TopCat.of (U ∩ V : Set D)) (Y := TopCat.of B) eI).mpr hfB
  refine ⟨finiteHomologyType_of_openCover D U V K hU hV hcover hfU hfV hfI, ?_⟩
  have he := eulerChar_openCover D U V K hU hV hcover hfU hfV hfI
  rw [eulerChar_eq_of_homotopyEquiv K (X := TopCat.of U) (Y := TopCat.of X) eU,
    eulerChar_eq_of_homotopyEquiv K (X := TopCat.of V) (Y := TopCat.of X) eV,
    eulerChar_eq_of_homotopyEquiv K (X := TopCat.of (U ∩ V : Set D)) (Y := TopCat.of B) eI] at he
  linarith

end DifferentialGeometry.Homology
