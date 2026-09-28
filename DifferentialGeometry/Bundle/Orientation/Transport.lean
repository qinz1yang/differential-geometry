import DifferentialGeometry.Bundle.Orientation.Classes
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Basic.Real.Sign



noncomputable section
open scoped Topology
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X]


@[instance_reducible]
def orientationTopology : TopologicalSpace (Orientation ℝ V (Fin n)) := ⊥

attribute [local instance] orientationTopology
local instance : DiscreteTopology (Orientation ℝ V (Fin n)) := ⟨rfl⟩

omit [FiniteDimensional ℝ V] in
theorem isLocallyConstant_det_sign (A : X → V ≃L[ℝ] V)
    (hA : Continuous (fun x => (A x : V →L[ℝ] V))) :
    IsLocallyConstant (fun x => Real.sign (A x : V →L[ℝ] V).det) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hd := (ContinuousLinearMap.continuous_det.comp hA).continuousAt (x := x)
  rcases lt_or_gt_of_ne ((A x).toLinearEquiv.isUnit_det'.ne_zero) with hn | hp
  · exact (hd.eventually_lt_const hn).mono
      (fun y hy => (Real.sign_of_neg hy).trans (Real.sign_of_neg hn).symm)
  · exact (hd.eventually_const_lt hp).mono
      (fun y hy => (Real.sign_of_pos hy).trans (Real.sign_of_pos hp).symm)

theorem continuous_orientation_transport (hdim : Module.finrank ℝ V = n)
    (A : X → V ≃L[ℝ] V) (hA : Continuous (fun x => (A x : V →L[ℝ] V))) :
    Continuous (fun z : X × Orientation ℝ V (Fin n) =>
      Orientation.map (Fin n) (A z.1).toLinearEquiv z.2) := by
  have hdet : Continuous (fun z : X × Orientation ℝ V (Fin n) =>
      (A z.1 : V →L[ℝ] V).det) :=
    (ContinuousLinearMap.continuous_det.comp hA).comp continuous_fst
  rw [continuous_iff_continuousAt]
  intro z
  have hne : (A z.1 : V →L[ℝ] V).det ≠ 0 :=
    (A z.1).toLinearEquiv.isUnit_det'.ne_zero
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hn : ∀ᶠ w in 𝓝 z, (A w.1 : V →L[ℝ] V).det < 0 :=
      hdet.continuousAt.eventually_lt_const hneg
    apply ((continuous_of_discreteTopology : Continuous (fun o : Orientation ℝ V (Fin n) => -o)).comp continuous_snd).continuousAt.congr_of_eventuallyEq
    exact hn.mono (fun w hw =>
      ((w.2).map_eq_neg_iff_det_neg (A w.1).toLinearEquiv (by simpa using hdim.symm)).mpr hw)
  · have hp : ∀ᶠ w in 𝓝 z, 0 < (A w.1 : V →L[ℝ] V).det :=
      hdet.continuousAt.eventually_const_lt hpos
    apply continuous_snd.continuousAt.congr_of_eventuallyEq
    exact hp.mono (fun w hw => (map_orientation_eq_iff hdim w.2 (A w.1).toLinearEquiv).mpr hw)


theorem continuousOn_orientation_transport (hdim : Module.finrank ℝ V = n)
    (A : X → V ≃L[ℝ] V) {s : Set X}
    (hA : ContinuousOn (fun x => (A x : V →L[ℝ] V)) s) :
    ContinuousOn (fun z : X × Orientation ℝ V (Fin n) =>
      Orientation.map (Fin n) (A z.1).toLinearEquiv z.2) (s ×ˢ Set.univ) := by
  have hA' := continuousOn_iff_continuous_domRestrict.mp hA
  have h := continuous_orientation_transport hdim (fun x : s => A x) hA'
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun z : s ×ˢ (Set.univ : Set (Orientation ℝ V (Fin n))) =>
      (⟨z.val.1, z.property.1⟩, z.val.2) :
        s ×ˢ (Set.univ : Set (Orientation ℝ V (Fin n))) → s × Orientation ℝ V (Fin n)) :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  convert h.comp hc using 1
  rfl

end DifferentialGeometry.VectorBundle
