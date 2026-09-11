import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem endpoint_derivatives_of_continuous
    {a b : ℝ} (hab : a < b) {f F : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (F t) (Icc a b) t) :
    HasDerivWithinAt f (F a) (Ici a) a ∧ HasDerivWithinAt f (F b) (Iic b) b := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt f (F t) t :=
    (hderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hdiff : DifferentiableOn ℝ f (Ioo a b) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  constructor
  · apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab)
    have hlim : ContinuousWithinAt F (Ici a) a :=
      (continuousWithinAt_Icc_iff_Ici hab).mp (hF a ⟨le_rfl, hab.le⟩)
    apply (hlim.mono Ioi_subset_Ici_self).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (hd t ht).deriv.symm
  · apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
      ((hf b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab)
    have hlim : ContinuousWithinAt F (Iic b) b :=
      (continuousWithinAt_Icc_iff_Iic hab).mp (hF b ⟨hab.le, le_rfl⟩)
    apply (hlim.mono Iio_subset_Iic_self).congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (hd t ht).deriv.symm

namespace OrientedThreeStage.ClosedSlab

variable {P : OrientedThreeStage.{u}} {u v : ℝ} (G : P.ClosedSlab u v)

theorem ricciAt_continuousOn (x : P.Carrier) (X Y : TangentSpace ThreeModel x) :
    ContinuousOn (fun t => G.flow.ricciAt t x (vec2 X Y)) (Icc u v) := by
  have heval := tensor0SFamilyContinuousOnSet.eval_continuous
    (I := ThreeModel) (M := P.Carrier) (s := 2) G.equation.ricciCont
    (P := Icc u v) (τ := fun t => t.1) (b := fun _ => x)
    continuous_subtype_val (fun t => t.2) continuous_const
    (v := fun i _ => vec2 X Y i) (fun _ => continuous_const)
  rw [continuousOn_iff_continuous_domRestrict]
  exact heval

theorem endpoint_derivatives (x : P.Carrier) (X Y : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun t => (G.flow.base.metric t).inner x X Y)
      (-2 * G.flow.ricciAt u x (vec2 X Y)) (Ici u) u ∧
    HasDerivWithinAt (fun t => (G.flow.base.metric t).inner x X Y)
      (-2 * G.flow.ricciAt v x (vec2 X Y)) (Iic v) v := by
  apply endpoint_derivatives_of_continuous G.lt
    (G.equation.smoothMetric.coeff_cont x X Y)
    (continuousOn_const.mul (G.ricciAt_continuousOn x X Y))
  intro t ht
  exact G.equation.equation ⟨t, ht⟩ x X Y

def restrictClosed {a b : ℝ} (hua : u ≤ a) (hab : a < b) (hbv : b ≤ v) :
    P.ClosedSlab a b where
  lt := hab
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨hua.trans ht.1, ht.2.trans hbv⟩)
    (fun _ ht => ⟨hua.trans_lt ht.1, ht.2.trans_le hbv⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨hua.trans ht.1, ht.2.trans hbv⟩)

def restrictIncoming {a b : ℝ} (hua : u ≤ a) (hab : a < b) (hbv : b ≤ v) :
    P.IncomingSlab a b where
  lt := hab
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨hua.trans ht.1, ht.2.le.trans hbv⟩)
    (fun _ ht => ⟨hua.trans_lt ht.1, ht.2.trans_le hbv⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨hua.trans ht.1, ht.2.le.trans hbv⟩)

end OrientedThreeStage.ClosedSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
