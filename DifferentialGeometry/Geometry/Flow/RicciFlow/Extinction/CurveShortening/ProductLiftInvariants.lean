import DifferentialGeometry.Analysis.Calculus.Periodic.CircleLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import Mathlib.Topology.Covering.AddCircle

section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {M : Type*}

theorem deriv_y_eq_of_snd_map_eq
    (c d : ProductCurve M) {s t : ℝ}
    (hmap : ∀ z, (c.map z s).2 = (d.map z t).2) (x : ℝ)
    (hc : ContinuousAt (fun z => c.y z s) x)
    (hd : ContinuousAt (fun z => d.y z t) x) :
    deriv (fun z => c.y z s) x = deriv (fun z => d.y z t) x := by
  exact DifferentialGeometry.Topology.deriv_eq_of_addCircle_coe_eventuallyEq
    (period := 1) hc hd (Filter.Eventually.of_forall
      (fun z => by
        change (c.y z s : AddCircle (1 : ℝ)) = (d.y z t : AddCircle (1 : ℝ))
        rw [c.lift_eq z s, d.lift_eq z t, hmap]))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

end

section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

theorem degree_eq_of_snd_map_eq {M N : Type*} (c : ProductCurve M) (d : ProductCurve N)
    {s t : ℝ} (hc : ContinuousOn (fun x => c.y x s) (Icc (0 : ℝ) 1))
    (hd : ContinuousOn (fun x => d.y x t) (Icc (0 : ℝ) 1))
    (hmap : ∀ z, (c.map z s).2 = (d.map z t).2) : c.degree = d.degree := by
  have hzero (x : ℝ) : ((c.y x s - d.y x t : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, c.lift_eq x s, d.lift_eq x t, hmap, sub_self]
  have hconst : c.y 1 s - d.y 1 t = c.y 0 s - d.y 0 t :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).constOn_of_comp
      (g := fun x => c.y x s - d.y x t) isPreconnected_Icc (hc.sub hd)
      (fun x _ y _ => by rw [hzero x, hzero y]) (by norm_num) (by norm_num)
  have hcinc := c.increment 0 s
  have hdinc := d.increment 0 t
  simp only [zero_add] at hcinc hdinc
  have hcast : (c.degree : ℝ) = (d.degree : ℝ) := by linarith
  exact_mod_cast hcast

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

end
