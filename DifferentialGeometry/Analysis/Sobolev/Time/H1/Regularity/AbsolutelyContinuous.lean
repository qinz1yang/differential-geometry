import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
  [FiniteDimensional Real X]

namespace timeH1

theorem exists_of_absolutelyContinuousOnInterval {T : Real} (f : Real → X)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : MemLp (_root_.deriv f) 2 (timeMeasure T)) :
    ∃ u : timeH1 X T,
      EqOn u.toFun f (Icc (0 : Real) T) ∧
        u.deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  let u : timeH1 X T := mk (f 0) (hderiv.toLp (_root_.deriv f))
  have huDeriv : u.deriv =ᵐ[timeMeasure T] _root_.deriv f :=
    hderiv.coeFn_toLp
  refine ⟨u, ?_, huDeriv⟩
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Ι (0 : Real) t ⊆ Icc (0 : Real) T := by
    rw [uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  have hae : (fun s ↦ u.deriv s) =ᵐ[volume.restrict (Ι 0 t)]
      _root_.deriv f := by
    change ∀ᵐ s ∂volume.restrict (Ι 0 t), u.deriv s = _root_.deriv f s
    exact ae_mono (Measure.restrict_mono hsub le_rfl) huDeriv
  rw [toFun_apply, show u.initial = f 0 by rfl,
    intervalIntegral.integral_congr_ae_restrict hae]
  have hft : AbsolutelyContinuousOnInterval f 0 t :=
    hf.mono (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
  rw [hft.integral_deriv_eq_sub_vector]
  abel

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
