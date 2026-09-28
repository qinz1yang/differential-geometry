import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {T : ℝ}

theorem ofContDiffOn_affine_eq_mk (hT : 0 ≤ T) (x v : X) :
    ofContDiffOn hT (fun t : ℝ ↦ x + t • v)
      (contDiff_const.add (contDiff_id.smul_const v)).contDiffOn =
      mk x (TimeSobolev.const T v) := by
  apply timeH1.ext
  · simp only [ofContDiffOn, initial_mk, zero_smul, add_zero]
  · apply Lp.ext
    filter_upwards [deriv_ofContDiffOn hT (fun t : ℝ ↦ x + t • v)
      (contDiff_const.add (contDiff_id.smul_const v)).contDiffOn,
      TimeSobolev.coeFn_const (T := T) v] with t ht hv
    rw [ht]
    change _ = (TimeSobolev.const T v) t
    rw [hv]
    simpa only [one_smul, id_eq] using (((hasDerivAt_id t).smul_const v).const_add x).deriv

variable [CompleteSpace X] [CompleteSpace Y]

theorem toFun_mk_const (x v : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (mk x (TimeSobolev.const T v)).toFun t = x + t • v := by
  rw [← ofContDiffOn_affine_eq_mk (ht.1.trans ht.2)]
  exact toFun_ofContDiffOn (ht.1.trans ht.2) _ _ ht

theorem toFunL2_mk_const_ae (x v : X) :
    (mk x (TimeSobolev.const T v)).toFunL2 =ᵐ[timeMeasure T] fun t ↦ x + t • v := by
  filter_upwards [TimeSobolev.coeFn_ofContinuousOn
    (mk x (TimeSobolev.const T v)).continuousOn_toFun,
    ae_restrict_mem measurableSet_Icc] with t ht hmem
  exact ht.trans (toFun_mk_const x v hmem)

theorem compLpL_toFunL2_mk_const (L : X →L[ℝ] Y) (x v : X) :
    L.compLpL 2 (timeMeasure T) (mk x (TimeSobolev.const T v)).toFunL2 =
      (mk (L x) (TimeSobolev.const T (L v))).toFunL2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (mk x (TimeSobolev.const T v)).toFunL2,
    toFunL2_mk_const_ae (T := T) x v,
    toFunL2_mk_const_ae (T := T) (L x) (L v)] with t hL hx hy
  rw [hL, hx, hy, map_add, map_smul]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1
end

noncomputable section

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {X : Type*} [NormedAddCommGroup X] {T : ℝ}

@[simp] theorem norm_mk_zero (x : X) : ‖mk x (0 : timeL2 X T)‖ = ‖x‖ :=
  WithLp.norm_toLp_fst 2 X (timeL2 X T) x

theorem isometry_mk_zero : Isometry (fun x : X => mk x (0 : timeL2 X T)) :=
  fun x y => WithLp.edist_toLp_fst 2 X (timeL2 X T) x y

theorem lipschitzWith_mk_zero_add {P : Type*} [PseudoEMetricSpace P]
    {f : P → X} {u : P → timeH1 X T} {Kf Ku : ℝ≥0}
    (hf : LipschitzWith Kf f) (hu : LipschitzWith Ku u) :
    LipschitzWith (Kf + Ku) (fun p => mk (f p) 0 + u p) := by
  have hc : LipschitzWith Kf (fun p => mk (f p) (0 : timeL2 X T)) := by
    simpa only [one_mul, Function.comp_def] using (isometry_mk_zero (X := X) (T := T)).lipschitzWith.comp hf
  exact hc.add hu

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

end
