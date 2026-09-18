import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_timeH1_of_hasDerivWithinAt_separating
    {ι : Type*} (J : ι → X →L[ℝ] Y)
    (hJ : Function.Injective (fun x : X => fun i => J i x))
    {T : ℝ} (hT : 0 < T) (w v : ℝ → X)
    (hv : ContinuousOn v (Icc 0 T))
    (hw : ∀ i t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => J i (w s)) (J i (v t)) (Icc 0 T) t) :
    ∃ u : timeH1 X T,
      timeH1.trace0 X T u = w 0 ∧ EqOn u.toFun w (Icc 0 T) ∧
        u.deriv =ᵐ[timeMeasure T] v := by
  let hvmem := memLp_of_continuousOn hv
  let u : timeH1 X T := timeH1.mk (w 0) (hvmem.toLp v)
  have hud : u.deriv =ᵐ[timeMeasure T] v := hvmem.coeFn_toLp
  refine ⟨u, rfl, ?_, hud⟩
  have hu (i : ι) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => J i (u.toFun s)) (J i (v t)) (Icc 0 T) t :=
    (J i).hasFDerivAt.comp_hasDerivWithinAt t
      (u.hasDerivWithinAt_toFun_of_continuousOn hv hud ht)
  intro t ht
  apply hJ
  funext i
  apply eq_of_derivWithin_eq
    (fun s hs => (hu i s hs).differentiableWithinAt)
    (fun s hs => (hw i s hs).differentiableWithinAt) ?_ ?_ t ht
  · intro s hs
    have hscc : s ∈ Icc 0 T := ⟨hs.1, hs.2.le⟩
    rw [(hu i s hscc).derivWithin ((uniqueDiffOn_Icc hT) s hscc),
      (hw i s hscc).derivWithin ((uniqueDiffOn_Icc hT) s hscc)]
  · rw [timeH1.toFun_zero]
    rfl

theorem exists_timeH1_lift_of_hasDerivWithinAt_separating
    {Z ι : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P L : Z →L[ℝ] X) (J : ι → X →L[ℝ] Y)
    (hJ : Function.Injective (fun x : X => fun i => J i x))
    {T : ℝ} (hT : 0 < T) (W : ℝ → Z) (V : ℝ → X)
    (hW : ContinuousOn W (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (heq : ∀ i t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => J i (P (W s))) (J i (V t)) (Icc 0 T) t) :
    ∃ (u : timeH1 X T) (field : timeL2 Z T) (force : timeL2 X T),
      timeH1.trace0 X T u = P (W 0) ∧
        EqOn u.toFun (fun t => P (W t)) (Icc 0 T) ∧
        field =ᵐ[timeMeasure T] W ∧
        force =ᵐ[timeMeasure T] (fun t => V t - L (W t)) ∧
        P.compLpL 2 (timeMeasure T) field = u.toFunL2 ∧
        timeH1.timeDeriv X T u = L.compLpL 2 (timeMeasure T) field + force := by
  obtain ⟨u, htrace, hrep, hud⟩ := exists_timeH1_of_hasDerivWithinAt_separating
    J hJ hT (fun t => P (W t)) V hV heq
  let hWmem := memLp_of_continuousOn hW
  let field : timeL2 Z T := hWmem.toLp W
  let hFmem := memLp_of_continuousOn (hV.sub (L.continuous.comp_continuousOn hW))
  let force : timeL2 X T := hFmem.toLp (fun t => V t - L (W t))
  have hf : field =ᵐ[timeMeasure T] W := hWmem.coeFn_toLp
  have hforce : force =ᵐ[timeMeasure T] (fun t => V t - L (W t)) := hFmem.coeFn_toLp
  have hucoe : ⇑u.toFunL2 =ᵐ[timeMeasure T] u.toFun :=
    coeFn_ofContinuousOn u.continuousOn_toFun
  refine ⟨u, field, force, htrace, hrep, hf, hforce, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [P.coeFn_compLpL field, hf, hucoe,
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht hft hut htt
    rw [ht, hft, hut, hrep htt]
  · apply Lp.ext
    filter_upwards [hud, L.coeFn_compLpL field, hf, hforce,
      Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) force]
      with t hut ht hft hforcet hadd
    change u.deriv t = _
    rw [hut, hadd, Pi.add_apply, ht, hft, hforcet]
    abel

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
