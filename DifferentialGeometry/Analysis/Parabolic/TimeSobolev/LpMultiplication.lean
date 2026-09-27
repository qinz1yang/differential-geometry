import DifferentialGeometry.Analysis.Integration.Lp.Lifting
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import Mathlib.MeasureTheory.Function.Holder

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

private theorem exists_l2_to_l1_embedding :
    ∃ J : Lp ℝ 2 ν →L[ℝ] Lp ℝ 1 ν,
      Function.Injective J ∧ ∀ z : Lp ℝ 2 ν, J z =ᵐ[ν] z := by
  let h1 : MemLp (fun _ : Y => (1 : ℝ)) 2 ν := memLp_const 1
  let one₂ := h1.toLp (fun _ : Y => (1 : ℝ))
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL ν 2 2 1
  let J := B one₂
  have hJ (z : Lp ℝ 2 ν) : J z =ᵐ[ν] z := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder
      (r := 1) one₂ z, h1.coeFn_toLp] with x hx h1x
    change J z x = one₂ x * z x at hx
    change one₂ x = 1 at h1x
    simpa only [h1x, one_mul] using hx
  refine ⟨J, ?_, hJ⟩
  intro z w hzw
  apply Lp.ext
  exact (hJ z).symm.trans ((congrArg (fun f : Lp ℝ 1 ν => (f : Y → ℝ)) hzw).eventuallyEq.trans (hJ w))

theorem exists_lp_mul_of_ae_bound [TopologicalSpace.SeparableSpace (Lp ℝ 2 ν)]
    (a : X → Lp ℝ 2 ν) (ha : AEStronglyMeasurable a μ)
    (b : Lp (Lp ℝ 2 ν) 2 μ) {K : ℝ}
    (hbound : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, |a t x| ≤ K) :
    ∃ w : Lp (Lp ℝ 2 ν) 2 μ,
      (∀ᵐ t ∂μ, w t =ᵐ[ν] fun x => a t x * b t x) ∧
      ∀ᵐ t ∂μ, ‖w t‖ ≤ K * ‖b t‖ := by
  obtain ⟨J, hJinj, hJ⟩ := exists_l2_to_l1_embedding (ν := ν)
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL ν 2 2 1
  have hg : AEStronglyMeasurable (fun t => B (a t) (b t)) μ :=
    B.aestronglyMeasurable_comp₂ ha (Lp.aestronglyMeasurable b)
  have hex : ∀ᵐ t ∂μ, ∃ e : Lp ℝ 2 ν,
      J e = B (a t) (b t) ∧ ‖e‖ ≤ K * ‖b t‖ := by
    filter_upwards [hbound] with t ht
    have htop : MemLp (fun x => a t x) ∞ ν :=
      memLp_top_of_bound (Lp.aestronglyMeasurable (a t)) K (by simpa only [Real.norm_eq_abs] using ht)
    have hp : MemLp (fun x => a t x * b t x) 2 ν := by
      have hh : MemLp ((b t : Y → ℝ) * fun x => a t x) 2 ν := htop.mul (Lp.memLp (b t))
      exact hh.ae_eq (Eventually.of_forall fun x => mul_comm _ _)
    let e := hp.toLp (fun x => a t x * b t x)
    refine ⟨e, ?_, ?_⟩
    · apply Lp.ext
      filter_upwards [hJ e, hp.coeFn_toLp,
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 1) (a t) (b t)]
        with x hjx hex hbx
      change B (a t) (b t) x = a t x * b t x at hbx
      rw [hjx, hex, hbx]
    · apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hp.coeFn_toLp, ht] with x hx htx
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right htx (norm_nonneg _)
  obtain ⟨w, hw, hwnorm⟩ := exists_lp_lift_of_ae_exists_norm_le J.continuous hJinj hg
    ((Lp.memLp b).norm.const_mul K) hex
  refine ⟨w, ?_, hwnorm⟩
  filter_upwards [hw] with t ht
  filter_upwards [hJ (w t),
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 1) (a t) (b t)] with x hjx hbx
  change B (a t) (b t) x = a t x * b t x at hbx
  rw [← hjx, ht, hbx]

end MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {T : ℝ}

theorem exists_timeH1_mul_of_ae_bound
    (u v : timeH1 (Lp ℝ 2 μ) T) {K L : ℝ}
    (hu : ∀ᵐ t ∂timeMeasure T, ∀ᵐ x ∂μ, |u.toFun t x| ≤ K)
    (hud : ∀ᵐ t ∂timeMeasure T, ∀ᵐ x ∂μ, |u.deriv t x| ≤ L)
    (w₀ : Lp ℝ 2 μ) (hinit : w₀ =ᵐ[μ] fun x => u.initial x * v.initial x) :
    ∃ w : timeH1 (Lp ℝ 2 μ) T,
      w.initial = w₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t =ᵐ[μ] fun x => u.toFun t x * v.toFun t x) ∧
      (∀ᵐ t ∂timeMeasure T,
        w.deriv t =ᵐ[μ] fun x => u.deriv t x * v.toFun t x + u.toFun t x * v.deriv t x) := by
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL μ 2 2 1
  obtain ⟨J, hJinj, hJ⟩ := MeasureTheory.exists_l2_to_l1_embedding (ν := μ)
  have hv : v.toFunL2 =ᵐ[timeMeasure T] v.toFun := coeFn_ofContinuousOn v.continuousOn_toFun
  obtain ⟨q₁, hq₁, _⟩ := exists_lp_mul_of_ae_bound (fun t => u.deriv t)
    (Lp.aestronglyMeasurable u.deriv) v.toFunL2 hud
  obtain ⟨q₂, hq₂, _⟩ := exists_lp_mul_of_ae_bound u.toFun
    (memLp_of_continuousOn u.continuousOn_toFun).aestronglyMeasurable v.deriv hu
  obtain ⟨z, hz0, hz, hzd⟩ := exists_timeH1_bilin B u v
  let w : timeH1 (Lp ℝ 2 μ) T := timeH1.mk w₀ (q₁ + q₂)
  obtain ⟨Jw, hJw0, hJw, hJwd⟩ := exists_timeH1_comp_clm J w
  have hEq : Jw = z := by
    apply timeH1.ext
    · rw [hJw0, hz0]
      apply Lp.ext
      filter_upwards [hJ w₀, hinit,
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 1) u.initial v.initial]
        with x hjx hix hbx
      change B u.initial v.initial x = u.initial x * v.initial x at hbx
      change J w₀ x = _
      rw [hjx, hix, hbx]
    · apply Lp.ext
      filter_upwards [hJwd, hzd, hq₁, hq₂, hv, Lp.coeFn_add q₁ q₂] with t hJt hzt hqt₁ hqt₂ hvt hqt
      rw [hJt, hzt]
      change J ((q₁ + q₂) t) = _
      rw [hqt, Pi.add_apply, map_add, ← hvt]
      apply Lp.ext
      filter_upwards [hJ (q₁ t), hJ (q₂ t), hqt₁, hqt₂,
        Lp.coeFn_add (J (q₁ t)) (J (q₂ t)),
        Lp.coeFn_add (B (u.deriv t) (v.toFunL2 t)) (B (u.toFun t) (v.deriv t)),
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 1) (u.deriv t) (v.toFunL2 t),
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 1) (u.toFun t) (v.deriv t)]
        with x hj₁ hj₂ hq₁x hq₂x hs₁ hs₂ hb₁ hb₂
      change B (u.deriv t) (v.toFunL2 t) x = u.deriv t x * v.toFunL2 t x at hb₁
      change B (u.toFun t) (v.deriv t) x = u.toFun t x * v.deriv t x at hb₂
      simp only [hs₁, hs₂, Pi.add_apply, hj₁, hj₂, hq₁x, hq₂x, hb₁, hb₂]
  refine ⟨w, rfl, ?_, ?_⟩
  · intro t ht
    have hval : J (w.toFun t) = B (u.toFun t) (v.toFun t) := by
      rw [← hJw t ht, hEq, hz t ht]
    filter_upwards [hJ (w.toFun t),
      (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 1) (u.toFun t) (v.toFun t)]
      with x hjx hbx
    change B (u.toFun t) (v.toFun t) x = u.toFun t x * v.toFun t x at hbx
    rw [← hjx, hval, hbx]
  · filter_upwards [hq₁, hq₂, hv, Lp.coeFn_add q₁ q₂] with t hqt₁ hqt₂ hvt hqt
    change (q₁ + q₂) t =ᵐ[μ] _
    rw [hqt, Pi.add_apply]
    filter_upwards [hqt₁, hqt₂, Lp.coeFn_add (q₁ t) (q₂ t)] with x hx₁ hx₂ hx
    simp only [hx, Pi.add_apply, hx₁, hx₂, hvt]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
