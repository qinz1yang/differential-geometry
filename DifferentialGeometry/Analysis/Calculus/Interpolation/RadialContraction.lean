import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantOutsideCompactFlow
import DifferentialGeometry.Analysis.ODE.Flow.Planar.FlowSupport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_larger_closedBall_subset_open {r : ℝ} (hr : 0 ≤ r)
    {U : Set E} (hU : IsOpen U) (hsub : closedBall (0 : E) r ⊆ U) :
    ∃ R : ℝ, r < R ∧ closedBall (0 : E) R ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : E) r).exists_cthickening_subset_open hU hsub
  refine ⟨r + δ, by linarith, ?_⟩
  simpa only [cthickening_closedBall hδ.le hr, add_comm δ r] using hδU

theorem exists_compact_flow_contracting_closedBall {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ s t, D (s + t) = (D s).trans (D t)) ∧
      (∀ t x, 0 ≤ t → x ∈ closedBall 0 r → D t x = Real.exp (-t) • x) ∧
      ∀ t x, x ∉ closedBall 0 R → D t x = x ∧ (D t).symm x = x := by
  let β : ContDiffBump (0 : E) := ⟨r, R, hr, hrR⟩
  let w : E → E := fun x ↦ β x • (-x)
  have hw : ContDiff ℝ ∞ w := β.contDiff.smul contDiff_id.neg
  have hwc : HasCompactSupport w := β.hasCompactSupport.smul_right
  obtain ⟨D, hD, hderiv, hzero, hadd, hinv⟩ := exists_smoothFlow_of_eq_const_off_compact hw 0
    (by simpa only [sub_zero] using hwc)
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) := by
    simp_rw [hinv]
    exact hD.comp (contDiff_fst.neg.prodMk contDiff_snd)
  have hrad (t : ℝ) (x : E) (ht : 0 ≤ t) (hx : x ∈ closedBall 0 r) :
      D t x = Real.exp (-t) • x := by
    have hcurve (s : ℝ) (hs : s ∈ Icc 0 t) :
        HasDerivAt (fun u ↦ Real.exp (-u) • x) (w (Real.exp (-s) • x)) s := by
      have hnorm : ‖Real.exp (-s) • x‖ ≤ r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-s) * ‖x‖ ≤ 1 * ‖x‖ :=
              mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))
                (norm_nonneg x)
          _ ≤ r := by simpa only [one_mul] using (mem_closedBall_zero_iff.mp hx)
      have hβ : β (Real.exp (-s) • x) = 1 :=
        β.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hnorm)
      have hd := (((hasDerivAt_id s).neg).exp).smul_const x
      simpa only [w, hβ, one_smul, mul_neg_one, neg_smul, Pi.neg_apply, id_eq] using hd
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hw
      (a := 0) (b := t) (fun s _ ↦ (hderiv x s).hasDerivWithinAt)
      (fun s hs ↦ (hcurve s hs).hasDerivWithinAt) (by simp [hzero])
    exact he ⟨ht, le_rfl⟩
  have hs : tsupport w ⊆ closedBall 0 R := by
    have hh : tsupport w ⊆ tsupport (β : E → ℝ) := tsupport_smul_subset_left β (fun x ↦ -x)
    exact hh.trans_eq β.tsupport_eq
  have hfix (t : ℝ) (x : E) (hx : x ∉ closedBall 0 R) : D t x = x := by
    have hDs := tsupport_integralCurveFamily_sub_subset (hw.of_le (by simp))
      (Γ := fun x t ↦ D t x) (fun x ↦ by rw [hzero]; rfl) hderiv t
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun x ↦ D t x - x) (fun h ↦ hx (hs (hDs h))))
  refine ⟨D, hD, hDi, hzero, hadd, hrad, ?_⟩
  intro t x hx
  refine ⟨hfix t x hx, ?_⟩
  rw [hinv]
  exact hfix (-t) x hx

theorem exists_compact_flow_contracting_closedBall_in_open {r : ℝ} (hr : 0 < r)
    {U : Set E} (hU : IsOpen U) (hsub : closedBall (0 : E) r ⊆ U) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t x, 0 ≤ t → x ∈ closedBall 0 r → D t x = Real.exp (-t) • x) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧
        ∀ t x, x ∉ K → D t x = x ∧ (D t).symm x = x := by
  obtain ⟨R, hrR, hRU⟩ := exists_larger_closedBall_subset_open hr.le hU hsub
  obtain ⟨D, hD, hDi, hzero, _, hrad, hfix⟩ :=
    exists_compact_flow_contracting_closedBall (E := E) hr hrR
  exact ⟨D, hD, hDi, hzero, hrad, closedBall 0 R, isCompact_closedBall _ _, hRU, hfix⟩

end Poincare.Analysis
