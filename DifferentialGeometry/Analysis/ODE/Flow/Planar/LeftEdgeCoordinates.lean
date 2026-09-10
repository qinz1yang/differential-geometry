import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareBackwardCrossing
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantHalfSpaceFlow

open Set
open scoped ContDiff

namespace Poincare.Analysis

theorem injective_leftEdge_flow_coordinates
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ 0 → v z = 1) :
    Function.Injective (fun p : ℝ × ℝ ↦ φ p.2 (p.1 • Complex.I)) := by
  intro p q he
  change φ p.2 (p.1 • Complex.I) = φ q.2 (q.1 • Complex.I) at he
  have hhit : φ (p.2 - q.2) (p.1 • Complex.I) = q.1 • Complex.I := by
    calc
      φ (p.2 - q.2) (p.1 • Complex.I) = φ (-q.2) (φ p.2 (p.1 • Complex.I)) := by
        rw [← φ.map_add]; congr 1; ring
      _ = φ (-q.2) (φ q.2 (q.1 • Complex.I)) := congrArg (φ (-q.2)) he
      _ = q.1 • Complex.I := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]
  have htime : p.2 - q.2 = 0 :=
    eq_of_integralCurve_constant_incoming_halfSpace_crossings hv Complex.reCLM (1 : ℂ)
      (b := 0) (by simp) hfixed (hderiv (p.1 • Complex.I))
      (by rw [hhit]; simp [Complex.real_smul]) (t := 0)
      (by rw [φ.map_zero_apply]; simp [Complex.real_smul])
  have ht : p.2 = q.2 := sub_eq_zero.mp htime
  have hseed : p.1 • Complex.I = q.1 • Complex.I :=
    (φ.toHomeomorph q.2).injective (by simpa only [ht, φ.toHomeomorph_apply] using he)
  refine Prod.ext ?_ ht
  simpa [Complex.real_smul] using congrArg Complex.im hseed

theorem exists_leftEdge_flow_coordinates
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v z = 1)
    {z : ℂ} (hzre : z.re ∈ Icc 0 1) (hzim : z.im ∈ Icc 0 1) :
    ∃ y ∈ Icc (0 : ℝ) 1, ∃ t ≥ 0, φ t (y • Complex.I) = z ∧
      ∀ y' t', φ t' (y' • Complex.I) = z → y' = y ∧ t' = t := by
  have huniq := injective_leftEdge_flow_coordinates φ hv hderiv
    (fun x hx ↦ hfixed x (Or.inl hx))
  have hseed (w : ℂ) (hw : w.re = 0) : w.im • Complex.I = w := by
    apply Complex.ext <;> simp [Complex.real_smul, hw]
  have hrep : ∃ y ∈ Icc (0 : ℝ) 1, ∃ t ≥ 0, φ t (y • Complex.I) = z := by
    rcases eq_or_lt_of_le hzre.1 with hz | hz
    · exact ⟨z.im, hzim, 0, le_rfl, (φ.map_zero_apply _).trans (hseed z hz.symm)⟩
    obtain ⟨s, hs, hleft⟩ := exists_neg_leftEdge_crossing φ hv hnz hderiv hfixed
      ⟨hz, hzre.2⟩ hzim
    have hlo := le_iff_of_integralCurve_constant_hyperplane (hv.of_le (by simp))
      (-Complex.imCLM) 1 (by simp) (b := 0)
      (fun x hx ↦ hfixed x (Or.inr (Or.inr (Or.inl (by simpa using hx.ge)))))
      (hderiv z) s 0
    have hhi := le_iff_of_integralCurve_constant_hyperplane (hv.of_le (by simp))
      Complex.imCLM 1 (by simp) (b := 1)
      (fun x hx ↦ hfixed x (Or.inr (Or.inr (Or.inr hx.ge)))) (hderiv z) s 0
    have hy : (φ s z).im ∈ Icc (0 : ℝ) 1 := by
      constructor
      · simpa using hlo.mpr (by simpa using hzim.1)
      · exact hhi.mpr (by simpa only [φ.map_zero_apply, Complex.imCLM_apply] using hzim.2)
    refine ⟨(φ s z).im, hy, -s, (neg_pos.mpr hs).le, ?_⟩
    rw [hseed (φ s z) hleft, ← φ.map_add, neg_add_cancel, φ.map_zero_apply]
  obtain ⟨y, hy, t, ht, htz⟩ := hrep
  refine ⟨y, hy, t, ht, htz, fun y' t' he ↦ ?_⟩
  have hp := huniq (a₁ := (y', t')) (a₂ := (y, t)) (he.trans htz.symm)
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

end Poincare.Analysis
