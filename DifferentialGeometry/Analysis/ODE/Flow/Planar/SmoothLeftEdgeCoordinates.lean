import DifferentialGeometry.Analysis.ODE.Flow.Planar.LeftEdgeCoordinates
import DifferentialGeometry.Analysis.ODE.Flow.Planar.TransverseHittingTime

open Set
open scoped ContDiff

namespace Poincare.Analysis

theorem exists_smooth_leftEdge_coordinates
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {v : P × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : P → _root_.Flow ℝ ℂ)
    (hφ : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2)) {S : Set P}
    (hnz : ∀ p ∈ S, ∀ z, v (p, z) ≠ 0)
    (hderiv : ∀ p ∈ S, ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ S, ∀ z : ℂ,
      z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v (p, z) = 1) :
    ∃ R : P × ℂ → ℝ × ℝ,
      ContDiffOn ℝ ∞ R (S ×ˢ Complex.reProdIm (Icc 0 1) (Icc 0 1)) ∧
      ∀ p ∈ S, ∀ z : ℂ, z.re ∈ Icc 0 1 → z.im ∈ Icc 0 1 →
        (R (p, z)).1 ∈ Icc 0 1 ∧ 0 ≤ (R (p, z)).2 ∧
        φ p (R (p, z)).2 ((R (p, z)).1 • Complex.I) = z ∧
        ∀ y t, φ p t (y • Complex.I) = z → (y, t) = R (p, z) := by
  let Q : Set (P × ℂ) := S ×ˢ Complex.reProdIm (Icc 0 1) (Icc 0 1)
  let H : (P × ℂ) × ℝ → ℝ := fun q ↦ (φ q.1.1 q.2 q.1.2).re
  have hH : ContDiff ℝ ∞ H := Complex.reCLM.contDiff.comp
    (hφ.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)))
  have hvs (p : P) : ContDiff ℝ ∞ (fun z ↦ v (p, z)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hcoords (q : P × ℂ) (hq : q ∈ Q) :=
    exists_leftEdge_flow_coordinates (φ q.1) (hvs q.1) (hnz q.1 hq.1)
      (hderiv q.1 hq.1) (hfixed q.1 hq.1) hq.2.1 hq.2.2
  have hback (p : P) (z : ℂ) (y t : ℝ) (he : φ p t (y • Complex.I) = z) :
      φ p (-t) z = y • Complex.I := by
    rw [← he, ← (φ p).map_add, neg_add_cancel, (φ p).map_zero_apply]
  have hunique (q : P × ℂ) (hq : q ∈ Q) : ∃! t : ℝ, H (q, t) = 0 := by
    obtain ⟨y, _, t, _, he, _⟩ := hcoords q hq
    have ht : H (q, -t) = 0 := by
      dsimp only [H]
      rw [hback q.1 q.2 y t he]
      simp [Complex.real_smul]
    refine ⟨-t, ht, fun s hs ↦ ?_⟩
    exact eq_of_integralCurve_constant_incoming_halfSpace_crossings (hvs q.1)
      Complex.reCLM (1 : ℂ) (by simp)
      (fun z hz ↦ hfixed q.1 hq.1 z (Or.inl hz)) (hderiv q.1 hq.1 q.2) hs ht
  have htrans (q : P × ℂ) (hq : q ∈ Q) (t : ℝ) (ht : H (q, t) = 0) :
      fderiv ℝ H (q, t) (0, 1) ≠ 0 := by
    have hd : HasDerivAt (fun t ↦ H (q, t)) (1 : ℝ) t := by
      have hd' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hderiv q.1 hq.1 q.2 t)
      simpa only [H, Function.comp_def,
        hfixed q.1 hq.1 _ (Or.inl ht.le), Complex.reCLM_apply, Complex.one_re] using hd'
    have hdf : HasDerivAt (fun t ↦ H (q, t)) (fderiv ℝ H (q, t) (0, 1)) t :=
      (hH.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t q).prodMk (hasDerivAt_id t))
    exact (hdf.unique hd).trans_ne one_ne_zero
  obtain ⟨θ, hθ, _, hθunique⟩ := exists_contDiffOn_transverse_hittingTime
    (V := univ) isOpen_univ (subset_univ Q) hH.contDiffOn contDiffOn_const hunique htrans
  let R : P × ℂ → ℝ × ℝ := fun q ↦ ((φ q.1 (θ q) q.2).im, -θ q)
  have hR : ContDiffOn ℝ ∞ R Q :=
    (Complex.imCLM.contDiff.comp_contDiffOn
      (hφ.comp_contDiffOn (contDiffOn_fst.prodMk (hθ.prodMk contDiffOn_snd)))).prodMk hθ.neg
  refine ⟨R, hR, fun p hp z hzre hzim ↦ ?_⟩
  have hq : (p, z) ∈ Q := ⟨hp, hzre, hzim⟩
  obtain ⟨y, hy, t, ht, he, huniq⟩ := hcoords (p, z) hq
  have hroot : H ((p, z), -t) = 0 := by
    dsimp only [H]
    rw [hback p z y t he]
    simp [Complex.real_smul]
  have hθeq : θ (p, z) = -t := (hθunique (p, z) hq (-t) hroot).symm
  have hReq : R (p, z) = (y, t) := by
    dsimp only [R]
    rw [hθeq, hback p z y t he]
    simp [Complex.real_smul]
  rw [hReq]
  refine ⟨hy, ht, he, fun y' t' he' ↦ ?_⟩
  exact Prod.ext (huniq y' t' he').1 (huniq y' t' he').2

end Poincare.Analysis
