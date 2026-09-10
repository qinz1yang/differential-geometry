import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareFlowBoundaryStrips
import DifferentialGeometry.Analysis.Calculus.Interpolation.RelativeIntervalDiffeomorph
import DifferentialGeometry.Analysis.Calculus.Interpolation.VerticalInterpolation

noncomputable section
open Set
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem exists_boundary_fixed_square_reconstruction
    {v : ℝ × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : ℝ → _root_.Flow ℝ ℂ)
    (hφ : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2))
    {δ : ℝ} (hδ : 0 < δ)
    (hnz : ∀ p ∈ Icc (0 : ℝ) 1, ∀ z, v (p, z) ≠ 0)
    (hderiv : ∀ p ∈ Icc (0 : ℝ) 1, ∀ z t,
      HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ Icc (0 : ℝ) 1, ∀ z : ℂ,
      z.re ≤ δ ∨ 1 - δ ≤ z.re ∨ z.im ≤ δ ∨ 1 - δ ≤ z.im → v (p, z) = 1)
    {τ : ℝ × ℝ → ℝ} (hτ : ContDiffOn ℝ ∞ τ (Icc 0 1 ×ˢ Icc 0 1))
    (hτpos : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, 0 < τ (p, y))
    (hexit : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      (φ p (τ (p, y)) (y • Complex.I)).re = 1) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      D 1 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞ ∧ ∃ F G : ℝ × ℂ → ℂ,
      ContDiffOn ℝ ∞ F (univ ×ˢ Complex.reProdIm (Icc 0 1) (Icc 0 1)) ∧
      ContDiffOn ℝ ∞ G (univ ×ˢ Complex.reProdIm (Icc 0 1) (Icc 0 1)) ∧
      (∀ i : ℝ, i = 0 ∨ i = 1 →
        (∀ y ∈ Icc (0 : ℝ) 1, rightEdgeExitMap φ τ (i, y) = y) →
        ∀ z ∈ Complex.reProdIm (Icc (0 : ℝ) 1) (Icc 0 1),
          F (i, z) = leftEdgeSquareMap φ τ D (i, z)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ p : ℝ,
        MapsTo (fun z ↦ F (p, z)) (Complex.reProdIm (Icc 0 1) (Icc 0 1))
          (Complex.reProdIm (Icc 0 1) (Icc 0 1)) ∧
        MapsTo (fun z ↦ G (p, z)) (Complex.reProdIm (Icc 0 1) (Icc 0 1))
          (Complex.reProdIm (Icc 0 1) (Icc 0 1)) ∧
        (∀ z ∈ Complex.reProdIm (Icc (0 : ℝ) 1) (Icc 0 1), G (p, F (p, z)) = z) ∧
        (∀ z ∈ Complex.reProdIm (Icc (0 : ℝ) 1) (Icc 0 1), F (p, G (p, z)) = z) ∧
        ∀ z ∈ Complex.reProdIm (Icc (0 : ℝ) 1) (Icc 0 1),
          z.re ≤ ε ∨ 1 - ε ≤ z.re ∨ z.im ≤ ε ∨ 1 - ε ≤ z.im →
            F (p, z) = z ∧ G (p, z) = z := by
  let Q : Set ℂ := Complex.reProdIm (Icc 0 1) (Icc 0 1)
  have hunit (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (z : ℂ)
      (hz : z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im) : v (p, z) = 1 := by
    apply hfixed p hp z
    rcases hz with hz | hz | hz | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  obtain ⟨D, hD, hDi, hDone, hDmap, η, hη, hηhalf, hηδ, hstrips⟩ :=
    exists_reparametrization_with_uniform_square_strips hv φ isCompact_Icc hδ hderiv hfixed hτ hτpos hexit
  obtain ⟨J, hA, hJ, hAJ⟩ := exists_smooth_inverse_leftEdgeSquareMap hv φ hφ hnz hderiv
    hunit hτ hτpos hexit D hD hDi hDmap
  let A := leftEdgeSquareMap φ τ D
  obtain ⟨g, hgplus, hg, hgprop⟩ := exists_smooth_inverse_rightEdgeExitMap hv φ hφ hnz hderiv
    hunit hτ hτpos hexit
  have hgfix (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1)
      (he : y ≤ δ ∨ 1 - δ ≤ y) : rightEdgeExitMap φ τ (p, y) = y ∧ g (p, y) = y := by
    apply (hgprop p hp).2.2.2.2 y hy
    intro z hz
    apply hfixed p hp z
    rcases he with he | he
    · exact Or.inr (Or.inr (Or.inl (hz ▸ he)))
    · exact Or.inr (Or.inr (Or.inr (hz ▸ he)))
  obtain ⟨E, hE, hEi, hEprop⟩ := exists_diffeomorph_extension_of_interval_family
    (a := 0) (b := 1) (ε := δ) (by norm_num) hδ hg hgplus
    (fun p hp ↦ (hgprop p hp).2.1) (fun p hp ↦ (hgprop p hp).1)
    (fun p hp ↦ (hgprop p hp).2.2.2.1) (fun p hp ↦ (hgprop p hp).2.2.1)
    (fun p hp y hy he ↦ (hgfix p hp y hy (by simpa only [zero_add] using he)).symm)
  let κ := Real.smoothTransition
  have hκ : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff
  have hκrange (p : ℝ) : κ p ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg p, Real.smoothTransition.le_one p⟩
  let f : ℝ × ℝ → ℝ := fun q ↦ E (κ q.1) q.2
  have hf : ContDiff ℝ ∞ f := contDiffOn_univ.mp
    (hE.comp ((hκ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q _ ↦ ⟨hκrange q.1, mem_univ _⟩))
  have hfpos (p y : ℝ) : 0 < deriv (fun y ↦ f (p, y)) y := (hEprop _ (hκrange p)).2.2.2 y
  have hfid (p y : ℝ) (hy : y ≤ 0 ∨ 1 ≤ y) : f (p, y) = y := by
    rw [show f (p, y) = extendIntervalById 0 1 g (κ p, y) from (hEprop _ (hκrange p)).1 y]
    by_cases hi : y ∈ Icc (0 : ℝ) 1
    · rw [extendIntervalById, if_pos hi]
      exact (hgfix _ (hκrange p) y hi (hy.imp (fun h ↦ by linarith) (fun h ↦ by linarith))).2
    · exact if_neg hi
  let ε : ℝ := min η (1 / 4)
  have hε : 0 < ε := lt_min hη (by norm_num)
  have hεη : ε ≤ η := min_le_left _ _
  have hεδ : ε ≤ δ := hεη.trans hηδ
  have hεquarter : ε ≤ 1 / 4 := min_le_right _ _
  let β : ℝ → ℝ := fun x ↦ Real.smoothTransition ((x - (1 - 2 * ε)) / ε)
  have hβ : ContDiff ℝ ∞ β := Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const ε)
  have hβrange (x : ℝ) : β x ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hβzero (x : ℝ) (hx : x ≤ ε) : β x = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
  have hβone (x : ℝ) (hx : 1 - ε ≤ x) : β x = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith))
  obtain ⟨K, hK, hKi, hKprop⟩ := exists_vertical_interpolation_diffeomorphs hf hβ hβrange hfpos hfid
  have hKmap (p : ℝ) : BijOn (K p) Q Q := (hKprop p).2 0 1
  have hKimap (p : ℝ) : MapsTo (K p).symm Q Q := by
    intro z hz
    obtain ⟨w, hw, he⟩ := (hKmap p).surjOn hz
    rw [← he, Diffeomorph.symm_apply_apply]
    exact hw
  let F : ℝ × ℂ → ℂ := fun q ↦ K q.1 (A (κ q.1, q.2))
  let G : ℝ × ℂ → ℂ := fun q ↦ J (κ q.1, (K q.1).symm q.2)
  have hAflat : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ ↦ A (κ q.1, q.2)) (univ ×ˢ Q) :=
    hA.comp ((hκ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq ↦ ⟨hκrange q.1, hq.2⟩)
  have hF : ContDiffOn ℝ ∞ F (univ ×ˢ Q) :=
    hK.comp_contDiffOn (contDiffOn_fst.prodMk hAflat)
  have hG : ContDiffOn ℝ ∞ G (univ ×ˢ Q) :=
    hJ.comp ((hκ.comp contDiff_fst).contDiffOn.prodMk hKi.contDiffOn)
      (fun q hq ↦ ⟨hκrange q.1, hKimap q.1 hq.2⟩)
  have hFG (p : ℝ) (z : ℂ) (hz : z ∈ Q) : F (p, G (p, z)) = z := by
    change K p (leftEdgeSquareMap φ τ D (κ p, J (κ p, (K p).symm z))) = z
    rw [(hAJ _ (hκrange p)).2.2.2 _ (hKimap p hz), Diffeomorph.apply_symm_apply]
  have hGF (p : ℝ) (z : ℂ) (hz : z ∈ Q) : G (p, F (p, z)) = z := by
    change J (κ p, (K p).symm (K p (A (κ p, z)))) = z
    rw [Diffeomorph.symm_apply_apply]
    exact (hAJ _ (hκrange p)).2.2.1 z hz
  have hrepr (z : ℂ) : (z.re : ℂ) + z.im • Complex.I = z := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hKfix (p : ℝ) (z : ℂ) (he : f (p, z.im) = z.im) : K p z = z := by
    rw [(hKprop p).1, he]
    have hs : (1 - β z.re) * z.im + β z.re * z.im = z.im := by ring
    rw [hs]
    exact hrepr z
  have hboundary (p : ℝ) (z : ℂ) (hz : z ∈ Q)
      (he : z.re ≤ ε ∨ 1 - ε ≤ z.re ∨ z.im ≤ ε ∨ 1 - ε ≤ z.im) : F (p, z) = z := by
    have hstrip := hstrips (κ p) (hκrange p) z.im hz.2
    have hAy : z.im ∈ Icc (0 : ℝ) 1 := hz.2
    rcases he with he | he | he | he
    · have ha : A (κ p, z) = z := by simpa only [hrepr] using hstrip.1 z.re (he.trans hεη)
      change K p (A (κ p, z)) = z
      rw [ha, (hKprop p).1, hβzero z.re he]
      simp
    · have ha : A (κ p, z) = (z.re : ℂ) + rightEdgeExitMap φ τ (κ p, z.im) • Complex.I := by
        simpa only [hrepr] using hstrip.2.1 z.re (by linarith)
      have hyplus := (hgprop _ (hκrange p)).1 hAy
      have heinv : f (p, rightEdgeExitMap φ τ (κ p, z.im)) = z.im := by
        rw [show f (p, rightEdgeExitMap φ τ (κ p, z.im)) =
          extendIntervalById 0 1 g (κ p, rightEdgeExitMap φ τ (κ p, z.im)) from
            (hEprop _ (hκrange p)).1 _]
        rw [extendIntervalById, if_pos hyplus]
        exact (hgprop _ (hκrange p)).2.2.1 z.im hAy
      change K p (A (κ p, z)) = z
      rw [ha, (hKprop p).1]
      simp [Complex.real_smul, hβone z.re he, heinv]
    · have hyedge : z.im ≤ δ ∨ 1 - δ ≤ z.im := Or.inl (he.trans hεδ)
      have ha : A (κ p, z) = z := by simpa only [hrepr] using hstrip.2.2 z.re hyedge
      change K p (A (κ p, z)) = z
      rw [ha]
      apply hKfix
      rw [show f (p, z.im) = extendIntervalById 0 1 g (κ p, z.im) from (hEprop _ (hκrange p)).1 _]
      rw [extendIntervalById, if_pos hAy]
      exact (hgfix _ (hκrange p) z.im hAy hyedge).2
    · have hyedge : z.im ≤ δ ∨ 1 - δ ≤ z.im := Or.inr (by linarith)
      have ha : A (κ p, z) = z := by simpa only [hrepr] using hstrip.2.2 z.re hyedge
      change K p (A (κ p, z)) = z
      rw [ha]
      apply hKfix
      rw [show f (p, z.im) = extendIntervalById 0 1 g (κ p, z.im) from (hEprop _ (hκrange p)).1 _]
      rw [extendIntervalById, if_pos hAy]
      exact (hgfix _ (hκrange p) z.im hAy hyedge).2
  refine ⟨D, hDone, F, G, hF, hG, ?_, ε, hε, by linarith, fun p ↦ ?_⟩
  · intro i hi hexitid z _
    have hκi : κ i = i := by rcases hi with rfl | rfl <;> simp [κ]
    have hfi (y : ℝ) : f (i, y) = y := by
      rw [show f (i, y) = extendIntervalById 0 1 g (κ i, y) from (hEprop _ (hκrange i)).1 y, hκi]
      by_cases hy : y ∈ Icc (0 : ℝ) 1
      · rw [extendIntervalById, if_pos hy]
        have hip : i ∈ Icc (0 : ℝ) 1 := hκi ▸ hκrange i
        have he := (hgprop i hip).2.2.1 y hy
        rw [hexitid y hy] at he
        exact he
      · exact if_neg hy
    change K i (A (κ i, z)) = A (i, z)
    rw [hκi]
    exact hKfix i _ (hfi _)
  · refine ⟨fun z hz ↦ (hKmap p).mapsTo ((hAJ _ (hκrange p)).1 hz),
      fun z hz ↦ (hAJ _ (hκrange p)).2.1 (hKimap p hz), hGF p, hFG p, fun z hz he ↦ ?_⟩
    have hfz := hboundary p z hz he
    exact ⟨hfz, by have hi := hGF p z hz; rw [hfz] at hi; exact hi⟩

end Poincare.Analysis
