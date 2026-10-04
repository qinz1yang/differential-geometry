import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSpray

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ContinuousDualEquiv E] [FiniteDimensional ℝ E]

theorem raisedKoszulOp_contDiffOn
    {n : WithTop ℕ∞} {U : Set E}
    {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {D : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContDiffOn ℝ n g U) (hD : ContDiffOn ℝ n D U)
    (hco : ∀ x ∈ U, IsCoercive (g x)) :
    ContDiffOn ℝ n (fun x => raisedKoszulOp (g x) (D x)) U := by
  let gram : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
    ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap
  let riesz : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
        (ContinuousDualEquiv.equiv (E := E)).symm.toContinuousLinearMap)).comp
      koszulCovCLM
  let post : (E →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)).comp
      (ContinuousLinearMap.compL ℝ E E E)
  have hunit : ∀ x ∈ U, IsUnit (gram (g x)) := by
    intro x hx
    let eB : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
      ContinuousLinearEquiv.ofBijective (g x)
        (LinearMap.ker_eq_bot.mpr (hco x hx).bilin_injective)
        (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective (hco x hx)))
    let e : E ≃L[ℝ] E := eB.trans (ContinuousDualEquiv.equiv (E := E)).symm
    exact ⟨e.toUnit, rfl⟩
  have hgram : ContDiffOn ℝ n (fun x => gram (g x)) U :=
    gram.contDiff.comp_contDiffOn hg
  have hinv : ContDiffOn ℝ n (fun x => Ring.inverse (gram (g x))) U :=
    (DifferentialGeometry.Analysis.contDiffOn_ringInverse
      (R := E →L[ℝ] E) (𝕜 := ℝ) n).comp hgram hunit
  have hriesz : ContDiffOn ℝ n (fun x => riesz (D x)) U :=
    riesz.contDiff.comp_contDiffOn hD
  change ContDiffOn ℝ n (fun x => post (Ring.inverse (gram (g x))) (riesz (D x))) U
  exact post.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hinv hriesz

theorem raisedOp_contDiffOn_succ
    {n : WithTop ℕ∞} {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContDiffOn ℝ (n + 1) g U)
    (hco : ∀ x ∈ U, IsCoercive (g x)) :
    ContDiffOn ℝ n (fun x => raisedKoszulOp (g x) (fderiv ℝ g x)) U := by
  exact raisedKoszulOp_contDiffOn
    (hg.of_le (le_add_of_nonneg_right zero_le_one))
    (hg.fderiv_of_isOpen hU le_rfl) hco

theorem metricSpray_contDiffOn_succ
    {n : WithTop ℕ∞} {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContDiffOn ℝ (n + 1) g U)
    (hco : ∀ x ∈ U, IsCoercive (g x)) :
    ContDiffOn ℝ n (metricSpray g) (U ×ˢ Set.univ) := by
  have hR := raisedOp_contDiffOn_succ hU hg hco
  have hdiag : ContDiffOn ℝ n
      (fun z : E × E => raisedKoszulOp (g z.1) (fderiv ℝ g z.1) z.2 z.2)
      (U ×ˢ Set.univ) :=
    ((hR.comp contDiffOn_fst (fun z hz => hz.1)).clm_apply
      contDiffOn_snd).clm_apply contDiffOn_snd
  exact contDiffOn_snd.prodMk hdiag.neg

end DifferentialGeometry.MetricKoszul
