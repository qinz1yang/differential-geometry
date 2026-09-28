import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Coefficients
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Uniqueness
import DifferentialGeometry.Analysis.Parabolic.Euclidean.PeriodicJet

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis.Parabolic

private theorem graph_diffusion_sub_residual_norm_le
    {P E : Type*} [NormedAddCommGroup P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : P) (r s : E) :
    ‖(graphDiffusionCoefficient p • r - graphDiffusionCoefficient q • s) -
        graphDiffusionCoefficient p • (r - s)‖ ≤ ‖p - q‖ * ‖s‖ := by
  have heq : (graphDiffusionCoefficient p • r - graphDiffusionCoefficient q • s) -
      graphDiffusionCoefficient p • (r - s) =
        (graphDiffusionCoefficient p - graphDiffusionCoefficient q) • s := by
    simp only [smul_sub, sub_smul]
    abel
  rw [heq, norm_smul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    (graphDiffusionCoefficient_lipschitz (E := P)).dist_le_mul p q

private theorem graph_diffusion_sub_residual_norm_le_of_norm_le
    {P E : Type*} [NormedAddCommGroup P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : P) (r s : E) {B : ℝ} (hs : ‖s‖ ≤ B) :
    ‖(graphDiffusionCoefficient p • r - graphDiffusionCoefficient q • s) -
        graphDiffusionCoefficient p • (r - s)‖ ≤ B * ‖p - q‖ := by
  exact (graph_diffusion_sub_residual_norm_le p q r s).trans
    ((mul_le_mul_of_nonneg_left hs (norm_nonneg (p - q))).trans_eq (mul_comm _ _))

private theorem graphical_equation_difference_residual_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → ℝ → E) {t x B : ℝ}
    (hF : ContDiff ℝ 2 (F t)) (hG : ContDiff ℝ 2 (G t))
    (hFt : HasDerivAt (fun s => F s x)
      (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t)
    (hGt : HasDerivAt (fun s => G s x)
      (graphDiffusionCoefficient (deriv (G t) x) • deriv (deriv (G t)) x) t)
    (hGxx : ‖deriv (deriv (G t)) x‖ ≤ B) :
    let w := fun s y => F s y - G s y
    ‖deriv (fun s => w s x) t -
        graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (w t)) x‖ ≤
      B * ‖deriv (w t) x‖ := by
  intro w
  have hFx := hF.differentiable (by norm_num)
  have hGx := hG.differentiable (by norm_num)
  have hFd : Differentiable ℝ (deriv (F t)) :=
    hF.differentiable_deriv_two
  have hGd : Differentiable ℝ (deriv (G t)) :=
    hG.differentiable_deriv_two
  have hx : deriv (w t) = fun y => deriv (F t) y - deriv (G t) y := by
    funext y
    exact deriv_sub (hFx y) (hGx y)
  have hxx : deriv (deriv (w t)) x = deriv (deriv (F t)) x - deriv (deriv (G t)) x := by
    rw [hx]
    exact deriv_sub (hFd x) (hGd x)
  have ht : deriv (fun s => w s x) t =
      graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x -
        graphDiffusionCoefficient (deriv (G t) x) • deriv (deriv (G t)) x :=
    (hFt.sub hGt).deriv
  rw [ht, hxx, hx]
  exact graph_diffusion_sub_residual_norm_le_of_norm_le _ _ _ _ hGxx

private theorem graphical_curve_shortening_eq_of_derivative_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F G : ℝ → ℝ → E) {s T R B : ℝ} (hsT : s < T) (hB : 0 ≤ B)
    (hFper : ∀ t ∈ Icc s T, Function.Periodic (F t) 1)
    (hGper : ∀ t ∈ Icc s T, Function.Periodic (G t) 1)
    (hFcont : ContinuousOn (Function.uncurry F) (Icc s T ×ˢ Icc 0 1))
    (hGcont : ContinuousOn (Function.uncurry G) (Icc s T ×ˢ Icc 0 1))
    (hFspace : ∀ t ∈ Ioo s T, ContDiff ℝ 2 (F t))
    (hGspace : ∀ t ∈ Ioo s T, ContDiff ℝ 2 (G t))
    (hFtime : ∀ t ∈ Ioo s T, ∀ x, HasDerivAt (fun r => F r x)
      (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t)
    (hGtime : ∀ t ∈ Ioo s T, ∀ x, HasDerivAt (fun r => G r x)
      (graphDiffusionCoefficient (deriv (G t) x) • deriv (deriv (G t)) x) t)
    (hFslope : ∀ t ∈ Ioo s T, ∀ x, ‖deriv (F t) x‖ ≤ R)
    (hGsecond : ∀ t ∈ Ioo s T, ∀ x, ‖deriv (deriv (G t)) x‖ ≤ B)
    (hinit : ∀ x, F s x = G s x) :
    ∀ t ∈ Icc s T, ∀ x, F t x = G t x := by
  classical
  let w : ℝ → ℝ → E := fun x t => if t ∈ Icc s T then F t x - G t x else 0
  have hw (t : ℝ) (ht : t ∈ Icc s T) :
      (fun x => w x t) = fun x => F t x - G t x := by
    funext x
    exact ite_eq_left ht
  have hwt (x t : ℝ) (ht : t ∈ Ioo s T) :
      (fun r => w x r) =ᶠ[𝓝 t] fun r => F r x - G r x := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact ite_eq_left hr
  have hwper (x t : ℝ) : w (x + 1) t = w x t := by
    by_cases ht : t ∈ Icc s T
    · simp only [w, ite_eq_left ht, hFper t ht x, hGper t ht x]
    · simp only [w, ite_eq_right ht]
  have hwcont : ContinuousOn (Function.uncurry w) (Icc 0 1 ×ˢ Icc s T) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1 - G p.2 p.1)
        (Icc 0 1 ×ˢ Icc s T) :=
      (hFcont.sub hGcont).comp continuous_swap.continuousOn (fun _ ht => ⟨ht.2, ht.1⟩)
    apply hc.congr
    intro p hp
    exact ite_eq_left hp.2
  have hwtime (x t : ℝ) (ht : t ∈ Ioo s T) :
      DifferentiableAt ℝ (fun r => w x r) t :=
    ((hFtime t ht x).sub (hGtime t ht x)).differentiableAt.congr_of_eventuallyEq (hwt x t ht)
  have hzero := periodic_eq_zero_of_parabolic_residual_bound
    (u := w) (a := fun x t => graphDiffusionCoefficient (deriv (F t) x))
    (δ := (1 + R ^ 2)⁻¹) (L := B) hsT (by positivity) hwper hwcont
    (fun x => by rw [congrFun (hw s ⟨le_rfl, hsT.le⟩) x, hinit, sub_self])
    (fun x t ht => by
      rw [hw t ⟨ht.1.le, ht.2.le⟩]
      exact ((hFspace t ht).sub (hGspace t ht)).contDiffAt)
    hwtime (fun x t ht => graphDiffusionCoefficient_lower_bound (hFslope t ht x))
    (fun x t ht => by
      rw [(hwt x t ht).deriv_eq, hw t ⟨ht.1.le, ht.2.le⟩]
      have h := graphical_equation_difference_residual_norm_le F G (hFspace t ht) (hGspace t ht)
        (hFtime t ht x) (hGtime t ht x) (hGsecond t ht x)
      exact h.trans (by
        rw [congrFun (hw t ⟨ht.1.le, ht.2.le⟩) x]
        nlinarith [mul_nonneg hB (norm_nonneg (F t x - G t x))]))
  intro t ht x
  exact sub_eq_zero.mp ((congrFun (hw t ht) x).symm.trans (hzero x t ht))

theorem graphical_curve_shortening_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F G : ℝ → ℝ → E) {s T : ℝ} (hsT : s ≤ T)
    (hFper : ∀ t ∈ Icc s T, Function.Periodic (F t) 1)
    (hGper : ∀ t ∈ Icc s T, Function.Periodic (G t) 1)
    (hFcont : ContinuousOn (Function.uncurry F) (Icc s T ×ˢ Icc 0 1))
    (hGcont : ContinuousOn (Function.uncurry G) (Icc s T ×ˢ Icc 0 1))
    (hFspace : ∀ t ∈ Ioo s T, ContDiff ℝ 2 (F t))
    (hGspace : ∀ t ∈ Ioo s T, ContDiff ℝ 2 (G t))
    (hFtime : ∀ t ∈ Ioo s T, ∀ x, HasDerivAt (fun r => F r x)
      (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t)
    (hGtime : ∀ t ∈ Ioo s T, ∀ x, HasDerivAt (fun r => G r x)
      (graphDiffusionCoefficient (deriv (G t) x) • deriv (deriv (G t)) x) t)
    (hFslope : ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc s T ×ˢ Icc 0 1))
    (hGsecond : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (G p.1)) p.2) (Icc s T ×ˢ Icc 0 1))
    (hinit : ∀ x, F s x = G s x) :
    ∀ t ∈ Icc s T, ∀ x, F t x = G t x := by
  rcases hsT.eq_or_lt with rfl | hsT
  · intro t ht x
    have he : t = s := le_antisymm ht.2 ht.1
    subst t
    exact hinit x
  obtain ⟨R, hR⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hFslope
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hGsecond
  apply graphical_curve_shortening_eq_of_derivative_bounds F G hsT (le_max_right B 0)
    hFper hGper hFcont hGcont hFspace hGspace hFtime hGtime (R := R) (B := max B 0)
  · intro t ht x
    have ht' : t ∈ Icc s T := ⟨ht.1.le, ht.2.le⟩
    obtain ⟨y, hy, he⟩ := (hFper t ht').deriv.exists_mem_Ico₀ (by norm_num : (0 : ℝ) < 1) x
    rw [he]
    exact hR (t, y) ⟨ht', hy.1, hy.2.le⟩
  · intro t ht x
    have ht' : t ∈ Icc s T := ⟨ht.1.le, ht.2.le⟩
    obtain ⟨y, hy, he⟩ := (hGper t ht').deriv.deriv.exists_mem_Ico₀ (by norm_num : (0 : ℝ) < 1) x
    rw [he]
    exact (hB (t, y) ⟨ht', hy.1, hy.2.le⟩).trans (le_max_left B 0)
  · exact hinit

end DifferentialGeometry.Analysis.Parabolic
