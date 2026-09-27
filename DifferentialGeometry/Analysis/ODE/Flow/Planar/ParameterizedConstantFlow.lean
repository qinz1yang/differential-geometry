import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantOutsideCompactFlow
import DifferentialGeometry.Analysis.Calculus.Cutoff.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter Topology Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
theorem exists_smoothFlow_family_of_uniform_const_off_compact
    {v : P × E → E} (hv : ContDiff ℝ ∞ v) (c : E)
    {K : Set P} (hK : IsCompact K) {L : Set E} (hL : IsCompact L)
    (hfixed : ∀ p x, x ∉ L → v (p, x) = c) :
    ∃ D : P → ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : P × ℝ × E ↦ D q.1 q.2.1 q.2.2) ∧
      (∀ p ∈ K, ∀ x t, HasDerivAt (fun r ↦ D p r x) (v (p, D p t x)) t) ∧
      (∀ p, D p 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞) ∧
      (∀ p s t, D p (s + t) = (D p s).trans (D p t)) ∧
      ∀ p t, (D p t).symm = D p (-t) := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : P)
  obtain ⟨χ, hχ, hχone, hχsupp, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_one_on hK isOpen_ball hKR
  have hχcompact : IsCompact (tsupport χ) := (isCompact_closedBall (0 : P) R).of_isClosed_subset
    (isClosed_tsupport χ) (hχsupp.trans ball_subset_closedBall)
  let W : P × E → P × E := fun q ↦ (0, c + χ q.1 • (v q - c))
  have hW : ContDiff ℝ ∞ W := contDiff_const.prodMk
    (contDiff_const.add ((hχ.comp contDiff_fst).smul (hv.sub contDiff_const)))
  have hWcompact : HasCompactSupport (fun q ↦ W q - (0, c)) := by
    apply HasCompactSupport.intro (hχcompact.prod hL)
    intro q hq
    by_cases hp : q.1 ∈ tsupport χ
    · have hx : q.2 ∉ L := fun hx ↦ hq ⟨hp, hx⟩
      simp [W, hfixed q.1 q.2 hx]
    · simp [W, image_eq_zero_of_notMem_tsupport hp]
  obtain ⟨F, hF, hderiv, hzero, hadd, hinv⟩ :=
    exists_smoothFlow_of_eq_const_off_compact hW (0, c) hWcompact
  have hparam (q : P × E) (t : ℝ) : (F t q).1 = q.1 := by
    have hd (r : ℝ) : HasDerivAt (fun r ↦ (F r q).1) (0 : P) r := (hderiv q r).fst
    have he := is_const_of_deriv_eq_zero (fun r ↦ (hd r).differentiableAt)
      (fun r ↦ (hd r).deriv) t 0
    exact he.trans (by rw [hzero]; rfl)
  have hpair (p : P) (t : ℝ) (x : E) : (p, (F t (p, x)).2) = F t (p, x) :=
    Prod.ext (hparam (p, x) t).symm rfl
  let D (p : P) (t : ℝ) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { toEquiv :=
        { toFun := fun x ↦ (F t (p, x)).2
          invFun := fun x ↦ (F (-t) (p, x)).2
          left_inv := fun x ↦ by
            change (F (-t) (p, (F t (p, x)).2)).2 = x
            rw [hpair, ← hinv, (F t).symm_apply_apply]
          right_inv := fun x ↦ by
            change (F t (p, (F (-t) (p, x)).2)).2 = x
            rw [hpair, ← hinv, (F t).apply_symm_apply] }
      contMDiff_toFun := (hF.comp
        (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).snd.contMDiff
      contMDiff_invFun := (hF.comp
        (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).snd.contMDiff }
  have hD : ContDiff ℝ ∞ (fun q : P × ℝ × E ↦ D q.1 q.2.1 q.2.2) :=
    (hF.comp (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd))).snd
  refine ⟨D, hD, ?_, ?_, ?_, ?_⟩
  · intro p hp x t
    have hd : HasDerivAt (fun r ↦ (F r (p, x)).2) (W (F t (p, x))).2 t :=
      (hderiv (p, x) t).snd
    have hs : (W (F t (p, x))).2 = v (p, D p t x) := by
      change c + χ (F t (p, x)).1 • (v (F t (p, x)) - c) = _
      rw [← hpair, hχone hp]
      simp only [Pi.one_apply, one_smul]
      change c + (v (p, D p t x) - c) = _
      abel
    rw [hs] at hd
    exact hd
  · intro p
    apply Diffeomorph.ext
    intro x
    change (F 0 (p, x)).2 = x
    rw [hzero]
    rfl
  · intro p s t
    apply Diffeomorph.ext
    intro x
    change (F (s + t) (p, x)).2 = (F t (p, (F s (p, x)).2)).2
    rw [hpair, hadd]
    rfl
  · intro p t
    apply Diffeomorph.ext
    exact fun _ ↦ rfl

end DifferentialGeometry.Analysis
