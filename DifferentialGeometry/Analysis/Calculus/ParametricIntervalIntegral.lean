import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Analysis.Calculus

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def inlCLM (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    E →L[ℝ] E × F :=
  (1 : E →L[ℝ] E).prod (0 : E →L[ℝ] F)

omit [ProperSpace E] [CompleteSpace F] in
private theorem fderiv_partial_eq_comp {f : E → ℝ → F} (p : E × ℝ)
    (hd : DifferentiableAt ℝ (fun q : E × ℝ => f q.1 q.2) p) :
    fderiv ℝ (fun y : E => f y p.2) p.1 =
      (fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p).comp (inlCLM E ℝ) := by
  have hseg : HasFDerivAt (fun y : E => (y, p.2)) (inlCLM E ℝ) p.1 := by
    dsimp [inlCLM]
    have hseg0 : HasFDerivAt (fun y : E => (y, (0 : ℝ)))
        ((1 : E →L[ℝ] E).prod (0 : E →L[ℝ] ℝ)) p.1 :=
      ContinuousLinearMap.hasFDerivAt
        (f := ((1 : E →L[ℝ] E).prod (0 : E →L[ℝ] ℝ) : E →L[ℝ] E × ℝ)) (x := p.1)
    have hcst : HasFDerivAt (fun y : E => (0, p.2)) (0 : E →L[ℝ] E × ℝ) p.1 :=
      by
        let c0 : E × ℝ := Prod.mk 0 p.2
        have hc0 : HasFDerivAt (fun _ : E => c0) (0 : E →L[ℝ] E × ℝ) p.1 :=
          hasFDerivAt_const c0 p.1
        have hfun : (fun y : E => (0, p.2)) = fun _ : E => c0 := by
          funext y
          rfl
        rwa [hfun]
    have hsum := hseg0.add hcst
    convert hsum using 1
    · ext y <;> simp [Prod.mk_add_mk]
    · simp [add_zero]
  have hcomp := hd.hasFDerivAt.comp p.1 hseg
  have hfun : (fun y : E => f y p.2) = (fun q : E × ℝ => f q.1 q.2) ∘ (fun y : E => (y, p.2)) := by
    funext y
    rfl
  rw [← hfun] at hcomp
  exact hcomp.fderiv

omit [ProperSpace E] [CompleteSpace F] in
private theorem partial_fderiv_contDiffOn {f : E → ℝ → F}
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => f p.1 p.2) Set.univ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => fderiv ℝ (fun y : E => f y p.2) p.1) Set.univ := by
  have hfd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p) Set.univ :=
    hf.fderiv_of_isOpen isOpen_univ
      (le_of_eq (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
  have hcompOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => (fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p).comp (inlCLM E ℝ)) Set.univ := by
    let precompA : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
      { toLinearMap :=
          { toFun := fun L => L.comp (inlCLM E ℝ)
            map_add' := by intro L M; ext x; simp
            map_smul' := by intro c L; ext x; simp }
        cont := by
          fun_prop }
    have hpre : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun L : (E × ℝ) →L[ℝ] F => L.comp (inlCLM E ℝ)) := by
      exact (precompA : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F).contDiff
    exact ContDiff.comp_contDiffOn hpre hfd
  convert hcompOn using 1
  funext p
  exact fderiv_partial_eq_comp (f := f) p
    (((hf p (Set.mem_univ _)).differentiableWithinAt (by
      norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem)

omit [CompleteSpace F] in
private theorem hasFDerivAt_paramIntervalIntegral (f : E → ℝ → F)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => f p.1 p.2) Set.univ)
    (x₀ : E) :
    HasFDerivAt (fun x : E => ∫ t in (0 : ℝ)..1, f x t)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E => f y t) x₀) x₀ := by
  let Ff : E → ℝ → F := f
  let F' : E → ℝ → E →L[ℝ] F := fun x t => fderiv ℝ (fun y : E => Ff y t) x
  let s : Set E := Metric.ball x₀ 1
  have hs : s ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by norm_num)
  have hFcont : ∀ x : E, Continuous (fun t : ℝ => Ff x t) := by
    intro x
    have hprod : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
    have hprodOn : ContinuousOn (fun t : ℝ => (x, t)) Set.univ := continuousOn_univ.mpr hprod
    have hcontOn := ((hf.of_le le_rfl).continuousOn.comp hprodOn (by intro t ht; trivial))
    exact continuousOn_univ.mp hcontOn
  have hF'_cont : ∀ x : E, Continuous (fun t : ℝ => F' x t) := by
    intro x
    have hpar : Continuous (fun p : E × ℝ => fderiv ℝ (fun y : E => f y p.2) p.1) :=
      continuousOn_univ.mp (partial_fderiv_contDiffOn hf).continuousOn
    have hprod : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
    exact hpar.comp hprod
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (Ff x) (volume.restrict (Ι (0 : ℝ) 1)) := by
    exact Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable)
  have hF_int : Integrable (Ff x₀) (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hIcc : IntegrableOn (Ff x₀) (Set.Icc (0 : ℝ) 1) volume :=
      ContinuousOn.integrableOn_Icc
        ((continuousOn_univ.mpr (hFcont x₀)).mono (by intro t ht; trivial))
    have hIoc : IntegrableOn (Ff x₀) (Ι (0 : ℝ) 1) volume :=
      hIcc.mono_set (by intro t ht; exact (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc] using ht)))
    simpa [IntegrableOn] using hIoc
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι (0 : ℝ) 1)) :=
    (hF'_cont x₀).aestronglyMeasurable
  have hfdCont : Continuous (fun p : E × ℝ => fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p) :=
    continuousOn_univ.mp (hf.fderiv_of_isOpen isOpen_univ
      (le_of_eq (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (↑(⊤ : ℕ∞) : WithTop ℕ∞)))).continuousOn
  have hfdNormCont : ContinuousOn (fun p : E × ℝ =>
      ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p‖)
      ((Metric.closedBall x₀ 1 : Set E).prod (Set.Icc (0 : ℝ) 1)) :=
    (continuous_norm.comp hfdCont).continuousOn
  have hcompct : IsCompact ((Metric.closedBall x₀ 1 : Set E).prod (Set.Icc (0 : ℝ) 1)) :=
    (isCompact_closedBall (x := x₀) (r := 1)).prod isCompact_Icc
  rcases IsCompact.exists_bound_of_continuousOn hcompct hfdNormCont with ⟨M, hM⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (x₀, 0) (by
    constructor <;> simp))
  let C : ℝ := ‖(inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ * (M + 1)
  have hCbound : ∀ y ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' y t‖ ≤ C := by
    intro y hy t ht
    have hyc : y ∈ Metric.closedBall x₀ 1 := by
      have hyt : dist y x₀ ≤ 1 := le_of_lt (Metric.mem_ball.mp hy)
      exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hyt)
    have hb : ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)‖ ≤ M := by
      simpa using hM (y, t) ⟨hyc, ht⟩
    have hcompnorm : ‖(fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)).comp (inlCLM E ℝ)‖ ≤
        ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)‖ * ‖(inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    calc
      ‖F' y t‖ = ‖(fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)).comp (inlCLM E ℝ)‖ := by
        congr 1
        exact fderiv_partial_eq_comp (f := f) (y, t)
          (((hf (y, t) (Set.mem_univ _)).differentiableWithinAt (by
            norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem)
      _ ≤ ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)‖ * ‖(inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ :=
        hcompnorm
      _ ≤ M * ‖(inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ := by
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ ‖(inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ * (M + 1) := by
        nlinarith [hM0, norm_nonneg (inlCLM E ℝ : E →L[ℝ] E × ℝ)]
      _ = C := by
        simp [C]
  have h_bound : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s, ‖F' x t‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro x hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have h0 : (0 : ℝ) ≤ t := le_of_lt (by simpa using ht.1)
      have h1 : t ≤ 1 := by simpa using ht.2
      exact ⟨h0, h1⟩
    exact hCbound x hx t htIcc
  have h_diff : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s,
      HasFDerivAt (fun y : E => Ff y t) (F' x t) x := by
    exact Eventually.of_forall (fun t => by
      intro x hx
      have hdiff : DifferentiableAt ℝ (fun y : E => Ff y t) x :=
        by
          have hdiffUnc : DifferentiableAt ℝ (fun q : E × ℝ => Ff q.1 q.2) (x, t) :=
            ((hf (x, t) (Set.mem_univ _)).differentiableWithinAt (by
              norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
          have hemb : DifferentiableAt ℝ (fun y : E => (y, t)) x := by
            have h0 : HasFDerivAt (fun y : E => (y, t)) (inlCLM E ℝ) x := by
              have hseg0 : HasFDerivAt (fun y : E => (y, (0 : ℝ)))
                  ((1 : E →L[ℝ] E).prod (0 : E →L[ℝ] ℝ)) x :=
                ContinuousLinearMap.hasFDerivAt
                  (f := ((1 : E →L[ℝ] E).prod (0 : E →L[ℝ] ℝ) : E →L[ℝ] E × ℝ)) (x := x)
              have hcst : HasFDerivAt (fun y : E => (0, t)) (0 : E →L[ℝ] E × ℝ) x := by
                let c0 : E × ℝ := Prod.mk 0 t
                have hc0 : HasFDerivAt (fun _ : E => c0) (0 : E →L[ℝ] E × ℝ) x :=
                  hasFDerivAt_const c0 x
                have hfun : (fun y : E => (0, t)) = fun _ : E => c0 := by
                  funext y
                  rfl
                rwa [hfun]
              have hsum := hseg0.add hcst
              convert hsum using 1
              · ext y <;> simp [Prod.mk_add_mk]
              · simp [inlCLM, add_zero]
            exact h0.differentiableAt
          exact hdiffUnc.comp x hemb
      simpa [F'] using hdiff.hasFDerivAt)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ι (0 : ℝ) 1))
    (F := Ff) (x₀ := x₀) (bound := fun _ : ℝ => C) (s := s) (F' := F')
    hs hF_meas hF_int hF'_meas h_bound
    (by
      simp) h_diff
  simpa [Ff, intervalIntegral] using hmain

theorem contDiffOn_paramIntervalIntegral (f : E → ℝ → F)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => f p.1 p.2) Set.univ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => ∫ t in (0 : ℝ)..1, f x t) Set.univ := by
  have hall : ∀ m : ℕ, ∀ (F' : Type) [NormedAddCommGroup F'] [NormedSpace ℝ F']
      [CompleteSpace F'], ∀ H : E → ℝ → F',
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => H p.1 p.2) Set.univ →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x : E => ∫ t in (0 : ℝ)..1, H x t) Set.univ := by
    intro m
    induction m with
    | zero =>
      intro F' hF'1 hF'2 hF'3 H hH
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (fun x : E => ∫ t in (0 : ℝ)..1, H x t) Set.univ
      rw [contDiffOn_zero]
      intro x hx
      rw [ContinuousWithinAt, nhdsWithin_univ]
      exact (hasFDerivAt_paramIntervalIntegral H hH x).continuousAt
    | succ m ih =>
      intro F' hF'1 hF'2 hF'3 H hH
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (fun x : E => ∫ t in (0 : ℝ)..1, H x t) Set.univ
      rw [contDiffOn_succ_iff_fderivWithin (s := Set.univ) uniqueDiffOn_univ]
      constructor
      · intro x hx
        exact (hasFDerivAt_paramIntervalIntegral H hH x).differentiableAt.differentiableWithinAt
      · constructor
        · intro hmω
          exact (WithTop.natCast_ne_top (α := ℕ∞) m hmω).elim
        · have hpar : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
              (fun p : E × ℝ => fderiv ℝ (fun y : E => H y p.2) p.1) Set.univ :=
            partial_fderiv_contDiffOn hH
          have hIH := ih (E →L[ℝ] F') (fun y t => fderiv ℝ (fun z : E => H z t) y) hpar
          have hfdEq : ∀ x : E, fderiv ℝ (fun y : E => ∫ t in (0 : ℝ)..1, H y t) x =
              ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E => H y t) x := by
            intro x
            exact (hasFDerivAt_paramIntervalIntegral H hH x).fderiv
          have hfw : (fun x : E => fderivWithin ℝ (fun y : E => ∫ t in (0 : ℝ)..1, H y t) Set.univ x) =
              (fun x : E => ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E => H y t) x) := by
            funext x
            rw [fderivWithin_univ, hfdEq x]
          simpa [hfw] using hIH
  rw [contDiffOn_iff_forall_nat_le]
  intro m hm
  exact hall m F f hf

end DifferentialGeometry.Analysis.Calculus
