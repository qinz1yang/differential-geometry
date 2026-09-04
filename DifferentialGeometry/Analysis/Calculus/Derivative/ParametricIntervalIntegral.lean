import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Analysis.Calculus

universe uE uF

variable {E : Type uE} {F : Type uF}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def inlCLM (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    E →L[ℝ] E × F :=
  (1 : E →L[ℝ] E).prod (0 : E →L[ℝ] F)

omit [ProperSpace E] [CompleteSpace F] in
private theorem fderiv_partial_eq_comp {f : E → ℝ → F} (p : E × ℝ)
    (hd : DifferentiableAt ℝ (fun q : E × ℝ => f q.1 q.2) p) :
    fderiv ℝ (fun y : E => f y p.2) p.1 =
      (fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p).comp (inlCLM E ℝ) := by
  have hseg : HasFDerivAt (fun y : E => (y, p.2)) (inlCLM E ℝ) p.1 := by
    change HasFDerivAt (fun y : E => (id y, p.2))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) p.1
    exact (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
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
              change HasFDerivAt (fun y : E => (id y, t))
                ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x
              exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
            exact h0.differentiableAt
          exact hdiffUnc.comp x hemb
      simpa [F'] using hdiff.hasFDerivAt)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ι (0 : ℝ) 1))
    (F := Ff) (x₀ := x₀) (bound := fun _ : ℝ => C) (s := s) (F' := F')
    hs hF_meas hF_int hF'_meas h_bound
    (by
      simp) h_diff
  simpa [Ff, intervalIntegral] using hmain

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem paramInt_tube
    (G : E × ℝ → F) (U : Set E) (hU : IsOpen U)
    (a b : ℝ) (S : Set ℝ) (hSI : Set.uIcc a b ⊆ S)
    (x₀ : E) (hx₀ : x₀ ∈ U) (hG : ContinuousOn G (U ×ˢ S)) :
    ∃ C : ℝ, ∀ᶠ x in nhds x₀, ∀ t ∈ Ι a b, ‖G (x, t)‖ ≤ C := by
  obtain ⟨K, ⟨hKnhds, hKcomp⟩, hKU⟩ :=
    (compact_basis_nhds x₀).mem_iff.1 (hU.mem_nhds hx₀)
  have hcompact : IsCompact (K ×ˢ Set.uIcc a b) :=
    hKcomp.prod isCompact_uIcc
  have hsub : K ×ˢ Set.uIcc a b ⊆ U ×ˢ S :=
    fun p hp ↦ ⟨hKU hp.1, hSI hp.2⟩
  obtain ⟨C, hC⟩ :=
    (hcompact.image_of_continuousOn (hG.mono hsub).norm).bddAbove
  exact ⟨C, by
    filter_upwards [hKnhds] with x hx t ht
    exact hC ⟨(x, t), ⟨hx, Set.uIoc_subset_uIcc ht⟩, rfl⟩⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [ProperSpace E] [CompleteSpace F] in
private theorem paramInt_slice
    (G : E × ℝ → F) (U : Set E) (hU : IsOpen U)
    (S : Set ℝ) (hS : IsOpen S)
    (hG : ContinuousOn G (U ×ˢ S)) (x : E) (hx : x ∈ U) :
    ContinuousOn (fun t : ℝ ↦ G (x, t)) S := by
  intro t ht
  refine (hG.continuousAt ((hU.prod hS).mem_nhds ⟨hx, ht⟩)).comp_continuousWithinAt ?_
  exact continuousWithinAt_const.prodMk continuousWithinAt_id

omit [ProperSpace E] [CompleteSpace F] in
private theorem paramInt_fderiv
    (G : E × ℝ → F) (U : Set E) (hU : IsOpen U)
    (S : Set ℝ) (hS : IsOpen S)
    (hG : ContDiffOn ℝ 1 G (U ×ˢ S)) :
    ContDiffOn ℝ 0
      (fun p : E × ℝ ↦ fderiv ℝ (fun x : E ↦ G (x, p.2)) p.1)
      (U ×ˢ S) := by
  have hopen : IsOpen (U ×ˢ S) := hU.prod hS
  rw [hopen.contDiffOn_iff] at hG ⊢
  intro p hp
  apply ContDiffAt.fderiv (n := (1 : WithTop ℕ∞)) (m := (0 : WithTop ℕ∞))
  · exact (hG hp).comp _
      (by
        fun_prop : ContDiffAt ℝ 1
          (fun w : (E × ℝ) × E ↦ (w.2, w.1.2)) (p, p.1))
  · fun_prop
  · norm_num

omit [CompleteSpace F] in
theorem hasFDerivAt_paramInt
    (f : E → ℝ → F) (U : Set E) (hU : IsOpen U)
    (a b : ℝ) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc a b ⊆ S) (x₀ : E) (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℝ 1 (fun p : E × ℝ ↦ f p.1 p.2) (U ×ˢ S)) :
    HasFDerivAt (fun x : E ↦ ∫ t in a..b, f x t)
      (∫ t in a..b, fderiv ℝ (fun y : E ↦ f y t) x₀) x₀ := by
  let G : E × ℝ → F := fun p ↦ f p.1 p.2
  let Gp : E × ℝ → E →L[ℝ] F := fun p ↦
    fderiv ℝ (fun y : E ↦ G (y, p.2)) p.1
  have hfG : ContDiffOn ℝ 1 G (U ×ˢ S) := by
    simpa only [G] using hf
  have hopen : IsOpen (U ×ˢ S) := hU.prod hS
  have hGc : ContinuousOn G (U ×ˢ S) := hf.continuousOn
  have hGp : ContDiffOn ℝ 0 Gp (U ×ˢ S) := by
    simpa only [Gp] using paramInt_fderiv G U hU S hS hfG
  have hGpc : ContinuousOn Gp (U ×ˢ S) := hGp.continuousOn
  obtain ⟨C, hC⟩ := paramInt_tube Gp U hU a b S hSI x₀ hx₀ hGpc
  let s : Set E := {x | ∀ t ∈ Ι a b, ‖Gp (x, t)‖ ≤ C} ∩ U
  have hs : s ∈ nhds x₀ := Filter.inter_mem hC (hU.mem_nhds hx₀)
  have hsU : s ⊆ U := Set.inter_subset_right
  have hI : ∀ t ∈ Ι a b, t ∈ S :=
    fun t ht ↦ hSI (Set.uIoc_subset_uIcc ht)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (μ := volume) (F := fun x t ↦ G (x, t))
    (F' := fun x t ↦ Gp (x, t)) (bound := fun _ ↦ C)
    (x₀ := x₀) (s := s) (a := a) (b := b) hs
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    exact ((paramInt_slice G U hU S hS hGc x hx).mono
      (fun t ht ↦ hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
  · exact ((paramInt_slice G U hU S hS hGc x₀ hx₀).mono hSI).intervalIntegrable
  · exact ((paramInt_slice Gp U hU S hS hGpc x₀ hx₀).mono
      (fun t ht ↦ hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
  · rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all _ fun t ht x hx ↦ hx.1 t ht
  · exact intervalIntegrable_const
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine ae_of_all _ fun t ht x hx ↦ ?_
    have hmem : ((x, t) : E × ℝ) ∈ U ×ˢ S := ⟨hsU hx, hI t ht⟩
    have hAt : ContDiffAt ℝ 1 G (x, t) :=
      hfG.contDiffAt (hopen.mem_nhds hmem)
    have hslice : ContDiffAt ℝ 1 (fun y : E ↦ G (y, t)) x :=
      hAt.comp₂ contDiffAt_id contDiffAt_const
    simpa only [Gp, G] using (hslice.differentiableAt (by norm_num)).hasFDerivAt

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem paramInt_tendstoUniform
    (G : E × ℝ → F) (K U : Set E) (S : Set ℝ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsOpen S) (h0S : 0 ∈ S)
    (hG : ContinuousOn G (U ×ˢ S)) :
    TendstoUniformlyOn
      (fun s z ↦ ∫ t in (0 : ℝ)..1, G (z, t * s))
      (fun z ↦ G (z, 0)) (𝓝 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hS 0 h0S
  let r₀ : ℝ := r / 2
  have hr₀ : 0 < r₀ := div_pos hr (by norm_num)
  let C : Set (E × ℝ) := K ×ˢ Metric.closedBall 0 r₀
  have hCcompact : IsCompact C := hK.prod (isCompact_closedBall 0 r₀)
  have hCsub : C ⊆ U ×ˢ S := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    refine ⟨hKU hz, hrS ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hs
    exact hs.trans_lt (by dsimp only [r₀]; linarith)
  have hGc : ContinuousOn G C := hG.mono hCsub
  have hGu : UniformContinuousOn G C :=
    hCcompact.uniformContinuousOn_of_continuous hGc
  rw [Metric.uniformContinuousOn_iff] at hGu
  obtain ⟨δ, hδ, hδG⟩ := hGu (ε / 2) (by positivity)
  filter_upwards [Metric.ball_mem_nhds 0 (lt_min hr₀ hδ)] with s hs z hz
  have hs' : |s| < min r₀ δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs
  have hs_r : |s| < r₀ := hs'.trans_le (min_le_left _ _)
  have hs_δ : |s| < δ := hs'.trans_le (min_le_right _ _)
  have hpath : Continuous (fun t : ℝ ↦ (z, t * s)) :=
    continuous_const.prodMk (continuous_id.mul continuous_const)
  have hmaps : Set.MapsTo (fun t : ℝ ↦ (z, t * s)) (Set.Icc 0 1) C := by
    intro t ht
    refine ⟨hz, ?_⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul]
    have ht_abs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    exact (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg s)).trans
      (by simpa only [one_mul] using hs_r.le)
  have hslice : ContinuousOn (fun t : ℝ ↦ G (z, t * s)) (Set.Icc 0 1) :=
    hGc.comp hpath.continuousOn hmaps
  have hslice_int : IntervalIntegrable (fun t : ℝ ↦ G (z, t * s)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hslice
  have hconst : (∫ _t : ℝ in (0 : ℝ)..1, G (z, 0)) = G (z, 0) := by
    simp
  rw [dist_eq_norm, norm_sub_rev, ← hconst,
    ← intervalIntegral.integral_sub hslice_int intervalIntegrable_const]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2)
    fun t ht ↦ ?_).trans_lt ?_
  · have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      exact ⟨htIoc.1.le, htIoc.2⟩
    have hzt : (z, t * s) ∈ C := hmaps htIcc
    have hz0 : (z, (0 : ℝ)) ∈ C := by
      refine ⟨hz, Metric.mem_closedBall_self hr₀.le⟩
    have hclose := (hδG _ hzt _ hz0 (by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq,
        sub_zero, abs_mul]
      have ht_abs : |t| ≤ 1 := by
        rw [abs_of_nonneg htIcc.1]
        exact htIcc.2
      exact (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg s)).trans_lt
        (by simpa only [one_mul] using hs_δ))).le
    simpa only [dist_eq_norm] using hclose
  · simpa only [abs_sub_comm, sub_zero, abs_one, mul_one] using (half_lt_self hε)

theorem contDiffOn_paramIntervalIntegral
    {E₀ : Type uE} {F₀ : Type uF}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [ProperSpace E₀] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    [CompleteSpace F₀] (f : E₀ → ℝ → F₀)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E₀ × ℝ => f p.1 p.2) Set.univ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E₀ => ∫ t in (0 : ℝ)..1, f x t) Set.univ := by
  have hall : ∀ m : ℕ, ∀ (F' : Type (max uE uF))
      [NormedAddCommGroup F'] [NormedSpace ℝ F']
      [CompleteSpace F'], ∀ H : E₀ → ℝ → F',
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : E₀ × ℝ => H p.1 p.2) Set.univ →
      ContDiffOn ℝ (m : WithTop ℕ∞)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, H x t) Set.univ := by
    intro m
    induction m with
    | zero =>
      intro F' hF'1 hF'2 hF'3 H hH
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, H x t) Set.univ
      rw [contDiffOn_zero]
      intro x hx
      rw [ContinuousWithinAt, nhdsWithin_univ]
      exact (hasFDerivAt_paramIntervalIntegral H hH x).continuousAt
    | succ m ih =>
      intro F' hF'1 hF'2 hF'3 H hH
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, H x t) Set.univ
      rw [contDiffOn_succ_iff_fderivWithin (s := Set.univ) uniqueDiffOn_univ]
      constructor
      · intro x hx
        exact (hasFDerivAt_paramIntervalIntegral H hH x).differentiableAt.differentiableWithinAt
      · constructor
        · intro hmω
          exact (WithTop.natCast_ne_top (α := ℕ∞) m hmω).elim
        · have hpar : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
              (fun p : E₀ × ℝ => fderiv ℝ (fun y : E₀ => H y p.2) p.1) Set.univ :=
            partial_fderiv_contDiffOn hH
          have hIH := ih (E₀ →L[ℝ] F')
            (fun y t => fderiv ℝ (fun z : E₀ => H z t) y) hpar
          have hfdEq : ∀ x : E₀,
              fderiv ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, H y t) x =
                ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E₀ => H y t) x := by
            intro x
            exact (hasFDerivAt_paramIntervalIntegral H hH x).fderiv
          have hfw : (fun x : E₀ =>
              fderivWithin ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, H y t) Set.univ x) =
              (fun x : E₀ => ∫ t in (0 : ℝ)..1,
                fderiv ℝ (fun y : E₀ => H y t) x) := by
            funext x
            rw [fderivWithin_univ, hfdEq x]
          simpa [hfw] using hIH
  rw [contDiffOn_iff_forall_nat_le]
  intro m _hm
  cases m with
  | zero =>
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, f x t) Set.univ
      rw [contDiffOn_zero]
      intro x hx
      rw [ContinuousWithinAt, nhdsWithin_univ]
      exact (hasFDerivAt_paramIntervalIntegral f hf x).continuousAt
  | succ m =>
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, f x t) Set.univ
      rw [contDiffOn_succ_iff_fderivWithin (s := Set.univ) uniqueDiffOn_univ]
      constructor
      · intro x hx
        exact (hasFDerivAt_paramIntervalIntegral f hf x).differentiableAt.differentiableWithinAt
      · constructor
        · intro hmω
          exact (WithTop.natCast_ne_top (α := ℕ∞) m hmω).elim
        · have hpar : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
              (fun p : E₀ × ℝ => fderiv ℝ (fun y : E₀ => f y p.2) p.1) Set.univ :=
            partial_fderiv_contDiffOn hf
          have hIH := hall m (E₀ →L[ℝ] F₀)
            (fun y t => fderiv ℝ (fun z : E₀ => f z t) y) hpar
          have hfdEq : ∀ x : E₀,
              fderiv ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, f y t) x =
                ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E₀ => f y t) x := by
            intro x
            exact (hasFDerivAt_paramIntervalIntegral f hf x).fderiv
          have hfw : (fun x : E₀ =>
              fderivWithin ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, f y t) Set.univ x) =
              (fun x : E₀ => ∫ t in (0 : ℝ)..1,
                fderiv ℝ (fun y : E₀ => f y t) x) := by
            funext x
            rw [fderivWithin_univ, hfdEq x]
          simpa [hfw] using hIH

end DifferentialGeometry.Analysis.Calculus
