import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.NormNum

theorem HasCompactSupport.comp_prodMk_right
    {T E A : Type*} [TopologicalSpace T] [TopologicalSpace E] [Zero A]
    {φ : T × E → A} (hφ : HasCompactSupport φ) (t : T) :
    HasCompactSupport (fun x => φ (t, x)) := by
  apply (hφ.isCompact.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  exact ⟨(t, x), tsupport_comp_subset_preimage φ
    (continuous_const.prodMk continuous_id) hx, rfl⟩

theorem DifferentiableAt.fderiv_prodMk_right_apply
    {𝕜 T E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {φ : T × E → F} {t : T} {x : E} (hφ : DifferentiableAt 𝕜 φ (t, x)) (v : E) :
    fderiv 𝕜 (fun y => φ (t, y)) x v = fderiv 𝕜 φ (t, x) (0, v) := by
  have heq := (hφ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  exact congrArg (fun L => L v) heq

theorem ContDiff.fderiv_fderiv_prodMk_right_apply
    {𝕜 T E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {φ : T × E → F} (hφ : ContDiff 𝕜 2 φ) (t : T) (x v : E) :
    fderiv 𝕜 (fun y => fderiv 𝕜 (fun z => φ (t, z)) y v) x v =
      fderiv 𝕜 (fun p => fderiv 𝕜 φ p (0, v)) (t, x) (0, v) := by
  have hfirst : ∀ y, fderiv 𝕜 (fun z => φ (t, z)) y v =
      fderiv 𝕜 φ (t, y) (0, v) := fun y =>
    (hφ.differentiable (by norm_num) (t, y)).fderiv_prodMk_right_apply v
  simp only [hfirst]
  have hD : ContDiff 𝕜 1 (fun p => fderiv 𝕜 φ p (0, v)) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (hD.differentiable one_ne_zero (t, x)).fderiv_prodMk_right_apply v
