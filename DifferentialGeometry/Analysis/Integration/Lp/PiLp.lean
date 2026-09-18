import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section
open scoped ENNReal BigOperators

namespace MeasureTheory.Lp

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
  (μ : Measure α)

private def piLpForward :
    Lp (PiLp 2 X) 2 μ →L[𝕜] PiLp 2 (fun i => Lp (X i) 2 μ) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun i => Lp (X i) 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ)

private theorem piLpForward_apply (u : Lp (PiLp 2 X) 2 μ) (i : ι) :
    (piLpForward (𝕜 := 𝕜) μ u i : α → X i) =ᵐ[μ] (fun a => u a i) := by
  exact (PiLp.proj (𝕜 := 𝕜) 2 X i).coeFn_compLpL u

private def piLpBackward (u : PiLp 2 (fun i => Lp (X i) 2 μ)) :
    Lp (PiLp 2 X) 2 μ :=
  (MemLp.of_eval_piLp (fun i => Lp.memLp (u i))).toLp
    (fun a => WithLp.toLp 2 (fun i => u i a))

omit [∀ i, NormedSpace 𝕜 (X i)] in
private theorem piLpBackward_apply (u : PiLp 2 (fun i => Lp (X i) 2 μ)) :
    (piLpBackward μ u : α → PiLp 2 X) =ᵐ[μ]
      (fun a => WithLp.toLp 2 (fun i => u i a)) :=
  MemLp.coeFn_toLp _

private theorem piLpBackward_forward (u : Lp (PiLp 2 X) 2 μ) :
    piLpBackward μ (piLpForward (𝕜 := 𝕜) μ u) = u := by
  apply Lp.ext
  have hf : ∀ᵐ a ∂μ, ∀ i, piLpForward (𝕜 := 𝕜) μ u i a = u a i :=
    ae_all_iff.mpr (piLpForward_apply (𝕜 := 𝕜) μ u)
  filter_upwards [piLpBackward_apply μ (piLpForward (𝕜 := 𝕜) μ u), hf] with a hb hf
  rw [hb]
  exact PiLp.ext hf

private theorem piLpForward_backward (u : PiLp 2 (fun i => Lp (X i) 2 μ)) :
    piLpForward (𝕜 := 𝕜) μ (piLpBackward μ u) = u := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [piLpForward_apply (𝕜 := 𝕜) μ (piLpBackward μ u) i, piLpBackward_apply μ u] with a hf hb
  rw [hf, hb]

private theorem norm_sq_eq_integral {Y : Type*} [NormedAddCommGroup Y]
    (u : Lp Y 2 μ) : ‖u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂μ := by
  have h := (Lp.memLp u).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hI : 0 ≤ ∫ a, ‖u a‖ ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [Lp.norm_def, h]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt hI]

private theorem integrable_norm_sq {Y : Type*} [NormedAddCommGroup Y]
    (u : Lp Y 2 μ) : Integrable (fun a => ‖u a‖ ^ 2) μ := by
  have h := (Lp.memLp u).norm_rpow
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  simpa using (memLp_one_iff_integrable.mp h)

private theorem piLpForward_norm (u : Lp (PiLp 2 X) 2 μ) :
    ‖piLpForward (𝕜 := 𝕜) μ u‖ = ‖u‖ := by
  have hn : ‖piLpForward (𝕜 := 𝕜) μ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, norm_sq_eq_integral μ]
    simp_rw [norm_sq_eq_integral μ]
    rw [← integral_finsetSum _ (fun i _ => integrable_norm_sq μ (piLpForward (𝕜 := 𝕜) μ u i))]
    apply integral_congr_ae
    have hf : ∀ᵐ a ∂μ, ∀ i, piLpForward (𝕜 := 𝕜) μ u i a = u a i :=
      ae_all_iff.mpr (piLpForward_apply (𝕜 := 𝕜) μ u)
    filter_upwards [hf] with a ha
    simp only [ha, PiLp.norm_sq_eq_of_L2]
  nlinarith only [hn, norm_nonneg (piLpForward (𝕜 := 𝕜) μ u), norm_nonneg u]

def piLpEquiv :
    Lp (PiLp 2 X) 2 μ ≃ₗᵢ[𝕜] PiLp 2 (fun i => Lp (X i) 2 μ) where
  toFun := piLpForward (𝕜 := 𝕜) μ
  invFun := piLpBackward μ
  left_inv := piLpBackward_forward (𝕜 := 𝕜) μ
  right_inv := piLpForward_backward (𝕜 := 𝕜) μ
  map_add' := map_add (piLpForward (𝕜 := 𝕜) μ)
  map_smul' := map_smul (piLpForward (𝕜 := 𝕜) μ)
  norm_map' := piLpForward_norm (𝕜 := 𝕜) μ

theorem piLpEquiv_apply (u : Lp (PiLp 2 X) 2 μ) (i : ι) :
    (piLpEquiv (𝕜 := 𝕜) μ u i : α → X i) =ᵐ[μ] (fun a => u a i) :=
  piLpForward_apply (𝕜 := 𝕜) μ u i

theorem piLpEquiv_symm_apply (u : PiLp 2 (fun i => Lp (X i) 2 μ)) :
    ((piLpEquiv (𝕜 := 𝕜) μ).symm u : α → PiLp 2 X) =ᵐ[μ]
      (fun a => WithLp.toLp 2 (fun i => u i a)) :=
  piLpBackward_apply μ u

theorem piLpEquiv_apply_eq (u : Lp (PiLp 2 X) 2 μ) (i : ι) :
    piLpEquiv (𝕜 := 𝕜) μ u i = (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ u := rfl

theorem proj_comp_piLpEquiv (i : ι) :
    (PiLp.proj (𝕜 := 𝕜) 2 (fun i => Lp (X i) 2 μ) i).comp
        (piLpEquiv (𝕜 := 𝕜) (X := X) μ).toContinuousLinearEquiv.toContinuousLinearMap =
      (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ := rfl

theorem compLpL_proj_piLpEquiv_symm (u : PiLp 2 (fun i => Lp (X i) 2 μ)) (i : ι) :
    (PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ ((piLpEquiv (𝕜 := 𝕜) μ).symm u) = u i := by
  rw [← piLpEquiv_apply_eq, LinearIsometryEquiv.apply_symm_apply]

theorem compLpL_proj_comp_piLpEquiv_symm (i : ι) :
    ((PiLp.proj (𝕜 := 𝕜) 2 X i).compLpL 2 μ).comp
        (piLpEquiv (𝕜 := 𝕜) (X := X) μ).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      PiLp.proj (𝕜 := 𝕜) 2 (fun i => Lp (X i) 2 μ) i := by
  apply ContinuousLinearMap.ext
  intro u
  exact compLpL_proj_piLpEquiv_symm (𝕜 := 𝕜) μ u i

variable {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace 𝕜 (Y i)]

theorem piLpEquiv_compLpL (L : ∀ i, X i →L[𝕜] Y i) (u : Lp (PiLp 2 X) 2 μ) :
    piLpEquiv (𝕜 := 𝕜) μ ((ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ u) =
      ContinuousLinearMap.piLpMap 2 (fun i => (L i).compLpL 2 μ) (piLpEquiv (𝕜 := 𝕜) μ u) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [piLpEquiv_apply (𝕜 := 𝕜) μ ((ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ u) i,
    (ContinuousLinearMap.piLpMap 2 L).coeFn_compLpL u,
    (L i).coeFn_compLpL (piLpEquiv (𝕜 := 𝕜) μ u i), piLpEquiv_apply (𝕜 := 𝕜) μ u i] with a h₁ h₂ h₃ h₄
  change piLpEquiv (𝕜 := 𝕜) μ ((ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ u) i a =
    ((L i).compLpL 2 μ (piLpEquiv (𝕜 := 𝕜) μ u i)) a
  rw [h₁, h₂, ContinuousLinearMap.piLpMap_apply, h₃, h₄]

theorem piLpEquiv_symm_piLpMap (L : ∀ i, X i →L[𝕜] Y i)
    (u : PiLp 2 (fun i => Lp (X i) 2 μ)) :
    (piLpEquiv (𝕜 := 𝕜) μ).symm
        (ContinuousLinearMap.piLpMap 2 (fun i => (L i).compLpL 2 μ) u) =
      (ContinuousLinearMap.piLpMap 2 L).compLpL 2 μ ((piLpEquiv (𝕜 := 𝕜) μ).symm u) := by
  apply (piLpEquiv (𝕜 := 𝕜) μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, piLpEquiv_compLpL,
    LinearIsometryEquiv.apply_symm_apply]

end MeasureTheory.Lp

open Filter MeasureTheory
open scoped Topology ENNReal

namespace MeasureTheory.Lp

theorem tendsto_piLp_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Ω X ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (μ : Measure Ω) {l : Filter X} {f : X → Lp (PiLp 2 E) 2 μ}
    {f0 : Lp (PiLp 2 E) 2 μ} :
    Tendsto f l (𝓝 f0) ↔ ∀ i,
      Tendsto (fun x => (PiLp.proj (𝕜 := 𝕜) 2 E i).compLpL 2 μ (f x)) l
        (𝓝 ((PiLp.proj (𝕜 := 𝕜) 2 E i).compLpL 2 μ f0)) := by
  constructor
  · intro hf i
    exact ((PiLp.proj (𝕜 := 𝕜) 2 E i).compLpL 2 μ).continuous.tendsto f0 |>.comp hf
  · intro hf
    let e := piLpEquiv (𝕜 := 𝕜) (X := E) μ
    have hc (i : ι) : Tendsto (fun x => e (f x) i) l (𝓝 (e f0 i)) := hf i
    have hp : Tendsto (fun x i => e (f x) i) l (𝓝 (fun i => e f0 i)) :=
      tendsto_pi_nhds.mpr hc
    have he : Tendsto (fun x => e (f x)) l (𝓝 (e f0)) :=
      (PiLp.continuous_toLp (p := 2) (β := fun i => Lp (E i) 2 μ)).tendsto _ |>.comp hp
    have hi : Tendsto (fun x => e.symm (e (f x))) l (𝓝 (e.symm (e f0))) :=
      (e.symm.continuous.tendsto (e f0)).comp he
    simpa only [e.symm_apply_apply] using hi

end MeasureTheory.Lp
