import DifferentialGeometry.Analysis.InnerProductSpace.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter InnerProductSpace
open scoped Topology ContDiff InnerProductSpace

private theorem second_partial_norm_sq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => ‖f y‖ ^ 2) q v) x w =
      2 * ⟪fderiv ℝ f x w, fderiv ℝ f x v⟫_ℝ +
        2 * ⟪f x, fderiv ℝ (fderiv ℝ f) x w v⟫_ℝ := by
  have hd := hf.differentiableAt (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) x :=
    hdd.clm_apply (differentiableAt_const v)
  have hnear : (fun q => fderiv ℝ (fun y => ‖f y‖ ^ 2) q v) =ᶠ[𝓝 x]
      (fun q => 2 * ⟪f q, fderiv ℝ f q v⟫_ℝ) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    rw [(hq.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp [two_smul, two_mul]
  rw [hnear.fderiv_eq]
  erw [fderiv_const_mul (hd.inner ℝ hp) (2 : ℝ)]
  simp only [_root_.smul_apply, smul_eq_mul]
  have hpderiv : fderiv ℝ (fun q => fderiv ℝ f q v) x w =
      fderiv ℝ (fderiv ℝ f) x w v := by
    rw [fderiv_clm_apply hdd (differentiableAt_const v)]
    simp
  rw [fderiv_inner_apply ℝ hd hp, hpderiv]
  ring

theorem ContDiffAt.laplacian_norm_sq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x =
      2 * ⟪f x, Laplacian.laplacian f x⟫_ℝ +
        2 * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x) := by
  simp only [ContinuousLinearMap.hilbertSchmidtInner, real_inner_self_eq_norm_sq]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdd := ((hf.norm_sq ℝ).fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have he (v : E) :
      fderiv ℝ (fderiv ℝ (fun y => ‖f y‖ ^ 2)) x v v =
        fderiv ℝ (fun q => fderiv ℝ (fun y => ‖f y‖ ^ 2) q v) x v := by
    rw [fderiv_clm_apply hdd (differentiableAt_const v)]
    simp
  simp only [he, second_partial_norm_sq hf, real_inner_self_eq_norm_sq,
    Finset.sum_add_distrib, ← Finset.mul_sum, inner_sum]
  ring

theorem InnerProductSpace.laplacian_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) :
    Laplacian.laplacian (fun y : E => ‖y‖ ^ 2) x = 2 * Module.finrank ℝ E := by
  have h := (contDiffAt_id : ContDiffAt ℝ 2 (fun y : E => y) x).laplacian_norm_sq
  have hid : Laplacian.laplacian (id : E → E) x = 0 := by
    have he : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
      ext z v
      simp
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply,
      he, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, Finset.sum_const_zero]
  simpa [hid, ContinuousLinearMap.hilbertSchmidtInner] using h

private theorem second_partial_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → ℝ} {f : E → F} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => a y • f y) q v) x w =
      a x • fderiv ℝ (fderiv ℝ f) x w v +
        (fderiv ℝ a x w) • (fderiv ℝ f x v) +
        (fderiv ℝ a x v) • (fderiv ℝ f x w) +
        (fderiv ℝ (fderiv ℝ a) x w v) • f x := by
  have had := ha.differentiableAt (by norm_num)
  have hfd := hf.differentiableAt (by norm_num)
  have hadd := (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpa := hadd.clm_apply (differentiableAt_const v)
  have hpf := hfdd.clm_apply (differentiableAt_const v)
  have hnear : (fun q => fderiv ℝ (fun y => a y • f y) q v) =ᶠ[𝓝 x]
      (fun q => a q • fderiv ℝ f q v + (fderiv ℝ a q v) • f q) := by
    filter_upwards [ha.eventually (by norm_num), hf.eventually (by norm_num)] with q haq hfq
    rw [fderiv_fun_smul (haq.differentiableAt (by norm_num))
      (hfq.differentiableAt (by norm_num))]
    simp
  rw [hnear.fderiv_eq]
  erw [fderiv_fun_add (had.smul hpf) (hpa.smul hfd),
    fderiv_fun_smul had hpf, fderiv_fun_smul hpa hfd,
    fderiv_clm_apply hfdd (differentiableAt_const v),
    fderiv_clm_apply hadd (differentiableAt_const v)]
  simp
  abel

private theorem laplacian_fun_smul_sum
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → ℝ} {f : E → F} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian (fun y => a y • f y) x =
      a x • Laplacian.laplacian f x +
        (2 : ℝ) • (∑ i : Fin (Module.finrank ℝ E),
          (fderiv ℝ a x ((stdOrthonormalBasis ℝ E) i)) •
            (fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i))) +
        Laplacian.laplacian a x • f x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdd := ((ha.smul hf).fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have he (v : E) :
      fderiv ℝ (fderiv ℝ (fun y => a y • f y)) x v v =
        fderiv ℝ (fun q => fderiv ℝ (fun y => a y • f y) q v) x v := by
    erw [fderiv_clm_apply hdd (differentiableAt_const v)]
    simp
    rfl
  simp only [he, second_partial_smul ha hf, Finset.sum_add_distrib,
    ← Finset.smul_sum, ← Finset.sum_smul, two_smul]
  abel

theorem ContDiffAt.laplacian_fun_smul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → ℝ} {f : E → F} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian (fun y => a y • f y) x =
      a x • Laplacian.laplacian f x +
        (2 : ℝ) • (fderiv ℝ f x (gradient a x)) +
        Laplacian.laplacian a x • f x := by
  rw [laplacian_fun_smul_sum ha hf]
  have he := congrArg (fderiv ℝ f x) ((stdOrthonormalBasis ℝ E).sum_repr' (gradient a x))
  simp only [map_sum, map_smul, inner_gradient_right, conj_trivial] at he
  rw [he]

theorem ContDiffAt.norm_laplacian_fun_smul_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E → ℝ} {f : E → F} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hf : ContDiffAt ℝ 2 f x) :
    ‖Laplacian.laplacian (fun y => a y • f y) x‖ ≤
      ‖a x‖ * ‖Laplacian.laplacian f x‖ +
        2 * ‖fderiv ℝ a x‖ * ‖fderiv ℝ f x‖ +
        ‖Laplacian.laplacian a x‖ * ‖f x‖ := by
  rw [ha.laplacian_fun_smul hf]
  have hn : ‖fderiv ℝ f x (gradient a x)‖ ≤
      ‖fderiv ℝ a x‖ * ‖fderiv ℝ f x‖ := by
    simpa only [gradient, LinearIsometryEquiv.norm_map, mul_comm] using
      (fderiv ℝ f x).le_opNorm (gradient a x)
  calc
    _ ≤ ‖a x • Laplacian.laplacian f x‖ +
        ‖(2 : ℝ) • fderiv ℝ f x (gradient a x)‖ +
        ‖Laplacian.laplacian a x • f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_smul, Real.norm_ofNat]
      nlinarith only [hn]

theorem LinearIsometryEquiv.laplacian_comp
    {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] G) (f : G → F) (x : E) :
    Laplacian.laplacian (f ∘ e) x = Laplacian.laplacian f (e x) := by
  let b := stdOrthonormalBasis ℝ E
  have he := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
    (s := Set.univ) uniqueDiffOn_univ (x := x) (Set.mem_univ _) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at he
  change iteratedFDeriv ℝ 2 (f ∘ e) x =
    (iteratedFDeriv ℝ 2 f (e x)).compContinuousLinearMap
      (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap) at he
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map e)]
  dsimp only
  rw [he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.map_apply,
    Matrix.vec_single_eq_const, Matrix.vecCons_const]
  rfl

theorem ContDiffAt.continuousAt_laplacian
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (Laplacian.laplacian f) x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact tendsto_finsetSum _ (fun i _ =>
    (hf.continuousAt_iteratedFDeriv (by norm_num : (2 : ℕ∞ω) ≤ 2)).eval_const _)

namespace DifferentialGeometry.Analysis
open Set

theorem tsupport_laplacian_subset
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) :
    tsupport (Laplacian.laplacian f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  contrapose! hz
  have he : iteratedFDeriv ℝ 2 f z = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hz (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2 h))
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, he]

theorem laplacian_comp_const_sub
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a z : E) :
    Laplacian.laplacian (fun w => f (a - w)) z = Laplacian.laplacian f (a - z) := by
  let e := LinearIsometryEquiv.neg ℝ (E := E)
  have he := e.laplacian_comp (fun w => f (a + w)) z
  have hf : (fun w => f (a - w)) = (fun w => f (a + w)) ∘ e := by
    ext w
    simp [e, sub_eq_add_neg]
  rw [hf, he]
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_add_left]
  simp only [e, LinearIsometryEquiv.coe_neg, sub_eq_add_neg]

end DifferentialGeometry.Analysis
