import DifferentialGeometry.Analysis.Parabolic.Euclidean.FourierL2Bridge
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatDuhamelCore
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatHessL2
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatResolvent
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Physical realization of the spacetime heat Hessian

This file identifies the causal second-spatial-derivative heat potential of a
smooth compactly supported source with the spacetime `L²` Fourier multiplier.
-/

noncomputable section

open Complex MeasureTheory Real Set
open scoped ContDiff Convolution FourierTransform LineDeriv RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

private def spaceDir (v : V) : WithLp 2 (ℝ × V) :=
  WithLp.toLp 2 (0, v)

private noncomputable def sourceSch (f : ℝ × V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    SchwartzMap (WithLp 2 (ℝ × V)) ℂ := by
  let g : WithLp 2 (ℝ × V) → ℂ := fun z => (f (WithLp.ofLp z) : ℂ)
  have hg_smooth : ContDiff ℝ ∞ g := by
    exact Complex.ofRealCLM.contDiff.comp
      (hf.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).contDiff)
  have hg_compact : HasCompactSupport g := by
    have hraw : HasCompactSupport (fun z : WithLp 2 (ℝ × V) =>
        f (WithLp.ofLp z)) := by
      simpa only [Function.comp_apply] using
        hfc.comp_homeomorph (WithLp.homeomorphProd 2 ℝ V)
    simpa only [g] using hraw.comp_left (map_zero Complex.ofRealCLM)
  exact hg_compact.toSchwartzMap hg_smooth

private noncomputable def sourceD2Sch (v w : V) (f : ℝ × V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    SchwartzMap (WithLp 2 (ℝ × V)) ℂ :=
  ∂_{spaceDir v} (∂_{spaceDir w} (sourceSch f hf hfc))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
private theorem sourceD2_apply (v w : V) (f : ℝ × V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (s : ℝ) (y : V) :
    sourceD2Sch v w f hf hfc (WithLp.toLp 2 (s, y)) =
      ((fderiv ℝ (fun z : V =>
        fderiv ℝ (fun q : V => f (s, q)) z w) y v : ℝ) : ℂ) := by
  rw [sourceD2Sch, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hinner : (∂_{spaceDir w} (sourceSch f hf hfc) :
      SchwartzMap (WithLp 2 (ℝ × V)) ℂ) = fun x =>
        fderiv ℝ (sourceSch f hf hfc) x (spaceDir w) := by
    funext x
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
  rw [hinner]
  let x : WithLp 2 (ℝ × V) := WithLp.toLp 2 (s, y)
  let mW : Fin 2 → WithLp 2 (ℝ × V) := ![spaceDir v, spaceDir w]
  let slice : V → ℝ := fun q => f (s, q)
  let mV : Fin 2 → V := ![v, w]
  have h12 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have h1inf : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by
    simpa using (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hsrcD : DifferentiableAt ℝ (fderiv ℝ (sourceSch f hf hfc)) x :=
    ((((sourceSch f hf hfc).smooth 2).fderiv_right
      (m := (1 : WithTop ℕ∞)) h12).differentiable (by norm_num)) x
  have hsliceS : ContDiff ℝ ∞ slice := by
    exact hf.comp (contDiff_const.prodMk contDiff_id)
  have hsliceD : DifferentiableAt ℝ (fderiv ℝ slice) y :=
    ((hsliceS.fderiv_right (m := (1 : WithTop ℕ∞)) h1inf).differentiable
      (by norm_num)) y
  have hleft :
      fderiv ℝ (fun z => fderiv ℝ (sourceSch f hf hfc) z (spaceDir w)) x
          (spaceDir v) =
        iteratedFDeriv ℝ 2 (sourceSch f hf hfc) x mW := by
    rw [fderiv_clm_apply hsrcD (differentiableAt_const (spaceDir w))]
    simp [ContinuousLinearMap.flip_apply, iteratedFDeriv_two_apply, mW]
  have hright :
      fderiv ℝ (fun z => fderiv ℝ slice z w) y v =
        iteratedFDeriv ℝ 2 slice y mV := by
    rw [fderiv_clm_apply hsliceD (differentiableAt_const w)]
    simp [ContinuousLinearMap.flip_apply, iteratedFDeriv_two_apply, mV]
  change fderiv ℝ (fun z => fderiv ℝ (sourceSch f hf hfc) z (spaceDir w)) x
      (spaceDir v) = (fderiv ℝ (fun z => fderiv ℝ slice z w) y v : ℂ)
  rw [hleft, hright]
  let P : WithLp 2 (ℝ × V) ≃L[ℝ] ℝ × V :=
    WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V
  have hsrcfun : (sourceSch f hf hfc : WithLp 2 (ℝ × V) → ℂ) =
      Complex.ofRealCLM ∘ (f ∘ P.toContinuousLinearMap) := by
    rfl
  have hfp : ContDiff ℝ ∞ (f ∘ P.toContinuousLinearMap) :=
    hf.comp P.toContinuousLinearMap.contDiff
  have hout := Complex.ofRealCLM.iteratedFDeriv_comp_left
    (x := x) hfp.contDiffAt (i := 2)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hin := P.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (i := 2) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  rw [hsrcfun, hout, hin]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  let J : V →L[ℝ] ℝ × V := ContinuousLinearMap.inr ℝ ℝ V
  let shift : ℝ × V → ℝ := fun p => f (p + (s, 0))
  have hshift : ContDiff ℝ ∞ shift := by
    exact hf.comp (by fun_prop)
  have hslicefun : slice = shift ∘ J := by
    funext z
    simp [slice, shift, J]
  have hJ := J.iteratedFDeriv_comp_right hshift y (i := 2)
    (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  rw [hslicefun, hJ]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change ofRealCLM ((iteratedFDeriv ℝ 2 f (P x)) fun i => P (mW i)) =
    ((iteratedFDeriv ℝ 2 (fun p : ℝ × V => f (p + (s, 0))) (J y))
      fun i => J (mV i) : ℂ)
  rw [iteratedFDeriv_comp_add_right]
  simp [x, mW, mV, P, J, spaceDir]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [Nontrivial V] in
private theorem sourceD2_fourier (v w : V) (f : ℝ × V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (q : WithLp 2 (ℝ × V)) :
    𝓕 (sourceD2Sch v w f hf hfc) q =
      -(((4 * π ^ 2 * inner ℝ v q.snd * inner ℝ w q.snd : ℝ) : ℂ)) *
        𝓕 (sourceSch f hf hfc) q := by
  rw [sourceD2Sch, SchwartzMap.fourier_lineDerivOp_eq,
    SchwartzMap.fourier_lineDerivOp_eq]
  have hv : (fun x : WithLp 2 (ℝ × V) =>
      inner ℝ x (spaceDir v)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (spaceDir v)).hasTemperateGrowth
  have hw : (fun x : WithLp 2 (ℝ × V) =>
      inner ℝ x (spaceDir w)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (spaceDir w)).hasTemperateGrowth
  rw [← SchwartzMap.smulLeftCLM_ofReal ℂ hv,
    ← SchwartzMap.smulLeftCLM_ofReal ℂ hw]
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [smul_eq_mul]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [spaceDir, WithLp.ofLp_toLp, inner_zero_right, zero_add,
    real_inner_comm, WithLp.ofLp_snd]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  rw [neg_inj]
  simp [mul_assoc, mul_left_comm, mul_comm]

omit [Nontrivial V] in
private theorem fourier_conv_l1
    {g h : WithLp 2 (ℝ × V) → ℂ}
    (hg : Integrable g) (hh : Integrable h)
    (q : WithLp 2 (ℝ × V)) :
    𝓕 (g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) q =
      𝓕 g q * 𝓕 h q := by
  let tg : WithLp 2 (ℝ × V) → ℂ := fun x =>
    𝐞 (-inner ℝ x q) • g x
  let th : WithLp 2 (ℝ × V) → ℂ := fun x =>
    𝐞 (-inner ℝ x q) • h x
  have htg : Integrable tg := by
    simpa only [tg] using
      (Real.fourierIntegral_convergent_iff (f := g) q).2 hg
  have hth : Integrable th := by
    simpa only [th] using
      (Real.fourierIntegral_convergent_iff (f := h) q).2 hh
  have hpoint (x : WithLp 2 (ℝ × V)) :
      (tg ⋆[ContinuousLinearMap.mul ℂ ℂ] th) x =
        𝐞 (-inner ℝ x q) •
          (g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) x := by
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def,
      Circle.smul_def, ← MeasureTheory.integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [tg, th, ContinuousLinearMap.mul_apply']
    rw [smul_mul_smul, ← AddChar.map_add_eq_mul, Circle.smul_def]
    congr 1
    rw [inner_sub_left]
    ring_nf
  calc
    𝓕 (g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) q =
        ∫ x, 𝐞 (-inner ℝ x q) •
          (g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) x :=
      Real.fourier_eq _ _
    _ = ∫ x, (tg ⋆[ContinuousLinearMap.mul ℂ ℂ] th) x := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => (hpoint x).symm)
    _ = ContinuousLinearMap.mul ℂ ℂ (∫ x, tg x) (∫ x, th x) :=
      MeasureTheory.integral_convolution
        (L := ContinuousLinearMap.mul ℂ ℂ)
        (μ := volume) (ν := volume) htg hth
    _ = 𝓕 g q * 𝓕 h q := by
      simp only [ContinuousLinearMap.mul_apply', tg, th, Real.fourier_eq]

private def dampD2Past (δ : ℝ) (v w : V) (f : ℝ × V → ℝ)
    (z : WithLp 2 (ℝ × V)) : ℂ :=
  ∫ s : ℝ, if s < z.fst then
    Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
      ∫ y : V,
        ((heatD2 (z.fst - s) v w (z.snd - y) * f (s, y) : ℝ) : ℂ)
  else 0

private theorem dampPast_eq_conv {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    dampD2Past δ v w f =ᵐ[volume]
      sourceD2Sch v w f hf hfc ⋆[ContinuousLinearMap.mul ℂ ℂ]
        dampHeat (V := V) δ := by
  have hsrc : Integrable (sourceD2Sch v w f hf hfc)
      (volume : Measure (WithLp 2 (ℝ × V))) :=
    (sourceD2Sch v w f hf hfc).integrable
  have hker : Integrable (dampHeat (V := V) δ)
      (volume : Measure (WithLp 2 (ℝ × V))) :=
    dampHeat_int (V := V) hδ
  have hprod : Integrable (fun p :
      WithLp 2 (ℝ × V) × WithLp 2 (ℝ × V) =>
        ContinuousLinearMap.mul ℂ ℂ (sourceD2Sch v w f hf hfc p.2)
          (dampHeat (V := V) δ (p.1 - p.2)))
      ((volume : Measure (WithLp 2 (ℝ × V))).prod volume) :=
    hsrc.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hker
  have hslices : ∀ᵐ z : WithLp 2 (ℝ × V) ∂volume,
      Integrable (fun u => ContinuousLinearMap.mul ℂ ℂ
        (sourceD2Sch v w f hf hfc u) (dampHeat (V := V) δ (z - u))) :=
    ((integrable_prod_iff hprod.aestronglyMeasurable).mp hprod).1
  filter_upwards [hslices] with z hz
  have hraw := hz
  rw [← (WithLp.volume_preserving_toLp (U := ℝ) (V := V)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ℝ × V)).measurableEmbedding,
    Measure.volume_eq_prod] at hraw
  change dampD2Past δ v w f z =
    ∫ u : WithLp 2 (ℝ × V), ContinuousLinearMap.mul ℂ ℂ
      (sourceD2Sch v w f hf hfc u) (dampHeat (V := V) δ (z - u))
  rw [← (WithLp.volume_preserving_toLp (U := ℝ) (V := V)).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × V)).measurableEmbedding,
    Measure.volume_eq_prod]
  change dampD2Past δ v w f z =
    ∫ p : ℝ × V, ((fun u : WithLp 2 (ℝ × V) =>
      ContinuousLinearMap.mul ℂ ℂ (sourceD2Sch v w f hf hfc u)
        (dampHeat (V := V) δ (z - u))) ∘ WithLp.toLp 2) p
      ∂((volume : Measure ℝ).prod (volume : Measure V))
  rw [integral_prod _ hraw]
  unfold dampD2Past
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s < z.fst
  · have ht : 0 < z.fst - s := sub_pos.mpr hs
    simp only [hs, ↓reduceIte, Function.comp_apply,
      ContinuousLinearMap.mul_apply', sourceD2_apply, dampHeat,
      WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      ht]
    calc
      Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
          ∫ y : V, ((heatD2 (z.fst - s) v w (z.snd - y) * f (s, y) : ℝ) : ℂ) =
        Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
          ((∫ y : V, heatD2 (z.fst - s) v w (z.snd - y) * f (s, y) : ℝ) : ℂ) := by
            congr 1
            exact integral_complex_ofReal
      _ = Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
          ((∫ y : V, heatKernel (z.fst - s) (z.snd - y) *
            fderiv ℝ (fun q : V =>
              fderiv ℝ (fun r : V => f (s, r)) q w) y v : ℝ) : ℂ) := by
            rw [heatD2_slice2 ht v w z.snd s f (hf := hf) (hfc := hfc)]
      _ = Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
          ∫ y : V, ((heatKernel (z.fst - s) (z.snd - y) *
            fderiv ℝ (fun q : V =>
              fderiv ℝ (fun r : V => f (s, r)) q w) y v : ℝ) : ℂ) := by
            congr 1
            exact integral_complex_ofReal.symm
      _ = ∫ y : V, Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
          ((heatKernel (z.fst - s) (z.snd - y) *
            fderiv ℝ (fun q : V =>
              fderiv ℝ (fun r : V => f (s, r)) q w) y v : ℝ) : ℂ) := by
            exact (integral_const_mul _ _).symm
      _ = ∫ y : V,
          ((fderiv ℝ (fun q : V =>
            fderiv ℝ (fun r : V => f (s, r)) q w) y v : ℝ) : ℂ) *
            (Complex.exp (((-δ * (z.fst - s) : ℝ) : ℂ)) *
              (heatKernel (z.fst - s) (z.snd - y) : ℂ)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            push_cast
            ring
  · have ht : ¬0 < z.fst - s := by linarith
    simp only [hs, ↓reduceIte, Function.comp_apply,
      ContinuousLinearMap.mul_apply', sourceD2_apply, dampHeat,
      WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst,
      ht, mul_zero, integral_zero]

omit [Nontrivial V] in
private theorem translate_src_ae
    (src : SchwartzMap (WithLp 2 (ℝ × V)) ℂ) (y : WithLp 2 (ℝ × V)) :
    lpTranslate y (src.toLp 2) =ᵐ[volume] fun x => src (x - y) := by
  unfold lpTranslate
  unfold SchwartzMap.toLp
  rw [DomAddAct.mk_vadd_toLp]
  refine (MemLp.coeFn_toLp _).trans ?_
  filter_upwards with x
  simp [sub_eq_add_neg, add_comm]

private noncomputable def dampConvOut (δ : ℝ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
  lpOpKernel
    (fun y => ContinuousLinearMap.mul ℝ ℂ (dampHeat (V := V) δ y))
    ((sourceD2Sch v w f hf hfc).toLp 2)

private theorem dampConv_rep {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (sourceD2Sch v w f hf hfc ⋆[ContinuousLinearMap.mul ℂ ℂ]
      dampHeat (V := V) δ) =ᵐ[volume]
        (dampConvOut δ v w f hf hfc : WithLp 2 (ℝ × V) → ℂ) := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    ContinuousLinearMap.mul ℝ ℂ
  let src : WithLp 2 (ℝ × V) → ℂ := sourceD2Sch v w f hf hfc
  let k : WithLp 2 (ℝ × V) → ℂ := dampHeat (V := V) δ
  let out : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
    dampConvOut δ v w f hf hfc
  change (src ⋆[ContinuousLinearMap.mul ℂ ℂ] k) =ᵐ[volume]
    (out : WithLp 2 (ℝ × V) → ℂ)
  have hflip :
      (k ⋆[ContinuousLinearMap.mul ℂ ℂ] src) =
        src ⋆[ContinuousLinearMap.mul ℂ ℂ] k := by
    simpa only [ContinuousLinearMap.flip_mul] using
      (MeasureTheory.convolution_flip
        (L := ContinuousLinearMap.mul ℂ ℂ) (f := src) (g := k))
  rw [← hflip]
  have hsrc : Integrable src := (sourceD2Sch v w f hf hfc).integrable
  have hk : Integrable k := dampHeat_int (V := V) hδ
  have hK : Integrable (fun y => B (k y)) := B.integrable_comp hk
  have hconv : Integrable (k ⋆[ContinuousLinearMap.mul ℂ ℂ] src) :=
    hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hsrc
  have hout : MemLp (out : WithLp 2 (ℝ × V) → ℂ) 2 volume := Lp.memLp out
  apply ae_eq_of_integral_contDiff_smul_eq hconv.locallyIntegrable
    (hout.locallyIntegrable (by norm_num))
  intro φ hφ hφc
  simp only [convolution_def]
  let srcLp : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
    (sourceD2Sch v w f hf hfc).toLp 2
  let φC : WithLp 2 (ℝ × V) → ℂ := fun x => (φ x : ℂ)
  have hφC_cont : Continuous φC :=
    Complex.ofRealCLM.continuous.comp hφ.continuous
  have hφC_supp : HasCompactSupport φC := by
    simpa only [φC] using hφc.comp_left (map_zero Complex.ofRealCLM)
  have hφC_mem : MemLp φC 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
    hφC_cont.memLp_of_hasCompactSupport hφC_supp
  let φLp : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
    hφC_mem.toLp φC
  have hφLp_ae : (φLp : WithLp 2 (ℝ × V) → ℂ) =ᵐ[volume] φC := by
    simpa only [φLp] using hφC_mem.coeFn_toLp
  have hjoint0 : Integrable (fun p :
      WithLp 2 (ℝ × V) × WithLp 2 (ℝ × V) =>
        B (k p.2) (src (p.1 - p.2))) :=
    hk.convolution_integrand B hsrc
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hjoint : Integrable (fun p :
      WithLp 2 (ℝ × V) × WithLp 2 (ℝ × V) =>
        φ p.1 • B (k p.2) (src (p.1 - p.2))) :=
    hjoint0.bdd_smul C hφ.continuous.aestronglyMeasurable.comp_fst
      (Filter.Eventually.of_forall fun p => hC p.1)
  have hinner (y : WithLp 2 (ℝ × V)) :
      (∫ x, φ x • B (k y) (src (x - y))) =
        inner ℂ φLp (lpOpIntegrand (fun q => B (k q)) srcLp y) := by
    rw [L2.inner_def]
    have htr : lpTranslate y srcLp =ᵐ[volume] fun x => src (x - y) := by
      simpa only [srcLp, src] using translate_src_ae (sourceD2Sch v w f hf hfc) y
    have hop :
        (lpOpIntegrand (fun q => B (k q)) srcLp y :
          WithLp 2 (ℝ × V) → ℂ) =ᵐ[volume]
            fun x => B (k y) ((lpTranslate y srcLp) x) := by
      simpa only [lpOpIntegrand, liftLp_apply] using
        (B (k y)).coeFn_compLpL (lpTranslate y srcLp)
    refine integral_congr_ae ?_
    filter_upwards [hφLp_ae, htr, hop] with x hφx htrx hopx
    rw [hφx, hopx, htrx]
    simp only [φC, B, ContinuousLinearMap.mul_apply', RCLike.inner_apply,
      conj_ofReal, real_smul]
    ring
  change (∫ x, φ x • ∫ y, B (k y) (src (x - y))) =
    ∫ x, φ x • out x
  calc
    (∫ x, φ x • ∫ y, B (k y) (src (x - y))) =
        ∫ x, ∫ y, φ x • B (k y) (src (x - y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact (integral_smul (φ x) (fun y => B (k y) (src (x - y)))).symm
    _ = ∫ y, ∫ x, φ x • B (k y) (src (x - y)) :=
      integral_integral_swap hjoint
    _ = ∫ y, inner ℂ φLp
        (lpOpIntegrand (fun q => B (k q)) srcLp y) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = inner ℂ φLp
        (lpOpKernel (fun q => B (k q)) srcLp) := by
          letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
          unfold lpOpKernel
          exact integral_inner (lpOpKernel_int hK srcLp) φLp
    _ = inner ℂ φLp out := by rfl
    _ = ∫ x, φ x • out x := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hφLp_ae] with x hφx
      rw [hφx]
      simp only [φC, RCLike.inner_apply, conj_ofReal, real_smul]
      ring

private theorem dampConv_memLp {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    MemLp (sourceD2Sch v w f hf hfc ⋆[ContinuousLinearMap.mul ℂ ℂ]
      dampHeat (V := V) δ) 2 volume := by
  exact MemLp.ae_eq (dampConv_rep hδ v w f hf hfc).symm
    (Lp.memLp (dampConvOut δ v w f hf hfc))

private def dampHessSym (δ : ℝ) (v w : V)
    (q : WithLp 2 (ℝ × V)) : ℂ :=
  -(((4 * π ^ 2 * inner ℝ v q.snd * inner ℝ w q.snd : ℝ) : ℂ)) /
    (((δ + 4 * π ^ 2 * ‖q.snd‖ ^ 2 : ℝ) : ℂ) +
      (((2 * π * q.fst : ℝ) : ℂ) * I))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V] in
private theorem dampSym_norm {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (q : WithLp 2 (ℝ × V)) :
    ‖dampHessSym δ v w q‖ ≤ ‖v‖ * ‖w‖ := by
  let k : ℝ := 4 * π ^ 2
  let d : ℂ := ((δ + k * ‖q.snd‖ ^ 2 : ℝ) : ℂ) +
    (((2 * π * q.fst : ℝ) : ℂ) * I)
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hd_re : d.re = δ + k * ‖q.snd‖ ^ 2 := by
    change (↑(δ + k * ‖q.snd‖ ^ 2) + ↑(2 * π * q.fst) * I : ℂ).re = _
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      I_re, mul_zero, Complex.ofReal_im, I_im, zero_mul, sub_zero, add_zero]
  have hd_base : k * ‖q.snd‖ ^ 2 ≤ d.re := by
    rw [hd_re]
    exact le_add_of_nonneg_left hδ.le
  have hd_lower : k * ‖q.snd‖ ^ 2 ≤ ‖d‖ :=
    hd_base.trans (re_le_norm d)
  have hd_re_pos : 0 < d.re := by
    rw [hd_re]
    positivity
  have hd_pos : 0 < ‖d‖ := hd_re_pos.trans_le (re_le_norm d)
  have hv := norm_inner_le_norm (𝕜 := ℝ) v q.snd
  have hw := norm_inner_le_norm (𝕜 := ℝ) w q.snd
  have hv' : |inner ℝ v q.snd| ≤ ‖v‖ * ‖q.snd‖ := by
    simpa only [Real.norm_eq_abs] using hv
  have hw' : |inner ℝ w q.snd| ≤ ‖w‖ * ‖q.snd‖ := by
    simpa only [Real.norm_eq_abs] using hw
  change ‖-((k * inner ℝ v q.snd * inner ℝ w q.snd : ℝ) : ℂ) / d‖ ≤
    ‖v‖ * ‖w‖
  rw [norm_div]
  apply (div_le_iff₀ hd_pos).2
  calc
    ‖-((k * inner ℝ v q.snd * inner ℝ w q.snd : ℝ) : ℂ)‖ =
        k * |inner ℝ v q.snd| * |inner ℝ w q.snd| := by
          simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_of_pos hk]
    _ ≤ k * (‖v‖ * ‖q.snd‖) * (‖w‖ * ‖q.snd‖) := by
      gcongr
    _ = (‖v‖ * ‖w‖) * (k * ‖q.snd‖ ^ 2) := by ring
    _ ≤ (‖v‖ * ‖w‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_left hd_lower
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

omit [Nontrivial V] in
private theorem dampSym_meas (δ : ℝ) (v w : V) :
    Measurable (dampHessSym δ v w) := by
  unfold dampHessSym
  measurability

omit [Nontrivial V] in
private theorem dampSym_memLp {δ : ℝ} (hδ : 0 < δ) (v w : V) :
    MemLp (dampHessSym δ v w) ⊤
      (volume : Measure (WithLp 2 (ℝ × V))) :=
  memLp_top_of_bound (dampSym_meas δ v w).aestronglyMeasurable
    (‖v‖ * ‖w‖) (Filter.Eventually.of_forall (dampSym_norm hδ v w))

private theorem dampConv_fourier {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (q : WithLp 2 (ℝ × V)) :
    𝓕 (sourceD2Sch v w f hf hfc ⋆[ContinuousLinearMap.mul ℂ ℂ]
      dampHeat (V := V) δ) q =
      dampHessSym δ v w q * 𝓕 (sourceSch f hf hfc) q := by
  rw [fourier_conv_l1 (sourceD2Sch v w f hf hfc).integrable
    (dampHeat_int (V := V) hδ) q]
  rw [← SchwartzMap.fourier_coe (sourceD2Sch v w f hf hfc)]
  rw [sourceD2_fourier, dampHeat_fourier hδ]
  simp only [dampHessSym, div_eq_mul_inv]
  ring

omit [Nontrivial V] in
private theorem dampProd_memLp {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    MemLp (fun q : WithLp 2 (ℝ × V) =>
      dampHessSym δ v w q * 𝓕 (sourceSch f hf hfc) q) 2 volume := by
  have hFsrc : MemLp (fun q : WithLp 2 (ℝ × V) =>
      𝓕 (sourceSch f hf hfc) q) 2 volume :=
    (𝓕 (sourceSch f hf hfc)).memLp 2
  simpa only [smul_eq_mul] using
    hFsrc.smul (dampSym_memLp hδ v w)

private theorem dampConv_fourierLp {δ : ℝ} (hδ : 0 < δ) (v w : V)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ
        ((dampConv_memLp hδ v w f hf hfc).toLp
          (sourceD2Sch v w f hf hfc ⋆[ContinuousLinearMap.mul ℂ ℂ]
            dampHeat (V := V) δ)) =
      (dampProd_memLp hδ v w f hf hfc).toLp
        (fun q : WithLp 2 (ℝ × V) =>
          dampHessSym δ v w q * 𝓕 (sourceSch f hf hfc) q) := by
  let conv : WithLp 2 (ℝ × V) → ℂ :=
    sourceD2Sch v w f hf hfc ⋆[ContinuousLinearMap.mul ℂ ℂ]
      dampHeat (V := V) δ
  let prod : WithLp 2 (ℝ × V) → ℂ := fun q =>
    dampHessSym δ v w q * 𝓕 (sourceSch f hf hfc) q
  have hconv_int : Integrable conv :=
    (sourceD2Sch v w f hf hfc).integrable.integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) (dampHeat_int (V := V) hδ)
  have hEq : 𝓕 conv =ᵐ[volume] prod := by
    exact Filter.Eventually.of_forall fun q => by
      simpa only [conv, prod] using dampConv_fourier hδ v w f hf hfc q
  have hprod : MemLp prod 2 volume := by
    simpa only [prod] using dampProd_memLp hδ v w f hf hfc
  have hFconv : MemLp (𝓕 conv) 2 volume :=
    MemLp.ae_eq hEq.symm hprod
  change Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ
      ((dampConv_memLp hδ v w f hf hfc).toLp conv) =
    hprod.toLp prod
  calc
    Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ
        ((dampConv_memLp hδ v w f hf hfc).toLp conv) =
        hFconv.toLp (𝓕 conv) :=
      fourier_toLp_two conv hconv_int
        (dampConv_memLp hδ v w f hf hfc) hFconv
    _ = hprod.toLp prod := MemLp.toLp_congr hFconv hprod hEq

/-- The physical causal heat potential with two spatial derivatives. -/
def heatD2Past (v w : V) (f : ℝ × V → ℝ)
    (z : WithLp 2 (ℝ × V)) : ℂ :=
  ∫ s : ℝ, if s < z.fst then
    ∫ y : V, ((heatD2 (z.fst - s) v w (z.snd - y) * f (s, y) : ℝ) : ℂ)
  else 0

end DifferentialGeometry.Analysis.Parabolic.Euclidean
