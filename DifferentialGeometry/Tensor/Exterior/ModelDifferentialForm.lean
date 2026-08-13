import DifferentialGeometry.Tensor.Exterior.Model

noncomputable section

open ContinuousAlternatingMap Set

namespace DifferentialGeometry

structure ModelDifferentialForm (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  toFun : E → E [⋀^Fin n]→L[ℝ] F
  smooth : ContDiff ℝ ⊤ toFun

notation "Ω^" n "⟮" E ", " F "⟯" => ModelDifferentialForm n E F

namespace ModelDifferentialForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m k l : ℕ}

instance : FunLike (Ω^n⟮E, F⟯) E (E [⋀^Fin n]→L[ℝ] F) where
  coe := ModelDifferentialForm.toFun
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    cases h
    rfl

@[ext]
theorem ext {ω τ : Ω^n⟮E, F⟯} (h : ∀ x, ω x = τ x) : ω = τ :=
  DFunLike.ext _ _ h

instance instZero : Zero (Ω^n⟮E, F⟯) where
  zero := ⟨0, contDiff_const⟩

instance instAdd : Add (Ω^n⟮E, F⟯) where
  add ω τ := ⟨fun x => ω x + τ x, ω.smooth.add τ.smooth⟩

instance instNeg : Neg (Ω^n⟮E, F⟯) where
  neg ω := ⟨fun x => -ω x, ω.smooth.neg⟩

instance instSMulNat : SMul ℕ (Ω^n⟮E, F⟯) where
  smul m ω := ⟨fun x => m • ω x, ω.smooth.const_smul m⟩

instance instSub : Sub (Ω^n⟮E, F⟯) where
  sub ω τ := ⟨fun x => ω x - τ x, ω.smooth.sub τ.smooth⟩

instance instSMulInt : SMul ℤ (Ω^n⟮E, F⟯) where
  smul z ω := ⟨fun x => z • ω x, ω.smooth.const_smul z⟩

instance instSMul : SMul ℝ (Ω^n⟮E, F⟯) where
  smul c ω := ⟨fun x => c • ω x, ω.smooth.const_smul c⟩

@[simp]
theorem coe_zero : ⇑(0 : Ω^n⟮E, F⟯) = (0 : E → E [⋀^Fin n]→L[ℝ] F) := rfl

@[simp]
theorem coe_add (ω τ : Ω^n⟮E, F⟯) : ⇑(ω + τ) = ⇑ω + ⇑τ := rfl

@[simp]
theorem coe_neg (ω : Ω^n⟮E, F⟯) : ⇑(-ω) = -⇑ω := rfl

@[simp]
theorem coe_sub (ω τ : Ω^n⟮E, F⟯) : ⇑(ω - τ) = ⇑ω - ⇑τ := rfl

@[simp]
theorem coe_nsmul (ω : Ω^n⟮E, F⟯) (m : ℕ) : ⇑(m • ω) = m • ⇑ω := rfl

@[simp]
theorem coe_zsmul (ω : Ω^n⟮E, F⟯) (z : ℤ) : ⇑(z • ω) = z • ⇑ω := rfl

@[simp]
theorem coe_smul (c : ℝ) (ω : Ω^n⟮E, F⟯) : ⇑(c • ω) = c • ⇑ω := rfl

instance instAddZeroClass : AddZeroClass (Ω^n⟮E, F⟯) :=
  DFunLike.coe_injective.addZeroClass (M₂ := E → E [⋀^Fin n]→L[ℝ] F) DFunLike.coe
    coe_zero coe_add

noncomputable def coeAddHom : Ω^n⟮E, F⟯ →+ (E → E [⋀^Fin n]→L[ℝ] F) where
  toFun := DFunLike.coe
  map_zero' := coe_zero
  map_add' := coe_add

instance instAddCommGroup : AddCommGroup (Ω^n⟮E, F⟯) :=
  DFunLike.coe_injective.addCommGroup (M₂ := E → E [⋀^Fin n]→L[ℝ] F) DFunLike.coe
    coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instModule : Module ℝ (Ω^n⟮E, F⟯) :=
  { smul := (· • ·)
    smul_zero := by intro c; ext x; simp
    zero_smul := by intro a; ext x; simp
    smul_add := by intro c a b; ext x; simp [smul_add]
    add_smul := by intro c d a; ext x; simp [add_smul]
    mul_smul := by intro c d a; ext x; simp [mul_smul]
    one_smul := by intro a; ext x; simp }

noncomputable def extDeriv (ω : Ω^n⟮E, F⟯) : Ω^(n + 1)⟮E, F⟯ :=
  ⟨fun x => _root_.extDeriv ω x, by
    rw [← contDiffOn_univ]
    exact DifferentialGeometry.DifferentialForm.contDiffOn_extDeriv ω.toFun
      (by simpa [contDiffOn_univ] using ω.smooth) isOpen_univ⟩

@[simp]
theorem extDeriv_apply (ω : Ω^n⟮E, F⟯) (x : E) : (extDeriv ω) x = _root_.extDeriv ω x := rfl

theorem extDeriv_extDeriv (ω : Ω^n⟮E, F⟯) : extDeriv (extDeriv ω) = 0 := by
  apply ModelDifferentialForm.ext
  intro x
  change _root_.extDeriv (_root_.extDeriv ω.toFun) x = 0
  rw [_root_.extDeriv_extDeriv (ω := ω.toFun) (r := ⊤) ω.smooth
    (by simp [minSmoothness_of_isRCLikeNormedField])]
  simp

noncomputable def wedge (ω : Ω^k⟮E, ℝ⟯) (τ : Ω^l⟮E, ℝ⟯) : Ω^(k + l)⟮E, ℝ⟯ :=
  ⟨fun x => ω x ∧[ℝ] τ x, by
    rw [← contDiffOn_univ]
    exact DifferentialGeometry.DifferentialForm.contDiffOn_wedge_product
      (a := ω.toFun) (b := τ.toFun)
      (by simpa [contDiffOn_univ] using ω.smooth)
      (by simpa [contDiffOn_univ] using τ.smooth)⟩

@[simp]
theorem wedge_apply (ω : Ω^k⟮E, ℝ⟯) (τ : Ω^l⟮E, ℝ⟯) (x : E) :
    (wedge ω τ) x = ω x ∧[ℝ] τ x := rfl

noncomputable def domDomCongrL (e : Fin k ≃ Fin l) :
    (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := fun T => ContinuousAlternatingMap.domDomCongr e T
      map_add' := fun T U => ContinuousAlternatingMap.domDomCongr_add e T U
      map_smul' := by
        intro c T
        ext v
        simp }
    1 (fun T => by
      have hnorm : ‖ContinuousAlternatingMap.domDomCongr e T‖ = ‖T‖ := by
        change ‖(ContinuousAlternatingMap.domDomCongr e T).toContinuousMultilinearMap‖ = ‖T‖
        change ‖(T.toContinuousMultilinearMap.domDomCongr e : ContinuousMultilinearMap ℝ
          (fun _ : Fin l => E) F)‖ = ‖T‖
        rw [ContinuousMultilinearMap.norm_domDomCongr]
        rw [ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      simp [hnorm])

noncomputable def reindex (e : Fin k ≃ Fin l) (ω : Ω^k⟮E, F⟯) : Ω^l⟮E, F⟯ :=
  ⟨fun x => ContinuousAlternatingMap.domDomCongr e (ω x), by
    simpa [contDiffOn_univ, domDomCongrL] using
      (contDiff_const (c := domDomCongrL (E := E) (F := F) e)).clm_apply
        (by simpa [contDiffOn_univ] using ω.smooth)⟩

@[simp]
theorem reindex_apply (e : Fin k ≃ Fin l) (ω : Ω^k⟮E, F⟯) (x : E) :
    (reindex e ω) x = ContinuousAlternatingMap.domDomCongr e (ω x) := rfl

noncomputable def pullback {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E → E') (hf : ContDiff ℝ ⊤ f) (ω : Ω^n⟮E', F⟯) :
    Ω^n⟮E, F⟯ :=
  ⟨fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x), by
    rw [← contDiffOn_univ]
    exact DifferentialGeometry.DifferentialForm.contDiffOn_pullback (s := univ)
      (t := univ) f ω.toFun
      (by simpa [contDiffOn_univ] using hf)
      (by simpa [contDiffOn_univ] using ω.smooth)
      (by intro x hx; exact hx) isOpen_univ⟩

@[simp]
theorem pullback_apply {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E → E') (hf : ContDiff ℝ ⊤ f) (ω : Ω^n⟮E', F⟯) (x : E) :
    (pullback f hf ω) x = (ω (f x)).compContinuousLinearMap (fderiv ℝ f x) := rfl

theorem extDeriv_pullback {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E → E') (hf : ContDiff ℝ ⊤ f) (ω : Ω^n⟮E', F⟯) :
    pullback f hf (extDeriv ω) = extDeriv (pullback f hf ω) := by
  apply ModelDifferentialForm.ext
  intro x
  change (extDeriv ω (f x)).compContinuousLinearMap (fderiv ℝ f x) =
    _root_.extDeriv (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) x
  exact (_root_.extDeriv_pullback (𝕜 := ℝ) (E := E) (F := E') (G := F) (n := n)
    (ω := ω.toFun) (f := f) (x := x)
    (hω := (ω.smooth.differentiable (by norm_num)).differentiableAt)
    (hf := hf.contDiffAt)
    (hr := by simp [minSmoothness_of_isRCLikeNormedField])).symm

end ModelDifferentialForm

end DifferentialGeometry

end
