import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Abelian

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace Poincare.ChainComplex
variable {C : Type*} [Category* C] [Abelian C]
  {K L M : ChainComplex C ℕ} {A B D : C}
  {ε : K.X 0 ⟶ A} {η : L.X 0 ⟶ B} {θ : M.X 0 ⟶ D}
  (hε : K.d 1 0 ≫ ε = 0) (hη : L.d 1 0 ≫ η = 0)


def augmentMap (f : K ⟶ L) (a : A ⟶ B) (w : f.f 0 ≫ η = ε ≫ a) :
    K.augment ε hε ⟶ L.augment η hη where
  f
    | 0 => a
    | n + 1 => f.f n
  comm' i j _ := by
    rcases i with _ | i
    · cases j <;> simp [ChainComplex.augment]
    rcases j with _ | j
    · cases i
      · exact w
      · simp [ChainComplex.augment]
    simpa only [ChainComplex.augment_d_succ_succ] using! f.comm i j


@[simp]
theorem augmentMap_f_zero (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) : (augmentMap hε hη f a w).f 0 = a := rfl


@[simp]
theorem augmentMap_f_succ (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) (n : ℕ) :
    (augmentMap hε hη f a w).f (n + 1) = f.f n := rfl


@[simp]
theorem augmentMap_id :
    augmentMap hε hε (𝟙 K) (𝟙 A) (by simp) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n <;> rfl


theorem augmentMap_comp (hθ : M.d 1 0 ≫ θ = 0)
    (f : K ⟶ L) (g : L ⟶ M) (a : A ⟶ B) (b : B ⟶ D)
    (w : f.f 0 ≫ η = ε ≫ a) (v : g.f 0 ≫ θ = η ≫ b) :
    augmentMap hε hθ (f ≫ g) (a ≫ b) (by
      change (f.f 0 ≫ g.f 0) ≫ θ = ε ≫ a ≫ b
      rw [Category.assoc, v, ← Category.assoc, w, Category.assoc]) =
      augmentMap hε hη f a w ≫ augmentMap hη hθ g b v := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n <;> rfl

private def augmentToZeroShortComplex :
    (K.augment ε hε).sc' 2 1 0 ⟶ K.sc' 1 0 0 where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 0
  comm₁₂ := by change 𝟙 _ ≫ K.d 1 0 = K.d 1 0 ≫ 𝟙 _; simp
  comm₂₃ := by change 𝟙 _ ≫ K.d 0 0 = ε ≫ 0; simp

private theorem isIso_zero_opcyclesMap (f : K ⟶ L) [QuasiIsoAt f 0] :
    IsIso (ShortComplex.opcyclesMap
      ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f)) := by
  let φ := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f
  have hφ : ShortComplex.QuasiIso φ := (ChainComplex.quasiIsoAt₀_iff f).mp inferInstance
  have := (K.sc' 1 0 0).isIso_homologyι (by change K.d 0 0 = 0; simp)
  have := (L.sc' 1 0 0).isIso_homologyι (by change L.d 0 0 = 0; simp)
  have : IsIso (ShortComplex.homologyMap φ) := hφ.isIso
  have h := ShortComplex.homologyι_naturality φ
  exact IsIso.of_isIso_fac_left h.symm

private theorem isIso_augment_one_opcyclesMap (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) [QuasiIsoAt f 0] :
    IsIso (ShortComplex.opcyclesMap
      ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0).map
        (augmentMap hε hη f a w))) := by
  let φ := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0).map
    (augmentMap hε hη f a w)
  let ψ := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f
  have : IsIso (ShortComplex.opcyclesMap ψ) := isIso_zero_opcyclesMap f
  have : IsIso (ShortComplex.opcyclesMap (augmentToZeroShortComplex hε)) :=
    ShortComplex.isIso_opcyclesMap_of_isIso_of_epi' _ (by change IsIso (𝟙 (K.X 0)); infer_instance)
      (by change Epi (𝟙 (K.X 1)); infer_instance)
  have : IsIso (ShortComplex.opcyclesMap (augmentToZeroShortComplex hη)) :=
    ShortComplex.isIso_opcyclesMap_of_isIso_of_epi' _ (by change IsIso (𝟙 (L.X 0)); infer_instance)
      (by change Epi (𝟙 (L.X 1)); infer_instance)
  have h : φ ≫ augmentToZeroShortComplex hη = augmentToZeroShortComplex hε ≫ ψ := by
    ext
    · change f.f 1 ≫ 𝟙 _ = 𝟙 _ ≫ f.f 1; simp
    · change f.f 0 ≫ 𝟙 _ = 𝟙 _ ≫ f.f 0; simp
    · change a ≫ (0 : B ⟶ L.X 0) = (0 : A ⟶ K.X 0) ≫ f.f 0; simp
  have hh := congrArg ShortComplex.opcyclesMap h
  simp only [ShortComplex.opcyclesMap_comp] at hh
  exact IsIso.of_isIso_fac_right hh

private def augmentZeroQuotient : ShortComplex C :=
  ShortComplex.mk ((K.sc' 1 0 0).descOpcycles ε hε) (0 : A ⟶ A) (by simp)

private def augmentZeroToQuotient :
    (K.augment ε hε).sc' 1 0 0 ⟶ augmentZeroQuotient hε where
  τ₁ := (K.sc' 1 0 0).pOpcycles
  τ₂ := 𝟙 A
  τ₃ := 𝟙 A
  comm₁₂ := by
    change (K.sc' 1 0 0).pOpcycles ≫ (K.sc' 1 0 0).descOpcycles ε hε = ε ≫ 𝟙 A
    exact ((K.sc' 1 0 0).p_descOpcycles ε hε).trans (Category.comp_id ε).symm
  comm₂₃ := by
    change 𝟙 A ≫ (0 : A ⟶ A) = (0 : A ⟶ A) ≫ 𝟙 A
    simp

private theorem isIso_augmentZeroToQuotient_homologyMap :
    IsIso (ShortComplex.homologyMap (augmentZeroToQuotient hε)) := by
  have : Epi (augmentZeroToQuotient hε).τ₁ := by
    change Epi (K.sc' 1 0 0).pOpcycles; infer_instance
  have : IsIso (augmentZeroToQuotient hε).τ₂ := by change IsIso (𝟙 A); infer_instance
  have : Mono (augmentZeroToQuotient hε).τ₃ := by change Mono (𝟙 A); infer_instance
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono _

private def augmentZeroQuotientMap (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) : augmentZeroQuotient hε ⟶ augmentZeroQuotient hη where
  τ₁ := ShortComplex.opcyclesMap
    ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f)
  τ₂ := a
  τ₃ := a
  comm₁₂ := by
    apply (cancel_epi (K.sc' 1 0 0).pOpcycles).mp
    change (K.sc' 1 0 0).pOpcycles ≫
        (ShortComplex.opcyclesMap
          ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f) ≫
            (L.sc' 1 0 0).descOpcycles η hη) =
      (K.sc' 1 0 0).pOpcycles ≫ (K.sc' 1 0 0).descOpcycles ε hε ≫ a
    rw [ShortComplex.p_opcyclesMap_assoc]
    have hL := congrArg (fun z ↦ f.f 0 ≫ z) ((L.sc' 1 0 0).p_descOpcycles η hη)
    have hK := congrArg (fun z ↦ z ≫ a) ((K.sc' 1 0 0).p_descOpcycles ε hε)
    simpa only [Category.assoc] using! hL.trans (w.trans hK.symm)
  comm₂₃ := by change a ≫ (0 : B ⟶ B) = (0 : A ⟶ A) ≫ a; simp

private theorem isIso_augment_zero_homologyMap (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) [QuasiIsoAt f 0] [IsIso a] :
    IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map
        (augmentMap hε hη f a w))) := by
  let φ := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map
    (augmentMap hε hη f a w)
  let ψ := augmentZeroQuotientMap hε hη f a w
  have hi : IsIso ψ.τ₁ := isIso_zero_opcyclesMap f
  have h₂ : IsIso ψ.τ₂ := by change IsIso a; infer_instance
  have h₃ : Mono ψ.τ₃ := by change Mono a; infer_instance
  have hψ : IsIso (ShortComplex.homologyMap ψ) :=
    ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono _
  have hp := isIso_augmentZeroToQuotient_homologyMap hε
  have hq := isIso_augmentZeroToQuotient_homologyMap hη
  have h : φ ≫ augmentZeroToQuotient hη = augmentZeroToQuotient hε ≫ ψ := by
    ext
    · exact (ShortComplex.p_opcyclesMap
        ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f)).symm
    · change a ≫ 𝟙 B = 𝟙 A ≫ a; simp
    · change a ≫ 𝟙 B = 𝟙 A ≫ a; simp
  have hh : ShortComplex.homologyMap φ ≫
        ShortComplex.homologyMap (augmentZeroToQuotient hη) =
      ShortComplex.homologyMap (augmentZeroToQuotient hε) ≫ ShortComplex.homologyMap ψ := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp, h]
  exact IsIso.of_isIso_fac_right hh

theorem quasiIso_augmentMap (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) [QuasiIso f]
    [IsIso a] : QuasiIso (augmentMap hε hη f a w) := by
  rw [quasiIso_iff]
  intro n
  rcases n with _ | _ | n
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff]
    exact isIso_augment_zero_homologyMap hε hη f a w
  · rw [quasiIsoAt_iff' _ 2 1 0 (by simp) (by simp),
      ShortComplex.quasiIso_iff]
    exact ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono
      (isIso_augment_one_opcyclesMap hε hη f a w) (by change Mono a; infer_instance)
  · rw [quasiIsoAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
    have hf := (quasiIsoAt_iff' f (n + 2) (n + 1) n
      (by simp) (by simp)).mp inferInstance
    exact hf

end Poincare.ChainComplex
