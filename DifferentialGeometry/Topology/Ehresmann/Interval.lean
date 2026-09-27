import DifferentialGeometry.Topology.Ehresmann.RegularFiber

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Ehresmann

variable {m : ℕ}
variable {H : Type} [TopologicalSpace H]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}

def intervalTranslationHomeomorph (a b : ℝ) :
    Set.Icc a b ≃ₜ Set.Icc (0 : ℝ) (b - a) where
  toFun t := ⟨t.1 - a, sub_nonneg.mpr t.2.1, sub_le_sub_right t.2.2 a⟩
  invFun t := ⟨t.1 + a, by constructor <;> linarith [t.2.1, t.2.2]⟩
  left_inv t := by
    apply Subtype.ext
    simp
  right_inv t := by
    apply Subtype.ext
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def regularBandHomeomorph
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ) (_hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0) :
    LevelSetSpace f a × Set.Icc a b ≃ₜ (f ⁻¹' Set.Icc a b) := by
  let hshift : LevelSetSpace f a × Set.Icc a b ≃ₜ
      LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) :=
    Homeomorph.prodCongr (Homeomorph.refl _) (intervalTranslationHomeomorph a b)
  let hcollar := levelSetCollarHomeomorph I f hf v hv hsupp hdfOn hrate
  let htarget : {x : M // x ∈ sublevel f b ∧ a ≤ f x} ≃ₜ
      (f ⁻¹' Set.Icc a b) :=
    Homeomorph.setCongr (by
      ext x
      simp only [sublevel, Set.mem_preimage, Set.mem_Icc]
      exact and_comm)
  exact hshift.trans (hcollar.trans htarget)

theorem regularBandHomeomorph_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (p : LevelSetSpace f a × Set.Icc a b) :
    (regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate p).1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1 (a - p.2.1) := by
  simp only [regularBandHomeomorph, intervalTranslationHomeomorph,
    DifferentialGeometry.Topology.Morse.levelSetCollarHomeomorph]
  change curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1
      (-(p.2.1 - a)) = _
  congr 1
  ring

theorem regularBandHomeomorph_height
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (p : LevelSetSpace f a × Set.Icc a b) :
    f (regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate p).1 = p.2.1 := by
  rw [regularBandHomeomorph_apply]
  have ht : p.2.1 - a ∈ Set.Icc (0 : ℝ) (b - a) := by
    exact ⟨sub_nonneg.mpr p.2.2.1, sub_le_sub_right p.2.2.2 a⟩
  have hvalue := reverseFlow_value_on_levelSet (I := I) (f := f) (hf := hf)
    (v := v) (hv := hv) (hsupp := hsupp) (hdfOn := hdfOn) (hrate := hrate)
    (x := p.1.1) p.1.2 ht
  rw [show a - p.2.1 = -(p.2.1 - a) by ring]
  calc
    f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        p.1.1 (-(p.2.1 - a))) = a + (p.2.1 - a) := hvalue
    _ = p.2.1 := by ring

theorem regularBandHomeomorph_lower_endpoint
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (x : LevelSetSpace f a) :
    (regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate
      (x, ⟨a, le_rfl, hab.le⟩)).1 = x.1 := by
  rw [regularBandHomeomorph_apply]
  simp [curveAt_zero]

theorem regularBandHomeomorph_upper_endpoint
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (x : LevelSetSpace f a) :
    f (regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate
      (x, ⟨b, hab.le, le_rfl⟩)).1 = b := by
  exact regularBandHomeomorph_height f a b hab hf v hv hsupp hdfOn hrate
    (x, ⟨b, hab.le, le_rfl⟩)

theorem regularBandHomeomorph_symm_formula
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (y : f ⁻¹' Set.Icc a b) :
  let q := (regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate).symm y;
    q.1.1 = curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        y.1 (f y.1 - a) ∧ q.2.1 = f y.1 := by
  let Hband := regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate
  let q := Hband.symm y
  have hHq : Hband q = y := Hband.apply_symm_apply y
  have hqheight := regularBandHomeomorph_height f a b hab hf v hv hsupp hdfOn hrate q
  have htime : q.2.1 = f y.1 := by
    rw [hHq] at hqheight
    exact hqheight.symm
  have hforward := regularBandHomeomorph_apply f a b hab hf v hv hsupp hdfOn hrate q
  have hyflow : curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
      q.1.1 (a - q.2.1) = y.1 := by
    rw [← hforward]
    exact congrArg Subtype.val hHq
  have hv1 : ContMDiff I
      (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) 1
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  have hadd := curveAt_add v hv1
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp) q.1.1
    (a - q.2.1) (q.2.1 - a)
  have hreturn : q.1.1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        y.1 (q.2.1 - a) := by
    rw [show (a - q.2.1) + (q.2.1 - a) = 0 by ring,
      curveAt_zero] at hadd
    rw [hyflow] at hadd
    exact hadd
  constructor
  · rw [hreturn, htime]
  · exact htime

theorem nonempty_regularBandHomeomorph
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    Nonempty (LevelSetSpace f a × Set.Icc a b ≃ₜ (f ⁻¹' Set.Icc a b)) := by
  rcases exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular with
    ⟨v, hv, hsupp, hdfOn, hrate⟩
  exact ⟨regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate⟩

def affineIntervalDiffeomorph (a b : ℝ) [h : Fact (a < b)] :
    Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (Set.Icc (0 : ℝ) 1) (Set.Icc a b)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  let e := (iccHomeoI a b h.out).symm
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · rw [contMDiff_iff_comp_subtypeVal_Icc]
    constructor
    · exact e.continuous
    · change ContMDiff (𝓡∂ 1) 𝓘(ℝ) _
        (fun x : Set.Icc (0 : ℝ) 1 ↦ (b - a) * x.1 + a)
      convert
        ((contMDiff_const.mul
          (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))).add contMDiff_const) using 1 <;>
        first | rfl | infer_instance
  · rw [contMDiff_iff_comp_subtypeVal_Icc]
    constructor
    · exact e.symm.continuous
    · change ContMDiff (𝓡∂ 1) 𝓘(ℝ) _
        (fun x : Set.Icc a b ↦ (x.1 - a) / (b - a))
      exact ((contMDiff_subtypeVal_Icc (x := a) (y := b)).sub contMDiff_const).div_const _

@[simp]
theorem affineIntervalDiffeomorph_apply (a b : ℝ) [h : Fact (a < b)]
    (t : Set.Icc (0 : ℝ) 1) :
    ((affineIntervalDiffeomorph a b t : Set.Icc a b) : ℝ) =
      (b - a) * t.1 + a := by
  exact iccHomeoI_symm_apply_coe a b h.out t

@[simp]
theorem affineIntervalDiffeomorph_symm_apply (a b : ℝ) [h : Fact (a < b)]
    (t : Set.Icc a b) :
    (((affineIntervalDiffeomorph a b).symm t : Set.Icc (0 : ℝ) 1) : ℝ) =
      (t.1 - a) / (b - a) := by
  exact iccHomeoI_apply_coe a b h.out t

section ProductReparametrization

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
variable {HS : Type*} [TopologicalSpace HS]
variable {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
variable {IS : ModelWithCorners ℝ ES HS}
variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
variable {HF : Type*} [TopologicalSpace HF]
variable {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
variable {IF : ModelWithCorners ℝ EF HF}
variable {EW : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
variable {HW : Type*} [TopologicalSpace HW]
variable {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]
variable {IW : ModelWithCorners ℝ EW HW}

def unitCylinderDiffeomorphOfProduct
    (a b : ℝ) [Fact (a < b)]
    (sphereToFiber : S ≃ₘ⟮IS, IF⟯ F)
    (productTrivialization :
      Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc a b) W
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)) :
    Diffeomorph (IS.prod (𝓡∂ 1)) IW (S × Set.Icc (0 : ℝ) 1) W
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
  (sphereToFiber.prodCongr (affineIntervalDiffeomorph a b)).trans productTrivialization

@[simp]
theorem unitCylinderDiffeomorphOfProduct_apply
    (a b : ℝ) [Fact (a < b)]
    (sphereToFiber : S ≃ₘ⟮IS, IF⟯ F)
    (productTrivialization :
      Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc a b) W
        (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (p : S × Set.Icc (0 : ℝ) 1) :
    unitCylinderDiffeomorphOfProduct a b sphereToFiber productTrivialization p =
      productTrivialization
        (sphereToFiber p.1, affineIntervalDiffeomorph a b p.2) :=
  rfl

theorem unitCylinderDiffeomorphOfProduct_lower
    (a b : ℝ) [Fact (a < b)]
    (sphereToFiber : S ≃ₘ⟮IS, IF⟯ F)
    (productTrivialization :
      Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc a b) W
        (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (x : S) :
    unitCylinderDiffeomorphOfProduct a b sphereToFiber productTrivialization
        (x, ⟨0, by norm_num⟩) =
      productTrivialization (sphereToFiber x, ⟨a, le_rfl, (Fact.out : a < b).le⟩) := by
  change productTrivialization
      (sphereToFiber x, affineIntervalDiffeomorph a b ⟨0, by norm_num⟩) = _
  congr 2
  apply Subtype.ext
  simp

theorem unitCylinderDiffeomorphOfProduct_upper
    (a b : ℝ) [Fact (a < b)]
    (sphereToFiber : S ≃ₘ⟮IS, IF⟯ F)
    (productTrivialization :
      Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc a b) W
        (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (x : S) :
    unitCylinderDiffeomorphOfProduct a b sphereToFiber productTrivialization
        (x, ⟨1, by norm_num⟩) =
      productTrivialization (sphereToFiber x, ⟨b, (Fact.out : a < b).le, le_rfl⟩) := by
  change productTrivialization
      (sphereToFiber x, affineIntervalDiffeomorph a b ⟨1, by norm_num⟩) = _
  congr 2
  apply Subtype.ext
  simp

end ProductReparametrization

section StandardCylinder

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
variable {HF : Type*} [TopologicalSpace HF]
variable {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
variable (IF : ModelWithCorners ℝ EF HF)

def standardCylinderTrivialization (a b : ℝ) [Fact (a < b)] :
    Diffeomorph (IF.prod (𝓡∂ 1)) (IF.prod (𝓡∂ 1))
      (F × Set.Icc a b) (F × Set.Icc a b)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
  Diffeomorph.refl (IF.prod (𝓡∂ 1)) (F × Set.Icc a b)
    (↑(⊤ : ℕ∞) : WithTop ℕ∞)

@[simp]
theorem standardCylinderTrivialization_apply (a b : ℝ) [Fact (a < b)]
    (p : F × Set.Icc a b) :
    standardCylinderTrivialization IF a b p = p :=
  rfl

theorem standardCylinderTrivialization_height (a b : ℝ) [Fact (a < b)]
    (p : F × Set.Icc a b) :
    (standardCylinderTrivialization IF a b p).2.1 = p.2.1 :=
  rfl

@[simp]
theorem standardCylinderTrivialization_lower_endpoint
    (a b : ℝ) [Fact (a < b)] (x : F) :
    standardCylinderTrivialization IF a b
      (x, ⟨a, le_rfl, (Fact.out : a < b).le⟩) =
        (x, ⟨a, le_rfl, (Fact.out : a < b).le⟩) :=
  rfl

@[simp]
theorem standardCylinderTrivialization_upper_endpoint
    (a b : ℝ) [Fact (a < b)] (x : F) :
    standardCylinderTrivialization IF a b
      (x, ⟨b, (Fact.out : a < b).le, le_rfl⟩) =
        (x, ⟨b, (Fact.out : a < b).le, le_rfl⟩) :=
  rfl

end StandardCylinder

end DifferentialGeometry.Topology.Ehresmann
