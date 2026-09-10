import DifferentialGeometry.Topology.Morse.RegularLevel.NoCriticalValues
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse

namespace Poincare.Topology.Ehresmann

variable {m : ℕ}
variable {H : Type} [TopologicalSpace H]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}

noncomputable def levelSetDiffeomorphOfAmbient
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (hmap : ∀ x, f x = a → f (Φ x) = b)
    (hmap_symm : ∀ x, f x = b → f (Φ.symm x) = a) :
    @Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _
      (modelWithCornersSelf ℝ (MorseModel m))
      (modelWithCornersSelf ℝ (MorseModel m))
      (@LevelSetSpace M f a) _
      (show ChartedSpace (MorseModel m) (@LevelSetSpace M f a) from
        manifoldLevelSetChartedSpace (m := m) I f a hf hregA)
      (@LevelSetSpace M f b) _
      (show ChartedSpace (MorseModel m) (@LevelSetSpace M f b) from
        manifoldLevelSetChartedSpace (m := m) I f b hf hregB)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  let _ := manifoldLevelSetChartedSpace (m := m) I f a hf hregA
  let _ := manifoldLevelSetIsManifold (m := m) I f a hf hregA
  let _ := manifoldLevelSetChartedSpace (m := m) I f b hf hregB
  let _ := manifoldLevelSetIsManifold (m := m) I f b hf hregB
  let toFun : LevelSetSpace f a → LevelSetSpace f b :=
    fun x ↦ ⟨Φ x.1, hmap x.1 x.2⟩
  let invFun : LevelSetSpace f b → LevelSetSpace f a :=
    fun x ↦ ⟨Φ.symm x.1, hmap_symm x.1 x.2⟩
  let e : LevelSetSpace f a ≃ LevelSetSpace f b :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        apply Subtype.ext
        exact Φ.symm_apply_apply x.1
      right_inv := by
        intro x
        apply Subtype.ext
        exact Φ.apply_symm_apply x.1 }
  refine
    { toEquiv := e
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hinc : ContMDiff (modelWithCornersSelf ℝ (MorseModel m)) I ∞
        (fun x : LevelSetSpace f a ↦ x.1) :=
      contMDiff_levelSetInclusion I f a hf hregA
    have hambient : ContMDiff (modelWithCornersSelf ℝ (MorseModel m)) I ∞
        (fun x : LevelSetSpace f a ↦ Φ x.1) :=
      Φ.contMDiff.comp hinc
    have hfactor := contMDiff_levelSet_factor I f b hf hregB
      (fun x : LevelSetSpace f a ↦ Φ x.1) hambient
      (fun x ↦ hmap x.1 x.2)
    simpa [e, toFun] using hfactor
  · have hinc : ContMDiff (modelWithCornersSelf ℝ (MorseModel m)) I ∞
        (fun x : LevelSetSpace f b ↦ x.1) :=
      contMDiff_levelSetInclusion I f b hf hregB
    have hambient : ContMDiff (modelWithCornersSelf ℝ (MorseModel m)) I ∞
        (fun x : LevelSetSpace f b ↦ Φ.symm x.1) :=
      Φ.symm.contMDiff.comp hinc
    have hfactor := contMDiff_levelSet_factor I f a hf hregA
      (fun x : LevelSetSpace f b ↦ Φ.symm x.1) hambient
      (fun x ↦ hmap_symm x.1 x.2)
    simpa [e, invFun] using hfactor

@[simp]
theorem levelSetDiffeomorphOfAmbient_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (hmap : ∀ x, f x = a → f (Φ x) = b)
    (hmap_symm : ∀ x, f x = b → f (Φ.symm x) = a)
    (x : LevelSetSpace f a) :
    (levelSetDiffeomorphOfAmbient f a b hf hregA hregB Φ hmap hmap_symm x).1 = Φ x.1 :=
  rfl

theorem levelSetDiffeomorphOfAmbient_symm_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (hmap : ∀ x, f x = a → f (Φ x) = b)
    (hmap_symm : ∀ x, f x = b → f (Φ.symm x) = a)
    (x : LevelSetSpace f b) :
    let _ := manifoldLevelSetChartedSpace (m := m) I f a hf hregA
    let _ := manifoldLevelSetChartedSpace (m := m) I f b hf hregB
    ((levelSetDiffeomorphOfAmbient f a b hf hregA hregB Φ hmap hmap_symm).toEquiv.symm x).1 =
      Φ.symm x.1 := by
  rfl

theorem nonempty_levelSetDiffeomorph_of_compact_regular_band
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    Nonempty
      (@Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
        (MorseModel m) _ (MorseModel m) _
        (modelWithCornersSelf ℝ (MorseModel m))
        (modelWithCornersSelf ℝ (MorseModel m))
        (@LevelSetSpace M f a) _
        (show ChartedSpace (MorseModel m) (@LevelSetSpace M f a) from
          manifoldLevelSetChartedSpace (m := m) I f a hf
            (fun x hx ↦ hregular x (by simpa [hx] using hab)))
        (@LevelSetSpace M f b) _
        (show ChartedSpace (MorseModel m) (@LevelSetSpace M f b) from
          manifoldLevelSetChartedSpace (m := m) I f b hf
            (fun x hx ↦ hregular x (by simpa [hx] using hab)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)) := by
  have hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x := by
    intro x hx
    apply hregular x
    simpa [hx] using hab
  have hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x := by
    intro x hx
    apply hregular x
    simpa [hx] using hab
  rcases no_critical_value_transport (I := I) f hf hab hcompact hregular with
    ⟨v, Φ, hv, hsupp, hdfOn, hrate, hflow, hmap, hstrict, hmap_symm, hstrict_symm⟩
  exact ⟨levelSetDiffeomorphOfAmbient f a b hf hregA hregB Φ hmap hmap_symm⟩

noncomputable def regularLevelFlowDiffeomorph
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hab : a ≤ b)
    (hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
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
    @Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _
      (modelWithCornersSelf ℝ (MorseModel m))
      (modelWithCornersSelf ℝ (MorseModel m))
      (@LevelSetSpace M f a) _
      (show ChartedSpace (MorseModel m) (@LevelSetSpace M f a) from
        manifoldLevelSetChartedSpace (m := m) I f a hf hregA)
      (@LevelSetSpace M f b) _
      (show ChartedSpace (MorseModel m) (@LevelSetSpace M f b) from
        manifoldLevelSetChartedSpace (m := m) I f b hf hregB)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  letI instChartA := manifoldLevelSetChartedSpace (m := m) I f a hf hregA
  letI instManifoldA := manifoldLevelSetIsManifold (m := m) I f a hf hregA
  letI instChartB := manifoldLevelSetChartedSpace (m := m) I f b hf hregB
  letI instManifoldB := manifoldLevelSetIsManifold (m := m) I f b hf hregB
  let e := levelSetTransportHomeomorph I f hf hab v hv hsupp hdfOn hrate
  let hcomplete := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hto : ContMDiff (modelWithCornersSelf ℝ (MorseModel m))
      (modelWithCornersSelf ℝ (MorseModel m)) ∞
      (fun x : LevelSetSpace f a ↦
        (⟨curveAt v hcomplete x.1 (a - b), (e x).2⟩ : LevelSetSpace f b)) := by
    have hinc : ContMDiff (modelWithCornersSelf ℝ (MorseModel m)) I ∞
        (fun x : LevelSetSpace f a ↦ x.1) :=
      contMDiff_levelSetInclusion I f a hf hregA
    have hflow : ContMDiff I I ∞
        (fun x : M ↦ curveAt v hcomplete x (a - b)) := by
      intro x
      exact contMDiffAt_globalFlow_of_compactSupport v hv hsupp (a - b) x
    have hambient := hflow.comp hinc
    have hfactor := contMDiff_levelSet_factor I f b hf hregB
      (fun x : LevelSetSpace f a ↦ curveAt v hcomplete x.1 (a - b)) hambient
      (fun x ↦ (e x).2)
    simpa [e, hcomplete, levelSetTransportHomeomorph] using hfactor
  have hinv : ContMDiff (modelWithCornersSelf ℝ (MorseModel m))
      (modelWithCornersSelf ℝ (MorseModel m)) ∞
      (fun x : LevelSetSpace f b ↦
        (⟨curveAt v hcomplete x.1 (b - a), (e.symm x).2⟩ : LevelSetSpace f a)) := by
    have hinc : ContMDiff (modelWithCornersSelf ℝ (MorseModel m)) I ∞
        (fun x : LevelSetSpace f b ↦ x.1) :=
      contMDiff_levelSetInclusion I f b hf hregB
    have hflow : ContMDiff I I ∞
        (fun x : M ↦ curveAt v hcomplete x (b - a)) := by
      intro x
      exact contMDiffAt_globalFlow_of_compactSupport v hv hsupp (b - a) x
    have hambient := hflow.comp hinc
    have hfactor := contMDiff_levelSet_factor I f a hf hregA
      (fun x : LevelSetSpace f b ↦ curveAt v hcomplete x.1 (b - a)) hambient
      (fun x ↦ (e.symm x).2)
    simpa [e, hcomplete, levelSetTransportHomeomorph] using hfactor
  let d : @Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _
      (modelWithCornersSelf ℝ (MorseModel m))
      (modelWithCornersSelf ℝ (MorseModel m))
      (LevelSetSpace f a) _ instChartA (LevelSetSpace f b) _ instChartB
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · apply hto.congr
      intro x
      apply Subtype.ext
      rfl
    · apply hinv.congr
      intro x
      apply Subtype.ext
      rfl
  exact d

theorem regularLevelFlowDiffeomorph_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hab : a ≤ b)
    (hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
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
    (regularLevelFlowDiffeomorph f a b hf hab hregA hregB v hv hsupp hdfOn hrate x).1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (a - b) :=
  rfl

theorem regularLevelFlowDiffeomorph_symm_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hab : a ≤ b)
    (hregA : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (hregB : ∀ x, f x = b → ¬ IsCriticalPointAt I f x)
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
    (x : LevelSetSpace f b) :
    let _ := manifoldLevelSetChartedSpace (m := m) I f a hf hregA
    let _ := manifoldLevelSetChartedSpace (m := m) I f b hf hregB
    ((regularLevelFlowDiffeomorph f a b hf hab hregA hregB v hv hsupp hdfOn hrate).symm x).1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (b - a) := by
  rfl

theorem regularLevelFlowDiffeomorph_self_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x, f x = a → ¬ IsCriticalPointAt I f x)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a a,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (x : LevelSetSpace f a) :
    regularLevelFlowDiffeomorph f a a hf le_rfl hreg hreg v hv hsupp hdfOn hrate x = x := by
  apply Subtype.ext
  rw [regularLevelFlowDiffeomorph_apply]
  simp [curveAt_zero]

theorem regularLevelFlowDiffeomorph_comp_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (s t r : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hst : s ≤ t) (htr : t ≤ r)
    (hregS : ∀ x, f x = s → ¬ IsCriticalPointAt I f x)
    (hregT : ∀ x, f x = t → ¬ IsCriticalPointAt I f x)
    (hregR : ∀ x, f x = r → ¬ IsCriticalPointAt I f x)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc s r,
      (NormedSpace.fromTangentSpace (f x))
        ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) ≤ 0)
    (x : LevelSetSpace f s) :
    let hdfST : ∀ y ∈ f ⁻¹' Set.Icc s t,
        (NormedSpace.fromTangentSpace (f y))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f y) (v y)) = -1 :=
      fun y hy ↦ hdfOn y ⟨hy.1, hy.2.trans htr⟩
    let hdfTR : ∀ y ∈ f ⁻¹' Set.Icc t r,
        (NormedSpace.fromTangentSpace (f y))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f y) (v y)) = -1 :=
      fun y hy ↦ hdfOn y ⟨hst.trans hy.1, hy.2⟩
    regularLevelFlowDiffeomorph f t r hf htr hregT hregR v hv hsupp hdfTR hrate
        (regularLevelFlowDiffeomorph f s t hf hst hregS hregT v hv hsupp hdfST hrate x) =
      regularLevelFlowDiffeomorph f s r hf (hst.trans htr) hregS hregR
        v hv hsupp hdfOn hrate x := by
  dsimp only
  apply Subtype.ext
  rw [regularLevelFlowDiffeomorph_apply, regularLevelFlowDiffeomorph_apply,
    regularLevelFlowDiffeomorph_apply]
  have hv1 : ContMDiff I
      (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) 1
      (fun y : M ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  have hadd := curveAt_add v hv1
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (s - t) (t - r)
  calc
    curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
          x.1 (s - t)) (t - r) =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        x.1 ((s - t) + (t - r)) := hadd.symm
    _ = curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        x.1 (s - r) := by
      congr 1
      ring

noncomputable def regularLevelFlowDiffeomorphOnBand
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
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
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x)
    (s t : ℝ) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    let hregS : ∀ x, f x = s → ¬ IsCriticalPointAt I f x :=
      fun x hx ↦ hregular x (by simpa [hx] using hs)
    let hregT : ∀ x, f x = t → ¬ IsCriticalPointAt I f x :=
      fun x hx ↦ hregular x (by simpa [hx] using ht)
    @Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _
      (modelWithCornersSelf ℝ (MorseModel m))
      (modelWithCornersSelf ℝ (MorseModel m))
      (@LevelSetSpace M f s) _
      (show ChartedSpace (MorseModel m) (@LevelSetSpace M f s) from
        manifoldLevelSetChartedSpace (m := m) I f s hf hregS)
      (@LevelSetSpace M f t) _
      (show ChartedSpace (MorseModel m) (@LevelSetSpace M f t) from
        manifoldLevelSetChartedSpace (m := m) I f t hf hregT)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  dsimp only
  let hregS : ∀ x, f x = s → ¬ IsCriticalPointAt I f x :=
    fun x hx ↦ hregular x (by simpa [hx] using hs)
  let hregT : ∀ x, f x = t → ¬ IsCriticalPointAt I f x :=
    fun x hx ↦ hregular x (by simpa [hx] using ht)
  letI instChartS := manifoldLevelSetChartedSpace (m := m) I f s hf hregS
  letI instManifoldS := manifoldLevelSetIsManifold (m := m) I f s hf hregS
  letI instChartT := manifoldLevelSetChartedSpace (m := m) I f t hf hregT
  letI instManifoldT := manifoldLevelSetIsManifold (m := m) I f t hf hregT
  by_cases hst : s ≤ t
  · let hdfST : ∀ x ∈ f ⁻¹' Set.Icc s t,
        (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1 :=
      fun x hx ↦ hdfOn x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
    exact regularLevelFlowDiffeomorph f s t hf hst hregS hregT
      v hv hsupp hdfST hrate
  · have hts : t ≤ s := le_of_not_ge hst
    let hdfTS : ∀ x ∈ f ⁻¹' Set.Icc t s,
        (NormedSpace.fromTangentSpace (f x))
          ((mfderiv I (modelWithCornersSelf ℝ ℝ) f x) (v x)) = -1 :=
      fun x hx ↦ hdfOn x ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩
    exact (regularLevelFlowDiffeomorph f t s hf hts hregT hregS
      v hv hsupp hdfTS hrate).symm

theorem regularLevelFlowDiffeomorphOnBand_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
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
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x)
    (s t : ℝ) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x : LevelSetSpace f s) :
    ((regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate hregular
      s t hs ht) x).1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (s - t) := by
  by_cases hst : s ≤ t
  · simp only [regularLevelFlowDiffeomorphOnBand, dif_pos hst]
    rfl
  · simp only [regularLevelFlowDiffeomorphOnBand, dif_neg hst]
    rfl

theorem regularLevelFlowDiffeomorphOnBand_symm_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
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
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x)
    (s t : ℝ) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x : LevelSetSpace f t) :
    let hregS : ∀ y, f y = s → ¬ IsCriticalPointAt I f y :=
      fun y hy ↦ hregular y (by simpa [hy] using hs)
    let hregT : ∀ y, f y = t → ¬ IsCriticalPointAt I f y :=
      fun y hy ↦ hregular y (by simpa [hy] using ht)
    let _ := manifoldLevelSetChartedSpace (m := m) I f s hf hregS
    let _ := manifoldLevelSetChartedSpace (m := m) I f t hf hregT
    (((regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate hregular
      s t hs ht).symm) x).1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (t - s) := by
  dsimp only
  by_cases hst : s ≤ t
  · simp only [regularLevelFlowDiffeomorphOnBand, dif_pos hst]
    rfl
  · simp only [regularLevelFlowDiffeomorphOnBand, dif_neg hst]
    rfl

theorem regularLevelFlowDiffeomorphOnBand_self_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
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
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x)
    (s : ℝ) (hs : s ∈ Set.Icc a b) (x : LevelSetSpace f s) :
    regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate hregular
      s s hs hs x = x := by
  apply Subtype.ext
  rw [regularLevelFlowDiffeomorphOnBand_apply]
  simp [curveAt_zero]

theorem regularLevelFlowDiffeomorphOnBand_comp_apply
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a b : ℝ)
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
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x)
    (s t r : ℝ) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hr : r ∈ Set.Icc a b) (x : LevelSetSpace f s) :
    regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate hregular
        t r ht hr
        (regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate hregular
          s t hs ht x) =
      regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate hregular
        s r hs hr x := by
  apply Subtype.ext
  rw [regularLevelFlowDiffeomorphOnBand_apply,
    regularLevelFlowDiffeomorphOnBand_apply,
    regularLevelFlowDiffeomorphOnBand_apply]
  have hv1 : ContMDiff I
      (I.prod (modelWithCornersSelf ℝ (MorseModel (m + 1)))) 1
      (fun y : M ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  have hadd := curveAt_add v hv1
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (s - t) (t - r)
  calc
    curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
          x.1 (s - t)) (t - r) =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        x.1 ((s - t) + (t - r)) := hadd.symm
    _ = curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        x.1 (s - r) := by
      congr 1
      ring

end Poincare.Topology.Ehresmann
