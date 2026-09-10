import DifferentialGeometry.Topology.Ehresmann.Interval
import DifferentialGeometry.Topology.Manifold.RegularSublevel

set_option autoImplicit false
noncomputable section

open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Ehresmann

private def setCongrDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] {s t : Set M}
    [cs : ChartedSpace H s] (h : s = t) :
    let _ : ChartedSpace H t := h ▸ cs
    s ≃ₘ⟮I, I⟯ t := by
  subst t
  exact Diffeomorph.refl I s ∞

private theorem setCongrDiffeomorph_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] {s t : Set M}
    [ChartedSpace H s] (h : s = t) (x : s) :
    (setCongrDiffeomorph I h x).1 = x.1 := by
  subst t
  rfl

private theorem setCongrDiffeomorph_symm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] {s t : Set M}
    [ChartedSpace H s] (h : s = t) (x : t) :
    let _ : ChartedSpace H t := h ▸ ‹ChartedSpace H s›
    ((setCongrDiffeomorph I h).symm x).1 = x.1 := by
  subst t
  rfl

private theorem setCongrIsManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] {s t : Set M}
    [cs : ChartedSpace H s] [IsManifold I ∞ s] (h : s = t) :
    let _ : ChartedSpace H t := h ▸ cs
    IsManifold I ∞ t := by
  subst t
  exact inferInstance

private theorem setCongr_mem_boundary_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] {s t : Set M}
    [cs : ChartedSpace H s] (h : s = t) (x : t) :
    let _ : ChartedSpace H t := h ▸ cs
    x ∈ I.boundary t ↔ (setCongrDiffeomorph I h).symm x ∈ I.boundary s := by
  subst t
  rfl

private theorem band_sublevel_eq {M : Type} (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    sublevel (fun x ↦ (f x - a) * (f x - b)) 0 = f ⁻¹' Set.Icc a b := by
  ext x
  change (f x - a) * (f x - b) ≤ 0 ↔ a ≤ f x ∧ f x ≤ b
  rw [mul_nonpos_iff]
  constructor
  · rintro (h | h) <;> constructor <;> linarith
  · intro h
    exact Or.inl ⟨sub_nonneg.mpr h.1, sub_nonpos.mpr h.2⟩

variable {m : ℕ} {H : Type} [TopologicalSpace H]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] in
private theorem band_definingFunction_regular
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x) :
    ∀ x, (f x - a) * (f x - b) = 0 →
      ¬ IsCriticalPointAt I (fun y ↦ (f y - a) * (f y - b)) x := by
  intro x hx
  have hend : f x = a ∨ f x = b := by
    simpa only [mul_eq_zero, sub_eq_zero] using hx
  have hd : HasDerivAt (fun t : ℝ ↦ (t - a) * (t - b))
      ((f x - b) + (f x - a)) (f x) := by
    convert ((hasDerivAt_id (f x)).sub_const a).mul
      ((hasDerivAt_id (f x)).sub_const b) using 1 <;> first | rfl | simp
  have hcomp := hd.hasFDerivAt.hasMFDerivAt.comp x
    ((hf x).mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hder : mfderiv I 𝓘(ℝ) (fun y ↦ (f y - a) * (f y - b)) x =
      ((f x - b) + (f x - a)) • mfderiv I 𝓘(ℝ) f x := by
    change mfderiv I 𝓘(ℝ) ((fun t : ℝ ↦ (t - a) * (t - b)) ∘ f) x = _
    rw [hcomp.mfderiv]
    ext v
    change (show ℝ from (mfderiv I 𝓘(ℝ) f x) v) * ((f x - b) + (f x - a)) =
      ((f x - b) + (f x - a)) * (show ℝ from (mfderiv I 𝓘(ℝ) f x) v)
    exact mul_comm _ _
  change mfderiv I 𝓘(ℝ) (fun y ↦ (f y - a) * (f y - b)) x ≠ 0
  intro hz
  have he : (((f x - b) + (f x - a)) • mfderiv I 𝓘(ℝ) f x :
      TangentSpace I x →L[ℝ] ℝ) = 0 := hder.symm.trans hz
  rcases smul_eq_zero.mp he with hzero | hzero
  · rcases hend with ha | hb
    · rw [ha] at hzero
      linarith
    · rw [hb] at hzero
      linarith
  · exact hreg x hend hzero

@[instance_reducible] def regularBandChartedSpace
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x) :
    ChartedSpace (MorseHalfSpace m) (f ⁻¹' Set.Icc a b) :=
  band_sublevel_eq f hab.le ▸
    manifoldSublevelChartedSpace I (fun x ↦ (f x - a) * (f x - b)) 0
      ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
      (band_definingFunction_regular f a b hab hf hreg)

theorem regularBandIsManifold
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x) :
    let _ := regularBandChartedSpace f a b hab hf hreg
    IsManifold (morseModelWithCornersHalfSpace m) ∞ (f ⁻¹' Set.Icc a b) := by
  let _ := manifoldSublevelChartedSpace I (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg)
  let _ := manifoldSublevelIsManifold I (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg)
  exact setCongrIsManifold (morseModelWithCornersHalfSpace m) (band_sublevel_eq f hab.le)

theorem mem_boundary_regularBand_iff
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x)
    (x : f ⁻¹' Set.Icc a b) :
    let _ := regularBandChartedSpace f a b hab hf hreg
    x ∈ (morseModelWithCornersHalfSpace m).boundary (f ⁻¹' Set.Icc a b) ↔
      f x.1 = a ∨ f x.1 = b := by
  let _ := manifoldSublevelChartedSpace I (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg)
  let _ := regularBandChartedSpace f a b hab hf hreg
  refine (setCongr_mem_boundary_iff (morseModelWithCornersHalfSpace m)
    (band_sublevel_eq f hab.le) x).trans ?_
  refine (DifferentialGeometry.Topology.Manifold.mem_boundary_manifoldSublevel_iff
    (I := I) (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg) _).trans ?_
  have he := setCongrDiffeomorph_symm_apply (morseModelWithCornersHalfSpace m)
    (band_sublevel_eq f hab.le) x
  rw [he]
  exact (mul_eq_zero.trans (or_congr sub_eq_zero sub_eq_zero))

theorem contMDiff_regularBandInclusion
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x) :
    let _ := regularBandChartedSpace f a b hab hf hreg
    ContMDiff (morseModelWithCornersHalfSpace m) I ∞
      (fun x : f ⁻¹' Set.Icc a b ↦ x.1) := by
  let _ := manifoldSublevelChartedSpace I (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg)
  let _ := regularBandChartedSpace f a b hab hf hreg
  let d := setCongrDiffeomorph (morseModelWithCornersHalfSpace m) (band_sublevel_eq f hab.le)
  have hi := DifferentialGeometry.Topology.Manifold.contMDiff_manifoldSublevelInclusion
    (I := I) (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg)
  exact (hi.comp d.symm.contMDiff).congr
    (fun x ↦ (setCongrDiffeomorph_symm_apply
      (morseModelWithCornersHalfSpace m) (band_sublevel_eq f hab.le) x).symm)

theorem contMDiff_regularBandCorestrict
    {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {X : Type} [TopologicalSpace X] [ChartedSpace H' X]
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x)
    (F : X → M) (hF : ContMDiff I' I ∞ F) (hmem : ∀ x, f (F x) ∈ Set.Icc a b) :
    let _ := regularBandChartedSpace f a b hab hf hreg
    ContMDiff I' (morseModelWithCornersHalfSpace m) ∞
      (fun x ↦ (⟨F x, hmem x⟩ : f ⁻¹' Set.Icc a b)) := by
  let _ := manifoldSublevelChartedSpace I (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg)
  let _ := regularBandChartedSpace f a b hab hf hreg
  let d := setCongrDiffeomorph (morseModelWithCornersHalfSpace m) (band_sublevel_eq f hab.le)
  have hmem' : ∀ x, (f (F x) - a) * (f (F x) - b) ≤ 0 := by
    intro x
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmem x).1)
      (sub_nonpos.mpr (hmem x).2)
  have hfactor := contMDiff_sublevelCorestrict (I := I)
    (fun x ↦ (f x - a) * (f x - b)) 0
    ((hf.sub contMDiff_const).mul (hf.sub contMDiff_const))
    (band_definingFunction_regular f a b hab hf hreg) F hF hmem'
  apply (d.contMDiff.comp hfactor).congr
  intro x
  apply Subtype.ext
  exact (setCongrDiffeomorph_apply (morseModelWithCornersHalfSpace m)
    (band_sublevel_eq f hab.le) ⟨F x, hmem' x⟩).symm

section Flow

variable [T2Space M]
  (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
  (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x)
  (v : (x : M) → TangentSpace I x)
  (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
    (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hsupp : IsCompact (tsupport v))
  (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
    (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ) f x) (v x)) = -1)
  (hrate : ∀ x,
    -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ) f x) (v x)) ∧
    (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ) f x) (v x)) ≤ 0)

def regularBandDiffeomorph :
    let _ : Fact (a < b) := ⟨hab⟩
    let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
    let _ := regularBandChartedSpace f a b hab hf hreg
    Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1))
      (morseModelWithCornersHalfSpace m)
      (LevelSetSpace f a × Set.Icc a b) (f ⁻¹' Set.Icc a b) ∞ := by
  let _ : Fact (a < b) := ⟨hab⟩
  let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
  let _ := manifoldLevelSetIsManifold I f a hf (fun x hx ↦ hreg x (Or.inl hx))
  let _ := regularBandChartedSpace f a b hab hf hreg
  let _ := regularBandIsManifold f a b hab hf hreg
  let e := regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate
  have hflow := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
  have hincA := contMDiff_levelSetInclusion I f a hf (fun x hx ↦ hreg x (Or.inl hx))
  have hincB := contMDiff_regularBandInclusion f a b hab hf hreg
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have ht : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
        (fun p : LevelSetSpace f a × Set.Icc a b ↦ a - p.2.1) :=
      contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
    have hamb := hflow.comp (ht.prodMk (hincA.comp contMDiff_fst))
    have he : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) I ∞
        (fun p ↦ (e p).1) :=
      hamb.congr (regularBandHomeomorph_apply f a b hab hf v hv hsupp hdfOn hrate)
    exact contMDiff_regularBandCorestrict f a b hab hf hreg _ he (fun p ↦ (e p).2)
  · have hheight : ContMDiff (morseModelWithCornersHalfSpace m) 𝓘(ℝ) ∞
        (fun y : f ⁻¹' Set.Icc a b ↦ f y.1) := hf.comp hincB
    have hamb := hflow.comp ((hheight.sub (contMDiff_const (c := a))).prodMk hincB)
    have he : ContMDiff (morseModelWithCornersHalfSpace m) I ∞
        (fun y ↦ (e.symm y).1.1) :=
      hamb.congr (fun y ↦
        (regularBandHomeomorph_symm_formula f a b hab hf v hv hsupp hdfOn hrate y).1)
    have hfirst := contMDiff_levelSet_factor I f a hf (fun x hx ↦ hreg x (Or.inl hx))
      _ he (fun y ↦ (e.symm y).1.2)
    have hsecond : ContMDiff (morseModelWithCornersHalfSpace m) (𝓡∂ 1) ∞
        (fun y ↦ (e.symm y).2) := by
      rw [contMDiff_iff_comp_subtypeVal_Icc]
      exact ⟨continuous_snd.comp e.symm.continuous,
        hheight.congr (fun y ↦
          (regularBandHomeomorph_symm_formula f a b hab hf v hv hsupp hdfOn hrate y).2)⟩
    exact hfirst.prodMk hsecond

theorem regularBandDiffeomorph_toHomeomorph :
    let _ : Fact (a < b) := ⟨hab⟩
    let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
    let _ := regularBandChartedSpace f a b hab hf hreg
    (regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate).toHomeomorph =
      regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate := rfl

theorem regularBandDiffeomorph_apply (p : LevelSetSpace f a × Set.Icc a b) :
    (regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate p).1 =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1 (a - p.2.1) :=
  regularBandHomeomorph_apply f a b hab hf v hv hsupp hdfOn hrate p

theorem regularBandDiffeomorph_height (p : LevelSetSpace f a × Set.Icc a b) :
    f (regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate p).1 = p.2.1 :=
  regularBandHomeomorph_height f a b hab hf v hv hsupp hdfOn hrate p

theorem regularBandDiffeomorph_lower_endpoint (x : LevelSetSpace f a) :
    (regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate
      (x, ⟨a, le_rfl, hab.le⟩)).1 = x.1 :=
  regularBandHomeomorph_lower_endpoint f a b hab hf v hv hsupp hdfOn hrate x

theorem regularBandDiffeomorph_upper_endpoint (x : LevelSetSpace f a) :
    f (regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate
      (x, ⟨b, hab.le, le_rfl⟩)).1 = b :=
  regularBandHomeomorph_upper_endpoint f a b hab hf v hv hsupp hdfOn hrate x

theorem regularBandDiffeomorph_symm_formula (y : f ⁻¹' Set.Icc a b) :
    let _ : Fact (a < b) := ⟨hab⟩
    let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
    let _ := regularBandChartedSpace f a b hab hf hreg
    let q := (regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate).toEquiv.symm y
    q.1.1 = curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
        y.1 (f y.1 - a) ∧ q.2.1 = f y.1 :=
  regularBandHomeomorph_symm_formula f a b hab hf v hv hsupp hdfOn hrate y

end Flow

theorem exists_regularBandDiffeomorph
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    let _ : Fact (a < b) := ⟨hab⟩
    let hreg := fun x (hx : f x = a ∨ f x = b) ↦
      hregular x (show f x ∈ Set.Icc a b from by
        rcases hx with ha | hb
        · simp [ha, hab.le]
        · simp [hb, hab.le])
    let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
    let _ := regularBandChartedSpace f a b hab hf hreg
    ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1))
        (morseModelWithCornersHalfSpace m)
        (LevelSetSpace f a × Set.Icc a b) (f ⁻¹' Set.Icc a b) ∞,
      (∀ p, f (d p).1 = p.2.1) ∧
      (∀ x, (d (x, ⟨a, le_rfl, hab.le⟩)).1 = x.1) := by
  dsimp only
  let _ : Fact (a < b) := ⟨hab⟩
  have hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x := by
    intro x hx
    apply hregular x
    rcases hx with ha | hb
    · simp [ha, hab.le]
    · simp [hb, hab.le]
  rcases exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular with
    ⟨v, hv, hsupp, hdfOn, hrate⟩
  exact ⟨regularBandDiffeomorph f a b hab hf hreg v hv hsupp hdfOn hrate,
    regularBandDiffeomorph_height f a b hab hf hreg v hv hsupp hdfOn hrate,
    regularBandDiffeomorph_lower_endpoint f a b hab hf hreg v hv hsupp hdfOn hrate⟩

end DifferentialGeometry.Topology.Ehresmann
