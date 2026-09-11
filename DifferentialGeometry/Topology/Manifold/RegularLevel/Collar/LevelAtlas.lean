import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates

set_option autoImplicit false
open Set Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Topology.Morse
noncomputable section
namespace DifferentialGeometry.Manifold.RegularLevel

private def insertZero (m : ℕ) (z : MorseModel m) : MorseModel (m + 1) :=
  levelSetSplit m (z, 0)

private theorem contDiff_insertZero (m : ℕ) : ContDiff ℝ ∞ (insertZero m) :=
  (levelSetSplit m).toContinuousLinearEquiv.contDiff.comp (contDiff_id.prodMk contDiff_const)

private theorem insertZero_fst {m : ℕ} {z : MorseModel (m + 1)}
    (hz : z (Fin.last m) = 0) : insertZero m (levelSetSplitFst m z) = z := by
  have h := (levelSetSplit m).apply_symm_apply z
  change levelSetSplit m (levelSetSplitFst m z, z (Fin.last m)) = z at h
  rwa [hz] at h

private theorem fst_insertZero {m : ℕ} (z : MorseModel m) :
    levelSetSplitFst m (insertZero m z) = z := levelSetSplitFst_split m z 0

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

private def levelCoordinates {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y = a}) :=
  (exists_coordinates_of_contMDiffOn I isOpen_univ hf.contMDiffOn
    (mem_univ (x : M)) (hr x x.2) a).choose

private theorem levelCoordinates_spec {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y = a}) :
    (x : M) ∈ (levelCoordinates I hf hr x).source ∧
      ∀ y ∈ (levelCoordinates I hf hr x).source,
        levelCoordinates I hf hr x y (Fin.last m) = a - f y := by
  have h := (exists_coordinates_of_contMDiffOn I isOpen_univ hf.contMDiffOn
    (mem_univ (x : M)) (hr x x.2) a).choose_spec
  exact ⟨h.1, h.2.2⟩

private theorem levelCoordinates_insert {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x y : {y : M // f y = a}) (hy : (y : M) ∈ (levelCoordinates I hf hr x).source) :
    insertZero m (levelSetSplitFst m (levelCoordinates I hf hr x y)) =
      levelCoordinates I hf hr x y := by
  apply insertZero_fst
  rw [(levelCoordinates_spec I hf hr x).2 y hy, y.2, sub_self]

private theorem levelCoordinates_inverse_mem {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y = a}) {z : MorseModel m}
    (hz : insertZero m z ∈ (levelCoordinates I hf hr x).target) :
    f ((levelCoordinates I hf hr x).symm (insertZero m z)) = a := by
  let Φ := levelCoordinates I hf hr x
  have h := (levelCoordinates_spec I hf hr x).2
    (Φ.symm (insertZero m z)) (Φ.map_target hz)
  erw [Φ.right_inv hz] at h
  have hzero : insertZero m z (Fin.last m) = 0 := by simp [insertZero, levelSetSplit]
  rw [hzero] at h
  linarith

private def levelChart {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y = a}) : OpenPartialHomeomorph ({y : M // f y = a}) (MorseModel m) := by
  classical
  let Φ := levelCoordinates I hf hr x
  have hmap (y : {y : M // f y = a}) (hy : (y : M) ∈ Φ.source) :
      insertZero m (levelSetSplitFst m (Φ y)) ∈ Φ.target := by
    rw [levelCoordinates_insert I hf hr x y hy]
    exact Φ.map_source hy
  exact {
    toFun := fun y => levelSetSplitFst m (Φ y)
    invFun := fun z => if hz : insertZero m z ∈ Φ.target then
      ⟨Φ.symm (insertZero m z), levelCoordinates_inverse_mem I hf hr x hz⟩ else x
    source := Subtype.val ⁻¹' Φ.source
    target := insertZero m ⁻¹' Φ.target
    map_source' := fun y hy => hmap y hy
    map_target' := by
      intro z hz
      change insertZero m z ∈ Φ.target at hz
      simp only [mem_preimage, dif_pos hz]
      exact Φ.map_target hz
    left_inv' := by
      intro y hy
      change (y : M) ∈ Φ.source at hy
      rw [dif_pos (hmap y hy)]
      apply Subtype.ext
      change Φ.symm (insertZero m (levelSetSplitFst m (Φ y))) = y
      rw [levelCoordinates_insert I hf hr x y hy]
      exact Φ.left_inv hy
    right_inv' := by
      intro z hz
      change insertZero m z ∈ Φ.target at hz
      rw [dif_pos hz]
      change levelSetSplitFst m (Φ (Φ.symm (insertZero m z))) = z
      erw [Φ.right_inv hz]
      exact fst_insertZero z
    open_source := Φ.open_source.preimage continuous_subtype_val
    open_target := Φ.open_target.preimage (contDiff_insertZero m).continuous
    continuousOn_toFun := (levelSetSplitFst m).continuous.comp_continuousOn
      (Φ.toOpenPartialHomeomorph.continuousOn.comp continuous_subtype_val.continuousOn
        (fun _ hx => hx))
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (Φ.symm.toOpenPartialHomeomorph.continuousOn.comp
        (contDiff_insertZero m).continuous.continuousOn (fun _ hz => hz)).congr
      intro z hz
      change insertZero m z ∈ Φ.target at hz
      simp only [Function.comp_apply, dif_pos hz]
      rfl }

private theorem levelChart_inverse {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y = a}) {z : MorseModel m}
    (hz : z ∈ (levelChart I hf hr x).target) :
    (((levelChart I hf hr x).symm z : {y : M // f y = a}) : M) =
      (levelCoordinates I hf hr x).symm (insertZero m z) := by
  change insertZero m z ∈ (levelCoordinates I hf hr x).target at hz
  simp [levelChart, hz]

@[reducible]
def levelChartedSpace {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ChartedSpace (MorseModel m) ({y : M // f y = a}) where
  atlas := range (levelChart I hf hr)
  chartAt := levelChart I hf hr
  mem_chart_source x := (levelCoordinates_spec I hf hr x).1
  chart_mem_atlas x := ⟨x, rfl⟩


theorem levelIsManifold {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := levelChartedSpace I hf hr
    IsManifold 𝓘(ℝ, MorseModel m) ∞ {y : M // f y = a} := by
  let _ := levelChartedSpace I hf hr
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ]
  let Φ := levelCoordinates I hf hr x
  let Ψ := levelCoordinates I hf hr y
  let e := levelChart I hf hr x
  let e' := levelChart I hf hr y
  have hraw : ContDiffOn ℝ ∞ (Ψ ∘ Φ.symm) (Φ.target ∩ Φ.symm ⁻¹' Ψ.source) :=
    (Φ.symm.trans Ψ).contMDiffOn.contDiffOn
  have hmaps : MapsTo (insertZero m) (e.symm.trans e').source
      (Φ.target ∩ Φ.symm ⁻¹' Ψ.source) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hsecond := hz.2
    change ((e.symm z : {y : M // f y = a}) : M) ∈ Ψ.source at hsecond
    rwa [levelChart_inverse I hf hr x hz.1] at hsecond
  have hsm := (levelSetSplitFst m).contDiff.comp_contDiffOn
    (hraw.comp (contDiff_insertZero m).contDiffOn hmaps)
  apply hsm.congr
  intro z hz
  change levelSetSplitFst m (Ψ ((e.symm z : {y : M // f y = a}) : M)) =
    levelSetSplitFst m (Ψ (Φ.symm (insertZero m z)))
  rw [levelChart_inverse I hf hr x hz.1]

theorem contMDiff_level_inclusion {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := levelChartedSpace I hf hr
    ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (Subtype.val : {y : M // f y = a} → M) := by
  let _ := levelChartedSpace I hf hr
  change ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (Subtype.val : {y : M // f y = a} → M)
  intro x
  let J := 𝓘(ℝ, MorseModel m)
  let Φ := levelCoordinates I hf hr x
  have hx : (x : M) ∈ Φ.source := (levelCoordinates_spec I hf hr x).1
  have hchart (y : {y : M // f y = a}) : extChartAt J x y = levelSetSplitFst m (Φ y) := rfl
  have htarget : insertZero m (extChartAt J x x) ∈ Φ.target := by
    rw [hchart, levelCoordinates_insert I hf hr x x hx]
    exact Φ.map_source hx
  have hinv := Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds htarget)
  have hsm := hinv.comp x
    ((contDiff_insertZero m).contMDiff.contMDiffAt.comp x
      (contMDiffAt_extChartAt (I := J) (n := ∞) (x := x)))
  apply hsm.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds (MorseModel m) x] with y hy
  change (y : M) = Φ.symm (insertZero m (extChartAt J x y))
  have hyΦ : (y : M) ∈ Φ.source := hy
  rw [hchart, levelCoordinates_insert I hf hr x y hyΦ]
  exact (Φ.left_inv hyΦ).symm

theorem contMDiff_level_factor {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] {X : Type*} [TopologicalSpace X]
    [ChartedSpace G X] {IX : ModelWithCorners ℝ E G}
    {F : X → M} (hF : ContMDiff IX I ∞ F) (hFa : ∀ x, f (F x) = a) :
    let _ := levelChartedSpace I hf hr
    ContMDiff IX 𝓘(ℝ, MorseModel m) ∞ (fun x => (⟨F x, hFa x⟩ : {y : M // f y = a})) := by
  let _ := levelChartedSpace I hf hr
  change ContMDiff IX 𝓘(ℝ, MorseModel m) ∞ (fun x => (⟨F x, hFa x⟩ : {y : M // f y = a}))
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(hF.continuous.subtype_mk hFa).continuousAt, ?_⟩
  let p : {y : M // f y = a} := ⟨F x, hFa x⟩
  let Φ := levelCoordinates I hf hr p
  have hx : F x ∈ Φ.source := (levelCoordinates_spec I hf hr p).1
  have hΦ := Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)
  exact (levelSetSplitFst m).contMDiff.contMDiffAt.comp x (hΦ.comp x (hF x))

end DifferentialGeometry.Manifold.RegularLevel
