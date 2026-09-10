import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.RegularLevel

private def restrictSubtypes {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (x₀ : S) (y₀ : T) : OpenPartialHomeomorph S T := by
  classical
  exact {
    toFun := fun x => if hx : (x : X) ∈ e.source then ⟨e x, (h.apply_mem_iff hx).mpr x.property⟩ else y₀
    invFun := fun y => if hy : (y : Y) ∈ e.target then ⟨e.symm y, (h.symm_apply_mem_iff hy).mpr y.property⟩ else x₀
    source := Subtype.val ⁻¹' e.source
    target := Subtype.val ⁻¹' e.target
    map_source' := by
      intro x hx
      change (x : X) ∈ e.source at hx
      simp only [mem_preimage, dif_pos hx]
      exact e.map_source hx
    map_target' := by
      intro y hy
      change (y : Y) ∈ e.target at hy
      simp only [mem_preimage, dif_pos hy]
      exact e.map_target hy
    left_inv' := by
      intro x hx
      change (x : X) ∈ e.source at hx
      simp only [dif_pos hx, dif_pos (e.map_source hx)]
      exact Subtype.ext (e.left_inv hx)
    right_inv' := by
      intro y hy
      change (y : Y) ∈ e.target at hy
      simp only [dif_pos hy, dif_pos (e.map_target hy)]
      exact Subtype.ext (e.right_inv hy)
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage continuous_subtype_val
    continuousOn_toFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr
      intro x hx
      change (x : X) ∈ e.source at hx
      simp only [Function.comp_apply, dif_pos hx]
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (e.symm.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)).congr
      intro y hy
      change (y : Y) ∈ e.target at hy
      simp only [Function.comp_apply, dif_pos hy] }

private theorem restrictSubtypes_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (x₀ : S) (y₀ : T) {x : S} (hx : (x : X) ∈ e.source) :
    ((restrictSubtypes e h x₀ y₀ x : T) : Y) = e x := by
  simp [restrictSubtypes, hx]

private theorem restrictSubtypes_symm_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (x₀ : S) (y₀ : T) {y : T} (hy : (y : Y) ∈ e.target) :
    (((restrictSubtypes e h x₀ y₀).symm y : S) : X) = e.symm y := by
  simp [restrictSubtypes, hy]

private def translation (m : ℕ) (v : MorseModel (m + 1)) :
    MorseModel (m + 1) ≃ₘ[ℝ] MorseModel (m + 1) where
  toEquiv := Equiv.addRight v
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

private theorem exists_sublevel_coordinates {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞,
      (x : M) ∈ Φ.source ∧
      Φ.toOpenPartialHomeomorph.IsImage {y | f y ≤ a} {z | 0 ≤ z (Fin.last m)} ∧
      ∀ y ∈ Φ.source, Φ y (Fin.last m) = 0 ↔ f y = a := by
  classical
  by_cases hxa : f x = a
  · obtain ⟨Φ, hx, _, hcoord, _, _⟩ := exists_level_coordinates I hf hxa (hr x hxa)
    refine ⟨Φ, hx, ?_, ?_⟩
    · intro y hy
      change 0 ≤ Φ y (Fin.last m) ↔ f y ≤ a
      rw [hcoord y hy]
      exact sub_nonneg
    · intro y hy
      rw [hcoord y hy]
      exact sub_eq_zero.trans eq_comm
  · have hlt : f x < a := lt_of_le_of_ne x.property hxa
    let c : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞ := {
      toPartialEquiv := extChartAt I (x : M)
      open_source := isOpen_extChartAt_source (I := I) (x : M)
      open_target := isOpen_extChartAt_target (I := I) (x : M)
      contMDiffOn_toFun := by simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := (x : M)) (n := ∞))
      contMDiffOn_invFun := contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x : M) }
    let v := (1 - c x (Fin.last m)) • (levelSetLastBasis (m := m))
    let d := c.trans (translation m v).toPartialDiffeomorph
    have hxd : (x : M) ∈ d.source := ⟨mem_extChartAt_source (I := I) (x : M), mem_univ _⟩
    have hdx : d x (Fin.last m) = 1 := by
      change (c x + v) (Fin.last m) = 1
      simp [v, levelSetLastBasis]
    have hcont : ContinuousAt (fun y : M => d y (Fin.last m)) x :=
      (continuous_apply (Fin.last m)).continuousAt.comp
        (d.toOpenPartialHomeomorph.continuousAt hxd)
    have hpos : {y : M | 0 < d y (Fin.last m)} ∈ 𝓝 (x : M) :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rw [hdx]; norm_num))
    have hfilt : {y : M | f y < a} ∈ 𝓝 (x : M) :=
      hf.continuous.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hpos hfilt)
    let e := d.toOpenPartialHomeomorph.restrOpen U hU
    let Φ : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞ := {
      toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := d.contMDiffOn.mono inter_subset_left
      contMDiffOn_invFun := d.symm.contMDiffOn.mono inter_subset_left }
    refine ⟨Φ, ⟨hxd, hxU⟩, ?_, ?_⟩
    · intro y hy
      have hh := hUsub hy.2
      change 0 ≤ d y (Fin.last m) ↔ f y ≤ a
      exact iff_of_true hh.1.le hh.2.le
    · intro y hy
      have hh := hUsub hy.2
      change d y (Fin.last m) = 0 ↔ f y = a
      exact iff_of_false (ne_of_gt hh.1) (ne_of_lt hh.2)

private def sublevelCoordinates {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) := (exists_sublevel_coordinates I hf hr x).choose

private theorem sublevelCoordinates_spec {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) :
    (x : M) ∈ (sublevelCoordinates I hf hr x).source ∧
      (sublevelCoordinates I hf hr x).toOpenPartialHomeomorph.IsImage
        {y | f y ≤ a} {z | 0 ≤ z (Fin.last m)} ∧
      ∀ y ∈ (sublevelCoordinates I hf hr x).source,
        sublevelCoordinates I hf hr x y (Fin.last m) = 0 ↔ f y = a :=
  (exists_sublevel_coordinates I hf hr x).choose_spec

private def sublevelChart {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) : OpenPartialHomeomorph {y : M // f y ≤ a} (MorseHalfSpace m) :=
  restrictSubtypes (sublevelCoordinates I hf hr x).toOpenPartialHomeomorph
    (sublevelCoordinates_spec I hf hr x).2.1 x ⟨(0 : MorseModel (m + 1)), by change (0 : ℝ) ≤ 0; exact le_rfl⟩

private theorem sublevelChart_apply {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) {y : {y : M // f y ≤ a}}
    (hy : (y : M) ∈ (sublevelCoordinates I hf hr x).source) :
    ((sublevelChart I hf hr x y : MorseHalfSpace m) : MorseModel (m + 1)) =
      sublevelCoordinates I hf hr x y :=
  restrictSubtypes_apply _ _ _ _ hy

private theorem sublevelChart_symm_apply {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) {z : MorseHalfSpace m}
    (hz : (z : MorseModel (m + 1)) ∈ (sublevelCoordinates I hf hr x).target) :
    (((sublevelChart I hf hr x).symm z : {y : M // f y ≤ a}) : M) =
      (sublevelCoordinates I hf hr x).symm z :=
  restrictSubtypes_symm_apply _ _ _ _ hz

private theorem contDiffOn_sublevelChart_transition {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x y : {z : M // f z ≤ a}) :
    ContDiffOn ℝ ∞
      (morseModelWithCornersHalfSpace m ∘
        (sublevelChart I hf hr x).symm.trans (sublevelChart I hf hr y) ∘
          (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelChart I hf hr x).symm.trans (sublevelChart I hf hr y)).source ∩
          range (morseModelWithCornersHalfSpace m)) := by
  let J := morseModelWithCornersHalfSpace m
  let Φ := sublevelCoordinates I hf hr x
  let Ψ := sublevelCoordinates I hf hr y
  let e := sublevelChart I hf hr x
  let e' := sublevelChart I hf hr y
  let D := J.symm ⁻¹' (e.symm.trans e').source ∩ range J
  have hF : ContDiffOn ℝ ∞ (Ψ ∘ Φ.symm) (Φ.target ∩ Φ.symm ⁻¹' Ψ.source) :=
    contMDiffOn_iff_contDiffOn.mp (Φ.symm.trans Ψ).contMDiffOn
  have hbase {z : MorseModel (m + 1)} (hz : z ∈ D) :
      ((J.symm z : MorseHalfSpace m) : MorseModel (m + 1)) = z := J.right_inv hz.2
  have hfirst {z : MorseModel (m + 1)} (hz : z ∈ D) : z ∈ Φ.target := by
    have hh := hz.1.1
    change ((J.symm z : MorseHalfSpace m) : MorseModel (m + 1)) ∈ Φ.target at hh
    rwa [hbase hz] at hh
  have hinverse {z : MorseModel (m + 1)} (hz : z ∈ D) :
      ((e.symm (J.symm z) : {z : M // f z ≤ a}) : M) = Φ.symm z :=
    (sublevelChart_symm_apply I hf hr x hz.1.1).trans (congrArg Φ.symm (hbase hz))
  have hsecond {z : MorseModel (m + 1)} (hz : z ∈ D) : Φ.symm z ∈ Ψ.source := by
    have hh := hz.1.2
    change ((e.symm (J.symm z) : {z : M // f z ≤ a}) : M) ∈ Ψ.source at hh
    rwa [hinverse hz] at hh
  apply (hF.mono (fun z hz => ⟨hfirst hz, hsecond hz⟩)).congr
  intro z hz
  change ((e' (e.symm (J.symm z)) : MorseHalfSpace m) : MorseModel (m + 1)) = Ψ (Φ.symm z)
  exact (sublevelChart_apply I hf hr y hz.1.2).trans (congrArg Ψ (hinverse hz))

@[reducible]
def sublevelChartedSpace {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ChartedSpace (MorseHalfSpace m) {y : M // f y ≤ a} where
  atlas := Set.range (sublevelChart I hf hr)
  chartAt := sublevelChart I hf hr
  mem_chart_source x := (sublevelCoordinates_spec I hf hr x).1
  chart_mem_atlas x := ⟨x, rfl⟩


theorem sublevelIsManifold {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := sublevelChartedSpace I hf hr
    IsManifold (morseModelWithCornersHalfSpace m) ∞ {y : M // f y ≤ a} := by
  let _ := sublevelChartedSpace I hf hr
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  exact contDiffOn_sublevelChart_transition I hf hr x y

theorem sublevelBoundary_iff {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x : {y : M // f y ≤ a}) :
    let _ := sublevelChartedSpace I hf hr
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ f x = a := by
  let _ := sublevelChartedSpace I hf hr
  change (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ f x = a
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_morseHalfSpace_range]
  change ((sublevelChart I hf hr x x : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m) = 0 ↔ f x = a
  rw [sublevelChart_apply I hf hr x (sublevelCoordinates_spec I hf hr x).1]
  exact (sublevelCoordinates_spec I hf hr x).2.2 x (sublevelCoordinates_spec I hf hr x).1


theorem sublevelBoundary {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := sublevelChartedSpace I hf hr
    (morseModelWithCornersHalfSpace m).boundary {y : M // f y ≤ a} =
      {x : {y : M // f y ≤ a} | f x.val = a} := by
  let _ := sublevelChartedSpace I hf hr
  ext x
  exact sublevelBoundary_iff I hf hr x

theorem contMDiff_sublevel_inclusion {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := sublevelChartedSpace I hf hr
    ContMDiff (morseModelWithCornersHalfSpace m) I ∞
      (Subtype.val : {y : M // f y ≤ a} → M) := by
  let _ := sublevelChartedSpace I hf hr
  change ContMDiff (morseModelWithCornersHalfSpace m) I ∞
    (Subtype.val : {y : M // f y ≤ a} → M)
  intro x
  let J := morseModelWithCornersHalfSpace m
  let Φ := sublevelCoordinates I hf hr x
  have hx : (x : M) ∈ Φ.source := (sublevelCoordinates_spec I hf hr x).1
  have hchart : extChartAt J x x = Φ x := sublevelChart_apply I hf hr x hx
  have hΦ : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ∞ Φ.symm (extChartAt J x x) := by
    rw [hchart]
    exact Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds (Φ.map_source hx))
  have hh := hΦ.comp x (contMDiffAt_extChartAt (I := J) (n := ∞) (x := x))
  apply hh.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds (MorseHalfSpace m) x] with y hy
  change (y : M) = Φ.symm (extChartAt J x y)
  have hyΦ : (y : M) ∈ Φ.source := hy
  have hychart : extChartAt J x y = Φ y := sublevelChart_apply I hf hr x hyΦ
  rw [hychart]
  exact (Φ.left_inv hyΦ).symm

theorem contMDiffWithinAt_sublevel_iff
    {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace X] [ChartedSpace H' X]
    (J : ModelWithCorners ℝ E' H')
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {n : WithTop ℕ∞} (hn : n ≤ ∞)
    {g : X → {y : M // f y ≤ a}} {s : Set X} {x : X} :
    let _ := sublevelChartedSpace I hf hr
    ContMDiffWithinAt J (morseModelWithCornersHalfSpace m) n g s x ↔
      ContMDiffWithinAt J I n (Subtype.val ∘ g) s x := by
  let _ := sublevelChartedSpace I hf hr
  constructor
  · intro hg
    exact ((contMDiff_sublevel_inclusion I hf hr).of_le hn).contMDiffAt.comp_contMDiffWithinAt x hg
  · intro hg
    let Φ := sublevelCoordinates I hf hr (g x)
    have hx : (g x : M) ∈ Φ.source := (sublevelCoordinates_spec I hf hr (g x)).1
    have hΦ : ContMDiffAt I 𝓘(ℝ, MorseModel (m + 1)) n Φ (g x : M) :=
      (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)).of_le hn
    have hh := hΦ.comp_contMDiffWithinAt x hg
    rw [contMDiffWithinAt_iff_target]
    refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hg.continuousWithinAt, ?_⟩
    apply hh.congr_of_eventuallyEq
    · filter_upwards [hg.continuousWithinAt.preimage_mem_nhdsWithin (Φ.open_source.mem_nhds hx)] with y hy
      exact sublevelChart_apply I hf hr (g x) hy
    · exact sublevelChart_apply I hf hr (g x) hx

theorem contMDiffAt_sublevel_iff
    {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace X] [ChartedSpace H' X]
    (J : ModelWithCorners ℝ E' H')
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {n : WithTop ℕ∞} (hn : n ≤ ∞)
    {g : X → {y : M // f y ≤ a}} {x : X} :
    let _ := sublevelChartedSpace I hf hr
    ContMDiffAt J (morseModelWithCornersHalfSpace m) n g x ↔
      ContMDiffAt J I n (Subtype.val ∘ g) x :=
  contMDiffWithinAt_sublevel_iff I J hf hr hn

theorem contMDiff_sublevel_iff
    {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace X] [ChartedSpace H' X]
    (J : ModelWithCorners ℝ E' H')
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {n : WithTop ℕ∞} (hn : n ≤ ∞)
    {g : X → {y : M // f y ≤ a}} :
    let _ := sublevelChartedSpace I hf hr
    ContMDiff J (morseModelWithCornersHalfSpace m) n g ↔
      ContMDiff J I n (Subtype.val ∘ g) := by
  let _ := sublevelChartedSpace I hf hr
  exact forall_congr' (fun _ => contMDiffAt_sublevel_iff I J hf hr hn)

end Poincare.Manifold.RegularLevel
