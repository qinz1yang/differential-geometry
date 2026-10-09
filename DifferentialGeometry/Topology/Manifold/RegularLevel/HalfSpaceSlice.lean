import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Half-space slice charts

Let `M` be a manifold modelled on `I` (possibly with boundary or corners) and `P : M → Prop`.
Suppose every point of `P` lies in the source of a smooth partial diffeomorphism
`Φ : M → ℍ^{d+1} × F` together with a height `c ≥ 0` such that on the source of `Φ`,
`P = {Φ.2 = 0, c ≤ (Φ.1)₀}`. Then `{x // P x}` is a smooth manifold with boundary modelled on
`𝓡∂ (d + 1)`; its chart at `x` is `y ↦ (Φ y).1 - c e₀`. The inclusion is smooth with injective
differential (bijective in codimension zero), maps into `{x // P x}` are smooth iff their
compositions with the inclusion are, and the boundary is read off from `(Φ x).1₀ = c`.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

section ModelSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H]

/-- A `C^n` self-map of a model space is `C^n` in the vector-space sense on `range I`. -/
theorem contDiffOn_of_contMDiffOn_modelSpace (I : ModelWithCorners 𝕜 E H) {n : WithTop ℕ∞}
    {g : H → H} {s : Set H} (hg : ContMDiffOn I I n g s) :
    ContDiffOn 𝕜 n (I ∘ g ∘ I.symm) (I.symm ⁻¹' s ∩ range I) := by
  intro z hz
  have h := ((contMDiffWithinAt_iff).mp (hg (I.symm z) hz.1)).2
  have hz' : I (I.symm z) = z := I.right_inv hz.2
  rw [extChartAt_self_apply, hz'] at h
  exact h

end ModelSpace

section Shift

variable (d : ℕ)

theorem slice_coord_add (v : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ) :
    (v + c • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))) 0 = v 0 + c := by
  simp

theorem slice_coord_sub (v : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ) :
    (v - c • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))) 0 = v 0 - c := by
  simp

/-- Translation of the half-space by `c e₀`. -/
def sliceShift (c : ℝ) (w : EuclideanHalfSpace (d + 1)) : EuclideanHalfSpace (d + 1) :=
  (𝓡∂ (d + 1)).symm (w.1 + c • EuclideanSpace.single 0 1)

/-- Translation of the half-space by `-c e₀` (meaningful on `{c ≤ w₀}`). -/
def sliceUnshift (c : ℝ) (w : EuclideanHalfSpace (d + 1)) : EuclideanHalfSpace (d + 1) :=
  (𝓡∂ (d + 1)).symm (w.1 - c • EuclideanSpace.single 0 1)

variable {d}

theorem sliceShift_val {c : ℝ} (hc : 0 ≤ c) (w : EuclideanHalfSpace (d + 1)) :
    (sliceShift d c w).1 = w.1 + c • EuclideanSpace.single 0 1 := by
  have h : 0 ≤ (w.1 + c • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))) 0 := by
    rw [slice_coord_add]
    linarith [w.2]
  rw [sliceShift, modelWithCornersEuclideanHalfSpace_symm_apply_of_le h]

theorem sliceShift_coord {c : ℝ} (hc : 0 ≤ c) (w : EuclideanHalfSpace (d + 1)) :
    (sliceShift d c w).1 0 = w.1 0 + c := by
  rw [sliceShift_val hc, slice_coord_add]

theorem sliceUnshift_val {c : ℝ} {w : EuclideanHalfSpace (d + 1)} (hw : c ≤ w.1 0) :
    (sliceUnshift d c w).1 = w.1 - c • EuclideanSpace.single 0 1 := by
  have h : 0 ≤ (w.1 - c • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))) 0 := by
    rw [slice_coord_sub]
    linarith
  rw [sliceUnshift, modelWithCornersEuclideanHalfSpace_symm_apply_of_le h]

theorem sliceShift_unshift {c : ℝ} (hc : 0 ≤ c) {w : EuclideanHalfSpace (d + 1)}
    (hw : c ≤ w.1 0) : sliceShift d c (sliceUnshift d c w) = w :=
  Subtype.ext (by rw [sliceShift_val hc, sliceUnshift_val hw, sub_add_cancel])

theorem sliceUnshift_shift {c : ℝ} (hc : 0 ≤ c) (w : EuclideanHalfSpace (d + 1)) :
    sliceUnshift d c (sliceShift d c w) = w := by
  have h : c ≤ (sliceShift d c w).1 0 := by
    rw [sliceShift_coord hc]
    linarith [w.2]
  exact Subtype.ext (by rw [sliceUnshift_val h, sliceShift_val hc, add_sub_cancel_right])

theorem contMDiff_sliceShift {c : ℝ} (hc : 0 ≤ c) :
    ContMDiff (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞ (sliceShift d c) := by
  have h : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun w : EuclideanHalfSpace (d + 1) => w.1 + c • EuclideanSpace.single 0 1) :=
    ((contDiff_id.add contDiff_const).contMDiff).comp ((𝓡∂ (d + 1)).contMDiff)
  refine ((𝓡∂ (d + 1)).contMDiffOn_symm).comp_contMDiff h (fun w => ?_)
  rw [range_modelWithCornersEuclideanHalfSpace]
  change 0 ≤ (w.1 + c • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))) 0
  rw [slice_coord_add]
  linarith [w.2]

theorem contMDiffOn_sliceUnshift (c : ℝ) :
    ContMDiffOn (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞ (sliceUnshift d c) {w | c ≤ w.1 0} := by
  have h : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun w : EuclideanHalfSpace (d + 1) => w.1 - c • EuclideanSpace.single 0 1) :=
    ((contDiff_id.sub contDiff_const).contMDiff).comp ((𝓡∂ (d + 1)).contMDiff)
  refine ((𝓡∂ (d + 1)).contMDiffOn_symm).comp h.contMDiffOn (fun w hw => ?_)
  rw [range_modelWithCornersEuclideanHalfSpace]
  change 0 ≤ (w.1 - c • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))) 0
  rw [slice_coord_sub]
  change c ≤ w.1 0 at hw
  linarith

theorem continuous_sliceUnshift (c : ℝ) : Continuous (sliceUnshift d c) :=
  (𝓡∂ (d + 1)).continuous_symm.comp (continuous_subtype_val.sub continuous_const)

end Shift

section Kernel

variable {d : ℕ} {E' H' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Inverse of a slice chart (total function, `x₀` off the target). -/
def sliceChartInv (P : M → Prop)
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    (c : ℝ) (x₀ : {x // P x}) (w : EuclideanHalfSpace (d + 1)) : {x // P x} := by
  classical
  exact if h : P (Φ.symm (sliceShift d c w, 0)) then ⟨Φ.symm (sliceShift d c w, 0), h⟩ else x₀

theorem sliceChartInv_val (P : M → Prop)
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) {w : EuclideanHalfSpace (d + 1)}
    (hw : (sliceShift d c w, (0 : F)) ∈ Φ.target) :
    (sliceChartInv P Φ c x₀ w).1 = Φ.symm (sliceShift d c w, 0) := by
  have hP : P (Φ.symm (sliceShift d c w, 0)) := by
    refine (hΦ _ (Φ.map_target hw)).mpr ⟨?_, ?_⟩
    · rw [Φ.right_inv hw]
    · rw [Φ.right_inv hw]
      change c ≤ (sliceShift d c w).1 0
      rw [sliceShift_coord hc]
      linarith [w.2]
  unfold sliceChartInv
  rw [dite_eq_left hP]

/-- The chart of `{x // P x}` attached to a slice chart `Φ` with height `c`. -/
def sliceChart (P : M → Prop)
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) : OpenPartialHomeomorph {x // P x} (EuclideanHalfSpace (d + 1)) where
  toFun y := sliceUnshift d c (Φ y.1).1
  invFun := sliceChartInv P Φ c x₀
  source := Subtype.val ⁻¹' Φ.source
  target := (fun w => (sliceShift d c w, (0 : F))) ⁻¹' Φ.target
  map_source' := by
    intro y hy
    have hP := (hΦ y.1 hy).mp y.2
    change (sliceShift d c (sliceUnshift d c (Φ y.1).1), (0 : F)) ∈ Φ.target
    rw [sliceShift_unshift hc hP.2]
    have he : ((Φ y.1).1, (0 : F)) = Φ y.1 := Prod.ext rfl hP.1.symm
    rw [he]
    exact Φ.map_source hy
  map_target' := by
    intro w hw
    change (sliceChartInv P Φ c x₀ w).1 ∈ Φ.source
    rw [sliceChartInv_val P Φ hc hΦ x₀ hw]
    exact Φ.map_target hw
  left_inv' := by
    intro y hy
    have hP := (hΦ y.1 hy).mp y.2
    have he : (sliceShift d c (sliceUnshift d c (Φ y.1).1), (0 : F)) = Φ y.1 := by
      rw [sliceShift_unshift hc hP.2]
      exact Prod.ext rfl hP.1.symm
    have hw : (sliceShift d c (sliceUnshift d c (Φ y.1).1), (0 : F)) ∈ Φ.target := by
      rw [he]
      exact Φ.map_source hy
    apply Subtype.ext
    rw [sliceChartInv_val P Φ hc hΦ x₀ hw, he]
    exact Φ.left_inv hy
  right_inv' := by
    intro w hw
    have hw' : (sliceShift d c w, (0 : F)) ∈ Φ.target := hw
    change sliceUnshift d c (Φ (sliceChartInv P Φ c x₀ w).1).1 = w
    have hr : Φ (Φ.symm (sliceShift d c w, (0 : F))) = (sliceShift d c w, 0) := Φ.right_inv hw'
    rw [sliceChartInv_val P Φ hc hΦ x₀ hw', hr]
    exact sliceUnshift_shift hc w
  open_source := Φ.open_source.preimage continuous_subtype_val
  open_target := Φ.open_target.preimage
    ((contMDiff_sliceShift hc).continuous.prodMk continuous_const)
  continuousOn_toFun := by
    refine ((continuous_sliceUnshift c).comp continuous_fst).comp_continuousOn ?_
    exact Φ.contMDiffOn.continuousOn.comp continuous_subtype_val.continuousOn (fun y hy => hy)
  continuousOn_invFun := by
    have hind : Topology.IsInducing (Subtype.val : {x // P x} → M) := ⟨rfl⟩
    rw [hind.continuousOn_iff]
    refine ContinuousOn.congr (f := fun w => Φ.symm (sliceShift d c w, (0 : F))) ?_ ?_
    · exact Φ.symm.contMDiffOn.continuousOn.comp
        ((contMDiff_sliceShift hc).continuous.prodMk continuous_const).continuousOn
        (fun w hw => hw)
    · intro w hw
      exact sliceChartInv_val P Φ hc hΦ x₀ hw

theorem sliceChart_apply_val (P : M → Prop)
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) {y : {x // P x}} (hy : y.1 ∈ Φ.source) :
    (sliceChart P Φ hc hΦ x₀ y).1 = (Φ y.1).1.1 - c • EuclideanSpace.single 0 1 :=
  sliceUnshift_val ((hΦ y.1 hy).mp y.2).2

theorem sliceChart_shift_eq (P : M → Prop)
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) {y : {x // P x}} (hy : y.1 ∈ Φ.source) :
    (sliceShift d c (sliceChart P Φ hc hΦ x₀ y), (0 : F)) = Φ y.1 := by
  have hP := (hΦ y.1 hy).mp y.2
  change (sliceShift d c (sliceUnshift d c (Φ y.1).1), (0 : F)) = Φ y.1
  rw [sliceShift_unshift hc hP.2]
  exact Prod.ext rfl hP.1.symm

theorem contMDiffAt_slice_coord
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    (c : ℝ) {x : M} (hx : x ∈ Φ.source) :
    ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun u => (Φ u).1.1 - c • EuclideanSpace.single 0 1) x := by
  have h1 : ContMDiffAt I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞ Φ x :=
    Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)
  have h2 : ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun q : EuclideanHalfSpace (d + 1) × F => q.1.1 - c • EuclideanSpace.single 0 1) :=
    ((contDiff_id.sub contDiff_const).contMDiff).comp (((𝓡∂ (d + 1)).contMDiff).comp contMDiff_fst)
  exact h2.contMDiffAt.comp x h1

theorem sliceChart_trans_contMDiffOn (P : M → Prop)
    (Φ₁ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hΦ₁ : ∀ y ∈ Φ₁.source, P y ↔ ((Φ₁ y).2 = 0 ∧ c₁ ≤ (Φ₁ y).1.1 0))
    (x₁ : {x // P x})
    (Φ₂ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c₂ : ℝ} (hc₂ : 0 ≤ c₂) (hΦ₂ : ∀ y ∈ Φ₂.source, P y ↔ ((Φ₂ y).2 = 0 ∧ c₂ ≤ (Φ₂ y).1.1 0))
    (x₂ : {x // P x}) :
    ContMDiffOn (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞
      ((sliceChart P Φ₁ hc₁ hΦ₁ x₁).symm ≫ₕ sliceChart P Φ₂ hc₂ hΦ₂ x₂)
      ((sliceChart P Φ₁ hc₁ hΦ₁ x₁).symm ≫ₕ sliceChart P Φ₂ hc₂ hΦ₂ x₂).source := by
  set e₁ := sliceChart P Φ₁ hc₁ hΦ₁ x₁ with he₁
  set e₂ := sliceChart P Φ₂ hc₂ hΦ₂ x₂ with he₂
  have hk : ContMDiff (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
      (fun w => (sliceShift d c₁ w, (0 : F))) :=
    (contMDiff_sliceShift hc₁).prodMk contMDiff_const
  have hinv : ∀ w ∈ (e₁.symm ≫ₕ e₂).source,
      (e₁.symm w).1 = Φ₁.symm (sliceShift d c₁ w, 0) :=
    fun w hw => sliceChartInv_val P Φ₁ hc₁ hΦ₁ x₁ hw.1
  have h1 : ContMDiffOn (𝓡∂ (d + 1)) I ∞ (fun w => Φ₁.symm (sliceShift d c₁ w, (0 : F)))
      (e₁.symm ≫ₕ e₂).source :=
    Φ₁.symm.contMDiffOn.comp hk.contMDiffOn (fun w hw => hw.1)
  have h2 : ContMDiffOn (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
      (fun w => Φ₂ (Φ₁.symm (sliceShift d c₁ w, (0 : F)))) (e₁.symm ≫ₕ e₂).source := by
    refine Φ₂.contMDiffOn.comp h1 (fun w hw => ?_)
    have h := hw.2
    change (e₁.symm w).1 ∈ Φ₂.source at h
    rw [hinv w hw] at h
    exact h
  have h3 : ContMDiffOn (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞
      (fun w => sliceUnshift d c₂ (Φ₂ (Φ₁.symm (sliceShift d c₁ w, (0 : F)))).1)
      (e₁.symm ≫ₕ e₂).source := by
    refine (contMDiffOn_sliceUnshift c₂).comp (contMDiff_fst.comp_contMDiffOn h2) (fun w hw => ?_)
    have h := hw.2
    change (e₁.symm w).1 ∈ Φ₂.source at h
    have hq := ((hΦ₂ _ h).mp (e₁.symm w).2).2
    rw [hinv w hw] at hq
    exact hq
  refine h3.congr (fun w hw => ?_)
  change sliceUnshift d c₂ (Φ₂ (e₁.symm w).1).1 = _
  rw [hinv w hw]

end Kernel

section Atlas

variable {d : ℕ} {E' H' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P Bd : M → Prop)
  (hP : ∀ x, P x → ∃ p : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
        (EuclideanHalfSpace (d + 1) × F) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, P y ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ Bd x))

/-- The chosen chart of `{x // P x}` at `x`. -/
def sliceAtlasChart (x : {x // P x}) :
    OpenPartialHomeomorph {x // P x} (EuclideanHalfSpace (d + 1)) :=
  sliceChart P (hP x.1 x.2).choose.1 (hP x.1 x.2).choose_spec.1
    (hP x.1 x.2).choose_spec.2.2.1 x

/-- The manifold-with-boundary charted space on `{x // P x}` given by slice charts. -/
@[reducible]
def sliceChartedSpace : ChartedSpace (EuclideanHalfSpace (d + 1)) {x // P x} where
  atlas := range (sliceAtlasChart P Bd hP)
  chartAt := sliceAtlasChart P Bd hP
  mem_chart_source x := (hP x.1 x.2).choose_spec.2.1
  chart_mem_atlas x := mem_range_self x

theorem slice_isManifold :
    letI := sliceChartedSpace P Bd hP
    IsManifold (𝓡∂ (d + 1)) ∞ {x // P x} := by
  let _ := sliceChartedSpace P Bd hP
  apply isManifold_of_contDiffOn (𝓡∂ (d + 1)) ∞ {x // P x}
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  exact contDiffOn_of_contMDiffOn_modelSpace (𝓡∂ (d + 1))
    (sliceChart_trans_contMDiffOn P _ _ _ x _ _ _ y)

variable {P Bd} in
theorem slice_isBoundaryPoint_iff {x : {x // P x}} :
    letI := sliceChartedSpace P Bd hP
    (𝓡∂ (d + 1)).IsBoundaryPoint x ↔ Bd x.1 := by
  let _ := sliceChartedSpace P Bd hP
  obtain ⟨hc, hx, hΦ, hB⟩ := (hP x.1 x.2).choose_spec
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  change (0 : ℝ) = (sliceAtlasChart P Bd hP x x).1 0 ↔ Bd x.1
  rw [sliceAtlasChart, sliceChart_apply_val P _ hc hΦ x hx, slice_coord_sub]
  constructor
  · intro h
    exact hB.mp (by linarith)
  · intro h
    have h' := hB.mpr h
    linarith

theorem slice_contMDiff_val :
    letI := sliceChartedSpace P Bd hP
    ContMDiff (𝓡∂ (d + 1)) I ∞ (Subtype.val : {x // P x} → M) := by
  let _ := sliceChartedSpace P Bd hP
  have _ : IsManifold (𝓡∂ (d + 1)) ∞ {x // P x} := slice_isManifold P Bd hP
  intro x
  obtain ⟨hc, hx, hΦ, -⟩ := (hP x.1 x.2).choose_spec
  have he : ContMDiffAt (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞ (chartAt (EuclideanHalfSpace (d + 1)) x) x :=
    contMDiffOn_chart.contMDiffAt
      ((chartAt (EuclideanHalfSpace (d + 1)) x).open_source.mem_nhds
        (mem_chart_source (EuclideanHalfSpace (d + 1)) x))
  have hk : ContMDiff (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
      (fun w => (sliceShift d (hP x.1 x.2).choose.2 w, (0 : F))) :=
    (contMDiff_sliceShift hc).prodMk contMDiff_const
  have hpt := sliceChart_shift_eq P _ hc hΦ x hx
  have hs : ContMDiffAt ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) I ∞ (hP x.1 x.2).choose.1.symm
      (sliceShift d (hP x.1 x.2).choose.2 (chartAt (EuclideanHalfSpace (d + 1)) x x), (0 : F)) := by
    refine (hP x.1 x.2).choose.1.symm.contMDiffOn.contMDiffAt
      ((hP x.1 x.2).choose.1.open_target.mem_nhds ?_)
    change (sliceShift d (hP x.1 x.2).choose.2 (sliceAtlasChart P Bd hP x x), (0 : F)) ∈ _
    rw [sliceAtlasChart, hpt]
    exact (hP x.1 x.2).choose.1.map_source hx
  have hcomp := (hs.comp (chartAt (EuclideanHalfSpace (d + 1)) x x) hk.contMDiffAt).comp x he
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(chartAt (EuclideanHalfSpace (d + 1)) x).open_source.mem_nhds
    (mem_chart_source (EuclideanHalfSpace (d + 1)) x)] with y hy
  change y.1 = (hP x.1 x.2).choose.1.symm
    (sliceShift d (hP x.1 x.2).choose.2 (sliceAtlasChart P Bd hP x y), (0 : F))
  rw [sliceAtlasChart, sliceChart_shift_eq P _ hc hΦ x hy]
  exact ((hP x.1 x.2).choose.1.left_inv hy).symm

theorem slice_mfderiv_val_injective (x : {x // P x}) :
    letI := sliceChartedSpace P Bd hP
    Injective (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x) := by
  let _ := sliceChartedSpace P Bd hP
  have _ : IsManifold (𝓡∂ (d + 1)) ∞ {x // P x} := slice_isManifold P Bd hP
  obtain ⟨hc, hx, hΦ, -⟩ := (hP x.1 x.2).choose_spec
  let a : M → EuclideanSpace ℝ (Fin (d + 1)) := fun u =>
    ((hP x.1 x.2).choose.1 u).1.1 - (hP x.1 x.2).choose.2 • EuclideanSpace.single 0 1
  have ha : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) a x.1 :=
    (contMDiffAt_slice_coord _ _ hx).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x :=
    (slice_contMDiff_val P Bd hP x).mdifferentiableAt (by simp)
  have heq : (a ∘ (Subtype.val : {x // P x} → M)) =ᶠ[𝓝 x] extChartAt (𝓡∂ (d + 1)) x := by
    filter_upwards [(chartAt (EuclideanHalfSpace (d + 1)) x).open_source.mem_nhds
      (mem_chart_source (EuclideanHalfSpace (d + 1)) x)] with y hy
    change _ = (sliceAtlasChart P Bd hP x y).1
    rw [sliceAtlasChart, sliceChart_apply_val P _ hc hΦ x hy]
    rfl
  have hcomp : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) a x.1).comp
      (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (d + 1))) := by
    rw [← mfderiv_comp x ha hv, heq.mfderiv_eq, mfderiv_extChartAt_self]
    rfl
  intro v w hvw
  have hv' := congrArg (fun L => L v) hcomp
  have hw' := congrArg (fun L => L w) hcomp
  change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) a x.1
    (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x v) = v at hv'
  change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) a x.1
    (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x w) = w at hw'
  rw [hvw] at hv'
  exact hv'.symm.trans hw'

theorem slice_mfderiv_val_bijective [FiniteDimensional ℝ F] (hF : Module.finrank ℝ F = 0)
    (x : {x // P x}) :
    letI := sliceChartedSpace P Bd hP
    Bijective (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x) := by
  let _ := sliceChartedSpace P Bd hP
  have _ : IsManifold (𝓡∂ (d + 1)) ∞ {x // P x} := slice_isManifold P Bd hP
  refine ⟨slice_mfderiv_val_injective P Bd hP x, ?_⟩
  obtain ⟨-, hx, -, -⟩ := (hP x.1 x.2).choose_spec
  have hloc := (hP x.1 x.2).choose.1.isLocalDiffeomorphAt I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞ hx
  let L : E' ≃L[ℝ] (EuclideanSpace ℝ (Fin (d + 1)) × F) :=
    hloc.mfderivToContinuousLinearEquiv (by simp)
  have : FiniteDimensional ℝ E' := L.symm.toLinearEquiv.finiteDimensional
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = Module.finrank ℝ E' := by
    rw [L.toLinearEquiv.finrank_eq, Module.finrank_prod, hF, add_zero]
  let f : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] E' :=
    (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x // P x} → M) x).toLinearMap
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f)).mp
    (slice_mfderiv_val_injective P Bd hP x)

variable {P Bd} in
theorem slice_contMDiffWithinAt_iff {F' G' X : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [TopologicalSpace G'] {J : ModelWithCorners ℝ F' G'} [TopologicalSpace X] [ChartedSpace G' X]
    {n : WithTop ℕ∞} (hn : n ≤ ∞) {g : X → {x // P x}} {s : Set X} {z : X} :
    letI := sliceChartedSpace P Bd hP
    ContMDiffWithinAt J (𝓡∂ (d + 1)) n g s z ↔
      ContMDiffWithinAt J I n (Subtype.val ∘ g) s z := by
  let _ := sliceChartedSpace P Bd hP
  constructor
  · intro hg
    exact ((slice_contMDiff_val P Bd hP).of_le hn).contMDiffAt.comp_contMDiffWithinAt z hg
  · intro hg
    have hind : Topology.IsInducing (Subtype.val : {x // P x} → M) := ⟨rfl⟩
    have hcont : ContinuousWithinAt g s z := hind.continuousWithinAt_iff.mpr hg.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    obtain ⟨hc, hx, hΦ, -⟩ := (hP (g z).1 (g z).2).choose_spec
    have ha := (contMDiffAt_slice_coord _ (hP (g z).1 (g z).2).choose.2 hx).of_le hn
    have h := ha.comp_contMDiffWithinAt z hg
    apply h.congr_of_eventuallyEq
    · filter_upwards [hcont ((chartAt (EuclideanHalfSpace (d + 1)) (g z)).open_source.mem_nhds
        (mem_chart_source (EuclideanHalfSpace (d + 1)) (g z)))] with y hy
      change (sliceAtlasChart P Bd hP (g z) (g y)).1 = _
      rw [sliceAtlasChart, sliceChart_apply_val P _ hc hΦ (g z) hy]
      rfl
    · change (sliceAtlasChart P Bd hP (g z) (g z)).1 = _
      rw [sliceAtlasChart, sliceChart_apply_val P _ hc hΦ (g z) hx]
      rfl

variable {P Bd} in
theorem slice_contMDiff_iff {F' G' X : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [TopologicalSpace G'] {J : ModelWithCorners ℝ F' G'} [TopologicalSpace X] [ChartedSpace G' X]
    {n : WithTop ℕ∞} (hn : n ≤ ∞) {g : X → {x // P x}} :
    letI := sliceChartedSpace P Bd hP
    ContMDiff J (𝓡∂ (d + 1)) n g ↔ ContMDiff J I n (Subtype.val ∘ g) := by
  let _ := sliceChartedSpace P Bd hP
  exact forall_congr' (fun z => slice_contMDiffWithinAt_iff hP hn (g := g) (s := univ) (z := z))

end Atlas

end DifferentialGeometry.Manifold.RegularLevel
