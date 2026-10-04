import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPunctured

/-!
# The two-cone fold through the charts of a block

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.1,
tier T1, with review 21 §4.1–§4.2). Let `C` be charts of a block with `d.k = 3`, all fillings at
inner holes, two fillings `m₁` (centre `3/2`) and `m₂` (centre `-3/2`) exhausting the fillings, and
let `D` be a fold datum for a shape with `θ₁ = π/p₁`, `θ₂ = π/p₂`, `pᵢ` the orders of the
fillings. The fold `foldMap : ModelCoordinates → W.pieceInterior ⊤` is the tube chart of `m₁`
composed with `tubeOne` on the cone disc about `v₁` (and its mirror), the tube chart of `m₂`
composed with `tubeTwo` on the cone disc about `v₂`, and the punctured chart composed with the
base lifts `liftT`, `liftS` on the main piece and its mirror. By the overlap identities of
`Seifert/FilledPantsGeometryOverlap` it equals each of these formulas on the whole corresponding
open piece (`foldMap_of_main`, `foldMap_of_mirrorMain`, ...), so it is a local diffeomorphism on
the open domain `foldDomain` (`isLocalDiffeomorphAt_foldMap`), and it is onto the interior
(`surjective_foldMap`: product and collar points from the doubled triangle via A4Q's
`foldExt_surjOn`, central fibres from the cone vertices).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount)

def chartNumbers : Numbers :=
  ⟨d.fillingOrder m₁, d.fillingOrder m₂, (d.fillingSlope m₁).2, (d.fillingSlope m₂).2, C.a m₁,
    C.a m₂, C.b m₁, C.b m₂⟩

variable (hk : d.k = 3) (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)

include hp in
theorem chartNumbers_bezout₁ :
    ((chartNumbers C m₁ m₂).p₁ : ℤ) * (chartNumbers C m₁ m₂).b₁ -
      (chartNumbers C m₁ m₂).a₁ * (chartNumbers C m₁ m₂).q₁ = 1 := by
  have h := C.bezout m₁
  rw [SeifertBlockCharts.fillingSlope_eq_fillingOrder (hp m₁)] at h
  exact h

include hp in
theorem chartNumbers_bezout₂ :
    ((chartNumbers C m₁ m₂).p₂ : ℤ) * (chartNumbers C m₁ m₂).b₂ -
      (chartNumbers C m₁ m₂).a₂ * (chartNumbers C m₁ m₂).q₂ = 1 := by
  have h := C.bezout m₂
  rw [SeifertBlockCharts.fillingSlope_eq_fillingOrder (hp m₂)] at h
  exact h

include hp in
theorem seamDir_eq_one (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) :
    C.seamDir m₁ = seamFwd ((3 / 2 : ℝ) : ℂ) (chartNumbers C m₁ m₂).p₁ (chartNumbers C m₁ m₂).p₁
      (chartNumbers C m₁ m₂).q₁ (chartNumbers C m₁ m₂).a₁ (chartNumbers C m₁ m₂).b₁ := by
  unfold SeifertBlockCharts.seamDir
  rw [hc₁, SeifertBlockCharts.fillingSlope_eq_fillingOrder (hp m₁)]
  rfl

include hp in
theorem seamDir_eq_two (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ)) :
    C.seamDir m₂ = seamFwd ((-(3 / 2) : ℝ) : ℂ) (chartNumbers C m₁ m₂).p₂ (chartNumbers C m₁ m₂).p₂
      (chartNumbers C m₁ m₂).q₂ (chartNumbers C m₁ m₂).a₂ (chartNumbers C m₁ m₂).b₂ := by
  unfold SeifertBlockCharts.seamDir
  rw [hc₂, SeifertBlockCharts.fillingSlope_eq_fillingOrder (hp m₂)]
  rfl

include hj hp in
theorem puncturedChart_seamDir {m : Fin d.fillingCount} {y : ℂ × Circle} (hy0 : y.1 ≠ 0)
    (hy1 : ‖y.1‖ < 1) : C.puncturedChart hk (C.seamDir m y) = C.tubeMap m y := by
  have hdist : ‖(C.seamDir m y).1 - C.tubeCentre m‖ < C.collarRadius m := by
    rw [SeifertBlockCharts.seamDir, norm_seamFwd_sub]
    have : ‖y.1‖ ^ d.fillingOrder m < 1 :=
      pow_lt_one₀ (norm_nonneg _) hy1 (SeifertBlockCharts.fillingOrder_pos (hp m)).ne'
    linarith [C.half_lt_collarRadius (hp m)]
  rw [C.puncturedChart_of_collar hk hj hp hdist, C.seamInv_seamDir (hp m) hy0]

include hk hp in
theorem mem_puncturedDomain_of (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ))
    (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ)) {u : ℂ} (t : Circle) (h3 : ‖u‖ < 3)
    (h1 : u ≠ 3 / 2) (h2 : u ≠ -(3 / 2)) : (u, t) ∈ C.puncturedDomain := by
  rw [SeifertBlockCharts.mem_puncturedDomain]
  by_cases hu : u ∈ planarOpen d.k
  · exact Or.inl hu
  right
  have hnot : ¬ planarFunction 3 u < 0 := fun h => hu (mem_planarOpen_of_planarFunction_neg hk h)
  rw [planarFunction_three_neg_iff, not_and_or, not_and_or] at hnot
  rcases hnot with h | h | h
  · exact absurd h3 h
  · refine ⟨m₁, ?_, ?_⟩
    · rw [hc₁]
      have : ‖u - ((3 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
        push_cast; push Not at h; exact h
      linarith [C.half_lt_collarRadius (hp m₁)]
    · rw [hc₁]; push_cast; exact h1
  · refine ⟨m₂, ?_, ?_⟩
    · rw [hc₂]
      have : ‖u - ((-(3 / 2) : ℝ) : ℂ)‖ ≤ 1 / 2 := by
        push_cast; rw [sub_neg_eq_add]; push Not at h; exact h
      linarith [C.half_lt_collarRadius (hp m₂)]
    · rw [hc₂]; push_cast; exact h2


section Map

variable {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)

open Classical in
def foldMap (p : ModelCoordinates) : W.pieceInterior ⊤ :=
  if zOf p ∈ discOne D hθ₁ then C.tubeMap m₁ (tubeOne D (chartNumbers C m₁ m₂) p)
  else if zOf p ∈ mirrorSet σ (discOne D hθ₁) then
    C.tubeMap m₁ (tubeOneS D (chartNumbers C m₁ m₂) p)
  else if zOf p ∈ discTwo D hθ₂ then C.tubeMap m₂ (tubeTwo D (chartNumbers C m₁ m₂) p)
  else if zOf p ∈ mainSet D hθ₁ hθ₂ then C.puncturedChart hk (liftT D (chartNumbers C m₁ m₂) p)
  else C.puncturedChart hk (liftS D (chartNumbers C m₁ m₂) p)

def foldDomain : TopologicalSpace.Opens ModelCoordinates :=
  ⟨zOf ⁻¹' baseDomain D hθ₁ hθ₂, (isOpen_baseDomain D hθ₁ hθ₂).preimage contDiff_zOf.continuous⟩

theorem norm_tubeOne_fst {p : ModelCoordinates} (hd : zOf p ∈ discOne D hθ₁) :
    ‖(tubeOne D (chartNumbers C m₁ m₂) p).1‖ < 1 := by
  change ‖coneDisc σ.vertexOne (zOf p) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact lt_of_lt_of_le hd.2 (radiusOne_le D hθ₁)

theorem norm_tubeTwo_fst {p : ModelCoordinates} (hd : zOf p ∈ discTwo D hθ₂) :
    ‖(tubeTwo D (chartNumbers C m₁ m₂) p).1‖ < 1 := by
  change ‖exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) * _‖ < 1
  rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_exp_ofReal_mul_I, one_mul]
  exact lt_of_lt_of_le hd.2 (radiusTwo_le D hθ₂)

theorem norm_tubeOneS_fst {p : ModelCoordinates} (hd : zOf p ∈ mirrorSet σ (discOne D hθ₁)) :
    ‖(tubeOneS D (chartNumbers C m₁ m₂) p).1‖ < 1 := by
  have hd' : zOf (flipMap (chartNumbers C m₁ m₂).c₀ p) ∈ discOne D hθ₁ := by
    rw [refl_zero_zOf_flip]; exact hd.2
  change ‖conj (tubeOne D (chartNumbers C m₁ m₂) (flipMap _ p)).1‖ < 1
  rw [norm_conj]
  exact norm_tubeOne_fst C m₁ m₂ D hθ₁ hd'

theorem tubeOne_fst_ne_zero {p : ModelCoordinates} (h : coneDisc σ.vertexOne (zOf p) ≠ 0) :
    (tubeOne D (chartNumbers C m₁ m₂) p).1 ≠ 0 :=
  mul_ne_zero h (Circle.coe_ne_zero _)

theorem tubeTwo_fst_ne_zero {p : ModelCoordinates}
    (h : exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) ≠ 0) :
    (tubeTwo D (chartNumbers C m₁ m₂) p).1 ≠ 0 :=
  mul_ne_zero h (Circle.coe_ne_zero _)

theorem foldMap_of_discOne {p : ModelCoordinates} (hd : zOf p ∈ discOne D hθ₁) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ p = C.tubeMap m₁ (tubeOne D (chartNumbers C m₁ m₂) p) := by
  unfold foldMap
  rw [ite_eq_left hd]

theorem foldMap_of_mirrorDiscOne {p : ModelCoordinates}
    (hd : zOf p ∈ mirrorSet σ (discOne D hθ₁)) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ p = C.tubeMap m₁ (tubeOneS D (chartNumbers C m₁ m₂) p) := by
  unfold foldMap
  rw [ite_eq_right (fun h => not_mem_mirrorDiscOne_of_discOne D hθ₁ h hd), ite_eq_left hd]

theorem foldMap_of_discTwo {p : ModelCoordinates} (hd : zOf p ∈ discTwo D hθ₂) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ p = C.tubeMap m₂ (tubeTwo D (chartNumbers C m₁ m₂) p) := by
  unfold foldMap
  rw [ite_eq_right (fun h => not_mem_discTwo_of_discOne D hθ₁ hθ₂ h hd),
    ite_eq_right (fun h => not_mem_discTwo_of_mirrorDiscOne D hθ₁ hθ₂ h hd), ite_eq_left hd]

variable (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))

include hj hp hc₁ in
theorem tubeOne_eq_puncturedChart {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂)
    (hd : zOf p ∈ discOne D hθ₁) :
    C.tubeMap m₁ (tubeOne D (chartNumbers C m₁ m₂) p) =
      C.puncturedChart hk (liftT D (chartNumbers C m₁ m₂) p) := by
  rw [liftT_eq_seamFwd_tubeOne D hθ₁ hθ₂ (chartNumbers_bezout₁ C m₁ m₂ hp) hm hd,
    ← seamDir_eq_one C m₁ m₂ hp hc₁, puncturedChart_seamDir C hk hj hp
      (tubeOne_fst_ne_zero C m₁ m₂ D (sector_one D hθ₁ hθ₂ hm hd).1)
      (norm_tubeOne_fst C m₁ m₂ D hθ₁ hd)]

include hj hp hc₂ in
theorem tubeTwo_eq_puncturedChart {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂)
    (hd : zOf p ∈ discTwo D hθ₂) :
    C.tubeMap m₂ (tubeTwo D (chartNumbers C m₁ m₂) p) =
      C.puncturedChart hk (liftT D (chartNumbers C m₁ m₂) p) := by
  rw [liftT_eq_seamFwd_tubeTwo D hθ₁ hθ₂ (chartNumbers_bezout₂ C m₁ m₂ hp) hm hd,
    ← seamDir_eq_two C m₁ m₂ hp hc₂, puncturedChart_seamDir C hk hj hp
      (tubeTwo_fst_ne_zero C m₁ m₂ D (sector_two D hθ₁ hθ₂ hm hd).1)
      (norm_tubeTwo_fst C m₁ m₂ D hθ₂ hd)]

include hj hp hc₁ hc₂ in
theorem foldMap_of_main {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ p = C.puncturedChart hk (liftT D (chartNumbers C m₁ m₂) p) := by
  by_cases h1 : zOf p ∈ discOne D hθ₁
  · rw [foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ h1]
    exact tubeOne_eq_puncturedChart C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hm h1
  by_cases h3 : zOf p ∈ discTwo D hθ₂
  · rw [foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ h3]
    exact tubeTwo_eq_puncturedChart C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₂ hm h3
  unfold foldMap
  rw [ite_eq_right h1, ite_eq_right (not_mem_mirrorDiscOne_of_main D hθ₁ hθ₂ hm),
    ite_eq_right h3, ite_eq_left hm]

include hj hp hc₁ hc₂ in
theorem foldMap_of_mirrorMain {p : ModelCoordinates}
    (hm : zOf p ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ p = C.puncturedChart hk (liftS D (chartNumbers C m₁ m₂) p) := by
  have hm' : zOf (flipMap (chartNumbers C m₁ m₂).c₀ p) ∈ mainSet D hθ₁ hθ₂ := by
    rw [refl_zero_zOf_flip]; exact hm.2
  have h1 : zOf p ∉ discOne D hθ₁ := not_mem_discOne_of_mirrorMain D hθ₁ hθ₂ hm
  by_cases h2 : zOf p ∈ mirrorSet σ (discOne D hθ₁)
  · rw [foldMap_of_mirrorDiscOne C m₁ m₂ hk D hθ₁ hθ₂ h2]
    have hd' : zOf (flipMap (chartNumbers C m₁ m₂).c₀ p) ∈ discOne D hθ₁ := by
      rw [refl_zero_zOf_flip]; exact h2.2
    unfold liftS tubeOneS
    rw [liftT_eq_seamFwd_tubeOne D hθ₁ hθ₂ (chartNumbers_bezout₁ C m₁ m₂ hp) hm' hd',
      ← seamFwd_conjPair, ← seamDir_eq_one C m₁ m₂ hp hc₁]
    refine (puncturedChart_seamDir C hk hj hp ?_ ?_).symm
    · change conj (tubeOne D (chartNumbers C m₁ m₂) (flipMap _ p)).1 ≠ 0
      rw [map_ne_zero]
      exact tubeOne_fst_ne_zero C m₁ m₂ D (sector_one D hθ₁ hθ₂ hm' hd').1
    · exact norm_tubeOneS_fst C m₁ m₂ D hθ₁ h2
  by_cases h3 : zOf p ∈ discTwo D hθ₂
  · rw [foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ h3]
    have hd' : zOf (flipMap (chartNumbers C m₁ m₂).c₀ p) ∈ discTwo D hθ₂ := by
      rw [refl_zero_zOf_flip]; exact refl_zero_mem_discTwo D hθ₂ h3
    unfold liftS
    rw [liftT_eq_seamFwd_tubeTwo D hθ₁ hθ₂ (chartNumbers_bezout₂ C m₁ m₂ hp) hm' hd',
      ← seamFwd_conjPair, conjPair_tubeTwo_flip D hθ₂ (chartNumbers_bezout₂ C m₁ m₂ hp) h3,
      ← seamDir_eq_two C m₁ m₂ hp hc₂]
    refine (puncturedChart_seamDir C hk hj hp ?_ (norm_tubeTwo_fst C m₁ m₂ D hθ₂ h3)).symm
    have := tubeTwo_fst_ne_zero C m₁ m₂ D (sector_two D hθ₁ hθ₂ hm' hd').1
    rw [← conjPair_tubeTwo_flip D hθ₂ (chartNumbers_bezout₂ C m₁ m₂ hp) h3]
    change conj (tubeTwo D (chartNumbers C m₁ m₂) (flipMap _ p)).1 ≠ 0
    rw [map_ne_zero]
    exact this
  by_cases h4 : zOf p ∈ mainSet D hθ₁ hθ₂
  · rw [foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ h4,
      liftT_eq_liftS D hθ₂ (mainSet_inter_mirror_subset D hθ₁ hθ₂ h4 hm)]
  unfold foldMap
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

include hk hp hc₁ hc₂ in
theorem liftT_mem_puncturedDomain {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂) :
    liftT D (chartNumbers C m₁ m₂) p ∈ C.puncturedDomain := by
  obtain ⟨-, -, -, h1, h2⟩ := mainSet_props D hθ₁ hθ₂ hm
  refine mem_puncturedDomain_of C m₁ m₂ hk hp hc₁ hc₂ _ (norm_f_lt_three_of_mainSet D hθ₁ hθ₂ hm)
    ?_ ?_
  · intro h
    rw [mem_phaseDomain_iff, h] at h1
    norm_num at h1
  · intro h
    rw [mem_phaseDomain_iff, h] at h2
    norm_num at h2

include hk hp hc₁ hc₂ in
theorem liftS_mem_puncturedDomain {p : ModelCoordinates}
    (hm : zOf p ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) :
    liftS D (chartNumbers C m₁ m₂) p ∈ C.puncturedDomain := by
  have hm' : zOf (flipMap (chartNumbers C m₁ m₂).c₀ p) ∈ mainSet D hθ₁ hθ₂ := by
    rw [refl_zero_zOf_flip]; exact hm.2
  have h := liftT_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂ hm'
  obtain ⟨-, -, -, h1, h2⟩ := mainSet_props D hθ₁ hθ₂ hm'
  refine mem_puncturedDomain_of C m₁ m₂ hk hp hc₁ hc₂ _ ?_ ?_ ?_
  · change ‖conj (D.f _)‖ < 3
    rw [norm_conj]; exact norm_f_lt_three_of_mainSet D hθ₁ hθ₂ hm'
  · change conj (D.f _) ≠ 3 / 2
    intro he
    have hf : D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ p)) = 3 / 2 := by
      have := congrArg conj he
      rw [Complex.conj_conj] at this
      rw [this]
      simp only [map_div₀, map_ofNat]
    rw [mem_phaseDomain_iff, hf] at h1
    norm_num at h1
  · change conj (D.f _) ≠ -(3 / 2)
    intro he
    have hf : D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ p)) = -(3 / 2) := by
      have := congrArg conj he
      rw [Complex.conj_conj] at this
      rw [this]
      simp only [map_neg, map_div₀, map_ofNat]
    rw [mem_phaseDomain_iff, hf] at h2
    norm_num at h2

include hj hp hc₁ hc₂ in
theorem isLocalDiffeomorphAt_foldMap {p : ModelCoordinates}
    (hp' : p ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (foldMap C m₁ m₂ hk D hθ₁ hθ₂) p := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hz : Continuous zOf := contDiff_zOf.continuous
  have hε : ∀ y : ℂ × Circle, ‖y.1‖ < 1 → ‖y.1‖ < 1 + C.ε := fun y hy => by
    linarith [C.ε_pos]
  rcases hp' with (((h | h) | h) | h) | h
  · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp
      (hf := isLocalDiffeomorphAt_liftT D hθ₁ hθ₂ h (n := chartNumbers C m₁ m₂))
      (hg := C.isLocalDiffeomorphAt_puncturedChart hk hj hp
        (liftT_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂ h)))
    filter_upwards [((isOpen_mainSet D hθ₁ hθ₂).preimage hz).mem_nhds h] with x hx
    exact foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx
  · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp
      (hf := isLocalDiffeomorphAt_liftS D hθ₁ hθ₂ h (n := chartNumbers C m₁ m₂))
      (hg := C.isLocalDiffeomorphAt_puncturedChart hk hj hp
        (liftS_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂ h)))
    filter_upwards [((isOpen_mirrorSet (isOpen_mainSet D hθ₁ hθ₂)).preimage hz).mem_nhds h]
      with x hx
    exact foldMap_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx
  · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp
      (hf := isLocalDiffeomorphAt_tubeOne D hθ₁ h (n := chartNumbers C m₁ m₂))
      (hg := C.isLocalDiffeomorphAt_tubeMap (m := m₁)
        (hε _ (norm_tubeOne_fst C m₁ m₂ D hθ₁ h))))
    filter_upwards [((isOpen_discOne D hθ₁).preimage hz).mem_nhds h] with x hx
    exact foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ hx
  · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp
      (hf := isLocalDiffeomorphAt_tubeOneS D hθ₁ h (n := chartNumbers C m₁ m₂))
      (hg := C.isLocalDiffeomorphAt_tubeMap (m := m₁)
        (hε _ (norm_tubeOneS_fst C m₁ m₂ D hθ₁ h))))
    filter_upwards [((isOpen_mirrorSet (isOpen_discOne D hθ₁)).preimage hz).mem_nhds h]
      with x hx
    exact foldMap_of_mirrorDiscOne C m₁ m₂ hk D hθ₁ hθ₂ hx
  · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp
      (hf := isLocalDiffeomorphAt_tubeTwo D hθ₂ h (n := chartNumbers C m₁ m₂))
      (hg := C.isLocalDiffeomorphAt_tubeMap (m := m₂)
        (hε _ (norm_tubeTwo_fst C m₁ m₂ D hθ₂ h))))
    filter_upwards [((isOpen_discTwo D hθ₂).preimage hz).mem_nhds h] with x hx
    exact foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ hx

theorem exists_eC_eq (w : Circle) : ∃ t : ℝ, eC t = w :=
  ⟨arg w / (2 * Real.pi), by
    rw [eC, mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)]
    exact Circle.exp_arg w⟩

include hk hc₁ hc₂ in
theorem norm_lt_three_of_puncturedDomain (hall : ∀ m, m = m₁ ∨ m = m₂) {y : ℂ × Circle}
    (hy : y ∈ C.puncturedDomain) :
    ‖y.1‖ < 3 ∧ y.1 ≠ 3 / 2 ∧ y.1 ≠ -(3 / 2) := by
  rcases C.mem_puncturedDomain.1 hy with h | ⟨m, hm, hne⟩
  · have := (planarFunction_three_neg_iff y.1).1 (planarFunction_neg_of_mem_planarOpen hk h)
    refine ⟨this.1, fun he => ?_, fun he => ?_⟩
    · have := this.2.1; rw [he] at this; norm_num at this
    · have := this.2.2; rw [he] at this; norm_num at this
  · have hR := C.collarRadius_le_three_halves (m := m)
    have key : ∀ c : ℝ, |c| = 3 / 2 → C.tubeCentre m = (c : ℂ) →
        ‖y.1‖ < 3 ∧ y.1 ≠ (c : ℂ) ∧ y.1 ≠ ((-c : ℝ) : ℂ) := by
      intro c hc hcm
      rw [hcm] at hm hne
      have hn := norm_sub_norm_le y.1 (c : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, hc] at hn
      refine ⟨by linarith, hne, fun he => ?_⟩
      rw [he, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show -c - c = -(2 * c) by ring, abs_neg, abs_mul, hc] at hm
      norm_num at hm
      linarith
    rcases hall m with rfl | rfl
    · obtain ⟨h1, h2, h3⟩ := key (3 / 2) (by norm_num) hc₁
      refine ⟨h1, fun he => h2 (by rw [he]; push_cast; ring), fun he => h3 (by
        rw [he]; push_cast; ring)⟩
    · obtain ⟨h1, h2, h3⟩ := key (-(3 / 2)) (by norm_num) hc₂
      refine ⟨h1, fun he => h3 (by rw [he]; push_cast; ring), fun he => h2 (by
        rw [he]; push_cast; ring)⟩

include hk hj hp hc₁ hc₂ in
theorem surjective_foldMap (hall : ∀ m, m = m₁ ∨ m = m₂) (x : W.pieceInterior ⊤) :
    ∃ p ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂, foldMap C m₁ m₂ hk D hθ₁ hθ₂ p = x := by
  set n := chartNumbers C m₁ m₂ with hn
  have hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (D.f z).im = 0 :=
    fun i z hz h => D.f_real_of_mem_foldWall ⟨hz, h⟩
  have hv1 := f_vertexOne D hθ₁
  have hv2 := f_vertexTwo D hθ₂
  rcases C.exists_puncturedChart_eq hk hj hp x with ⟨y, hy, rfl⟩ | ⟨m, w, rfl⟩
  · obtain ⟨h3, h1, h2⟩ := norm_lt_three_of_puncturedDomain C m₁ m₂ hk hc₁ hc₂ hall hy
    have hbase : y.1 ∈ σ.base := ⟨h3, fun h => absurd h (θ₂_pos hθ₂).ne'⟩
    obtain ⟨z, hz, hzf⟩ := foldExt_surjOn hreal D.bijOn_f hbase
    rcases σ.mem_domain_iff.1 hz with hT | hT
    · rw [σ.foldExt_of_mem_triangle D.f hT] at hzf
      have hne1 : z ≠ σ.vertexOne := fun he => h1 (by rw [← hzf, he, hv1])
      have hne2 : z ≠ σ.vertexTwo := fun he => h2 (by rw [← hzf, he, hv2])
      have hm := triangle_diff_subset_mainSet D hθ₁ hθ₂ hT hne1 hne2
      obtain ⟨t, ht⟩ := exists_eC_eq (y.2 * (basePhase n.k₁ n.k₂ y.1)⁻¹)
      refine ⟨logCoords ⟨z, hT.1⟩ t, ?_, ?_⟩
      · change zOf (logCoords ⟨z, hT.1⟩ t) ∈ baseDomain D hθ₁ hθ₂
        rw [show zOf (logCoords ⟨z, hT.1⟩ t) = z by simp [zOf]]
        exact Or.inl (Or.inl (Or.inl (Or.inl hm)))
      · have hz' : zOf (logCoords ⟨z, hT.1⟩ t) = z := by simp [zOf]
        rw [foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (by rw [hz']; exact hm)]
        congr 1
        unfold liftT
        rw [hz', hzf, logCoords_two, ht, inv_mul_cancel_right]
    · by_cases hzT : z ∈ σ.triangle
      · rw [σ.foldExt_of_mem_triangle D.f hzT] at hzf
        have hne1 : z ≠ σ.vertexOne := fun he => h1 (by rw [← hzf, he, hv1])
        have hne2 : z ≠ σ.vertexTwo := fun he => h2 (by rw [← hzf, he, hv2])
        have hm := triangle_diff_subset_mainSet D hθ₁ hθ₂ hzT hne1 hne2
        obtain ⟨t, ht⟩ := exists_eC_eq (y.2 * (basePhase n.k₁ n.k₂ y.1)⁻¹)
        refine ⟨logCoords ⟨z, hzT.1⟩ t, ?_, ?_⟩
        · change zOf (logCoords ⟨z, hzT.1⟩ t) ∈ baseDomain D hθ₁ hθ₂
          rw [show zOf (logCoords ⟨z, hzT.1⟩ t) = z by simp [zOf]]
          exact Or.inl (Or.inl (Or.inl (Or.inl hm)))
        · have hz' : zOf (logCoords ⟨z, hzT.1⟩ t) = z := by simp [zOf]
          rw [foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (by rw [hz']; exact hm)]
          congr 1
          unfold liftT
          rw [hz', hzf, logCoords_two, ht, inv_mul_cancel_right]
      rw [foldExt_of_refl_mem hreal hT] at hzf
      have hzim : 0 < z.im := by simpa [ConeShape.refl] using hT.1
      have hne1 : σ.refl 0 z ≠ σ.vertexOne := fun he => h1 (by
        rw [← hzf, he, hv1]; simp only [map_div₀, map_ofNat])
      have hne2 : σ.refl 0 z ≠ σ.vertexTwo := fun he => h2 (by
        rw [← hzf, he, hv2]; simp only [map_neg, map_div₀, map_ofNat])
      have hm := triangle_diff_subset_mainSet D hθ₁ hθ₂ hT hne1 hne2
      obtain ⟨t, ht⟩ := exists_eC_eq (y.2 * basePhase n.k₁ n.k₂ (D.f (σ.refl 0 z)) * eC n.c₀)
      refine ⟨logCoords ⟨z, hzim⟩ t, ?_, ?_⟩
      · change zOf (logCoords ⟨z, hzim⟩ t) ∈ baseDomain D hθ₁ hθ₂
        rw [show zOf (logCoords ⟨z, hzim⟩ t) = z by simp [zOf]]
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hzim, hm⟩)))
      · have hz' : zOf (logCoords ⟨z, hzim⟩ t) = z := by simp [zOf]
        rw [foldMap_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
          (by rw [hz']; exact ⟨hzim, hm⟩)]
        congr 1
        unfold liftS liftT conjPair
        rw [refl_zero_zOf_flip, hz', flipMap_two, logCoords_two, hzf]
        congr 1
        rw [eC, show 2 * Real.pi * (n.c₀ - t) = 2 * Real.pi * n.c₀ + -(2 * Real.pi * t) by ring,
          Circle.exp_add, Circle.exp_neg]
        change (Circle.exp (2 * Real.pi * n.c₀) * (eC t)⁻¹ *
          basePhase n.k₁ n.k₂ (D.f (σ.refl 0 z)))⁻¹ = y.2
        rw [ht]
        change (eC n.c₀ * _ * _)⁻¹ = y.2
        group
        rw [mul_comm _ y.2, mul_assoc, zpow_neg_one, inv_mul_cancel, mul_one]
  · rcases hall m with hm | hm
    · rw [hm]
      obtain ⟨t, ht⟩ := exists_eC_eq w
      have hp0 : ((chartNumbers C m₁ m₂).p₁ : ℝ) ≠ 0 := by exact_mod_cast p₁_ne_zero hθ₁
      set s := t / (chartNumbers C m₁ m₂).p₁ - betaOne D (chartNumbers C m₁ m₂) σ.vertexOne
        with hs
      refine ⟨logCoords ⟨σ.vertexOne, σ.vertexOne_im_pos⟩ s, ?_, ?_⟩
      · change zOf _ ∈ baseDomain D hθ₁ hθ₂
        rw [show zOf (logCoords ⟨σ.vertexOne, σ.vertexOne_im_pos⟩ s) = σ.vertexOne by simp [zOf]]
        exact Or.inl (Or.inl (Or.inr (vertexOne_mem_discOne D hθ₁)))
      · have hz' : zOf (logCoords ⟨σ.vertexOne, σ.vertexOne_im_pos⟩ s) = σ.vertexOne := by
          simp [zOf]
        rw [foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂
           (by rw [hz']; exact vertexOne_mem_discOne D hθ₁)]
        congr 1
        unfold tubeOne
        rw [hz', coneDisc_self, zero_mul, logCoords_two]
        congr 1
        rw [← ht]
        congr 1
        rw [hs]
        field_simp
        ring
    · rw [hm]
      obtain ⟨t, ht⟩ := exists_eC_eq w
      have hp0 : ((chartNumbers C m₁ m₂).p₂ : ℝ) ≠ 0 := by exact_mod_cast p₂_ne_zero hθ₂
      set s := t / (chartNumbers C m₁ m₂).p₂ - betaTwo D (chartNumbers C m₁ m₂) σ.vertexTwo
        with hs
      refine ⟨logCoords ⟨σ.vertexTwo, vertexTwo_im_pos' hθ₂⟩ s, ?_, ?_⟩
      · change zOf _ ∈ baseDomain D hθ₁ hθ₂
        rw [show zOf (logCoords ⟨σ.vertexTwo, vertexTwo_im_pos' hθ₂⟩ s) = σ.vertexTwo by
          simp [zOf]]
        exact Or.inr (vertexTwo_mem_discTwo D hθ₂)
      · have hz' : zOf (logCoords ⟨σ.vertexTwo, vertexTwo_im_pos' hθ₂⟩ s) = σ.vertexTwo := by
          simp [zOf]
        rw [foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂
           (by rw [hz']; exact vertexTwo_mem_discTwo D hθ₂)]
        congr 1
        unfold tubeTwo
        rw [hz', coneDisc_self, mul_zero, zero_mul, logCoords_two]
        congr 1
        rw [← ht]
        congr 1
        rw [hs]
        field_simp
        ring

end Map

end Fold

end TwoConeFold

end GC.Seifert
