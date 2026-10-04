import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypLifts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypGaugeWall
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatFold

/-!
# The fold of a hyperbolic closed triangle block

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3–4, with
review 33 §6.2: one layer for both rows). Let `C` be charts of a closed triangle block with
`orbChi < 0` and `D` a fold datum on the hyperbolic triangle `C.closedHypShape` (cone `j` at hole
`j`, the outer cone third). The model is `closedConnectionModel` (`H² × ℝ` if `e = 0`, `SL₂~`
otherwise), the signed fibre step is `ℓ = 1` if `e = 0` and `ℓ = A/e` otherwise
(`A = hypArea σ = 2(π - θ₁ - θ₂ - θ₃)`), and the local gauges are `0`, resp. the recentring gauges
`G_{vⱼ} = 2 arg (1 - v̄ⱼ w)` of the gauge lane, so the datum contract holds: the screw fibre
formulas (`screwAt_hyperbolicProduct_two`, `screwAt_universalSL2_two`), the wall-0 and wall-1
oddness and the real wall-2 period `(G₁ - G₂) + (G₁ - G₂) ∘ r₂ = A = ℓ e` (`hypGauge_wallTwo`)
(`hypDatum`).

The fold `hypMap` is the tube chart of hole `1` composed with `tubeOne` on the disc about `v₁`,
with `tubeOne ∘ S₃⁻¹` on its mirror, the tube charts of holes `2`, `0` composed with `tubeTwo`,
`tubeThree` on the discs about `v₂`, `0`, and `P ∘ liftP`, `P ∘ liftM` on the main set and its
mirror, all read in the base coordinate `hb`. In the good sectors the tube formulas equal the
punctured formulas (`tubeOne_eq_liftP`, …), so the fold equals `P ∘ liftP` on the main set and
`P ∘ liftM` on its mirror (`hypMap_of_main`, `hypMap_of_conjMain`); it is a local
diffeomorphism on the open domain `hypDomain` (`isLocalDiffeomorphAt_hypMap`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

theorem two_screw_field (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) (ψ : ℂ → ℝ) {c : ℂ}
    (hc : ‖c‖ < 1) (hcase : (m = .hyperbolicProduct ∧ ψ = 0) ∨
      (m = .universalSL2 ∧ ψ = hypGauge c)) (p : ℕ+) (q : ℤ) (ℓ : ℝ) (x : ModelCoordinates) :
    screwAt m hm (hypVertex c) p q ℓ x 2 =
      x 2 - ℓ * q / p + ψ (hb (screwAt m hm (hypVertex c) p q ℓ x)) - ψ (hb x) := by
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [screwAt_hyperbolicProduct_two]
    simp
  · exact screwAt_universalSL2_two hm hc p q ℓ x

section Datum

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : d.orbChi < 0)

def closedStepHyp : ℝ :=
  if d.euler = 0 then 1 else hypArea (C.closedHypShape hc h3 hχ) / closedEuler C hc h3

def gaugeOne : ℂ → ℝ :=
  if d.euler = 0 then 0 else hypGauge (C.closedHypShape hc h3 hχ).vertexOne

def gaugeTwo : ℂ → ℝ :=
  if d.euler = 0 then 0 else hypGauge (C.closedHypShape hc h3 hχ).vertexTwo

theorem closedStepHyp_ne_zero : closedStepHyp C hc h3 hχ ≠ 0 := by
  unfold closedStepHyp
  split_ifs with he
  · exact one_ne_zero
  · have hE : closedEuler C hc h3 ≠ 0 := fun h => he ((closedEuler_eq_zero_iff C hc h3).1 h)
    exact div_ne_zero (hypArea_pos (C.closedHypShape_curv hc h3 hχ)).ne' hE

theorem closedStepHyp_closing :
    closedStepHyp C hc h3 hχ * closedEuler C hc h3 =
      if d.euler = 0 then 0 else hypArea (C.closedHypShape hc h3 hχ) := by
  unfold closedStepHyp
  split_ifs with he
  · rw [(closedEuler_eq_zero_iff C hc h3).2 he, mul_zero]
  · have hE : closedEuler C hc h3 ≠ 0 := fun h => he ((closedEuler_eq_zero_iff C hc h3).1 h)
    field_simp

theorem gaugeOne_cases :
    (d.closedConnectionModel = .hyperbolicProduct ∧ gaugeOne C hc h3 hχ = 0) ∨
      (d.closedConnectionModel = .universalSL2 ∧
        gaugeOne C hc h3 hχ = hypGauge (C.closedHypShape hc h3 hχ).vertexOne) := by
  rw [d.closedConnectionModel_of_hyp hχ]
  unfold gaugeOne
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem gaugeTwo_cases :
    (d.closedConnectionModel = .hyperbolicProduct ∧ gaugeTwo C hc h3 hχ = 0) ∨
      (d.closedConnectionModel = .universalSL2 ∧
        gaugeTwo C hc h3 hχ = hypGauge (C.closedHypShape hc h3 hχ).vertexTwo) := by
  rw [d.closedConnectionModel_of_hyp hχ]
  unfold gaugeTwo
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

def hypDatum (D : (C.closedHypShape hc h3 hχ).FoldData) : HypDatum where
  σ := C.closedHypShape hc h3 hχ
  hσ := C.closedHypShape_curv hc h3 hχ
  D := D
  q₁ := C.holeTwist hc h3 1
  q₂ := C.holeTwist hc h3 2
  q₃ := C.holeTwist hc h3 0
  a₁ := C.holeA hc h3 1
  a₂ := C.holeA hc h3 2
  a₃ := C.holeA hc h3 0
  b₁ := C.holeB hc h3 1
  b₂ := C.holeB hc h3 2
  b₃ := C.holeB hc h3 0
  bez₁ := C.holeBezout hc h3 1
  bez₂ := C.holeBezout hc h3 2
  bez₃ := C.holeBezout hc h3 0
  m := d.closedConnectionModel
  hm := d.closedConnectionModel_hyp_cases hχ
  ℓ := closedStepHyp C hc h3 hχ
  ℓ_ne := closedStepHyp_ne_zero C hc h3 hχ
  ψ₁ := gaugeOne C hc h3 hχ
  ψ₂ := gaugeTwo C hc h3 hχ
  contDiffOn_ψ₁ := by
    unfold gaugeOne
    split_ifs
    · exact contDiffOn_const
    · exact contDiffOn_hypGauge _ (HypFold.norm_vertexOne_lt_one (C.closedHypShape_curv hc h3 hχ))
  contDiffOn_ψ₂ := by
    unfold gaugeTwo
    split_ifs
    · exact contDiffOn_const
    · exact contDiffOn_hypGauge _ (HypFold.norm_vertexTwo_lt_one (C.closedHypShape_curv hc h3 hχ))
  two_screwOne := fun x => two_screw_field _ _ _
    (HypFold.norm_vertexOne_lt_one (C.closedHypShape_curv hc h3 hχ)) (gaugeOne_cases C hc h3 hχ)
    _ _ _ x
  two_screwTwo := fun x => two_screw_field _ _ _
    (HypFold.norm_vertexTwo_lt_one (C.closedHypShape_curv hc h3 hχ)) (gaugeTwo_cases C hc h3 hχ)
    _ _ _ x
  ψ₂_conj := fun w hw => by
    unfold gaugeTwo
    split_ifs
    · simp
    · exact hypGauge_vertexTwo_conj (C.closedHypShape_curv hc h3 hχ) hw
  ψ₁_refl := fun w hw => by
    unfold gaugeOne
    split_ifs
    · simp
    · exact hypGauge_vertexOne_refl_one (C.closedHypShape_curv hc h3 hχ) hw
  wallTwo := fun w hw => by
    have hcl := closedStepHyp_closing C hc h3 hχ
    change _ = closedStepHyp C hc h3 hχ * closedEuler C hc h3
    rw [hcl]
    unfold gaugeOne gaugeTwo
    split_ifs
    · simp
    · exact hypGauge_wallTwo (C.closedHypShape_curv hc h3 hχ) hw

theorem hypDatum_m (D : (C.closedHypShape hc h3 hχ).FoldData) :
    (hypDatum C hc h3 hχ D).m = d.closedConnectionModel := rfl

end Datum

section Pieces

variable {σ : CompactShape} (hσ : σ.curv = .hyperbolic) {D : σ.FoldData}
include hσ

theorem im_pos_of_main_not_patchZero {z : ℂ} (hm : z ∈ mainSet D) (hz : z ∉ patchZero D) :
    0 < z.im := by
  have hk := kap_pos D hσ
  rcases hm with ((h | h) | h) | h
  · exact h.2 0
  · exact absurd h hz
  · have := h.2.1
    change kap D < z.im at this
    linarith
  · have := h.2.1
    change kap D < z.im at this
    linarith

theorem conj_mem_patchZero {z : ℂ} (hz : z ∈ patchZero D) : conj z ∈ patchZero D :=
  refl_mem_patchZero hσ hz

theorem mem_patchZero_of_main_conj {z : ℂ} (hm : z ∈ mainSet D) (hm' : conj z ∈ mainSet D) :
    z ∈ patchZero D := by
  by_contra hz
  have h1 := im_pos_of_main_not_patchZero hσ hm hz
  have h2 : conj z ∉ patchZero D := fun h => hz (by
    have := conj_mem_patchZero hσ h
    rwa [Complex.conj_conj] at this)
  have h3 := im_pos_of_main_not_patchZero hσ hm' h2
  rw [conj_im] at h3
  linarith

theorem not_mem_discOneMirror_of_main {z : ℂ} (hm : z ∈ mainSet D) : z ∉ discOneMirror D := by
  intro hd
  have him := im_neg_of_mem_discOneMirror hσ hd
  have hρ := rhoZero_pos (σ := σ)
  have hz : z ∈ patchZero D := by
    by_contra hz
    have := im_pos_of_main_not_patchZero hσ hm hz
    linarith
  have hre := re_f_of_mem_discOne hσ ((mem_discOneMirror_iff D).1 hd)
  have hfl : D.f (conj z) = conj (D.f z) := D.f_refl 0 z hz.1
  rw [hfl, conj_re] at hre
  linarith [hz.2.2.2.2.2.1]

theorem not_mem_discOne_of_conj_main {z : ℂ} (hm : conj z ∈ mainSet D) : z ∉ discOne D := by
  intro hd
  apply not_mem_discOneMirror_of_main hσ hm
  rw [mem_discOneMirror_iff, Complex.conj_conj]
  exact hd

theorem f_main_props {z : ℂ} (hm : z ∈ mainSet D) :
    ‖D.f z‖ < 7 / 2 ∧ D.f z ≠ 3 / 2 ∧ D.f z ≠ -(3 / 2) := by
  have hk := kap_pos D hσ
  have hne : ∀ w : ℂ, w.im ≠ 0 → w ≠ 3 / 2 ∧ w ≠ -(3 / 2) := by
    intro w hw
    constructor <;> rintro rfl <;> simp at hw
  have hre : ∀ w : ℂ, (w.re < -(3 / 2) ∨ 3 / 2 < w.re ∨ (-(3 / 2) < w.re ∧ w.re < 3 / 2)) →
      w ≠ 3 / 2 ∧ w ≠ -(3 / 2) := by
    intro w hw
    constructor <;> rintro rfl <;> norm_num at hw
  have hnT : ∀ {w : ℂ}, w ∈ σ.triangle → w ≠ 0 → ‖D.f w‖ < 7 / 2 :=
    fun hw h0 => (D.bijOn_f.mapsTo ⟨hw, h0⟩).1
  have hrefl : ∀ i : Fin 3, z ∈ D.V i → σ.refl i z ∈ intT σ → ‖D.f z‖ < 7 / 2 := by
    intro i hV hT
    have := hnT (intT_subset_triangle hT) (ne_zero_of_mem_intT hT)
    rwa [D.f_refl i z hV, Complex.norm_conj] at this
  have hnorm : ∀ i : Fin 3, z ≠ 0 → z ∈ D.V i →
      (z ∉ σ.triangle → σ.refl i z ∈ intT σ) → ‖D.f z‖ < 7 / 2 := by
    intro i h0 hV hr
    by_cases hT : z ∈ σ.triangle
    · exact hnT hT h0
    · exact hrefl i hV (hr hT)
  rcases hm with ((h | h) | h) | h
  · exact ⟨hnT (intT_subset_triangle h) (ne_zero_of_mem_intT h),
      hne _ (D.im_f_pos h.1 h.2).ne'⟩
  · have h0 : z ≠ 0 := by
      rintro rfl
      have := h.2.1
      rw [HypFold.wallSide_one_zero] at this
      linarith
    exact ⟨hnorm 0 h0 h.1 (refl_mem_intT_of_patchZero hσ h),
      hre _ (Or.inl h.2.2.2.2.2.1)⟩
  · have h0 : z ≠ 0 := by
      rintro rfl
      have := h.2.1
      rw [σ.wallSide_zero_eq, zero_im] at this
      linarith
    exact ⟨hnorm 1 h0 h.1 (refl_mem_intT_of_patchOne hσ h),
      hre _ (Or.inr (Or.inl h.2.2.2.2.2.1))⟩
  · have h0 : z ≠ 0 := by
      rintro rfl
      have := h.2.1
      rw [σ.wallSide_zero_eq, zero_im] at this
      linarith
    exact ⟨hnorm 2 h0 h.1 (refl_mem_intT_of_patchTwo hσ h),
      hre _ (Or.inr (Or.inr ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩))⟩

theorem refl_one_mem_discOne {z : ℂ} (hd : z ∈ discOne D) : σ.refl 1 z ∈ discOne D :=
  ⟨HypFold.norm_refl_lt_one hσ 1 hd.1, by
    rw [HypFold.rotOne_refl_one hσ, Complex.norm_conj]; exact hd.2⟩

end Pieces

theorem liftP_mem_closedDomain (K : HypDatum) {x : ModelCoordinates}
    (hm : hb x ∈ mainSet K.D) : K.liftP x ∈ closedDomain :=
  f_main_props K.hσ hm

theorem liftM_mem_closedDomain (K : HypDatum) {x : ModelCoordinates}
    (hm : conj (hb x) ∈ mainSet K.D) : K.liftM x ∈ closedDomain := by
  obtain ⟨h1, h2, h3⟩ := f_main_props K.hσ hm
  change ‖conj (K.D.f (hb (reflectMap K.c₀ x)))‖ < 7 / 2 ∧
    conj (K.D.f (hb (reflectMap K.c₀ x))) ≠ 3 / 2 ∧
      conj (K.D.f (hb (reflectMap K.c₀ x))) ≠ -(3 / 2)
  rw [HypDatum.hb_reflectMap, Complex.norm_conj]
  refine ⟨h1, fun h => h2 ?_, fun h => h3 ?_⟩
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this

section Map

theorem continuous_hb : Continuous hb :=
  contDiff_hypDisc.continuous.comp contDiff_planeOf.continuous

def hypBase (K : HypDatum) : Set ℂ :=
  mainSet K.D ∪ {z | conj z ∈ mainSet K.D} ∪ discOne K.D ∪ discOneMirror K.D ∪ discTwo K.D ∪
    discThree K.D

theorem isOpen_hypBase (K : HypDatum) : IsOpen (hypBase K) := by
  unfold hypBase
  refine ((((((isOpen_mainSet K.hσ).union ?_).union (isOpen_discOne K.hσ)).union
    (isOpen_discOneMirror K.hσ)).union (isOpen_discTwo K.hσ)).union isOpen_discThree)
  exact (isOpen_mainSet K.hσ).preimage Complex.continuous_conj

def hypDomain (K : HypDatum) : TopologicalSpace.Opens ModelCoordinates :=
  ⟨hb ⁻¹' hypBase K, (isOpen_hypBase K).preimage continuous_hb⟩

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

open Classical in
def hypMap (K : HypDatum) (x : ModelCoordinates) : W.pieceInterior ⊤ :=
  if hb x ∈ discOne K.D then C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne x)
  else if hb x ∈ discOneMirror K.D then
    C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne (K.rotThreeInv x))
  else if hb x ∈ discTwo K.D then C.tubeMap (C.closedHoleEquiv hc h3 2) (K.tubeTwo x)
  else if hb x ∈ discThree K.D then C.tubeMap (C.closedHoleEquiv hc h3 0) (K.tubeThree x)
  else if hb x ∈ mainSet K.D then C.closedChart hc h3 (K.liftP x)
  else C.closedChart hc h3 (K.liftM x)

theorem hypMap_of_discOne (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    hypMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne x) := by
  unfold hypMap
  rw [ite_eq_left hd]

theorem hypMap_of_discOneMirror (K : HypDatum) {x : ModelCoordinates}
    (hd : hb x ∈ discOneMirror K.D) :
    hypMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne (K.rotThreeInv x)) := by
  unfold hypMap
  rw [ite_eq_right (fun h => disjoint_left.mp (disjoint_discOne_discOneMirror K.hσ) h hd),
    ite_eq_left hd]

theorem hypMap_of_discTwo (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    hypMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 2) (K.tubeTwo x) := by
  unfold hypMap
  rw [ite_eq_right (fun h => disjoint_left.mp (disjoint_discOne_discTwo K.hσ) h hd),
    ite_eq_right (fun h => disjoint_left.mp (disjoint_discTwo_discOneMirror K.hσ) hd h),
    ite_eq_left hd]

theorem hypMap_of_discThree (K : HypDatum) {x : ModelCoordinates}
    (hd : hb x ∈ discThree K.D) :
    hypMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 0) (K.tubeThree x) := by
  unfold hypMap
  rw [ite_eq_right (fun h => disjoint_left.mp (disjoint_discOne_discThree K.hσ) h hd),
    ite_eq_right (fun h => disjoint_left.mp (disjoint_discThree_discOneMirror K.hσ) hd h),
    ite_eq_right (fun h => disjoint_left.mp (disjoint_discTwo_discThree K.hσ) h hd),
    ite_eq_left hd]

theorem hypMap_of_main_off (K : HypDatum) {x : ModelCoordinates} (hm : hb x ∈ mainSet K.D)
    (h1 : hb x ∉ discOne K.D) (h2 : hb x ∉ discTwo K.D) (h3' : hb x ∉ discThree K.D) :
    hypMap C hc h3 K x = C.closedChart hc h3 (K.liftP x) := by
  unfold hypMap
  rw [ite_eq_right h1, ite_eq_right (not_mem_discOneMirror_of_main K.hσ hm), ite_eq_right h2,
    ite_eq_right h3', ite_eq_left hm]

theorem hypMap_of_conjMain_off (K : HypDatum) {x : ModelCoordinates}
    (hm : conj (hb x) ∈ mainSet K.D) (hm' : hb x ∉ mainSet K.D)
    (h1 : hb x ∉ discOneMirror K.D) (h2 : hb x ∉ discTwo K.D) (h3' : hb x ∉ discThree K.D) :
    hypMap C hc h3 K x = C.closedChart hc h3 (K.liftM x) := by
  unfold hypMap
  rw [ite_eq_right (not_mem_discOne_of_conj_main K.hσ hm), ite_eq_right h1, ite_eq_right h2,
    ite_eq_right h3', ite_eq_right hm']

theorem norm_tubeOne_fst (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    ‖(K.tubeOne x).1‖ < 1 := by
  change ‖K.σ.rotOne (hb x) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact lt_of_lt_of_le hd.2 (by linarith [radOne_le_half K.D])

theorem norm_tubeTwo_fst (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    ‖(K.tubeTwo x).1‖ < 1 := by
  change ‖K.σ.rotTwo (hb x) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact lt_of_lt_of_le hd.2 (by linarith [radTwo_le_half K.D])

theorem norm_tubeThree_fst (K : HypDatum) {x : ModelCoordinates}
    (hd : hb x ∈ discThree K.D) : ‖(K.tubeThree x).1‖ < 1 := by
  change ‖(Circle.exp (Real.pi / K.σ.p₃) : ℂ) * hb x * _‖ < 1
  rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, mul_one]
  exact lt_of_lt_of_le hd (by linarith [radThree_le_half K.D])

theorem norm_tubeOne_rotThreeInv_fst (K : HypDatum) {x : ModelCoordinates}
    (hd : conj (hb x) ∈ discOne K.D) : ‖(K.tubeOne (K.rotThreeInv x)).1‖ < 1 := by
  change ‖K.σ.rotOne (hb (K.rotThreeInv x)) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one, K.hb_rotThreeInv, HypFold.rotOne_refl_one K.hσ,
    Complex.norm_conj]
  exact lt_of_lt_of_le hd.2 (by linarith [radOne_le_half K.D])

theorem tubeOne_fst_ne_zero (K : HypDatum) {x : ModelCoordinates}
    (h : K.σ.rotOne (hb x) ≠ 0) : (K.tubeOne x).1 ≠ 0 :=
  mul_ne_zero h (Circle.coe_ne_zero _)

theorem tubeTwo_fst_ne_zero (K : HypDatum) {x : ModelCoordinates}
    (h : K.σ.rotTwo (hb x) ≠ 0) : (K.tubeTwo x).1 ≠ 0 :=
  mul_ne_zero h (Circle.coe_ne_zero _)

theorem rotTwo_ne_zero_of_conj {σ : CompactShape} (hσ : σ.curv = .hyperbolic) {z : ℂ}
    (h : σ.rotTwo (conj z) ≠ 0) : σ.rotTwo z ≠ 0 := by
  intro h0
  apply h
  change σ.rotTwo (σ.refl 0 z) = 0
  rw [HypFold.rotTwo_refl_zero hσ, h0, map_zero, mul_zero]

variable (hχ : d.orbChi < 0) (D : (C.closedHypShape hc h3 hχ).FoldData)

set_option hygiene false in
local notation "𝒦" => hypDatum C hc h3 hχ D

theorem tubeOne_eq_liftP {x : ModelCoordinates} (hd : hb x ∈ discOne (𝒦).D)
    (hs : (𝒦).σ.rotOne (hb x) ≠ 0 ∧ -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (hb x)) ∧
      arg ((𝒦).σ.rotOne (hb x)) < 3 * (𝒦).σ.θ₁ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 1) ((𝒦).tubeOne x) = C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_seamFwd_tubeOne hd hs]
  exact (C.closedChart_seamFwd_one hc h3 (tubeOne_fst_ne_zero _ hs.1)
    (norm_tubeOne_fst _ hd)).symm

theorem tubeTwo_eq_liftP {x : ModelCoordinates} (hd : hb x ∈ discTwo (𝒦).D)
    (hs : (𝒦).σ.rotTwo (hb x) ≠ 0 ∧ -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (hb x)) ∧
      arg ((𝒦).σ.rotTwo (hb x)) < 3 * (𝒦).σ.θ₂ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 2) ((𝒦).tubeTwo x) = C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_seamFwd_tubeTwo hd hs]
  exact (C.closedChart_seamFwd_two hc h3 (tubeTwo_fst_ne_zero _ hs.1)
    (norm_tubeTwo_fst _ hd)).symm

theorem tubeThree_eq_liftP {x : ModelCoordinates} (hd : hb x ∈ discThree (𝒦).D)
    (hs : hb x ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg (hb x) ∧ arg (hb x) < 3 * (𝒦).σ.θ₃ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 0) ((𝒦).tubeThree x) =
      C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_outerFwd_tubeThree hd hs]
  exact (C.closedChart_outerFwd hc h3 (norm_tubeThree_fst _ hd)).symm

theorem tubeOne_eq_liftM {x : ModelCoordinates} (hd : conj (hb x) ∈ discOne (𝒦).D)
    (hs : (𝒦).σ.rotOne (conj (hb x)) ≠ 0 ∧
      -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (conj (hb x))) ∧
      arg ((𝒦).σ.rotOne (conj (hb x))) < 3 * (𝒦).σ.θ₁ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 1) ((𝒦).tubeOne ((𝒦).rotThreeInv x)) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : hb (reflectMap (𝒦).c₀ x) ∈ discOne (𝒦).D := by
    rw [HypDatum.hb_reflectMap]; exact hd
  have hs' : (𝒦).σ.rotOne (hb (reflectMap (𝒦).c₀ x)) ≠ 0 ∧
      -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (hb (reflectMap (𝒦).c₀ x))) ∧
      arg ((𝒦).σ.rotOne (hb (reflectMap (𝒦).c₀ x))) < 3 * (𝒦).σ.θ₁ / 2 := by
    rw [HypDatum.hb_reflectMap]; exact hs
  have hne : ((𝒦).tubeOne ((𝒦).rotThreeInv x)).1 ≠ 0 := by
    apply tubeOne_fst_ne_zero
    rw [HypDatum.hb_rotThreeInv, HypFold.rotOne_refl_one (𝒦).hσ, map_ne_zero]
    exact hs.1
  unfold HypDatum.liftM
  rw [(𝒦).liftP_eq_seamFwd_tubeOne hd' hs', ← seamFwd_conjPair,
    (𝒦).conjPair_tubeOne_reflect hd]
  exact (C.closedChart_seamFwd_one hc h3 hne (norm_tubeOne_rotThreeInv_fst _ hd)).symm

theorem tubeTwo_eq_liftM {x : ModelCoordinates} (hd : hb x ∈ discTwo (𝒦).D)
    (hs : (𝒦).σ.rotTwo (conj (hb x)) ≠ 0 ∧
      -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (conj (hb x))) ∧
      arg ((𝒦).σ.rotTwo (conj (hb x))) < 3 * (𝒦).σ.θ₂ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 2) ((𝒦).tubeTwo x) = C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : hb (reflectMap (𝒦).c₀ x) ∈ discTwo (𝒦).D := by
    rw [HypDatum.hb_reflectMap]; exact conj_mem_discTwo (𝒦).hσ hd
  have hs' : (𝒦).σ.rotTwo (hb (reflectMap (𝒦).c₀ x)) ≠ 0 ∧
      -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (hb (reflectMap (𝒦).c₀ x))) ∧
      arg ((𝒦).σ.rotTwo (hb (reflectMap (𝒦).c₀ x))) < 3 * (𝒦).σ.θ₂ / 2 := by
    rw [HypDatum.hb_reflectMap]; exact hs
  have hne : ((𝒦).tubeTwo x).1 ≠ 0 :=
    tubeTwo_fst_ne_zero _ (rotTwo_ne_zero_of_conj (𝒦).hσ hs.1)
  unfold HypDatum.liftM
  rw [(𝒦).liftP_eq_seamFwd_tubeTwo hd' hs', ← seamFwd_conjPair,
    (𝒦).conjPair_tubeTwo_reflect hd]
  exact (C.closedChart_seamFwd_two hc h3 hne (norm_tubeTwo_fst _ hd)).symm

theorem tubeThree_eq_liftM {x : ModelCoordinates} (hd : hb x ∈ discThree (𝒦).D)
    (hs : conj (hb x) ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg (conj (hb x)) ∧
      arg (conj (hb x)) < 3 * (𝒦).σ.θ₃ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 0) ((𝒦).tubeThree x) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : hb (reflectMap (𝒦).c₀ x) ∈ discThree (𝒦).D := by
    rw [HypDatum.hb_reflectMap]; exact conj_mem_discThree hd
  have hs' : hb (reflectMap (𝒦).c₀ x) ≠ 0 ∧
      -((𝒦).σ.θ₃ / 2) < arg (hb (reflectMap (𝒦).c₀ x)) ∧
      arg (hb (reflectMap (𝒦).c₀ x)) < 3 * (𝒦).σ.θ₃ / 2 := by
    rw [HypDatum.hb_reflectMap]; exact hs
  unfold HypDatum.liftM
  rw [(𝒦).liftP_eq_outerFwd_tubeThree hd' hs', ← outerFwd_conjPair,
    (𝒦).conjPair_tubeThree_reflect x]
  exact (C.closedChart_outerFwd hc h3 (norm_tubeThree_fst _ hd)).symm

theorem hypMap_of_main {x : ModelCoordinates} (hm : hb x ∈ mainSet (𝒦).D) :
    hypMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftP x) := by
  by_cases h1 : hb x ∈ discOne (𝒦).D
  · rw [hypMap_of_discOne C hc h3 _ h1]
    exact tubeOne_eq_liftP C hc h3 hχ D h1 (sector_one (𝒦).hσ hm h1)
  by_cases h2 : hb x ∈ discTwo (𝒦).D
  · rw [hypMap_of_discTwo C hc h3 _ h2]
    exact tubeTwo_eq_liftP C hc h3 hχ D h2 (sector_two (𝒦).hσ hm h2)
  by_cases h3' : hb x ∈ discThree (𝒦).D
  · rw [hypMap_of_discThree C hc h3 _ h3']
    exact tubeThree_eq_liftP C hc h3 hχ D h3' (sector_three (𝒦).hσ hm h3')
  exact hypMap_of_main_off C hc h3 _ hm h1 h2 h3'

theorem hypMap_of_conjMain {x : ModelCoordinates} (hm : conj (hb x) ∈ mainSet (𝒦).D) :
    hypMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftM x) := by
  by_cases h1 : hb x ∈ discOneMirror (𝒦).D
  · rw [hypMap_of_discOneMirror C hc h3 _ h1]
    have hd := (mem_discOneMirror_iff _).1 h1
    exact tubeOne_eq_liftM C hc h3 hχ D hd (sector_one (𝒦).hσ hm hd)
  by_cases h2 : hb x ∈ discTwo (𝒦).D
  · rw [hypMap_of_discTwo C hc h3 _ h2]
    exact tubeTwo_eq_liftM C hc h3 hχ D h2
      (sector_two (𝒦).hσ hm (conj_mem_discTwo (𝒦).hσ h2))
  by_cases h3' : hb x ∈ discThree (𝒦).D
  · rw [hypMap_of_discThree C hc h3 _ h3']
    exact tubeThree_eq_liftM C hc h3 hχ D h3' (sector_three (𝒦).hσ hm (conj_mem_discThree h3'))
  by_cases hm' : hb x ∈ mainSet (𝒦).D
  · rw [hypMap_of_main C hc h3 hχ D hm']
    have hz := mem_patchZero_of_main_conj (𝒦).hσ hm' hm
    rw [(𝒦).liftM_eq_liftP hz.1 hz.2.2.2.2.2.1]
  exact hypMap_of_conjMain_off C hc h3 _ hm hm' h1 h2 h3'

theorem isLocalDiffeomorphAt_hypMap {x : ModelCoordinates} (hx : x ∈ hypDomain (𝒦)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hypMap C hc h3 (𝒦)) x := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hpre : ∀ {S : Set ℂ}, IsOpen S → hb x ∈ S → hb ⁻¹' S ∈ 𝓝 x :=
    fun hS h => (hS.preimage continuous_hb).mem_nhds h
  have htube : ∀ (m : Fin d.fillingCount) {y : ℂ × Circle}, ‖y.1‖ < 1 →
      IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.tubeMap m) y :=
    fun m y hy => C.isLocalDiffeomorphAt_tubeMap (by linarith [C.ε_pos])
  change hb x ∈ hypBase (𝒦) at hx
  simp only [hypBase, mem_union, mem_ofPred_eq] at hx
  rcases hx with ((((hm | hm) | hd) | hd) | hd) | hd
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hpre (isOpen_mainSet (𝒦).hσ) hm)
          (fun y hy => hypMap_of_main C hc h3 hχ D hy))
        (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_liftP hm)
          (hg := C.isLocalDiffeomorphAt_closedChart hc h3 (liftP_mem_closedDomain _ hm)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem
          (hpre ((isOpen_mainSet (𝒦).hσ).preimage Complex.continuous_conj) hm)
          (fun y hy => hypMap_of_conjMain C hc h3 hχ D hy))
        (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_liftM hm)
          (hg := C.isLocalDiffeomorphAt_closedChart hc h3 (liftM_mem_closedDomain _ hm)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discOne (𝒦).hσ) hd)
        (fun y hy => hypMap_of_discOne C hc h3 _ hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeOne hd)
        (hg := htube _ (norm_tubeOne_fst _ hd)))
  · have hd' : conj (hb x) ∈ discOne (𝒦).D := (mem_discOneMirror_iff _).1 hd
    have hr : hb ((𝒦).screwThree.symm x) ∈ discOne (𝒦).D := by
      rw [HypDatum.screwThree_symm, HypDatum.hb_rotThreeInv]
      exact refl_one_mem_discOne (𝒦).hσ hd'
    have h1 := IsLocalDiffeomorphAt.comp (hf := (𝒦).screwThree.symm.isLocalDiffeomorph x)
      (hg := (𝒦).isLocalDiffeomorphAt_tubeOne hr)
    have h2 := IsLocalDiffeomorphAt.comp (hf := h1)
      (hg := htube (C.closedHoleEquiv hc h3 1) (by
        change ‖((𝒦).tubeOne ((𝒦).screwThree.symm x)).1‖ < 1
        rw [HypDatum.screwThree_symm]
        exact norm_tubeOne_rotThreeInv_fst _ hd'))
    refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discOneMirror (𝒦).hσ) hd)
        (fun y hy => ?_)) h2
    rw [hypMap_of_discOneMirror C hc h3 _ hy]
    change _ = C.tubeMap _ ((𝒦).tubeOne ((𝒦).screwThree.symm y))
    rw [HypDatum.screwThree_symm]
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discTwo (𝒦).hσ) hd)
        (fun y hy => hypMap_of_discTwo C hc h3 _ hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeTwo hd)
        (hg := htube _ (norm_tubeTwo_fst _ hd)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre isOpen_discThree hd)
        (fun y hy => hypMap_of_discThree C hc h3 _ hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeThree x)
        (hg := htube _ (norm_tubeThree_fst _ hd)))

end Map

end Hyp

end ClosedTriangle

end GC.Seifert
