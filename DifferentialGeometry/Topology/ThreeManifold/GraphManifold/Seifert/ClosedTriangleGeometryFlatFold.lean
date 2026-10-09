import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatLifts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryChart

/-!
# The fold of a flat closed triangle block

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§2.3, with review 27). Let `C` be charts of a closed triangle block (no port, three cones) with
`orbChi = 0`, and `D` a fold datum on the flat triangle `C.closedEuclidShape` (cone `j` at hole
`j`, the outer cone third). The model is `closedConnectionModel` (`E³` if `e = 0`, `Nil`
otherwise) and the signed fibre step is `ℓ = 1` if `e = 0`, `ℓ = -c (v₁ × v₂)/e` otherwise, so the
closing equation holds (`flatDatum`). The seam models of the three holes, read with the numbers of
the datum, compose with the closed punctured chart `P` to the tube charts
(`closedChart_seamFwd_one`, `closedChart_seamFwd_two`, `closedChart_outerFwd`).

The fold `flatMap` is the tube chart of hole `1` composed with `tubeOne` on the disc about `v₁`,
with `tubeOne ∘ S₃⁻¹` on its mirror, the tube charts of holes `2`, `0` composed with `tubeTwo`,
`tubeThree` on the discs about `v₂`, `0`, and `P ∘ liftP`, `P ∘ liftM` on the main set and its
mirror. In the good sectors the tube formulas equal the punctured formulas (`tubeOne_eq_liftP`,
...), so the fold equals `P ∘ liftP` on the main set and `P ∘ liftM` on its mirror
(`flatMap_of_main`, `flatMap_of_conjMain`); it is a local diffeomorphism on the open domain
`flatDomain` (`isLocalDiffeomorphAt_flatMap`). The main set, its mirror and the four vertex discs
are the open pieces of `flatBase`; the base lifts land in the domain of `P`
(`liftP_mem_closedDomain`, `liftM_mem_closedDomain`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace SeifertBlockCharts

section Data

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

theorem fillingOrder_closedHoleEquiv (j : Fin 3) :
    d.fillingOrder (C.closedHoleEquiv hc h3 j) = C.holeOrder hc h3 j := by
  have h1 := C.holeOrder_cast hc h3 j
  have h2 := SeifertBlockCharts.fillingSlope_eq_fillingOrder
    (C.fillingSlope_closedHoleEquiv_pos hc h3 j)
  rw [h2] at h1
  exact_mod_cast h1.symm

theorem seamDir_closedHoleEquiv_one :
    C.seamDir (C.closedHoleEquiv hc h3 1) = seamFwd ((3 / 2 : ℝ) : ℂ) (C.holeOrder hc h3 1)
      (C.holeOrder hc h3 1) (C.holeTwist hc h3 1) (C.holeA hc h3 1) (C.holeB hc h3 1) := by
  unfold SeifertBlockCharts.seamDir
  rw [C.tubeCentre_closedHoleEquiv_one hc h3, C.fillingOrder_closedHoleEquiv hc h3,
    C.holeOrder_cast hc h3]
  push_cast
  rfl

theorem seamDir_closedHoleEquiv_two :
    C.seamDir (C.closedHoleEquiv hc h3 2) = seamFwd ((-(3 / 2) : ℝ) : ℂ) (C.holeOrder hc h3 2)
      (C.holeOrder hc h3 2) (C.holeTwist hc h3 2) (C.holeA hc h3 2) (C.holeB hc h3 2) := by
  unfold SeifertBlockCharts.seamDir
  rw [C.tubeCentre_closedHoleEquiv_two hc h3, C.fillingOrder_closedHoleEquiv hc h3,
    C.holeOrder_cast hc h3]
  push_cast
  rfl

theorem outerSeamDir_closedHoleEquiv_zero :
    C.outerSeamDir (C.closedHoleEquiv hc h3 0) = outerFwd (C.holeOrder hc h3 0)
      (C.holeOrder hc h3 0) (C.holeTwist hc h3 0) (C.holeA hc h3 0) (C.holeB hc h3 0) := by
  unfold SeifertBlockCharts.outerSeamDir
  rw [C.fillingOrder_closedHoleEquiv hc h3, C.holeOrder_cast hc h3]
  rfl

theorem closedChart_seamFwd_one {y : ℂ × Circle} (hy0 : y.1 ≠ 0) (hy : ‖y.1‖ < 1) :
    C.closedChart hc h3 (seamFwd ((3 / 2 : ℝ) : ℂ) (C.holeOrder hc h3 1) (C.holeOrder hc h3 1)
      (C.holeTwist hc h3 1) (C.holeA hc h3 1) (C.holeB hc h3 1) y) =
        C.tubeMap (C.closedHoleEquiv hc h3 1) y := by
  have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 1
  rw [← C.seamDir_closedHoleEquiv_one hc h3]
  have hdist : ‖(C.seamDir (C.closedHoleEquiv hc h3 1) y).1 - 3 / 2‖ <
      C.collarRadius (C.closedHoleEquiv hc h3 1) := by
    have h : ‖(C.seamDir (C.closedHoleEquiv hc h3 1) y).1 -
        C.tubeCentre (C.closedHoleEquiv hc h3 1)‖ =
          ‖y.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 1) / 2 := norm_seamFwd_sub y
    rw [C.tubeCentre_closedHoleEquiv_one hc h3] at h
    rw [h]
    have : ‖y.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 1) < 1 :=
      pow_lt_one₀ (norm_nonneg _) hy (SeifertBlockCharts.fillingOrder_pos hp).ne'
    linarith [C.half_lt_collarRadius hp]
  rw [C.closedChart_of_innerCollar_one hc h3 hdist, C.seamInv_seamDir hp hy0]

theorem closedChart_seamFwd_two {y : ℂ × Circle} (hy0 : y.1 ≠ 0) (hy : ‖y.1‖ < 1) :
    C.closedChart hc h3 (seamFwd ((-(3 / 2) : ℝ) : ℂ) (C.holeOrder hc h3 2)
      (C.holeOrder hc h3 2) (C.holeTwist hc h3 2) (C.holeA hc h3 2) (C.holeB hc h3 2) y) =
        C.tubeMap (C.closedHoleEquiv hc h3 2) y := by
  have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 2
  rw [← C.seamDir_closedHoleEquiv_two hc h3]
  have hdist : ‖(C.seamDir (C.closedHoleEquiv hc h3 2) y).1 + 3 / 2‖ <
      C.collarRadius (C.closedHoleEquiv hc h3 2) := by
    have h : ‖(C.seamDir (C.closedHoleEquiv hc h3 2) y).1 -
        C.tubeCentre (C.closedHoleEquiv hc h3 2)‖ =
          ‖y.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 2) / 2 := norm_seamFwd_sub y
    rw [C.tubeCentre_closedHoleEquiv_two hc h3, sub_neg_eq_add] at h
    rw [h]
    have : ‖y.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 2) < 1 :=
      pow_lt_one₀ (norm_nonneg _) hy (SeifertBlockCharts.fillingOrder_pos hp).ne'
    linarith [C.half_lt_collarRadius hp]
  rw [C.closedChart_of_innerCollar_two hc h3 hdist, C.seamInv_seamDir hp hy0]

theorem closedChart_outerFwd {y : ℂ × Circle} (hy : ‖y.1‖ < 1) :
    C.closedChart hc h3 (outerFwd (C.holeOrder hc h3 0) (C.holeOrder hc h3 0)
      (C.holeTwist hc h3 0) (C.holeA hc h3 0) (C.holeB hc h3 0) y) =
        C.tubeMap (C.closedHoleEquiv hc h3 0) y := by
  have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 0
  have hP := SeifertBlockCharts.fillingOrder_pos hp
  rw [← C.outerSeamDir_closedHoleEquiv_zero hc h3]
  have hpow : ‖y.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 0) < 1 :=
    pow_lt_one₀ (norm_nonneg _) hy hP.ne'
  have hpowε : ‖y.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 0) <
      (1 + C.ε) ^ d.fillingOrder (C.closedHoleEquiv hc h3 0) :=
    pow_lt_pow_left₀ (by linarith [C.ε_pos]) (norm_nonneg _) hP.ne'
  have hn := norm_outerFwd_fst (P := d.fillingOrder (C.closedHoleEquiv hc h3 0))
    (p := (d.fillingSlope (C.closedHoleEquiv hc h3 0)).1)
    (q := (d.fillingSlope (C.closedHoleEquiv hc h3 0)).2)
    (a := C.a (C.closedHoleEquiv hc h3 0)) (b := C.b (C.closedHoleEquiv hc h3 0))
    (y := y) (by linarith)
  have hR : C.outerCollarRadius (C.closedHoleEquiv hc h3 0) <
      ‖(C.outerSeamDir (C.closedHoleEquiv hc h3 0) y).1‖ := by
    change _ < ‖(outerFwd _ _ _ _ _ y).1‖
    rw [hn]
    unfold SeifertBlockCharts.outerCollarRadius
    apply max_lt <;> linarith
  rw [C.closedChart_of_outerCollar hc h3 hR, C.outerSeamInv_outerSeamDir hp (by linarith)]

end Data

end SeifertBlockCharts

namespace ClosedTriangle

open TwoConeFold

theorem planeCrossC_vertexOne_vertexTwo (σ : EuclidShape) :
    planeCrossC σ.vertexOne σ.vertexTwo = -sProd σ := by
  simp only [planeCrossC, vertexOne_re, vertexOne_im, EuclidShape.vertexTwo, ofReal_re, ofReal_im,
    sProd]
  ring

section Datum

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (h0 : d.orbChi = 0)

def closedEuler : ℝ :=
  -((C.holeTwist hc h3 1 : ℝ) / (C.holeOrder hc h3 1 : ℕ) +
    (C.holeTwist hc h3 2 : ℝ) / (C.holeOrder hc h3 2 : ℕ) +
      (C.holeTwist hc h3 0 : ℝ) / (C.holeOrder hc h3 0 : ℕ))

theorem closedEuler_eq : closedEuler C hc h3 = (d.euler : ℝ) := by
  rw [C.euler_eq_holes hc h3, Fin.sum_univ_three]
  unfold closedEuler
  push_cast
  ring

theorem closedEuler_eq_zero_iff : closedEuler C hc h3 = 0 ↔ d.euler = 0 := by
  rw [closedEuler_eq]
  exact Rat.cast_eq_zero

def closedStep : ℝ :=
  if d.euler = 0 then 1 else
    -(d.closedConnectionModel.connectionCurvature *
      planeCrossC (C.closedEuclidShape hc h3 h0).vertexOne
        (C.closedEuclidShape hc h3 h0).vertexTwo) / closedEuler C hc h3

include h0 in
theorem connectionCurvature_of_flat :
    d.closedConnectionModel.connectionCurvature = if d.euler = 0 then 0 else -1 := by
  rw [d.closedConnectionModel_of_flat h0]
  split_ifs <;> rfl

theorem closedStep_ne_zero : closedStep C hc h3 h0 ≠ 0 := by
  unfold closedStep
  split_ifs with he
  · exact one_ne_zero
  · rw [connectionCurvature_of_flat h0, planeCrossC_vertexOne_vertexTwo]
    simp only [he, ↓reduceIte]
    have hs := sProd_pos (σ := C.closedEuclidShape hc h3 h0)
    have hE : closedEuler C hc h3 ≠ 0 := fun h => he ((closedEuler_eq_zero_iff C hc h3).1 h)
    exact div_ne_zero (by nlinarith) hE

theorem closedStep_closing :
    -d.closedConnectionModel.connectionCurvature *
        planeCrossC (C.closedEuclidShape hc h3 h0).vertexOne
          (C.closedEuclidShape hc h3 h0).vertexTwo =
      closedStep C hc h3 h0 * closedEuler C hc h3 := by
  unfold closedStep
  split_ifs with he
  · rw [connectionCurvature_of_flat h0, (closedEuler_eq_zero_iff C hc h3).2 he]
    simp only [he, ↓reduceIte]
    ring
  · have hE : closedEuler C hc h3 ≠ 0 := fun h => he ((closedEuler_eq_zero_iff C hc h3).1 h)
    field_simp

def flatDatum (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData) : FlatDatum where
  σ := C.closedEuclidShape hc h3 h0
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
  base_flat := d.closedConnectionModel_baseCurvature_eq_zero_iff.2 h0
  ℓ := closedStep C hc h3 h0
  ℓ_ne := closedStep_ne_zero C hc h3 h0
  closing := closedStep_closing C hc h3 h0

end Datum

section Model

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem f_main_props {z : ℂ} (hm : z ∈ mainSet D) :
    ‖D.f z‖ < 7 / 2 ∧ D.f z ≠ 3 / 2 ∧ D.f z ≠ -(3 / 2) := by
  have hk := kap_pos D
  have hne : ∀ w : ℂ, w.im ≠ 0 → w ≠ 3 / 2 ∧ w ≠ -(3 / 2) := by
    intro w hw
    constructor <;> rintro rfl <;> simp at hw
  have hre : ∀ w : ℂ, (w.re < -(3 / 2) ∨ 3 / 2 < w.re ∨ (-(3 / 2) < w.re ∧ w.re < 3 / 2)) →
      w ≠ 3 / 2 ∧ w ≠ -(3 / 2) := by
    intro w hw
    constructor <;> rintro rfl <;> norm_num at hw
  have hrefl : ∀ i : Fin 3, z ∈ D.V i → σ.refl i z ∈ intT σ → ‖D.f z‖ < 7 / 2 := by
    intro i hV hT
    have := norm_f_lt D (intT_subset_triangle hT) (ne_zero_of_mem_intT hT)
    rwa [f_refl' D i hV, Complex.norm_conj] at this
  have hnorm : ∀ i : Fin 3, z ≠ 0 → z ∈ D.V i →
      (z ∉ σ.triangle → σ.refl i z ∈ intT σ) → ‖D.f z‖ < 7 / 2 := by
    intro i h0 hV hr
    by_cases hT : z ∈ σ.triangle
    · exact norm_f_lt D hT h0
    · exact hrefl i hV (hr hT)
  rcases hm with ((h | h) | h) | h
  · exact ⟨norm_f_lt D (intT_subset_triangle h) (ne_zero_of_mem_intT h),
      hne _ (im_f_pos_of_intT D h).ne'⟩
  · have h0 : z ≠ 0 := by
      rintro rfl
      have := h.2.1
      rw [σ.wallSide_one_zero] at this
      linarith
    exact ⟨hnorm 0 h0 h.1 (refl_mem_intT_of_patchZero D h),
      hre _ (Or.inl h.2.2.2.2.2.1)⟩
  · have h0 : z ≠ 0 := by
      rintro rfl
      have := h.2.1
      rw [σ.wallSide_zero_zero] at this
      linarith
    exact ⟨hnorm 1 h0 h.1 (refl_mem_intT_of_patchOne D h),
      hre _ (Or.inr (Or.inl h.2.2.2.2.2.1))⟩
  · have h0 : z ≠ 0 := by
      rintro rfl
      have := h.2.1
      rw [σ.wallSide_zero_zero] at this
      linarith
    exact ⟨hnorm 2 h0 h.1 (refl_mem_intT_of_patchTwo D h),
      hre _ (Or.inr (Or.inr ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩))⟩

theorem liftP_mem_closedDomain (K : FlatDatum) {x : ModelCoordinates}
    (hm : planeOf x ∈ mainSet K.D) : K.liftP x ∈ closedDomain :=
  f_main_props K.D hm

theorem liftM_mem_closedDomain (K : FlatDatum) {x : ModelCoordinates}
    (hm : conj (planeOf x) ∈ mainSet K.D) : K.liftM x ∈ closedDomain := by
  obtain ⟨h1, h2, h3⟩ := f_main_props K.D hm
  change ‖conj (K.D.f (planeOf (reflectMap K.c₀ x)))‖ < 7 / 2 ∧
    conj (K.D.f (planeOf (reflectMap K.c₀ x))) ≠ 3 / 2 ∧
      conj (K.D.f (planeOf (reflectMap K.c₀ x))) ≠ -(3 / 2)
  rw [planeOf_reflectMap, Complex.norm_conj]
  refine ⟨h1, fun h => h2 ?_, fun h => h3 ?_⟩
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this

theorem refl_one_mem_discOne {z : ℂ} (hd : z ∈ discOne D) : σ.refl 1 z ∈ discOne D := by
  change ‖σ.refl 1 z - σ.vertexOne‖ < radOne D
  rw [σ.norm_refl_sub 1 z σ.vertexOne σ.wallSide_one_vertexOne]
  exact hd

end Model

section Map

def flatBase (K : FlatDatum) : Set ℂ :=
  mainSet K.D ∪ {z | conj z ∈ mainSet K.D} ∪ discOne K.D ∪ discOneMirror K.D ∪ discTwo K.D ∪
    discThree K.D

theorem isOpen_flatBase (K : FlatDatum) : IsOpen (flatBase K) := by
  unfold flatBase
  refine ((((((isOpen_mainSet K.D).union ?_).union (isOpen_discOne K.D)).union
    (isOpen_discOneMirror K.D)).union (isOpen_discTwo K.D)).union (isOpen_discThree K.D))
  exact (isOpen_mainSet K.D).preimage Complex.continuous_conj

def flatDomain (K : FlatDatum) : TopologicalSpace.Opens ModelCoordinates :=
  ⟨planeOf ⁻¹' flatBase K, (isOpen_flatBase K).preimage contDiff_planeOf.continuous⟩

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

open Classical in
def flatMap (K : FlatDatum) (x : ModelCoordinates) : W.pieceInterior ⊤ :=
  if planeOf x ∈ discOne K.D then C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne x)
  else if planeOf x ∈ discOneMirror K.D then
    C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne (K.rotThreeInv x))
  else if planeOf x ∈ discTwo K.D then C.tubeMap (C.closedHoleEquiv hc h3 2) (K.tubeTwo x)
  else if planeOf x ∈ discThree K.D then C.tubeMap (C.closedHoleEquiv hc h3 0) (K.tubeThree x)
  else if planeOf x ∈ mainSet K.D then C.closedChart hc h3 (K.liftP x)
  else C.closedChart hc h3 (K.liftM x)

theorem flatMap_of_discOne (K : FlatDatum) {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    flatMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne x) := by
  unfold flatMap
  rw [ite_eq_left hd]

theorem flatMap_of_discOneMirror (K : FlatDatum) {x : ModelCoordinates}
    (hd : planeOf x ∈ discOneMirror K.D) :
    flatMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne (K.rotThreeInv x)) := by
  unfold flatMap
  rw [ite_eq_right (fun h => disjoint_left.mp (disjoint_discOne_discOneMirror K.D) h hd),
    ite_eq_left hd]

theorem flatMap_of_discTwo (K : FlatDatum) {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    flatMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 2) (K.tubeTwo x) := by
  unfold flatMap
  rw [ite_eq_right (fun h => disjoint_left.mp (disjoint_discOne_discTwo K.D) h hd),
    ite_eq_right (fun h => disjoint_left.mp (disjoint_discTwo_discOneMirror K.D) hd h),
    ite_eq_left hd]

theorem flatMap_of_discThree (K : FlatDatum) {x : ModelCoordinates}
    (hd : planeOf x ∈ discThree K.D) :
    flatMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 0) (K.tubeThree x) := by
  unfold flatMap
  rw [ite_eq_right (fun h => disjoint_left.mp (disjoint_discOne_discThree K.D) h hd),
    ite_eq_right (fun h => disjoint_left.mp (disjoint_discThree_discOneMirror K.D) hd h),
    ite_eq_right (fun h => disjoint_left.mp (disjoint_discTwo_discThree K.D) h hd),
    ite_eq_left hd]

theorem flatMap_of_main_off (K : FlatDatum) {x : ModelCoordinates} (hm : planeOf x ∈ mainSet K.D)
    (h1 : planeOf x ∉ discOne K.D) (h2 : planeOf x ∉ discTwo K.D)
    (h3' : planeOf x ∉ discThree K.D) :
    flatMap C hc h3 K x = C.closedChart hc h3 (K.liftP x) := by
  unfold flatMap
  rw [ite_eq_right h1, ite_eq_right (not_mem_discOneMirror_of_main K.D hm), ite_eq_right h2,
    ite_eq_right h3', ite_eq_left hm]

theorem flatMap_of_conjMain_off (K : FlatDatum) {x : ModelCoordinates}
    (hm : conj (planeOf x) ∈ mainSet K.D) (hm' : planeOf x ∉ mainSet K.D)
    (h1 : planeOf x ∉ discOneMirror K.D) (h2 : planeOf x ∉ discTwo K.D)
    (h3' : planeOf x ∉ discThree K.D) :
    flatMap C hc h3 K x = C.closedChart hc h3 (K.liftM x) := by
  unfold flatMap
  rw [ite_eq_right (not_mem_discOne_of_conj_main K.D hm), ite_eq_right h1, ite_eq_right h2,
    ite_eq_right h3', ite_eq_right hm']

theorem norm_tubeOne_fst (K : FlatDatum) {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    ‖(K.tubeOne x).1‖ < 1 := by
  change ‖K.σ.rotOne (planeOf x) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one, norm_rotOne]
  exact lt_of_lt_of_le hd (by linarith [radOne_le_half K.D])

theorem norm_tubeTwo_fst (K : FlatDatum) {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    ‖(K.tubeTwo x).1‖ < 1 := by
  change ‖K.σ.rotTwo (planeOf x) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one, norm_rotTwo]
  exact lt_of_lt_of_le hd (by linarith [radTwo_le_half K.D])

theorem norm_tubeThree_fst (K : FlatDatum) {x : ModelCoordinates}
    (hd : planeOf x ∈ discThree K.D) : ‖(K.tubeThree x).1‖ < 1 := by
  change ‖(Circle.exp (Real.pi / K.σ.p₃) : ℂ) * planeOf x * _‖ < 1
  rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, mul_one]
  exact lt_of_lt_of_le hd (by linarith [radThree_le_half K.D])

theorem norm_tubeOne_rotThreeInv_fst (K : FlatDatum) {x : ModelCoordinates}
    (hd : conj (planeOf x) ∈ discOne K.D) : ‖(K.tubeOne (K.rotThreeInv x)).1‖ < 1 := by
  change ‖K.σ.rotOne (planeOf (K.rotThreeInv x)) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one, FlatDatum.rotThreeInv, planeOf_ofPlane,
    K.σ.rotOne_refl_one, Complex.norm_conj, norm_rotOne]
  exact lt_of_lt_of_le hd (by linarith [radOne_le_half K.D])

theorem tubeOne_fst_ne_zero (K : FlatDatum) {x : ModelCoordinates}
    (h : K.σ.rotOne (planeOf x) ≠ 0) : (K.tubeOne x).1 ≠ 0 :=
  mul_ne_zero h (Circle.coe_ne_zero _)

theorem tubeTwo_fst_ne_zero (K : FlatDatum) {x : ModelCoordinates}
    (h : K.σ.rotTwo (planeOf x) ≠ 0) : (K.tubeTwo x).1 ≠ 0 :=
  mul_ne_zero h (Circle.coe_ne_zero _)

theorem rotTwo_ne_zero_of_conj (σ : EuclidShape) {z : ℂ} (h : σ.rotTwo (conj z) ≠ 0) :
    σ.rotTwo z ≠ 0 := by
  intro h0
  apply h
  change σ.rotTwo (σ.refl 0 z) = 0
  rw [σ.rotTwo_refl_zero, h0, map_zero, mul_zero]

variable (h0 : d.orbChi = 0) (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

set_option hygiene false in
local notation "𝒦" => flatDatum C hc h3 h0 D

theorem tubeOne_eq_liftP {x : ModelCoordinates} (hd : planeOf x ∈ discOne (𝒦).D)
    (hs : (𝒦).σ.rotOne (planeOf x) ≠ 0 ∧ -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (planeOf x)) ∧
      arg ((𝒦).σ.rotOne (planeOf x)) < 3 * (𝒦).σ.θ₁ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 1) ((𝒦).tubeOne x) = C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_seamFwd_tubeOne hd hs]
  exact (C.closedChart_seamFwd_one hc h3 (tubeOne_fst_ne_zero _ hs.1)
    (norm_tubeOne_fst _ hd)).symm

theorem tubeTwo_eq_liftP {x : ModelCoordinates} (hd : planeOf x ∈ discTwo (𝒦).D)
    (hs : (𝒦).σ.rotTwo (planeOf x) ≠ 0 ∧ -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (planeOf x)) ∧
      arg ((𝒦).σ.rotTwo (planeOf x)) < 3 * (𝒦).σ.θ₂ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 2) ((𝒦).tubeTwo x) = C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_seamFwd_tubeTwo hd hs]
  exact (C.closedChart_seamFwd_two hc h3 (tubeTwo_fst_ne_zero _ hs.1)
    (norm_tubeTwo_fst _ hd)).symm

theorem tubeThree_eq_liftP {x : ModelCoordinates} (hd : planeOf x ∈ discThree (𝒦).D)
    (hs : planeOf x ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg (planeOf x) ∧
      arg (planeOf x) < 3 * (𝒦).σ.θ₃ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 0) ((𝒦).tubeThree x) =
      C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_outerFwd_tubeThree hd hs]
  exact (C.closedChart_outerFwd hc h3 (norm_tubeThree_fst _ hd)).symm

theorem tubeOne_eq_liftM {x : ModelCoordinates} (hd : conj (planeOf x) ∈ discOne (𝒦).D)
    (hs : (𝒦).σ.rotOne (conj (planeOf x)) ≠ 0 ∧
      -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (conj (planeOf x))) ∧
      arg ((𝒦).σ.rotOne (conj (planeOf x))) < 3 * (𝒦).σ.θ₁ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 1) ((𝒦).tubeOne ((𝒦).rotThreeInv x)) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : planeOf (reflectMap (𝒦).c₀ x) ∈ discOne (𝒦).D := by
    rw [planeOf_reflectMap]; exact hd
  have hs' : (𝒦).σ.rotOne (planeOf (reflectMap (𝒦).c₀ x)) ≠ 0 ∧
      -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (planeOf (reflectMap (𝒦).c₀ x))) ∧
      arg ((𝒦).σ.rotOne (planeOf (reflectMap (𝒦).c₀ x))) < 3 * (𝒦).σ.θ₁ / 2 := by
    rw [planeOf_reflectMap]; exact hs
  have hne : ((𝒦).tubeOne ((𝒦).rotThreeInv x)).1 ≠ 0 := by
    apply tubeOne_fst_ne_zero
    rw [FlatDatum.rotThreeInv, planeOf_ofPlane, (𝒦).σ.rotOne_refl_one, map_ne_zero]
    exact hs.1
  unfold FlatDatum.liftM
  rw [(𝒦).liftP_eq_seamFwd_tubeOne hd' hs', ← seamFwd_conjPair,
    (𝒦).conjPair_tubeOne_reflect hd]
  exact (C.closedChart_seamFwd_one hc h3 hne (norm_tubeOne_rotThreeInv_fst _ hd)).symm

theorem tubeTwo_eq_liftM {x : ModelCoordinates} (hd : planeOf x ∈ discTwo (𝒦).D)
    (hs : (𝒦).σ.rotTwo (conj (planeOf x)) ≠ 0 ∧
      -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (conj (planeOf x))) ∧
      arg ((𝒦).σ.rotTwo (conj (planeOf x))) < 3 * (𝒦).σ.θ₂ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 2) ((𝒦).tubeTwo x) = C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : planeOf (reflectMap (𝒦).c₀ x) ∈ discTwo (𝒦).D := by
    rw [planeOf_reflectMap]; exact conj_mem_discTwo _ hd
  have hs' : (𝒦).σ.rotTwo (planeOf (reflectMap (𝒦).c₀ x)) ≠ 0 ∧
      -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (planeOf (reflectMap (𝒦).c₀ x))) ∧
      arg ((𝒦).σ.rotTwo (planeOf (reflectMap (𝒦).c₀ x))) < 3 * (𝒦).σ.θ₂ / 2 := by
    rw [planeOf_reflectMap]; exact hs
  have hne : ((𝒦).tubeTwo x).1 ≠ 0 :=
    tubeTwo_fst_ne_zero _ (rotTwo_ne_zero_of_conj _ hs.1)
  unfold FlatDatum.liftM
  rw [(𝒦).liftP_eq_seamFwd_tubeTwo hd' hs', ← seamFwd_conjPair,
    (𝒦).conjPair_tubeTwo_reflect hd]
  exact (C.closedChart_seamFwd_two hc h3 hne (norm_tubeTwo_fst _ hd)).symm

theorem tubeThree_eq_liftM {x : ModelCoordinates} (hd : planeOf x ∈ discThree (𝒦).D)
    (hs : conj (planeOf x) ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg (conj (planeOf x)) ∧
      arg (conj (planeOf x)) < 3 * (𝒦).σ.θ₃ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 0) ((𝒦).tubeThree x) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : planeOf (reflectMap (𝒦).c₀ x) ∈ discThree (𝒦).D := by
    rw [planeOf_reflectMap]; exact conj_mem_discThree _ hd
  have hs' : planeOf (reflectMap (𝒦).c₀ x) ≠ 0 ∧
      -((𝒦).σ.θ₃ / 2) < arg (planeOf (reflectMap (𝒦).c₀ x)) ∧
      arg (planeOf (reflectMap (𝒦).c₀ x)) < 3 * (𝒦).σ.θ₃ / 2 := by
    rw [planeOf_reflectMap]; exact hs
  unfold FlatDatum.liftM
  rw [(𝒦).liftP_eq_outerFwd_tubeThree hd' hs', ← outerFwd_conjPair,
    (𝒦).conjPair_tubeThree_reflect x]
  exact (C.closedChart_outerFwd hc h3 (norm_tubeThree_fst _ hd)).symm

theorem flatMap_of_main {x : ModelCoordinates} (hm : planeOf x ∈ mainSet (𝒦).D) :
    flatMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftP x) := by
  by_cases h1 : planeOf x ∈ discOne (𝒦).D
  · rw [flatMap_of_discOne C hc h3 _ h1]
    exact tubeOne_eq_liftP C hc h3 h0 D h1 (sector_one _ hm h1)
  by_cases h2 : planeOf x ∈ discTwo (𝒦).D
  · rw [flatMap_of_discTwo C hc h3 _ h2]
    exact tubeTwo_eq_liftP C hc h3 h0 D h2 (sector_two _ hm h2)
  by_cases h3' : planeOf x ∈ discThree (𝒦).D
  · rw [flatMap_of_discThree C hc h3 _ h3']
    exact tubeThree_eq_liftP C hc h3 h0 D h3' (sector_three _ hm h3')
  exact flatMap_of_main_off C hc h3 _ hm h1 h2 h3'

theorem flatMap_of_conjMain {x : ModelCoordinates} (hm : conj (planeOf x) ∈ mainSet (𝒦).D) :
    flatMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftM x) := by
  by_cases h1 : planeOf x ∈ discOneMirror (𝒦).D
  · rw [flatMap_of_discOneMirror C hc h3 _ h1]
    have hd := (mem_discOneMirror_iff _).1 h1
    exact tubeOne_eq_liftM C hc h3 h0 D hd (sector_one _ hm hd)
  by_cases h2 : planeOf x ∈ discTwo (𝒦).D
  · rw [flatMap_of_discTwo C hc h3 _ h2]
    exact tubeTwo_eq_liftM C hc h3 h0 D h2 (sector_two _ hm (conj_mem_discTwo _ h2))
  by_cases h3' : planeOf x ∈ discThree (𝒦).D
  · rw [flatMap_of_discThree C hc h3 _ h3']
    exact tubeThree_eq_liftM C hc h3 h0 D h3' (sector_three _ hm (conj_mem_discThree _ h3'))
  by_cases hm' : planeOf x ∈ mainSet (𝒦).D
  · rw [flatMap_of_main C hc h3 h0 D hm']
    have hz := mem_patchZero_of_main_conj _ hm' hm
    rw [(𝒦).liftM_eq_liftP hz.1 hz.2.2.2.2.2.1]
  exact flatMap_of_conjMain_off C hc h3 _ hm hm' h1 h2 h3'

theorem isLocalDiffeomorphAt_flatMap {x : ModelCoordinates} (hx : x ∈ flatDomain (𝒦)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (flatMap C hc h3 (𝒦)) x := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hpre : ∀ {S : Set ℂ}, IsOpen S → planeOf x ∈ S → planeOf ⁻¹' S ∈ 𝓝 x :=
    fun hS h => (hS.preimage contDiff_planeOf.continuous).mem_nhds h
  have htube : ∀ (m : Fin d.fillingCount) {y : ℂ × Circle}, ‖y.1‖ < 1 →
      IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.tubeMap m) y :=
    fun m y hy => C.isLocalDiffeomorphAt_tubeMap (by linarith [C.ε_pos])
  change planeOf x ∈ flatBase (𝒦) at hx
  simp only [flatBase, mem_union, mem_ofPred_eq] at hx
  rcases hx with ((((hm | hm) | hd) | hd) | hd) | hd
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hpre (isOpen_mainSet _) hm)
          (fun y hy => flatMap_of_main C hc h3 h0 D hy))
        (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_liftP hm)
          (hg := C.isLocalDiffeomorphAt_closedChart hc h3 (liftP_mem_closedDomain _ hm)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem
          (hpre ((isOpen_mainSet _).preimage Complex.continuous_conj) hm)
          (fun y hy => flatMap_of_conjMain C hc h3 h0 D hy))
        (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_liftM hm)
          (hg := C.isLocalDiffeomorphAt_closedChart hc h3 (liftM_mem_closedDomain _ hm)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discOne _) hd)
        (fun y hy => flatMap_of_discOne C hc h3 _ hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeOne hd)
        (hg := htube _ (norm_tubeOne_fst _ hd)))
  · have hd' : conj (planeOf x) ∈ discOne (𝒦).D := (mem_discOneMirror_iff _).1 hd
    have hr : planeOf ((𝒦).screwThree.symm x) ∈ discOne (𝒦).D := by
      rw [FlatDatum.screwThree_symm, FlatDatum.rotThreeInv, planeOf_ofPlane]
      exact refl_one_mem_discOne _ hd'
    have h1 := IsLocalDiffeomorphAt.comp (hf := (𝒦).screwThree.symm.isLocalDiffeomorph x)
      (hg := (𝒦).isLocalDiffeomorphAt_tubeOne hr)
    have h2 := IsLocalDiffeomorphAt.comp (hf := h1)
      (hg := htube (C.closedHoleEquiv hc h3 1) (by
        change ‖((𝒦).tubeOne ((𝒦).screwThree.symm x)).1‖ < 1
        rw [FlatDatum.screwThree_symm]
        exact norm_tubeOne_rotThreeInv_fst _ hd'))
    refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discOneMirror _) hd)
        (fun y hy => ?_)) h2
    rw [flatMap_of_discOneMirror C hc h3 _ hy]
    change _ = C.tubeMap _ ((𝒦).tubeOne ((𝒦).screwThree.symm y))
    rw [FlatDatum.screwThree_symm]
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discTwo _) hd)
        (fun y hy => flatMap_of_discTwo C hc h3 _ hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeTwo hd)
        (hg := htube _ (norm_tubeTwo_fst _ hd)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre (isOpen_discThree _) hd)
        (fun y hy => flatMap_of_discThree C hc h3 _ hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeThree x)
        (hg := htube _ (norm_tubeThree_fst _ hd)))

end Map

end ClosedTriangle

end GC.Seifert
