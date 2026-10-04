import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphLayoutFacts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatFold

/-!
# The chart-level fold of a spherical closed triangle block

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §2, §5).
Let `C` be charts of a closed triangle block with `orbChi > 0` and `D` a fold datum on the
spherical triangle `C.closedSphShape` (cone `j` at hole `j`, the outer cone third). The signed
fibre step is `sphStep = π orbChi / e`, with `2π = n · sphStep` and the closing equation
`ℓ e = θ₁ + θ₂ + θ₃ - π` (`sphDatum`). For a layout `L` the fold `sphFoldMap` on `ModelCoordinates`
(the Hopf chart) is the tube chart of hole `1` composed with `tubeOne` on the disc about `v₁`, with
`tubeOne ∘ S₃⁻¹` on its mirror, the tube charts of holes `2`, `0` composed with `tubeTwo`,
`tubeThree` on the discs about `v₂`, `0`, and `P ∘ liftP`, `P ∘ liftM` on the main set and its
mirror (`P = C.closedChart`). In the good sectors the tube formulas equal the punctured formulas,
so the fold is `P ∘ liftP` on the main set and `P ∘ liftM` on its mirror (`sphFoldMap_of_main`,
`sphFoldMap_of_conjMain`); it is a local diffeomorphism on the open base `sphBase`
(`isLocalDiffeomorphAt_sphFoldMap`) and invariant under the Hopf period `2π`
(`sphFoldMap_period`), so it descends to the round sphere (`SphDescent`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

open TwoConeFold

section Datum

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)

theorem sphStep_closing :
    sphStep d * -((C.holeTwist hc h3 1 : ℝ) / (C.holeOrder hc h3 1 : ℕ) +
      (C.holeTwist hc h3 2 : ℝ) / (C.holeOrder hc h3 2 : ℕ) +
        (C.holeTwist hc h3 0 : ℝ) / (C.holeOrder hc h3 0 : ℕ)) =
      (C.closedSphShape hc h3 hχ).θ₁ + (C.closedSphShape hc h3 hχ).θ₂ +
        (C.closedSphShape hc h3 hχ).θ₃ - Real.pi := by
  have he := closedEuler_eq C hc h3
  unfold closedEuler at he
  rw [he, sphStep_mul_euler hc h3 hχ]
  have hO := C.orbChi_eq_holes hc h3
  rw [Fin.sum_univ_three] at hO
  have hOR : (d.orbChi : ℝ) = 1 / (C.holeOrder hc h3 0 : ℝ) + 1 / (C.holeOrder hc h3 1 : ℝ) +
      1 / (C.holeOrder hc h3 2 : ℝ) - 1 := by
    rw [hO]
    push_cast
    rfl
  rw [hOR]
  simp only [CompactShape.θ₁, CompactShape.θ₂, CompactShape.θ₃, SeifertBlockCharts.closedSphShape]
  ring

def sphDatum (D : (C.closedSphShape hc h3 hχ).FoldData) : SphDatum where
  σ := C.closedSphShape hc h3 hχ
  hσ := rfl
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
  ℓ := sphStep d
  ℓ_ne := sphStep_ne_zero hc h3 hχ
  n := Classical.choose (exists_two_pi_eq_mul_sphStep C hc h3 hχ)
  period := (Classical.choose_spec (exists_two_pi_eq_mul_sphStep C hc h3 hχ)).2
  closing := sphStep_closing C hc h3 hχ

end Datum

section Map

variable {K : SphDatum} (L : SphLayout K)

def sphBase : Set ℂ :=
  L.mainSet ∪ {z | conj z ∈ L.mainSet} ∪ L.discOne ∪ L.discOneMirror ∪ L.discTwo ∪ L.discThree

theorem isOpen_sphBase : IsOpen (sphBase L) := by
  unfold sphBase
  exact ((((L.isOpen_mainSet.union (L.isOpen_mainSet.preimage continuous_conj)).union
    L.isOpen_discOne).union L.isOpen_discOneMirror).union L.isOpen_discTwo).union
      L.isOpen_discThree

theorem disjoint_discOne_discOneMirror : Disjoint L.discOne L.discOneMirror := by
  rw [disjoint_left]
  intro z h1 h2
  have a := L.discOne_im_pos z h1
  have b := L.discOne_im_pos _ h2
  rw [conj_im] at b
  linarith

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

open Classical in
def sphFoldMap (x : ModelCoordinates) : W.pieceInterior ⊤ :=
  if planeOf x ∈ L.discOne then C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne x)
  else if planeOf x ∈ L.discOneMirror then
    C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne (K.rotThreeInv x))
  else if planeOf x ∈ L.discTwo then C.tubeMap (C.closedHoleEquiv hc h3 2) (K.tubeTwo x)
  else if planeOf x ∈ L.discThree then C.tubeMap (C.closedHoleEquiv hc h3 0) (K.tubeThree x)
  else if planeOf x ∈ L.mainSet then C.closedChart hc h3 (K.liftP x)
  else C.closedChart hc h3 (K.liftM x)

theorem sphFoldMap_of_discOne {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne) :
    sphFoldMap L C hc h3 x = C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne x) := by
  unfold sphFoldMap
  rw [ite_eq_left hd]

theorem sphFoldMap_of_discOneMirror {x : ModelCoordinates} (hd : planeOf x ∈ L.discOneMirror) :
    sphFoldMap L C hc h3 x =
      C.tubeMap (C.closedHoleEquiv hc h3 1) (K.tubeOne (K.rotThreeInv x)) := by
  have h1 : planeOf x ∉ L.discOne := fun h =>
    disjoint_left.mp (disjoint_discOne_discOneMirror L) h hd
  unfold sphFoldMap
  rw [ite_eq_right h1, ite_eq_left hd]

theorem sphFoldMap_of_discTwo {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo) :
    sphFoldMap L C hc h3 x = C.tubeMap (C.closedHoleEquiv hc h3 2) (K.tubeTwo x) := by
  have h1 : planeOf x ∉ L.discOne := fun h => disjoint_left.mp L.disjoint_one_two h hd
  have h1' : planeOf x ∉ L.discOneMirror := fun h => L.disjoint_two_mirror _ hd h
  unfold sphFoldMap
  rw [ite_eq_right h1, ite_eq_right h1', ite_eq_left hd]

theorem sphFoldMap_of_discThree {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree) :
    sphFoldMap L C hc h3 x = C.tubeMap (C.closedHoleEquiv hc h3 0) (K.tubeThree x) := by
  have h1 : planeOf x ∉ L.discOne := fun h => disjoint_left.mp L.disjoint_one_three h hd
  have h1' : planeOf x ∉ L.discOneMirror := fun h => L.disjoint_three_mirror _ hd h
  have h2 : planeOf x ∉ L.discTwo := fun h => disjoint_left.mp L.disjoint_two_three h hd
  unfold sphFoldMap
  rw [ite_eq_right h1, ite_eq_right h1', ite_eq_right h2, ite_eq_left hd]

theorem sphFoldMap_of_main_off {x : ModelCoordinates} (hm : planeOf x ∈ L.mainSet)
    (h1 : planeOf x ∉ L.discOne) (h2 : planeOf x ∉ L.discTwo) (h3' : planeOf x ∉ L.discThree) :
    sphFoldMap L C hc h3 x = C.closedChart hc h3 (K.liftP x) := by
  have h1' : planeOf x ∉ L.discOneMirror := L.main_mirror _ hm
  unfold sphFoldMap
  rw [ite_eq_right h1, ite_eq_right h1', ite_eq_right h2, ite_eq_right h3', ite_eq_left hm]

theorem sphFoldMap_of_conjMain_off {x : ModelCoordinates} (hm' : planeOf x ∉ L.mainSet)
    (h1 : planeOf x ∉ L.discOne) (h1' : planeOf x ∉ L.discOneMirror)
    (h2 : planeOf x ∉ L.discTwo) (h3' : planeOf x ∉ L.discThree) :
    sphFoldMap L C hc h3 x = C.closedChart hc h3 (K.liftM x) := by
  unfold sphFoldMap
  rw [ite_eq_right h1, ite_eq_right h1', ite_eq_right h2, ite_eq_right h3', ite_eq_right hm']

theorem rotOne_ne_zero {z : ℂ} (hd : z ∈ L.discOne) (hv : z ≠ K.σ.vertexOne) :
    K.σ.rotOne z ≠ 0 := by
  rw [rotOne_eq_of_sph K.hσ]
  refine mul_ne_zero (neg_ne_zero.2 (exp_ne_zero _)) (div_ne_zero (sub_ne_zero.2 hv) hd.1)

theorem rotTwo_ne_zero {z : ℂ} (hd : z ∈ L.discTwo) (hv : z ≠ K.σ.vertexTwo) :
    K.σ.rotTwo z ≠ 0 := by
  rw [rotTwo_eq_of_sph K.hσ]
  refine mul_ne_zero (neg_ne_zero.2 (exp_ne_zero _)) (div_ne_zero (sub_ne_zero.2 hv) hd.1)

theorem norm_tubeOne_fst {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne) :
    ‖(K.tubeOne x).1‖ < 1 := by
  change ‖K.σ.rotOne (planeOf x) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one]
  linarith [L.norm_rotOne_lt hd]

theorem norm_tubeTwo_fst {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo) :
    ‖(K.tubeTwo x).1‖ < 1 := by
  change ‖K.σ.rotTwo (planeOf x) * _‖ < 1
  rw [norm_mul, Circle.norm_coe, mul_one]
  linarith [L.norm_rotTwo_lt hd]

theorem norm_tubeThree_fst {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree) :
    ‖(K.tubeThree x).1‖ < 1 := by
  change ‖(Circle.exp (Real.pi / K.σ.p₃) : ℂ) * planeOf x * _‖ < 1
  rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, mul_one]
  linarith [L.norm_lt_of_discThree hd]

theorem planeOf_rotThreeInv (x : ModelCoordinates) :
    planeOf (K.rotThreeInv x) = K.σ.refl 1 (conj (planeOf x)) := by
  rw [SphDatum.rotThreeInv, planeOf_ofPlane]

theorem norm_tubeOne_rotThreeInv_fst {x : ModelCoordinates} (hd : conj (planeOf x) ∈ L.discOne) :
    ‖(K.tubeOne (K.rotThreeInv x)).1‖ < 1 :=
  norm_tubeOne_fst L (by rw [planeOf_rotThreeInv]; exact L.refl_one_mem_discOne hd)

end Map

section Overlap

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

set_option hygiene false in
local notation "𝒦" => sphDatum C hc h3 hχ D

theorem tubeOne_eq_liftP {x : ModelCoordinates} (hd : planeOf x ∈ L.discOne)
    (hs : (𝒦).σ.rotOne (planeOf x) ≠ 0 ∧ -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (planeOf x)) ∧
      arg ((𝒦).σ.rotOne (planeOf x)) < 3 * (𝒦).σ.θ₁ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 1) ((𝒦).tubeOne x) =
      C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_seamFwd_tubeOne (L.f_of_mem_discOne hd).2 (L.norm_rotOne_pow_le hd) hs]
  exact (C.closedChart_seamFwd_one hc h3 (mul_ne_zero hs.1 (Circle.coe_ne_zero _))
    (norm_tubeOne_fst L hd)).symm

theorem tubeTwo_eq_liftP {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo)
    (hs : (𝒦).σ.rotTwo (planeOf x) ≠ 0 ∧ -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (planeOf x)) ∧
      arg ((𝒦).σ.rotTwo (planeOf x)) < 3 * (𝒦).σ.θ₂ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 2) ((𝒦).tubeTwo x) =
      C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_seamFwd_tubeTwo (L.f_of_mem_discTwo hd).2 (L.norm_rotTwo_pow_le hd) hs]
  exact (C.closedChart_seamFwd_two hc h3 (mul_ne_zero hs.1 (Circle.coe_ne_zero _))
    (norm_tubeTwo_fst L hd)).symm

theorem tubeThree_eq_liftP {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree)
    (hs : planeOf x ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg (planeOf x) ∧
      arg (planeOf x) < 3 * (𝒦).σ.θ₃ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 0) ((𝒦).tubeThree x) =
      C.closedChart hc h3 ((𝒦).liftP x) := by
  rw [(𝒦).liftP_eq_outerFwd_tubeThree (L.f_of_mem_discThree hd hs.1).2
    (L.normSq_f_of_discThree hd hs.1) (L.norm_pow_lt_seven hd) hs]
  exact (C.closedChart_outerFwd hc h3 (norm_tubeThree_fst L hd)).symm

theorem tubeOne_eq_liftM {x : ModelCoordinates} (hd : conj (planeOf x) ∈ L.discOne)
    (hs : (𝒦).σ.rotOne (conj (planeOf x)) ≠ 0 ∧
      -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (conj (planeOf x))) ∧
      arg ((𝒦).σ.rotOne (conj (planeOf x))) < 3 * (𝒦).σ.θ₁ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 1) ((𝒦).tubeOne ((𝒦).rotThreeInv x)) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : planeOf (reflectMap (𝒦).c₀ x) ∈ L.discOne := by
    rw [planeOf_reflectMap]; exact hd
  have hs' : (𝒦).σ.rotOne (planeOf (reflectMap (𝒦).c₀ x)) ≠ 0 ∧
      -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne (planeOf (reflectMap (𝒦).c₀ x))) ∧
      arg ((𝒦).σ.rotOne (planeOf (reflectMap (𝒦).c₀ x))) < 3 * (𝒦).σ.θ₁ / 2 := by
    rw [planeOf_reflectMap]; exact hs
  have hne : ((𝒦).tubeOne ((𝒦).rotThreeInv x)).1 ≠ 0 := by
    refine mul_ne_zero ?_ (Circle.coe_ne_zero _)
    rw [planeOf_rotThreeInv, rotOne_refl_one_sph (𝒦).hσ, map_ne_zero]
    exact hs.1
  unfold SphDatum.liftM
  rw [(𝒦).liftP_eq_seamFwd_tubeOne (L.f_of_mem_discOne hd').2 (L.norm_rotOne_pow_le hd') hs',
    ← seamFwd_conjPair, (𝒦).conjPair_tubeOne_reflect (L.re_apexOne_gt hd)
      (L.discOne_slit _ hd)]
  exact (C.closedChart_seamFwd_one hc h3 hne (norm_tubeOne_rotThreeInv_fst L hd)).symm

theorem tubeTwo_eq_liftM {x : ModelCoordinates} (hd : planeOf x ∈ L.discTwo)
    (hs : (𝒦).σ.rotTwo (conj (planeOf x)) ≠ 0 ∧
      -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (conj (planeOf x))) ∧
      arg ((𝒦).σ.rotTwo (conj (planeOf x))) < 3 * (𝒦).σ.θ₂ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 2) ((𝒦).tubeTwo x) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : planeOf (reflectMap (𝒦).c₀ x) ∈ L.discTwo := by
    rw [planeOf_reflectMap]; exact L.conj_mem_discTwo hd
  have hs' : (𝒦).σ.rotTwo (planeOf (reflectMap (𝒦).c₀ x)) ≠ 0 ∧
      -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo (planeOf (reflectMap (𝒦).c₀ x))) ∧
      arg ((𝒦).σ.rotTwo (planeOf (reflectMap (𝒦).c₀ x))) < 3 * (𝒦).σ.θ₂ / 2 := by
    rw [planeOf_reflectMap]; exact hs
  have hne : ((𝒦).tubeTwo x).1 ≠ 0 := by
    refine mul_ne_zero ?_ (Circle.coe_ne_zero _)
    intro h0
    apply hs.1
    rw [rotTwo_conj_sph (𝒦).hσ, h0, map_zero, mul_zero]
  unfold SphDatum.liftM
  rw [(𝒦).liftP_eq_seamFwd_tubeTwo (L.f_of_mem_discTwo hd').2 (L.norm_rotTwo_pow_le hd') hs',
    ← seamFwd_conjPair, (𝒦).conjPair_tubeTwo_reflect (L.re_apexTwo_lt hd)
      (L.discTwo_slit _ hd)]
  exact (C.closedChart_seamFwd_two hc h3 hne (norm_tubeTwo_fst L hd)).symm

theorem tubeThree_eq_liftM {x : ModelCoordinates} (hd : planeOf x ∈ L.discThree)
    (hs : conj (planeOf x) ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg (conj (planeOf x)) ∧
      arg (conj (planeOf x)) < 3 * (𝒦).σ.θ₃ / 2) :
    C.tubeMap (C.closedHoleEquiv hc h3 0) ((𝒦).tubeThree x) =
      C.closedChart hc h3 ((𝒦).liftM x) := by
  have hd' : planeOf (reflectMap (𝒦).c₀ x) ∈ L.discThree := by
    rw [planeOf_reflectMap]; exact L.conj_mem_discThree hd
  have hs' : planeOf (reflectMap (𝒦).c₀ x) ≠ 0 ∧
      -((𝒦).σ.θ₃ / 2) < arg (planeOf (reflectMap (𝒦).c₀ x)) ∧
      arg (planeOf (reflectMap (𝒦).c₀ x)) < 3 * (𝒦).σ.θ₃ / 2 := by
    rw [planeOf_reflectMap]; exact hs
  unfold SphDatum.liftM
  rw [(𝒦).liftP_eq_outerFwd_tubeThree (L.f_of_mem_discThree hd' hs'.1).2
    (L.normSq_f_of_discThree hd' hs'.1) (L.norm_pow_lt_seven hd') hs', ← outerFwd_conjPair,
    (𝒦).conjPair_tubeThree_reflect x]
  exact (C.closedChart_outerFwd hc h3 (norm_tubeThree_fst L hd)).symm

theorem window_one {z : ℂ} (hm : z ∈ L.mainSet) (hd : z ∈ L.discOne) :
    (𝒦).σ.rotOne z ≠ 0 ∧ -((𝒦).σ.θ₁ / 2) < arg ((𝒦).σ.rotOne z) ∧
      arg ((𝒦).σ.rotOne z) < 3 * (𝒦).σ.θ₁ / 2 :=
  ⟨rotOne_ne_zero L hd (L.main_ne z hm).2.1, L.main_window_one z hm hd⟩

theorem window_two {z : ℂ} (hm : z ∈ L.mainSet) (hd : z ∈ L.discTwo) :
    (𝒦).σ.rotTwo z ≠ 0 ∧ -((𝒦).σ.θ₂ / 2) < arg ((𝒦).σ.rotTwo z) ∧
      arg ((𝒦).σ.rotTwo z) < 3 * (𝒦).σ.θ₂ / 2 :=
  ⟨rotTwo_ne_zero L hd (L.main_ne z hm).2.2, L.main_window_two z hm hd⟩

theorem window_three {z : ℂ} (hm : z ∈ L.mainSet) (hd : z ∈ L.discThree) :
    z ≠ 0 ∧ -((𝒦).σ.θ₃ / 2) < arg z ∧ arg z < 3 * (𝒦).σ.θ₃ / 2 :=
  ⟨(L.main_ne z hm).1, L.main_window_three z hm hd⟩

theorem sphFoldMap_of_main {x : ModelCoordinates} (hm : planeOf x ∈ L.mainSet) :
    sphFoldMap L C hc h3 x = C.closedChart hc h3 ((𝒦).liftP x) := by
  by_cases h1 : planeOf x ∈ L.discOne
  · rw [sphFoldMap_of_discOne L C hc h3 h1]
    exact tubeOne_eq_liftP C hc h3 hχ D L h1 (window_one C hc h3 hχ D L hm h1)
  by_cases h2 : planeOf x ∈ L.discTwo
  · rw [sphFoldMap_of_discTwo L C hc h3 h2]
    exact tubeTwo_eq_liftP C hc h3 hχ D L h2 (window_two C hc h3 hχ D L hm h2)
  by_cases h3' : planeOf x ∈ L.discThree
  · rw [sphFoldMap_of_discThree L C hc h3 h3']
    exact tubeThree_eq_liftP C hc h3 hχ D L h3' (window_three C hc h3 hχ D L hm h3')
  exact sphFoldMap_of_main_off L C hc h3 hm h1 h2 h3'

theorem sphFoldMap_of_conjMain {x : ModelCoordinates} (hm : conj (planeOf x) ∈ L.mainSet) :
    sphFoldMap L C hc h3 x = C.closedChart hc h3 ((𝒦).liftM x) := by
  by_cases h1 : planeOf x ∈ L.discOneMirror
  · rw [sphFoldMap_of_discOneMirror L C hc h3 h1]
    exact tubeOne_eq_liftM C hc h3 hχ D L h1 (window_one C hc h3 hχ D L hm h1)
  by_cases h2 : planeOf x ∈ L.discTwo
  · rw [sphFoldMap_of_discTwo L C hc h3 h2]
    exact tubeTwo_eq_liftM C hc h3 hχ D L h2
      (window_two C hc h3 hχ D L hm (L.conj_mem_discTwo h2))
  by_cases h3' : planeOf x ∈ L.discThree
  · rw [sphFoldMap_of_discThree L C hc h3 h3']
    exact tubeThree_eq_liftM C hc h3 hχ D L h3'
      (window_three C hc h3 hχ D L hm (L.conj_mem_discThree h3'))
  have h1' : planeOf x ∉ L.discOne := by
    intro h
    apply L.main_mirror _ hm
    rw [conj_conj]
    exact h
  by_cases hm' : planeOf x ∈ L.mainSet
  · rw [sphFoldMap_of_main C hc h3 hχ D L hm']
    have hz := L.main_conj _ hm' hm
    obtain ⟨hV, hre, -⟩ := L.patchZero_spec _ hz
    rw [(𝒦).liftM_eq_liftP hV hre (L.main_slit _ hm').2]
  exact sphFoldMap_of_conjMain_off L C hc h3 hm' h1' h1 h2 h3'

theorem rotThreeInv_eq_screw (x : ModelCoordinates) :
    (𝒦).rotThreeInv x = screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₃) ((𝒦).ℓ * (𝒦).k₃) x := by
  apply modelCoordinates_ext
  · rw [planeOf_rotThreeInv, planeOf_screwDiffeomorph]
    change exp (2 * ((𝒦).σ.θ₃ : ℂ) * I) * conj (conj (planeOf x)) = _
    rw [conj_conj, CompactShape.θ₃]
    congr 2
    push_cast
    ring
  · rw [SphDatum.rotThreeInv, ofPlane_apply_two, screwDiffeomorph_two]

theorem liftP_mem_closedDomain {x : ModelCoordinates} (hm : planeOf x ∈ L.mainSet) :
    (𝒦).liftP x ∈ closedDomain :=
  L.f_main_props hm

theorem liftM_mem_closedDomain {x : ModelCoordinates} (hm : conj (planeOf x) ∈ L.mainSet) :
    (𝒦).liftM x ∈ closedDomain := by
  obtain ⟨n1, n2, n3⟩ := L.f_main_props hm
  change ‖conj ((𝒦).D.f (planeOf (reflectMap (𝒦).c₀ x)))‖ < 7 / 2 ∧
    conj ((𝒦).D.f (planeOf (reflectMap (𝒦).c₀ x))) ≠ 3 / 2 ∧
      conj ((𝒦).D.f (planeOf (reflectMap (𝒦).c₀ x))) ≠ -(3 / 2)
  rw [planeOf_reflectMap, Complex.norm_conj]
  refine ⟨n1, fun h => n2 ?_, fun h => n3 ?_⟩
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this

theorem isLocalDiffeomorphAt_sphFoldMap {x : ModelCoordinates} (hx : planeOf x ∈ sphBase L) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (sphFoldMap L C hc h3) x := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hpre : ∀ {S : Set ℂ}, IsOpen S → planeOf x ∈ S → planeOf ⁻¹' S ∈ 𝓝 x :=
    fun hS h => (hS.preimage contDiff_planeOf.continuous).mem_nhds h
  have htube : ∀ (m : Fin d.fillingCount) {y : ℂ × Circle}, ‖y.1‖ < 1 →
      IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.tubeMap m) y :=
    fun m y hy => C.isLocalDiffeomorphAt_tubeMap (by linarith [C.ε_pos])
  have hOU := L.main_subset_U
  have hph : ∀ z ∈ L.mainSet, _ := fun z hz => L.main_phase hz
  have h1 : ∀ z ∈ L.mainSet, 1 + conj (𝒦).σ.vertexOne * z ∈ slitPlane :=
    fun z hz => (L.main_slit z hz).1
  have h2 : ∀ z ∈ L.mainSet, 1 + conj (𝒦).σ.vertexTwo * z ∈ slitPlane :=
    fun z hz => (L.main_slit z hz).2
  have hv : ∀ z ∈ L.mainSet, z ≠ (𝒦).σ.vertexOne ∧ z ≠ (𝒦).σ.vertexTwo :=
    fun z hz => (L.main_ne z hz).2
  change planeOf x ∈ sphBase L at hx
  simp only [sphBase, mem_union, mem_ofPred_eq] at hx
  rcases hx with ((((hm | hm) | hd) | hd) | hd) | hd
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hpre L.isOpen_mainSet hm)
          (fun y hy => sphFoldMap_of_main C hc h3 hχ D L hy))
        (IsLocalDiffeomorphAt.comp
          (hf := (𝒦).isLocalDiffeomorphAt_liftP L.isOpen_mainSet hOU hph h1 h2 hv hm)
          (hg := C.isLocalDiffeomorphAt_closedChart hc h3
            (liftP_mem_closedDomain C hc h3 hχ D L hm)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hpre (L.isOpen_mainSet.preimage continuous_conj) hm)
          (fun y hy => sphFoldMap_of_conjMain C hc h3 hχ D L hy))
        (IsLocalDiffeomorphAt.comp
          (hf := (𝒦).isLocalDiffeomorphAt_liftM L.isOpen_mainSet hOU hph h1 h2 hv hm)
          (hg := C.isLocalDiffeomorphAt_closedChart hc h3
            (liftM_mem_closedDomain C hc h3 hχ D L hm)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre L.isOpen_discOne hd)
        (fun y hy => sphFoldMap_of_discOne L C hc h3 hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeOne L.isOpen_discOne
          L.discOne_slit (fun z hz => L.re_apexOne_gt hz) hd)
        (hg := htube _ (norm_tubeOne_fst L hd)))
  · have hd' : conj (planeOf x) ∈ L.discOne := hd
    have hr : planeOf (screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₃) ((𝒦).ℓ * (𝒦).k₃) x) ∈
        L.discOne := by
      rw [← rotThreeInv_eq_screw, planeOf_rotThreeInv]
      exact L.refl_one_mem_discOne hd'
    have h1' := IsLocalDiffeomorphAt.comp
      (hf := (screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₃) ((𝒦).ℓ * (𝒦).k₃)).isLocalDiffeomorph x)
      (hg := (𝒦).isLocalDiffeomorphAt_tubeOne L.isOpen_discOne L.discOne_slit
        (fun z hz => L.re_apexOne_gt hz) hr)
    have h2' := IsLocalDiffeomorphAt.comp (hf := h1')
      (hg := htube (C.closedHoleEquiv hc h3 1) (by
        change ‖((𝒦).tubeOne (screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₃) ((𝒦).ℓ * (𝒦).k₃) x)).1‖ < 1
        rw [← rotThreeInv_eq_screw]
        exact norm_tubeOne_rotThreeInv_fst L hd'))
    refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre L.isOpen_discOneMirror hd)
        (fun y hy => ?_)) h2'
    rw [sphFoldMap_of_discOneMirror L C hc h3 hy]
    change _ = C.tubeMap _ ((𝒦).tubeOne
      (screwDiffeomorph (2 * Real.pi / (𝒦).σ.p₃) ((𝒦).ℓ * (𝒦).k₃) y))
    rw [rotThreeInv_eq_screw]
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre L.isOpen_discTwo hd)
        (fun y hy => sphFoldMap_of_discTwo L C hc h3 hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeTwo L.isOpen_discTwo
          L.discTwo_slit (fun z hz => L.re_apexTwo_lt hz) hd)
        (hg := htube _ (norm_tubeTwo_fst L hd)))
  · refine IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hpre L.isOpen_discThree hd)
        (fun y hy => sphFoldMap_of_discThree L C hc h3 hy))
      (IsLocalDiffeomorphAt.comp (hf := (𝒦).isLocalDiffeomorphAt_tubeThree x)
        (hg := htube _ (norm_tubeThree_fst L hd)))

theorem sphFoldMap_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / (𝒦).ℓ = y 2 / (𝒦).ℓ + m) :
    sphFoldMap L C hc h3 y' = sphFoldMap L C hc h3 y := by
  unfold sphFoldMap
  rw [hp, (𝒦).tubeOne_shift m hp h2, (𝒦).rotThreeInv_shift m hp h2, (𝒦).tubeTwo_shift m hp h2,
    (𝒦).tubeThree_shift m hp h2, (𝒦).liftP_shift m hp h2, (𝒦).liftM_shift m hp h2]

theorem sphFoldMap_period (x : ModelCoordinates) (m : ℤ) :
    sphFoldMap L C hc h3 (x + GC.Geometry.fibreShift (2 * Real.pi * m)) =
      sphFoldMap L C hc h3 x :=
  sphFoldMap_shift C hc h3 hχ D L _ (SphDatum.planeOf_add_fibreShift' x _) ((𝒦).period_div x m)

end Overlap

end Sph

end ClosedTriangle

end GC.Seifert
