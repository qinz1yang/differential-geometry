/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import DifferentialGeometry.Topology.PiecewiseLinear.Prism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace PLCrossSeamReading

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}

theorem injOn_chart_of_pLSeamTubeChart (C : PLSeamTubeChart M chart) :
    InjOn chart spliceCylinder := by
  have h := C.piece.bijOn.injOn
  rw [C.space_eq, C.map_eq] at h
  exact h

theorem injOn_resolvedCell (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    InjOn (R.resolvedCell C) R.tubeSource := by
  intro x hx z hz hxz
  rw [R.resolvedCell_apply_of_mem C hx, R.resolvedCell_apply_of_mem C hz] at hxz
  have hmodel := injOn_chart_of_pLSeamTubeChart C (R.mapsTo_resolve hx) (R.mapsTo_resolve hz) hxz
  exact R.bijOn_coord.injOn hx hz
    (injOn_crossSeamResolve (R.bijOn_coord.mapsTo hx) (R.bijOn_coord.mapsTo hz) hmodel)

theorem doublePointSet_resolvedCell (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) :
    doublePointSet (R.resolvedCell C) R.tubeSource = ∅ :=
  (doublePointSet_eq_empty_iff_injOn _ _).mpr (R.injOn_resolvedCell C)

end PLCrossSeamReading

noncomputable def seamWitnessPlane : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

theorem mem_image_seamWitnessPlane {S : Set (ℝ × ℝ)} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ ⇑seamWitnessPlane '' S ↔ seamWitnessPlane.symm x ∈ S := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [seamWitnessPlane.symm_apply_apply]
  · intro h
    exact ⟨seamWitnessPlane.symm x, h, seamWitnessPlane.apply_symm_apply x⟩

theorem isPiecewiseAffineOn_seamWitnessPlane {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPiecewiseAffineOn (⇑seamWitnessPlane) S :=
  (isPiecewiseAffineOn_of_affine seamWitnessPlane.toLinearMap.toAffineMap
    isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)

theorem isPLHomeomorphOn_seamWitnessPlane {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPLHomeomorphOn (⇑seamWitnessPlane) S (⇑seamWitnessPlane '' S) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hS (isPiecewiseAffineOn_seamWitnessPlane hS)
    seamWitnessPlane.injective.injOn.bijOn_image

theorem isPolyhedron_image_seamWitnessPlane {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPolyhedron (⇑seamWitnessPlane '' S) :=
  hS.image_of_isPiecewiseAffineOn (isPiecewiseAffineOn_seamWitnessPlane hS)
    seamWitnessPlane.injective.injOn

theorem bijOn_seamWitnessPlaneSymm (S : Set (ℝ × ℝ)) :
    BijOn (⇑seamWitnessPlane.symm) (⇑seamWitnessPlane '' S) S := by
  refine ⟨fun x hx => mem_image_seamWitnessPlane.mp hx, seamWitnessPlane.symm.injective.injOn,
    fun p hp => ⟨seamWitnessPlane p, ⟨p, hp, rfl⟩, seamWitnessPlane.symm_apply_apply p⟩⟩

theorem isPiecewiseAffineOn_seamWitnessPlaneSymm {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsPolyhedron S) : IsPiecewiseAffineOn (⇑seamWitnessPlane.symm) S :=
  (isPiecewiseAffineOn_of_affine seamWitnessPlane.symm.toLinearMap.toAffineMap
    isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)

theorem isPLHomeomorphOn_seamWitnessPlaneSymm {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPLHomeomorphOn (⇑seamWitnessPlane.symm) (⇑seamWitnessPlane '' S) S :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isPolyhedron_image_seamWitnessPlane hS)
    (isPiecewiseAffineOn_seamWitnessPlaneSymm (isPolyhedron_image_seamWitnessPlane hS))
    (bijOn_seamWitnessPlaneSymm S)

noncomputable def seamShift (b : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ where
  toFun p := p.1 - b
  linear := LinearMap.fst ℝ ℝ ℝ
  map_vadd' p v := by
    simp only [vadd_eq_add, Prod.fst_add, LinearMap.fst_apply]
    ring

noncomputable def seamScale (c : ℝ) : ℝ →ᵃ[ℝ] ℝ where
  toFun x := c * x
  linear := c • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

noncomputable def seamLine (c d : ℝ) : ℝ →ᵃ[ℝ] ℝ where
  toFun a := c * a + d
  linear := c • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

theorem isPiecewiseAffineOn_seamSnd :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.2) univ :=
  (isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ).congr
    fun _ _ => rfl

theorem isPiecewiseAffineOn_seamShift (b : ℝ) :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.1 - b) univ :=
  (isPiecewiseAffineOn_of_affine (seamShift b) isOpen_univ).congr fun _ _ => rfl

theorem isPiecewiseAffineOn_seamZero :
    IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
  (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
    fun _ _ => rfl

theorem isPiecewiseAffineOn_seamZeroLine :
    IsPiecewiseAffineOn (fun _ : ℝ => (0 : ℝ)) univ :=
  (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (0 : ℝ)) isOpen_univ).congr fun _ _ => rfl

noncomputable def seamRamp (c b : ℝ) (p : ℝ × ℝ) : ℝ := c * max (p.1 - b) 0

theorem isPiecewiseAffineOn_seamRamp (c b : ℝ) : IsPiecewiseAffineOn (seamRamp c b) univ :=
  (((isPiecewiseAffineOn_seamShift b).max isPiecewiseAffineOn_seamZero).affine_comp
    (seamScale c)).congr fun _ _ => rfl

noncomputable def seamArcX (p : ℝ × ℝ) : ℝ :=
  2 - p.1 + seamRamp (-1) 1 p + seamRamp 2 (3 / 2) p + seamRamp (-4) 2 p + seamRamp 6 (5 / 2) p
    + seamRamp (-2) (7 / 2) p

noncomputable def seamArcY (p : ℝ × ℝ) : ℝ :=
  seamRamp (-2) (3 / 2) p + seamRamp 6 (5 / 2) p + seamRamp (-4) 3 p + seamRamp 2 (7 / 2) p
    + seamRamp (-1) 4 p

noncomputable def seamModelMap (p : ℝ × ℝ) : (ℝ × ℝ) × ℝ := ((seamArcX p, seamArcY p), p.2)

theorem isPiecewiseAffineOn_seamArcX : IsPiecewiseAffineOn seamArcX univ := by
  have h0 : IsPiecewiseAffineOn (fun p : ℝ × ℝ => 2 - p.1) univ :=
    ((isPiecewiseAffineOn_seamShift 2).affine_comp (seamScale (-1))).congr fun _ _ => by
      simp [seamScale]
  exact ((((h0.add (isPiecewiseAffineOn_seamRamp (-1) 1)).add
    (isPiecewiseAffineOn_seamRamp 2 (3 / 2))).add (isPiecewiseAffineOn_seamRamp (-4) 2)).add
      (isPiecewiseAffineOn_seamRamp 6 (5 / 2))).add
        (isPiecewiseAffineOn_seamRamp (-2) (7 / 2))

theorem isPiecewiseAffineOn_seamArcY : IsPiecewiseAffineOn seamArcY univ :=
  (((((isPiecewiseAffineOn_seamRamp (-2) (3 / 2)).add
    (isPiecewiseAffineOn_seamRamp 6 (5 / 2))).add (isPiecewiseAffineOn_seamRamp (-4) 3)).add
      (isPiecewiseAffineOn_seamRamp 2 (7 / 2))).add (isPiecewiseAffineOn_seamRamp (-1) 4))

theorem isPiecewiseAffineOn_seamModelMap : IsPiecewiseAffineOn seamModelMap univ :=
  (isPiecewiseAffineOn_seamArcX.prod_mk isPiecewiseAffineOn_seamArcY).prod_mk
    isPiecewiseAffineOn_seamSnd

noncomputable def seamBentPos (a : ℝ) : ℝ × ℝ := (max (3 - 2 * a) 0, min (3 - 2 * a) 0)

noncomputable def seamBentNeg (a : ℝ) : ℝ × ℝ := (min (2 * a - 7) 0, max (2 * a - 7) 0)

theorem seamBentPos_sum (a : ℝ) : (seamBentPos a).1 + (seamBentPos a).2 = 3 - 2 * a := by
  simp only [seamBentPos]
  rw [max_add_min]
  ring

theorem seamBentNeg_sum (a : ℝ) : (seamBentNeg a).1 + (seamBentNeg a).2 = 2 * a - 7 := by
  simp only [seamBentNeg]
  rw [min_add_max]
  ring

theorem isPiecewiseAffineOn_seamBentPos : IsPiecewiseAffineOn seamBentPos univ := by
  have h : IsPiecewiseAffineOn (fun a : ℝ => 3 - 2 * a) univ :=
    (isPiecewiseAffineOn_of_affine (seamLine (-2) 3) isOpen_univ).congr fun _ _ => by
      simp [seamLine]; ring
  exact ((h.max isPiecewiseAffineOn_seamZeroLine).prod_mk
    (h.min isPiecewiseAffineOn_seamZeroLine))

theorem isPiecewiseAffineOn_seamBentNeg : IsPiecewiseAffineOn seamBentNeg univ := by
  have h : IsPiecewiseAffineOn (fun a : ℝ => 2 * a - 7) univ :=
    (isPiecewiseAffineOn_of_affine (seamLine 2 (-7)) isOpen_univ).congr fun _ _ => by
      simp [seamLine]; ring
  exact ((h.min isPiecewiseAffineOn_seamZeroLine).prod_mk
    (h.max isPiecewiseAffineOn_seamZeroLine))

theorem bijOn_seamBentPos : BijOn seamBentPos (Icc (1 : ℝ) 2) bentArcPos := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a ⟨h1, h2⟩
    rcases le_total (0 : ℝ) (3 - 2 * a) with hc | hc
    · refine mem_bentArcPos.mpr (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
      · rw [show (seamBentPos a).1 = max (3 - 2 * a) 0 from rfl, max_eq_left hc]
        linarith
      · rw [show (seamBentPos a).1 = max (3 - 2 * a) 0 from rfl, max_eq_left hc]
        linarith
      · rw [show (seamBentPos a).2 = min (3 - 2 * a) 0 from rfl, min_eq_right hc]
    · refine mem_bentArcPos.mpr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [show (seamBentPos a).1 = max (3 - 2 * a) 0 from rfl, max_eq_right hc]
      · rw [show (seamBentPos a).2 = min (3 - 2 * a) 0 from rfl, min_eq_left hc]
        linarith
      · rw [show (seamBentPos a).2 = min (3 - 2 * a) 0 from rfl, min_eq_left hc]
        linarith
  · intro a _ b _ hab
    have h := congrArg (fun q : ℝ × ℝ => q.1 + q.2) hab
    simp only [seamBentPos_sum] at h
    linarith
  · intro p hp
    rw [mem_bentArcPos] at hp
    rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · refine ⟨(3 - p.1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 3 - 2 * ((3 - p.1) / 2) = p.1 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentPos ((3 - p.1) / 2)).1 = max (3 - 2 * ((3 - p.1) / 2)) 0 from rfl,
          hval, max_eq_left h0]
      · rw [show (seamBentPos ((3 - p.1) / 2)).2 = min (3 - 2 * ((3 - p.1) / 2)) 0 from rfl,
          hval, min_eq_right h0, h2]
    · refine ⟨(3 - p.2) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 3 - 2 * ((3 - p.2) / 2) = p.2 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentPos ((3 - p.2) / 2)).1 = max (3 - 2 * ((3 - p.2) / 2)) 0 from rfl,
          hval, max_eq_right h2, h1]
      · rw [show (seamBentPos ((3 - p.2) / 2)).2 = min (3 - 2 * ((3 - p.2) / 2)) 0 from rfl,
          hval, min_eq_left h2]

theorem bijOn_seamBentNeg : BijOn seamBentNeg (Icc (3 : ℝ) 4) bentArcNeg := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a ⟨h1, h2⟩
    rcases le_total (2 * a - 7) (0 : ℝ) with hc | hc
    · refine mem_bentArcNeg.mpr (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
      · rw [show (seamBentNeg a).1 = min (2 * a - 7) 0 from rfl, min_eq_left hc]
        linarith
      · rw [show (seamBentNeg a).1 = min (2 * a - 7) 0 from rfl, min_eq_left hc]
        linarith
      · rw [show (seamBentNeg a).2 = max (2 * a - 7) 0 from rfl, max_eq_right hc]
    · refine mem_bentArcNeg.mpr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [show (seamBentNeg a).1 = min (2 * a - 7) 0 from rfl, min_eq_right hc]
      · rw [show (seamBentNeg a).2 = max (2 * a - 7) 0 from rfl, max_eq_left hc]
        linarith
      · rw [show (seamBentNeg a).2 = max (2 * a - 7) 0 from rfl, max_eq_left hc]
        linarith
  · intro a _ b _ hab
    have h := congrArg (fun q : ℝ × ℝ => q.1 + q.2) hab
    simp only [seamBentNeg_sum] at h
    linarith
  · intro p hp
    rw [mem_bentArcNeg] at hp
    rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · refine ⟨(p.1 + 7) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 2 * ((p.1 + 7) / 2) - 7 = p.1 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentNeg ((p.1 + 7) / 2)).1 = min (2 * ((p.1 + 7) / 2) - 7) 0 from rfl,
          hval, min_eq_left h1]
      · rw [show (seamBentNeg ((p.1 + 7) / 2)).2 = max (2 * ((p.1 + 7) / 2) - 7) 0 from rfl,
          hval, max_eq_right h1, h2]
    · refine ⟨(p.2 + 7) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 2 * ((p.2 + 7) / 2) - 7 = p.2 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentNeg ((p.2 + 7) / 2)).1 = min (2 * ((p.2 + 7) / 2) - 7) 0 from rfl,
          hval, min_eq_right h0, h1]
      · rw [show (seamBentNeg ((p.2 + 7) / 2)).2 = max (2 * ((p.2 + 7) / 2) - 7) 0 from rfl,
          hval, max_eq_left h0]

theorem isPLHomeomorphOn_seamBentPos :
    IsPLHomeomorphOn seamBentPos (Icc (1 : ℝ) 2) bentArcPos :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_seamBentPos.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron
      (subset_univ _)) bijOn_seamBentPos

theorem isPLHomeomorphOn_seamBentNeg :
    IsPLHomeomorphOn seamBentNeg (Icc (3 : ℝ) 4) bentArcNeg :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_seamBentNeg.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron
      (subset_univ _)) bijOn_seamBentNeg

theorem seamBentPos_one : seamBentPos 1 = ((1 : ℝ), (0 : ℝ)) := by
  have h : (3 : ℝ) - 2 * 1 = 1 := by norm_num
  simp only [seamBentPos, h]
  exact Prod.ext (max_eq_left zero_le_one) (min_eq_right zero_le_one)

theorem seamBentPos_two : seamBentPos 2 = ((0 : ℝ), (-1 : ℝ)) := by
  have h : (3 : ℝ) - 2 * 2 = -1 := by norm_num
  simp only [seamBentPos, h]
  exact Prod.ext (max_eq_right (by norm_num)) (min_eq_left (by norm_num))

theorem seamBentPos_mid : seamBentPos (3 / 2) = ((0 : ℝ), (0 : ℝ)) := by
  have h : (3 : ℝ) - 2 * (3 / 2) = 0 := by norm_num
  simp only [seamBentPos, h]
  exact Prod.ext (max_self 0) (min_self 0)

theorem seamBentNeg_three : seamBentNeg 3 = ((-1 : ℝ), (0 : ℝ)) := by
  have h : (2 : ℝ) * 3 - 7 = -1 := by norm_num
  simp only [seamBentNeg, h]
  exact Prod.ext (min_eq_left (by norm_num)) (max_eq_right (by norm_num))

theorem seamBentNeg_four : seamBentNeg 4 = ((0 : ℝ), (1 : ℝ)) := by
  have h : (2 : ℝ) * 4 - 7 = 1 := by norm_num
  simp only [seamBentNeg, h]
  exact Prod.ext (min_eq_right zero_le_one) (max_eq_left zero_le_one)

theorem seamBentNeg_mid : seamBentNeg (7 / 2) = ((0 : ℝ), (0 : ℝ)) := by
  have h : (2 : ℝ) * (7 / 2) - 7 = 0 := by norm_num
  simp only [seamBentNeg, h]
  exact Prod.ext (min_self 0) (max_self 0)

theorem seamBentPos_one_mem : seamBentPos 1 ∈ spliceSquareBoundary := by
  rw [seamBentPos_one]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩

theorem seamBentPos_two_mem : seamBentPos 2 ∈ spliceSquareBoundary := by
  rw [seamBentPos_two]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩

theorem seamBentNeg_three_mem : seamBentNeg 3 ∈ spliceSquareBoundary := by
  rw [seamBentNeg_three]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inl rfl⟩

theorem seamBentNeg_four_mem : seamBentNeg 4 ∈ spliceSquareBoundary := by
  rw [seamBentNeg_four]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩

noncomputable def seamSheetPos : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := Prod.map seamBentPos id

noncomputable def seamSheetNeg : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := Prod.map seamBentNeg id

theorem isPLHomeomorphOn_seamSheetPos :
    IsPLHomeomorphOn seamSheetPos (Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1) bentSheetPos :=
  isPLHomeomorphOn_seamBentPos.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

theorem isPLHomeomorphOn_seamSheetNeg :
    IsPLHomeomorphOn seamSheetNeg (Icc (3 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1) bentSheetNeg :=
  isPLHomeomorphOn_seamBentNeg.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

theorem seamArcX_lowFace {p : ℝ × ℝ} (h1 : p.1 ≤ 1) : seamArcX p = 2 - p.1 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_right (by linarith : p.1 - 1 ≤ 0), max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 2 ≤ 0), max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0)]
  ring

theorem seamArcX_bandPos {p : ℝ × ℝ} (h1 : 1 ≤ p.1) (h2 : p.1 ≤ 2) :
    seamArcX p = max (3 - 2 * p.1) 0 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 1),
    max_eq_right (by linarith : p.1 - 2 ≤ 0), max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0)]
  rcases le_total p.1 (3 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ 3 - 2 * p.1)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
      max_eq_right (by linarith : 3 - 2 * p.1 ≤ 0)]
    ring

theorem seamArcY_bandPos {p : ℝ × ℝ} (h2 : p.1 ≤ 2) :
    seamArcY p = min (3 - 2 * p.1) 0 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  rcases le_total p.1 (3 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
      min_eq_right (by linarith : (0 : ℝ) ≤ 3 - 2 * p.1)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
      min_eq_left (by linarith : 3 - 2 * p.1 ≤ 0)]
    ring

theorem seamArcY_connectorLow {p : ℝ × ℝ} (h1 : 2 ≤ p.1) (h2 : p.1 ≤ 5 / 2) :
    seamArcY p = 3 - 2 * p.1 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  ring

theorem seamArcX_connectorHigh {p : ℝ × ℝ} (h1 : 5 / 2 ≤ p.1) (h2 : p.1 ≤ 3) :
    seamArcX p = 2 * p.1 - 7 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 1),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2),
    max_eq_right (by linarith [h2] : p.1 - 7 / 2 ≤ 0)]
  ring

theorem seamArcX_bandNeg {p : ℝ × ℝ} (h1 : 3 ≤ p.1) :
    seamArcX p = min (2 * p.1 - 7) 0 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 1),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2)]
  rcases le_total p.1 (7 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
      min_eq_left (by linarith : 2 * p.1 - 7 ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 7 / 2),
      min_eq_right (by linarith : (0 : ℝ) ≤ 2 * p.1 - 7)]
    ring

theorem seamArcY_bandNeg {p : ℝ × ℝ} (h1 : 3 ≤ p.1) (h2 : p.1 ≤ 4) :
    seamArcY p = max (2 * p.1 - 7) 0 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  rcases le_total p.1 (7 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
      max_eq_right (by linarith : 2 * p.1 - 7 ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 7 / 2),
      max_eq_left (by linarith : (0 : ℝ) ≤ 2 * p.1 - 7)]
    ring

theorem seamArcY_highFace {p : ℝ × ℝ} (h1 : 4 ≤ p.1) :
    seamArcY p = p.1 - 3 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 7 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 4)]
  ring

theorem seamModelMap_eq_seamSheetPos {p : ℝ × ℝ} (h1 : 1 ≤ p.1) (h2 : p.1 ≤ 2) :
    seamModelMap p = seamSheetPos p :=
  Prod.ext (Prod.ext (seamArcX_bandPos h1 h2) (seamArcY_bandPos h2)) rfl

theorem seamModelMap_eq_seamSheetNeg {p : ℝ × ℝ} (h1 : 3 ≤ p.1) (h2 : p.1 ≤ 4) :
    seamModelMap p = seamSheetNeg p :=
  Prod.ext (Prod.ext (seamArcX_bandNeg h1) (seamArcY_bandNeg h1 h2)) rfl

theorem seamModelMap_notMem_spliceCylinder {p : ℝ × ℝ}
    (hpos : ¬(1 ≤ p.1 ∧ p.1 ≤ 2)) (hneg : ¬(3 ≤ p.1 ∧ p.1 ≤ 4)) :
    seamModelMap p ∉ spliceCylinder := by
  intro hmem
  have hsq : (seamArcX p, seamArcY p) ∈ spliceSquare := hmem.1
  rw [mem_spliceSquare] at hsq
  obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hsq
  rcases lt_or_ge p.1 1 with ha | ha
  · rw [seamArcX_lowFace (le_of_lt ha)] at hx2
    linarith
  rcases le_or_gt p.1 2 with hb | hb
  · exact hpos ⟨ha, hb⟩
  rcases lt_or_ge p.1 3 with hc | hc
  · rcases le_or_gt p.1 (5 / 2) with hd | hd
    · rw [seamArcY_connectorLow (le_of_lt hb) hd] at hy1
      linarith
    · rw [seamArcX_connectorHigh (le_of_lt hd) (le_of_lt hc)] at hx1
      linarith
  rcases le_or_gt p.1 4 with he | he
  · exact hneg ⟨hc, he⟩
  · rw [seamArcY_highFace (le_of_lt he)] at hy2
    linarith

def seamSourceRect : Set (ℝ × ℝ) := Icc (0 : ℝ) 5 ×ˢ Icc (0 : ℝ) 1

def seamRectPos : Set (ℝ × ℝ) := Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1

def seamRectNeg : Set (ℝ × ℝ) := Icc (3 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1

def seamFaceRect : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∪ Icc (2 : ℝ) 3 ×ˢ Icc (0 : ℝ) 1 ∪
    Icc (4 : ℝ) 5 ×ˢ Icc (0 : ℝ) 1

theorem isPolyhedron_seamSourceRect : IsPolyhedron seamSourceRect :=
  (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron

theorem isPolyhedron_seamRectPos : IsPolyhedron seamRectPos :=
  (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron

theorem isPolyhedron_seamRectNeg : IsPolyhedron seamRectNeg :=
  (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron

theorem isPolyhedron_seamFaceRect : IsPolyhedron seamFaceRect :=
  (((isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron.union
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron).union
      (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron)

theorem isPLBall_seamSourceRect : IsPLBall 2 seamSourceRect :=
  isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))

theorem seamRect_union : seamRectPos ∪ seamRectNeg ∪ seamFaceRect = seamSourceRect := by
  apply Subset.antisymm
  · intro p hp
    rcases hp with (h | h) | ((h | h) | h) <;>
      exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, h.2⟩
  · rintro p ⟨⟨h0, h5⟩, ht⟩
    rcases le_or_gt p.1 1 with h | h
    · exact Or.inr (Or.inl (Or.inl ⟨⟨h0, h⟩, ht⟩))
    rcases le_or_gt p.1 2 with h' | h'
    · exact Or.inl (Or.inl ⟨⟨le_of_lt h, h'⟩, ht⟩)
    rcases le_or_gt p.1 3 with h'' | h''
    · exact Or.inr (Or.inl (Or.inr ⟨⟨le_of_lt h', h''⟩, ht⟩))
    rcases le_or_gt p.1 4 with h''' | h'''
    · exact Or.inl (Or.inr ⟨⟨le_of_lt h'', h'''⟩, ht⟩)
    · exact Or.inr (Or.inr ⟨⟨le_of_lt h''', h5⟩, ht⟩)

noncomputable def seamWitnessCell : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) where
  domain := ⇑seamWitnessPlane '' seamSourceRect
  isPLBall_domain :=
    isPLBall_seamSourceRect.of_isPLHomeomorphOn
      (isPLHomeomorphOn_seamWitnessPlane isPolyhedron_seamSourceRect)
  toFun := ⇑spliceEmbedding ∘ seamModelMap ∘ ⇑seamWitnessPlane.symm
  isPLOn := by
    have hdom : IsPolyhedron (⇑seamWitnessPlane '' seamSourceRect) :=
      isPolyhedron_image_seamWitnessPlane isPolyhedron_seamSourceRect
    have hcomp : IsPiecewiseAffineOn (seamModelMap ∘ ⇑seamWitnessPlane.symm)
        (⇑seamWitnessPlane '' seamSourceRect) := by
      have h := isPiecewiseAffineOn_seamModelMap.comp
        (isPiecewiseAffineOn_seamWitnessPlaneSymm hdom)
      rwa [preimage_univ, inter_univ] at h
    have hpa : IsPiecewiseAffineOn
        (⇑spliceEmbedding ∘ seamModelMap ∘ ⇑seamWitnessPlane.symm)
        (⇑seamWitnessPlane '' seamSourceRect) :=
      (hcomp.affine_comp spliceEmbedding.toLinearMap.toAffineMap).congr fun _ _ => rfl
    exact fun x hx => ⟨hpa.continuousOn x hx, hpa x hx⟩

theorem seamWitnessCell_apply (x : EuclideanSpace ℝ (Fin 2)) :
    seamWitnessCell x = spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) := rfl

theorem seamWitnessCell_domain :
    seamWitnessCell.domain = ⇑seamWitnessPlane '' seamSourceRect := rfl

noncomputable def seamWitnessCoord (x : EuclideanSpace ℝ (Fin 2)) : Bool × ((ℝ × ℝ) × ℝ) :=
  if (seamWitnessPlane.symm x).1 ≤ 2 then (true, seamSheetPos (seamWitnessPlane.symm x))
  else (false, seamSheetNeg (seamWitnessPlane.symm x))

theorem seamWitnessCoord_of_mem_pos {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ ⇑seamWitnessPlane '' seamRectPos) :
    seamWitnessCoord x = (true, seamSheetPos (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  exact ite_eq_left h.1.2

theorem seamWitnessCoord_of_mem_neg {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ ⇑seamWitnessPlane '' seamRectNeg) :
    seamWitnessCoord x = (false, seamSheetNeg (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  exact ite_eq_right (by linarith [h.1.1] : ¬(seamWitnessPlane.symm x).1 ≤ 2)

theorem frontier_seamSourceRect :
    frontier seamSourceRect = seamSourceRect \ Ioo (0 : ℝ) 5 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [isPolyhedron_seamSourceRect.isClosed.frontier_eq, seamSourceRect, interior_prod_eq,
    interior_Icc, interior_Icc]

theorem frontier_seamWitnessCell_domain :
    frontier seamWitnessCell.domain = ⇑seamWitnessPlane '' frontier seamSourceRect :=
  (seamWitnessPlane.toHomeomorph.image_frontier seamSourceRect).symm

noncomputable def seamWitnessReading :
    PLCrossSeamReading (⇑spliceEmbedding) seamWitnessCell where
  coord := seamWitnessCoord
  sourcePos := ⇑seamWitnessPlane '' seamRectPos
  sourceNeg := ⇑seamWitnessPlane '' seamRectNeg
  face := ⇑seamWitnessPlane '' seamFaceRect
  isPLHomeomorphOn_pos :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm isPolyhedron_seamRectPos).trans
      isPLHomeomorphOn_seamSheetPos).congr fun x hx => by
        rw [seamWitnessCoord_of_mem_pos hx]
        rfl
  isPLHomeomorphOn_neg :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm isPolyhedron_seamRectNeg).trans
      isPLHomeomorphOn_seamSheetNeg).congr fun x hx => by
        rw [seamWitnessCoord_of_mem_neg hx]
        rfl
  coord_fst_pos := fun x hx => by rw [seamWitnessCoord_of_mem_pos hx]
  coord_fst_neg := fun x hx => by rw [seamWitnessCoord_of_mem_neg hx]
  source_eq := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · have h := mem_image_seamWitnessPlane.mp hx
        refine ⟨mem_image_seamWitnessPlane.mpr ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
          h.2⟩, ?_⟩
        refine ⟨seamModelMap (seamWitnessPlane.symm x), ?_, rfl⟩
        rw [seamModelMap_eq_seamSheetPos h.1.1 h.1.2]
        exact ⟨bentArcPos_subset_spliceSquare
          (isPLHomeomorphOn_seamBentPos.bijOn.mapsTo h.1), h.2⟩
      · have h := mem_image_seamWitnessPlane.mp hx
        refine ⟨mem_image_seamWitnessPlane.mpr ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
          h.2⟩, ?_⟩
        refine ⟨seamModelMap (seamWitnessPlane.symm x), ?_, rfl⟩
        rw [seamModelMap_eq_seamSheetNeg h.1.1 h.1.2]
        exact ⟨bentArcNeg_subset_spliceSquare
          (isPLHomeomorphOn_seamBentNeg.bijOn.mapsTo h.1), h.2⟩
    · rintro x ⟨hxd, hxc⟩
      have hd := mem_image_seamWitnessPlane.mp hxd
      have hcyl : seamModelMap (seamWitnessPlane.symm x) ∈ spliceCylinder := by
        obtain ⟨q, hq, hqe⟩ := hxc
        have : q = seamModelMap (seamWitnessPlane.symm x) := spliceEmbedding.injective hqe
        rwa [← this]
      by_cases hpos : 1 ≤ (seamWitnessPlane.symm x).1 ∧ (seamWitnessPlane.symm x).1 ≤ 2
      · exact Or.inl (mem_image_seamWitnessPlane.mpr ⟨hpos, hd.2⟩)
      by_cases hneg : 3 ≤ (seamWitnessPlane.symm x).1 ∧ (seamWitnessPlane.symm x).1 ≤ 4
      · exact Or.inr (mem_image_seamWitnessPlane.mpr ⟨hneg, hd.2⟩)
      · exact absurd hcyl (seamModelMap_notMem_spliceCylinder hpos hneg)
  isPolyhedron_face := isPolyhedron_image_seamWitnessPlane isPolyhedron_seamFaceRect
  union_eq := by
    rw [← image_union, ← image_union, seamRect_union]
    rfl
  reglued_eq := by
    rintro x (hx | hx)
    · have h := mem_image_seamWitnessPlane.mp hx
      rw [seamWitnessCell_apply]
      change spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) =
        spliceEmbedding (crossSeamInclude (seamWitnessCoord x))
      rw [seamWitnessCoord_of_mem_pos hx, seamModelMap_eq_seamSheetPos h.1.1 h.1.2]
      rfl
    · have h := mem_image_seamWitnessPlane.mp hx
      rw [seamWitnessCell_apply]
      change spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) =
        spliceEmbedding (crossSeamInclude (seamWitnessCoord x))
      rw [seamWitnessCoord_of_mem_neg hx, seamModelMap_eq_seamSheetNeg h.1.1 h.1.2]
      rfl
  overlap_lateral := by
    rintro x ⟨hx | hx, hf⟩
    · have h := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [seamWitnessCoord_of_mem_pos hx]
      refine ⟨?_, h.2⟩
      change seamBentPos (seamWitnessPlane.symm x).1 ∈ spliceSquareBoundary
      rcases hface with (⟨⟨-, hb⟩, -⟩ | ⟨⟨hb, -⟩, -⟩) | ⟨⟨hb, -⟩, -⟩
      · rw [le_antisymm hb h.1.1]
        exact seamBentPos_one_mem
      · rw [le_antisymm h.1.2 hb]
        exact seamBentPos_two_mem
      · exact absurd h.1.2 (by linarith)
    · have h := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [seamWitnessCoord_of_mem_neg hx]
      refine ⟨?_, h.2⟩
      change seamBentNeg (seamWitnessPlane.symm x).1 ∈ spliceSquareBoundary
      rcases hface with (⟨⟨-, hb⟩, -⟩ | ⟨⟨-, hb⟩, -⟩) | ⟨⟨hb, -⟩, -⟩
      · exact absurd h.1.1 (by linarith)
      · rw [le_antisymm hb h.1.1]
        exact seamBentNeg_three_mem
      · rw [le_antisymm h.1.2 hb]
        exact seamBentNeg_four_mem
  boundary_iff_end := by
    intro x hx
    have hband : 0 < (seamWitnessPlane.symm x).1 ∧ (seamWitnessPlane.symm x).1 < 5 ∧
        (seamWitnessPlane.symm x).2 ∈ Icc (0 : ℝ) 1 := by
      rcases hx with hx | hx
      · have h := mem_image_seamWitnessPlane.mp hx
        exact ⟨by linarith [h.1.1], by linarith [h.1.2], h.2⟩
      · have h := mem_image_seamWitnessPlane.mp hx
        exact ⟨by linarith [h.1.1], by linarith [h.1.2], h.2⟩
    have hcoord : (seamWitnessCoord x).2.2 = (seamWitnessPlane.symm x).2 := by
      rcases hx with hx | hx
      · rw [seamWitnessCoord_of_mem_pos hx]; rfl
      · rw [seamWitnessCoord_of_mem_neg hx]; rfl
    rw [hcoord, frontier_seamWitnessCell_domain, mem_image_seamWitnessPlane,
      frontier_seamSourceRect]
    constructor
    · rintro ⟨-, hout⟩
      by_contra hcon
      rw [not_or] at hcon
      exact hout ⟨⟨hband.1, hband.2.1⟩,
        lt_of_le_of_ne hband.2.2.1 (Ne.symm hcon.1),
        lt_of_le_of_ne hband.2.2.2 hcon.2⟩
    · intro hend
      refine ⟨⟨⟨le_of_lt hband.1, le_of_lt hband.2.1⟩, hband.2.2⟩, ?_⟩
      rintro ⟨-, ht1, ht2⟩
      rcases hend with h | h
      · rw [h] at ht1; exact absurd ht1 (lt_irrefl 0)
      · rw [h] at ht2; exact absurd ht2 (lt_irrefl 1)

theorem nonempty_plCrossSeamReading_seamWitnessCell :
    Nonempty (PLCrossSeamReading (⇑spliceEmbedding) seamWitnessCell) :=
  ⟨seamWitnessReading⟩

theorem seamWitnessReading_sourcePos_nonempty : seamWitnessReading.sourcePos.Nonempty :=
  seamWitnessReading.sourcePos_nonempty

theorem seamWitnessReading_sourceNeg_nonempty : seamWitnessReading.sourceNeg.Nonempty :=
  seamWitnessReading.sourceNeg_nonempty

theorem seamWitnessReading_face_nonempty : seamWitnessReading.face.Nonempty :=
  seamWitnessReading.face_nonempty

theorem seamWitnessReading_tubeSource_ssubset :
    seamWitnessReading.tubeSource ⊂ seamWitnessCell.domain :=
  seamWitnessReading.source_ssubset_domain

theorem seamWitnessPoint_pos_mem :
    seamWitnessPlane ((3 / 2 : ℝ), (0 : ℝ)) ∈ seamWitnessReading.sourcePos :=
  ⟨((3 / 2 : ℝ), (0 : ℝ)), ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, rfl⟩

theorem seamWitnessPoint_neg_mem :
    seamWitnessPlane ((7 / 2 : ℝ), (0 : ℝ)) ∈ seamWitnessReading.sourceNeg :=
  ⟨((7 / 2 : ℝ), (0 : ℝ)), ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, rfl⟩

theorem seamWitnessCell_apply_pos :
    seamWitnessCell (seamWitnessPlane ((3 / 2 : ℝ), (0 : ℝ))) =
      spliceEmbedding (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
  have hval : seamSheetPos ((3 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
    change (seamBentPos (3 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ))
    rw [seamBentPos_mid]
  rw [seamWitnessCell_apply, seamWitnessPlane.symm_apply_apply,
    seamModelMap_eq_seamSheetPos (by norm_num) (by norm_num), hval]

theorem seamWitnessCell_apply_neg :
    seamWitnessCell (seamWitnessPlane ((7 / 2 : ℝ), (0 : ℝ))) =
      spliceEmbedding (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
  have hval : seamSheetNeg ((7 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
    change (seamBentNeg (7 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ))
    rw [seamBentNeg_mid]
  rw [seamWitnessCell_apply, seamWitnessPlane.symm_apply_apply,
    seamModelMap_eq_seamSheetNeg (by norm_num) (by norm_num), hval]

theorem mem_doublePointSet_seamWitnessCell :
    spliceEmbedding (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈
      doublePointSet seamWitnessCell seamWitnessReading.tubeSource := by
  refine ⟨seamWitnessPlane ((3 / 2 : ℝ), (0 : ℝ)),
    seamWitnessReading.mem_tubeSource.mpr (Or.inl seamWitnessPoint_pos_mem),
    seamWitnessPlane ((7 / 2 : ℝ), (0 : ℝ)),
    seamWitnessReading.mem_tubeSource.mpr (Or.inr seamWitnessPoint_neg_mem), ?_,
    seamWitnessCell_apply_pos, seamWitnessCell_apply_neg⟩
  intro h
  have h' : ((3 / 2 : ℝ), (0 : ℝ)) = ((7 / 2 : ℝ), (0 : ℝ)) := seamWitnessPlane.injective h
  exact absurd (congrArg Prod.fst h') (by norm_num)

theorem seamWitnessCell_notInjOn :
    ¬InjOn seamWitnessCell seamWitnessCell.domain := by
  intro hinj
  have hpos := seamWitnessReading.source_subset_domain
    (seamWitnessReading.mem_tubeSource.mpr (Or.inl seamWitnessPoint_pos_mem))
  have hneg := seamWitnessReading.source_subset_domain
    (seamWitnessReading.mem_tubeSource.mpr (Or.inr seamWitnessPoint_neg_mem))
  have h := hinj hpos hneg (seamWitnessCell_apply_pos.trans seamWitnessCell_apply_neg.symm)
  have h' : ((3 / 2 : ℝ), (0 : ℝ)) = ((7 / 2 : ℝ), (0 : ℝ)) := seamWitnessPlane.injective h
  exact absurd (congrArg Prod.fst h') (by norm_num)

theorem doublePointSet_resolvedCell_seamWitness
    (C : PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding) :
    doublePointSet (seamWitnessReading.resolvedCell C) seamWitnessReading.tubeSource = ∅ :=
  seamWitnessReading.doublePointSet_resolvedCell C

end DifferentialGeometry.Topology.PiecewiseLinear
