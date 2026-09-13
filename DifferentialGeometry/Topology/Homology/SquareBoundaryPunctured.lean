import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Piecewise

noncomputable section

open Set ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

def squareBoundaryPuncture : Set Square := (Cube.boundary (Fin 2)) \ {squareNorthEast}

def squareBoundaryOriginPuncture : Set Square := (Cube.boundary (Fin 2)) \ {squareOrigin}

def squareBoundaryFirstCoord (s : ℝ) : ℝ := min 1 (max 0 (max (1 - s) (s - 2)))

def squareBoundarySecondCoord (s : ℝ) : ℝ := min 1 (max 0 (max (s - 3) (2 - s)))

theorem squareBoundaryFirstCoord_mem_unitInterval (s : ℝ) :
    squareBoundaryFirstCoord s ∈ unitInterval :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩

theorem squareBoundarySecondCoord_mem_unitInterval (s : ℝ) :
    squareBoundarySecondCoord s ∈ unitInterval :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩

def squareBoundaryCurve (s : ℝ) : Square :=
  ![⟨squareBoundaryFirstCoord s, squareBoundaryFirstCoord_mem_unitInterval s⟩,
    ⟨squareBoundarySecondCoord s, squareBoundarySecondCoord_mem_unitInterval s⟩]

@[simp] theorem squareBoundaryCurve_val_zero (s : ℝ) :
    ((squareBoundaryCurve s 0 : unitInterval) : ℝ) = squareBoundaryFirstCoord s := rfl

@[simp] theorem squareBoundaryCurve_val_one (s : ℝ) :
    ((squareBoundaryCurve s 1 : unitInterval) : ℝ) = squareBoundarySecondCoord s := rfl

theorem continuous_squareBoundaryFirstCoord : Continuous squareBoundaryFirstCoord := by
  unfold squareBoundaryFirstCoord
  fun_prop

theorem continuous_squareBoundarySecondCoord : Continuous squareBoundarySecondCoord := by
  unfold squareBoundarySecondCoord
  fun_prop

theorem continuous_squareBoundaryCurve : Continuous squareBoundaryCurve := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Continuous.subtype_mk continuous_squareBoundaryFirstCoord
      squareBoundaryFirstCoord_mem_unitInterval
  · exact Continuous.subtype_mk continuous_squareBoundarySecondCoord
      squareBoundarySecondCoord_mem_unitInterval

theorem squareBoundaryFirstCoord_of_nonneg_of_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    squareBoundaryFirstCoord s = 1 - s := by
  have hA : max (1 - s) (s - 2) = 1 - s := max_eq_left (by linarith)
  have hB : max 0 (1 - s) = 1 - s := max_eq_right (by linarith)
  rw [squareBoundaryFirstCoord, hA, hB]
  exact min_eq_right (by linarith)

theorem squareBoundaryFirstCoord_of_one_le_of_le_two {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    squareBoundaryFirstCoord s = 0 := by
  rw [squareBoundaryFirstCoord, max_eq_left (max_le (by linarith) (by linarith)),
    min_eq_right zero_le_one]

theorem squareBoundaryFirstCoord_of_two_le_of_le_three {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) :
    squareBoundaryFirstCoord s = s - 2 := by
  have hA : max (1 - s) (s - 2) = s - 2 := max_eq_right (by linarith)
  have hB : max 0 (s - 2) = s - 2 := max_eq_right (by linarith)
  rw [squareBoundaryFirstCoord, hA, hB]
  exact min_eq_right (by linarith)

theorem squareBoundaryFirstCoord_of_three_le {s : ℝ} (h3 : 3 ≤ s) :
    squareBoundaryFirstCoord s = 1 := by
  have hX : (1 : ℝ) ≤ max (1 - s) (s - 2) := le_trans (by linarith) (le_max_right _ _)
  exact min_eq_left (le_trans hX (le_max_right 0 _))

theorem squareBoundarySecondCoord_of_le_one {s : ℝ} (h1 : s ≤ 1) :
    squareBoundarySecondCoord s = 1 := by
  have hX : (1 : ℝ) ≤ max (s - 3) (2 - s) := le_trans (by linarith) (le_max_right _ _)
  exact min_eq_left (le_trans hX (le_max_right 0 _))

theorem squareBoundarySecondCoord_of_one_le_of_le_two {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    squareBoundarySecondCoord s = 2 - s := by
  have hA : max (s - 3) (2 - s) = 2 - s := max_eq_right (by linarith)
  have hB : max 0 (2 - s) = 2 - s := max_eq_right (by linarith)
  rw [squareBoundarySecondCoord, hA, hB]
  exact min_eq_right (by linarith)

theorem squareBoundarySecondCoord_of_two_le_of_le_three {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) :
    squareBoundarySecondCoord s = 0 := by
  rw [squareBoundarySecondCoord, max_eq_left (max_le (by linarith) (by linarith)),
    min_eq_right zero_le_one]

theorem squareBoundarySecondCoord_of_three_le_of_le_four {s : ℝ} (h3 : 3 ≤ s) (h4 : s ≤ 4) :
    squareBoundarySecondCoord s = s - 3 := by
  have hA : max (s - 3) (2 - s) = s - 3 := max_eq_left (by linarith)
  have hB : max 0 (s - 3) = s - 3 := max_eq_right (by linarith)
  rw [squareBoundarySecondCoord, hA, hB]
  exact min_eq_right (by linarith)

theorem squareBoundaryCurve_one_of_le_one {s : ℝ} (h1 : s ≤ 1) :
    squareBoundaryCurve s 1 = (1 : unitInterval) := by
  apply Subtype.ext
  rw [squareBoundaryCurve_val_one, squareBoundarySecondCoord_of_le_one h1]
  rfl

theorem squareBoundaryCurve_zero_of_one_le_of_le_two {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    squareBoundaryCurve s 0 = (0 : unitInterval) := by
  apply Subtype.ext
  rw [squareBoundaryCurve_val_zero, squareBoundaryFirstCoord_of_one_le_of_le_two h1 h2]
  rfl

theorem squareBoundaryCurve_one_of_two_le_of_le_three {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) :
    squareBoundaryCurve s 1 = (0 : unitInterval) := by
  apply Subtype.ext
  rw [squareBoundaryCurve_val_one, squareBoundarySecondCoord_of_two_le_of_le_three h2 h3]
  rfl

theorem squareBoundaryCurve_zero_of_three_le {s : ℝ} (h3 : 3 ≤ s) :
    squareBoundaryCurve s 0 = (1 : unitInterval) := by
  apply Subtype.ext
  rw [squareBoundaryCurve_val_zero, squareBoundaryFirstCoord_of_three_le h3]
  rfl

theorem squareBoundaryCurve_mem_boundary (s : ℝ) :
    squareBoundaryCurve s ∈ Cube.boundary (Fin 2) := by
  by_cases h1 : s ≤ 1
  · exact ⟨1, Or.inr (squareBoundaryCurve_one_of_le_one h1)⟩
  · by_cases h2 : s ≤ 2
    · exact ⟨0, Or.inl (squareBoundaryCurve_zero_of_one_le_of_le_two
        (le_of_lt (lt_of_not_ge h1)) h2)⟩
    · by_cases h3 : s ≤ 3
      · exact ⟨1, Or.inl (squareBoundaryCurve_one_of_two_le_of_le_three
          (le_of_lt (lt_of_not_ge h2)) h3)⟩
      · exact ⟨0, Or.inr (squareBoundaryCurve_zero_of_three_le (le_of_lt (lt_of_not_ge h3)))⟩

theorem squareBoundaryCurve_ne_northEast (s : ℝ) (hs : s ∈ Ioo 0 4) :
    squareBoundaryCurve s ≠ squareNorthEast := by
  intro h
  have h0 : squareBoundaryFirstCoord s = 1 := by
    have hc := congrArg (fun p : Square => ((p 0 : unitInterval) : ℝ)) h
    simpa [squareNorthEast, squarePoint] using hc
  have h1 : squareBoundarySecondCoord s = 1 := by
    have hc := congrArg (fun p : Square => ((p 1 : unitInterval) : ℝ)) h
    simpa [squareNorthEast, squarePoint] using hc
  by_cases hle : s ≤ 1
  · rw [squareBoundaryFirstCoord_of_nonneg_of_le_one (le_of_lt hs.1) hle] at h0
    linarith [hs.1]
  · by_cases hle2 : s ≤ 2
    · rw [squareBoundaryFirstCoord_of_one_le_of_le_two (le_of_lt (lt_of_not_ge hle)) hle2] at h0
      linarith
    · by_cases hle3 : s ≤ 3
      · rw [squareBoundarySecondCoord_of_two_le_of_le_three
          (le_of_lt (lt_of_not_ge hle2)) hle3] at h1
        linarith
      · rw [squareBoundarySecondCoord_of_three_le_of_le_four (le_of_lt (lt_of_not_ge hle3))
          (le_of_lt hs.2)] at h1
        linarith [hs.2]

theorem squareBoundaryCurve_mem_puncture (s : ℝ) (hs : s ∈ Ioo 0 4) :
    squareBoundaryCurve s ∈ squareBoundaryPuncture :=
  ⟨squareBoundaryCurve_mem_boundary s, squareBoundaryCurve_ne_northEast s hs⟩

theorem squareEast_mem_boundary : squareEast ∈ Cube.boundary (Fin 2) :=
  ⟨1, Or.inl rfl⟩

theorem squareEast_ne_northEast : squareEast ≠ squareNorthEast := by
  intro h
  have hc := congrArg (fun p : Square => ((p 1 : unitInterval) : ℝ)) h
  simp [squareEast, squareNorthEast, squarePoint] at hc

theorem squareBoundaryPuncture_nonempty : squareBoundaryPuncture.Nonempty :=
  ⟨squareEast, squareEast_mem_boundary, squareEast_ne_northEast⟩

theorem squarePoint_eq_northEast_of {p : Square}
    (h0 : ((p 0 : unitInterval) : ℝ) = 1) (h1 : ((p 1 : unitInterval) : ℝ) = 1) :
    p = squareNorthEast := by
  funext i
  fin_cases i
  · apply Subtype.ext
    simpa [squareNorthEast, squarePoint] using h0
  · apply Subtype.ext
    simpa [squareNorthEast, squarePoint] using h1

def squareBoundaryArclength (p : Square) : ℝ :=
  if ((p 1 : unitInterval) : ℝ) = 1 then 1 - ((p 0 : unitInterval) : ℝ)
  else if ((p 0 : unitInterval) : ℝ) = 0 then 2 - ((p 1 : unitInterval) : ℝ)
  else if ((p 1 : unitInterval) : ℝ) = 0 then 2 + ((p 0 : unitInterval) : ℝ)
  else 3 + ((p 1 : unitInterval) : ℝ)

theorem squareBoundaryArclength_mem_Ioo {p : Square} (hp : p ∈ squareBoundaryPuncture) :
    squareBoundaryArclength p ∈ Ioo (0 : ℝ) 4 := by
  have hx0 : 0 ≤ ((p 0 : unitInterval) : ℝ) := (p 0).property.1
  have hx1 : ((p 0 : unitInterval) : ℝ) ≤ 1 := (p 0).property.2
  have hy0 : 0 ≤ ((p 1 : unitInterval) : ℝ) := (p 1).property.1
  have hy1 : ((p 1 : unitInterval) : ℝ) ≤ 1 := (p 1).property.2
  by_cases hTy : ((p 1 : unitInterval) : ℝ) = 1
  · rw [squareBoundaryArclength, if_pos hTy]
    have hxlt : ((p 0 : unitInterval) : ℝ) < 1 := by
      rcases lt_or_eq_of_le hx1 with h | h
      · exact h
      · exact absurd (squarePoint_eq_northEast_of h hTy) hp.2
    exact ⟨by linarith, by linarith⟩
  · by_cases hLx : ((p 0 : unitInterval) : ℝ) = 0
    · rw [squareBoundaryArclength, if_neg hTy, if_pos hLx]
      exact ⟨by linarith, by linarith⟩
    · by_cases hBy : ((p 1 : unitInterval) : ℝ) = 0
      · rw [squareBoundaryArclength, if_neg hTy, if_neg hLx, if_pos hBy]
        exact ⟨by linarith, by linarith⟩
      · rw [squareBoundaryArclength, if_neg hTy, if_neg hLx, if_neg hBy]
        exact ⟨by linarith, by have h := lt_of_le_of_ne hy1 hTy; linarith⟩

theorem squareBoundaryArclength_curve (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 4) :
    squareBoundaryArclength (squareBoundaryCurve s) = s := by
  have hs0 : 0 < s := hs.1
  have hs4 : s < 4 := hs.2
  by_cases h1 : s ≤ 1
  · rw [squareBoundaryArclength, if_pos (by
      rw [squareBoundaryCurve_val_one, squareBoundarySecondCoord_of_le_one h1])]
    rw [squareBoundaryCurve_val_zero,
      squareBoundaryFirstCoord_of_nonneg_of_le_one (le_of_lt hs0) h1]
    ring
  · have h1' : 1 < s := lt_of_not_ge h1
    by_cases h2 : s ≤ 2
    · rw [squareBoundaryArclength,
        if_neg (by
          intro hh
          rw [squareBoundaryCurve_val_one,
            squareBoundarySecondCoord_of_one_le_of_le_two (le_of_lt h1') h2] at hh
          linarith),
        if_pos (by rw [squareBoundaryCurve_val_zero,
          squareBoundaryFirstCoord_of_one_le_of_le_two (le_of_lt h1') h2])]
      rw [squareBoundaryCurve_val_one,
        squareBoundarySecondCoord_of_one_le_of_le_two (le_of_lt h1') h2]
      ring
    · have h2' : 2 < s := lt_of_not_ge h2
      by_cases h3 : s ≤ 3
      · rw [squareBoundaryArclength,
          if_neg (by
            intro hh
            rw [squareBoundaryCurve_val_one,
              squareBoundarySecondCoord_of_two_le_of_le_three (le_of_lt h2') h3] at hh
            linarith)]
        by_cases hx0 : ((squareBoundaryCurve s 0 : unitInterval) : ℝ) = 0
        · rw [if_pos hx0]
          have hcoord : squareBoundaryFirstCoord s = 0 := by
            rw [← squareBoundaryCurve_val_zero]
            exact hx0
          have hs2 : s = 2 := by
            have h := squareBoundaryFirstCoord_of_two_le_of_le_three (le_of_lt h2') h3
            rw [hcoord] at h
            linarith
          have hval : squareBoundarySecondCoord 2 = 0 :=
            squareBoundarySecondCoord_of_two_le_of_le_three le_rfl (by norm_num)
          rw [hs2, squareBoundaryCurve_val_one, hval]
          norm_num
        · rw [if_neg hx0, if_pos (by rw [squareBoundaryCurve_val_one,
            squareBoundarySecondCoord_of_two_le_of_le_three (le_of_lt h2') h3])]
          rw [squareBoundaryCurve_val_zero,
            squareBoundaryFirstCoord_of_two_le_of_le_three (le_of_lt h2') h3]
          ring
      · have h3' : 3 < s := lt_of_not_ge h3
        rw [squareBoundaryArclength,
          if_neg (by
            intro hh
            rw [squareBoundaryCurve_val_one,
              squareBoundarySecondCoord_of_three_le_of_le_four (le_of_lt h3') (le_of_lt hs4)] at hh
            linarith),
          if_neg (by
            intro hh
            rw [squareBoundaryCurve_val_zero,
              squareBoundaryFirstCoord_of_three_le (le_of_lt h3')] at hh
            linarith),
          if_neg (by
            intro hh
            rw [squareBoundaryCurve_val_one,
              squareBoundarySecondCoord_of_three_le_of_le_four (le_of_lt h3') (le_of_lt hs4)] at hh
            linarith)]
        rw [squareBoundaryCurve_val_one,
          squareBoundarySecondCoord_of_three_le_of_le_four (le_of_lt h3') (le_of_lt hs4)]
        ring

theorem squareBoundaryCurve_arclength {p : Square} (hp : p ∈ squareBoundaryPuncture) :
    squareBoundaryCurve (squareBoundaryArclength p) = p := by
  have hx0 : 0 ≤ ((p 0 : unitInterval) : ℝ) := (p 0).property.1
  have hx1 : ((p 0 : unitInterval) : ℝ) ≤ 1 := (p 0).property.2
  have hy0 : 0 ≤ ((p 1 : unitInterval) : ℝ) := (p 1).property.1
  have hy1 : ((p 1 : unitInterval) : ℝ) ≤ 1 := (p 1).property.2
  by_cases hTy : ((p 1 : unitInterval) : ℝ) = 1
  · rw [squareBoundaryArclength, if_pos hTy]
    have h0 : squareBoundaryCurve (1 - ((p 0 : unitInterval) : ℝ)) 0 = p 0 := by
      apply Subtype.ext
      rw [squareBoundaryCurve_val_zero,
        squareBoundaryFirstCoord_of_nonneg_of_le_one (by linarith) (by linarith)]
      ring
    have h1 : squareBoundaryCurve (1 - ((p 0 : unitInterval) : ℝ)) 1 = p 1 := by
      apply Subtype.ext
      rw [squareBoundaryCurve_val_one, squareBoundarySecondCoord_of_le_one (by linarith)]
      exact hTy.symm
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · by_cases hLx : ((p 0 : unitInterval) : ℝ) = 0
    · rw [squareBoundaryArclength, if_neg hTy, if_pos hLx]
      have h0 : squareBoundaryCurve (2 - ((p 1 : unitInterval) : ℝ)) 0 = p 0 := by
        apply Subtype.ext
        rw [squareBoundaryCurve_val_zero,
          squareBoundaryFirstCoord_of_one_le_of_le_two (by linarith) (by linarith)]
        exact hLx.symm
      have h1 : squareBoundaryCurve (2 - ((p 1 : unitInterval) : ℝ)) 1 = p 1 := by
        apply Subtype.ext
        rw [squareBoundaryCurve_val_one,
          squareBoundarySecondCoord_of_one_le_of_le_two (by linarith) (by linarith)]
        ring
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · by_cases hBy : ((p 1 : unitInterval) : ℝ) = 0
      · rw [squareBoundaryArclength, if_neg hTy, if_neg hLx, if_pos hBy]
        have h0 : squareBoundaryCurve (2 + ((p 0 : unitInterval) : ℝ)) 0 = p 0 := by
          apply Subtype.ext
          rw [squareBoundaryCurve_val_zero,
            squareBoundaryFirstCoord_of_two_le_of_le_three (by linarith) (by linarith)]
          ring
        have h1 : squareBoundaryCurve (2 + ((p 0 : unitInterval) : ℝ)) 1 = p 1 := by
          apply Subtype.ext
          rw [squareBoundaryCurve_val_one,
            squareBoundarySecondCoord_of_two_le_of_le_three (by linarith) (by linarith)]
          exact hBy.symm
        funext i
        fin_cases i
        · exact h0
        · exact h1
      · have hx1' : ((p 0 : unitInterval) : ℝ) = 1 := by
          obtain ⟨i, hi⟩ := hp.1
          fin_cases i
          · rcases hi with hi | hi
            · exact absurd (congrArg (fun t : unitInterval => (t : ℝ)) hi) hLx
            · exact congrArg (fun t : unitInterval => (t : ℝ)) hi
          · rcases hi with hi | hi
            · exact absurd (congrArg (fun t : unitInterval => (t : ℝ)) hi) hBy
            · exact absurd (congrArg (fun t : unitInterval => (t : ℝ)) hi) hTy
        rw [squareBoundaryArclength, if_neg hTy, if_neg hLx, if_neg hBy]
        have h0 : squareBoundaryCurve (3 + ((p 1 : unitInterval) : ℝ)) 0 = p 0 := by
          apply Subtype.ext
          rw [squareBoundaryCurve_val_zero, squareBoundaryFirstCoord_of_three_le (by linarith)]
          exact hx1'.symm
        have h1 : squareBoundaryCurve (3 + ((p 1 : unitInterval) : ℝ)) 1 = p 1 := by
          apply Subtype.ext
          rw [squareBoundaryCurve_val_one,
            squareBoundarySecondCoord_of_three_le_of_le_four (by linarith) (by linarith)]
          ring
        funext i
        fin_cases i
        · exact h0
        · exact h1

theorem continuous_squareBoundaryArclength :
    Continuous fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val := by
  have hT : IsClosed {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 1} :=
    isClosed_eq (continuous_subtype_val.comp
      ((continuous_apply 1).comp continuous_subtype_val)) continuous_const
  have hL : IsClosed {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 0} :=
    isClosed_eq (continuous_subtype_val.comp
      ((continuous_apply 0).comp continuous_subtype_val)) continuous_const
  have hB : IsClosed {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 0} :=
    isClosed_eq (continuous_subtype_val.comp
      ((continuous_apply 1).comp continuous_subtype_val)) continuous_const
  have hR : IsClosed {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 1} :=
    isClosed_eq (continuous_subtype_val.comp
      ((continuous_apply 0).comp continuous_subtype_val)) continuous_const
  have hTcont : ContinuousOn (fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val)
      {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 1} :=
    have hg : Continuous fun p : ↥squareBoundaryPuncture => 1 - ((p.val 0 : unitInterval) : ℝ) :=
      continuous_const.sub (continuous_subtype_val.comp
        ((continuous_apply 0).comp continuous_subtype_val))
    hg.continuousOn.congr fun p hp => by
      have hp' : ((p.val 1 : unitInterval) : ℝ) = 1 := hp
      simp only [squareBoundaryArclength, if_pos hp']
  have hLcont : ContinuousOn (fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val)
      {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 0} :=
    have hg : Continuous fun p : ↥squareBoundaryPuncture => 2 - ((p.val 1 : unitInterval) : ℝ) :=
      continuous_const.sub (continuous_subtype_val.comp
        ((continuous_apply 1).comp continuous_subtype_val))
    hg.continuousOn.congr fun p hp => by
      have hp' : ((p.val 0 : unitInterval) : ℝ) = 0 := hp
      by_cases hy : ((p.val 1 : unitInterval) : ℝ) = 1
      · simp only [squareBoundaryArclength, if_pos hy]
        rw [hp', hy]
        norm_num
      · simp only [squareBoundaryArclength, if_neg hy, if_pos hp']
  have hBcont : ContinuousOn (fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val)
      {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 0} :=
    have hg : Continuous fun p : ↥squareBoundaryPuncture => 2 + ((p.val 0 : unitInterval) : ℝ) :=
      continuous_const.add (continuous_subtype_val.comp
        ((continuous_apply 0).comp continuous_subtype_val))
    hg.continuousOn.congr fun p hp => by
      have hp' : ((p.val 1 : unitInterval) : ℝ) = 0 := hp
      have hy : ((p.val 1 : unitInterval) : ℝ) ≠ 1 := by rw [hp']; norm_num
      by_cases hx : ((p.val 0 : unitInterval) : ℝ) = 0
      · simp only [squareBoundaryArclength, if_neg hy, if_pos hx]
        rw [hp', hx]
        norm_num
      · simp only [squareBoundaryArclength, if_neg hy, if_neg hx, if_pos hp']
  have hRcont : ContinuousOn (fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val)
      {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 1} :=
    have hg : Continuous fun p : ↥squareBoundaryPuncture => 3 + ((p.val 1 : unitInterval) : ℝ) :=
      continuous_const.add (continuous_subtype_val.comp
        ((continuous_apply 1).comp continuous_subtype_val))
    hg.continuousOn.congr fun p hp => by
      have hp' : ((p.val 0 : unitInterval) : ℝ) = 1 := hp
      have hx : ((p.val 0 : unitInterval) : ℝ) ≠ 0 := by rw [hp']; norm_num
      have hy : ((p.val 1 : unitInterval) : ℝ) ≠ 1 := by
        intro h
        exact p.property.2 (squarePoint_eq_northEast_of hp' h)
      by_cases hb : ((p.val 1 : unitInterval) : ℝ) = 0
      · simp only [squareBoundaryArclength, if_neg hy, if_neg hx, if_pos hb]
        rw [hp', hb]
        norm_num
      · simp only [squareBoundaryArclength, if_neg hy, if_neg hx, if_neg hb]
  have hTL : ContinuousOn (fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val)
      ({p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 1} ∪
        {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 0}) :=
    (continuousOn_union_iff_of_isClosed hT hL).mpr ⟨hTcont, hLcont⟩
  have hTLB : ContinuousOn (fun p : ↥squareBoundaryPuncture => squareBoundaryArclength p.val)
      ({p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 1} ∪
        {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 0} ∪
        {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 0}) :=
    (continuousOn_union_iff_of_isClosed (hT.union hL) hB).mpr ⟨hTL, hBcont⟩
  have hcover : {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 1} ∪
      {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 0} ∪
      {p : ↥squareBoundaryPuncture | ((p.val 1 : unitInterval) : ℝ) = 0} ∪
      {p : ↥squareBoundaryPuncture | ((p.val 0 : unitInterval) : ℝ) = 1} = univ := by
    ext p
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨i, hi⟩ := p.property.1
    fin_cases i
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl (Or.inr (congrArg (fun t : unitInterval => (t : ℝ)) hi)))
      · exact Or.inr (congrArg (fun t : unitInterval => (t : ℝ)) hi)
    · rcases hi with hi | hi
      · exact Or.inl (Or.inr (congrArg (fun t : unitInterval => (t : ℝ)) hi))
      · exact Or.inl (Or.inl (Or.inl (congrArg (fun t : unitInterval => (t : ℝ)) hi)))
  rw [← continuousOn_univ, ← hcover]
  exact (continuousOn_union_iff_of_isClosed ((hT.union hL).union hB) hR).mpr
    ⟨hTLB, hRcont⟩

def squareBoundaryPunctureHomeomorph :
    ↥squareBoundaryPuncture ≃ₜ ↥(Ioo (0 : ℝ) 4) where
  toFun p := ⟨squareBoundaryArclength p.val, squareBoundaryArclength_mem_Ioo p.property⟩
  invFun s := ⟨squareBoundaryCurve s.val, squareBoundaryCurve_mem_puncture s.val s.property⟩
  left_inv p := Subtype.ext (squareBoundaryCurve_arclength p.property)
  right_inv s := Subtype.ext (squareBoundaryArclength_curve s.val s.property)
  continuous_toFun := Continuous.subtype_mk continuous_squareBoundaryArclength _
  continuous_invFun := Continuous.subtype_mk
    (continuous_squareBoundaryCurve.comp continuous_subtype_val) _

theorem squareBoundaryPuncture_contractible : ContractibleSpace ↥squareBoundaryPuncture :=
  haveI : ContractibleSpace ↥(Ioo (0 : ℝ) 4) :=
    Convex.contractibleSpace (convex_Ioo (0 : ℝ) 4) ⟨2, by norm_num⟩
  squareBoundaryPunctureHomeomorph.contractibleSpace

theorem subsingleton_integralSingularHomology_squareBoundaryPuncture (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (integralSingularHomology n ↥squareBoundaryPuncture) :=
  haveI := squareBoundaryPuncture_contractible
  integralSingularHomology_subsingleton_of_contractible n hn _

theorem squareReflectCoord_mem_unitInterval (x : unitInterval) :
    1 - (x : ℝ) ∈ unitInterval :=
  ⟨by linarith [x.property.2], by linarith [x.property.1]⟩

def squareReflectCoord (x : unitInterval) : unitInterval :=
  ⟨1 - (x : ℝ), squareReflectCoord_mem_unitInterval x⟩

theorem squareReflectCoord_val (x : unitInterval) :
    ((squareReflectCoord x : unitInterval) : ℝ) = 1 - (x : ℝ) := rfl

theorem continuous_squareReflectCoord : Continuous squareReflectCoord :=
  Continuous.subtype_mk (f := fun x : unitInterval => 1 - (x : ℝ)) (by fun_prop)
    squareReflectCoord_mem_unitInterval

def squareReflect (p : Square) : Square := fun i => squareReflectCoord (p i)

theorem continuous_squareReflect : Continuous squareReflect :=
  continuous_pi fun i => continuous_squareReflectCoord.comp (continuous_apply i)

theorem squareReflect_involutive (p : Square) : squareReflect (squareReflect p) = p := by
  funext i
  apply Subtype.ext
  simp only [squareReflect, squareReflectCoord_val]
  ring

theorem squareReflect_mem_boundary_iff (p : Square) :
    squareReflect p ∈ Cube.boundary (Fin 2) ↔ p ∈ Cube.boundary (Fin 2) := by
  have hc (i : Fin 2) :
      ((squareReflect p i : unitInterval) : ℝ) = 1 - ((p i : unitInterval) : ℝ) := by
    simp only [squareReflect, squareReflectCoord_val]
  constructor
  · rintro ⟨i, hi | hi⟩
    · refine ⟨i, Or.inr ?_⟩
      have h : ((squareReflect p i : unitInterval) : ℝ) = 0 := by rw [hi]; rfl
      rw [hc i] at h
      refine Subtype.ext ?_
      change ((p i : unitInterval) : ℝ) = 1
      linarith
    · refine ⟨i, Or.inl ?_⟩
      have h : ((squareReflect p i : unitInterval) : ℝ) = 1 := by rw [hi]; rfl
      rw [hc i] at h
      refine Subtype.ext ?_
      change ((p i : unitInterval) : ℝ) = 0
      linarith
  · rintro ⟨i, hi | hi⟩
    · refine ⟨i, Or.inr ?_⟩
      apply Subtype.ext
      rw [hc i]
      have h : ((p i : unitInterval) : ℝ) = 0 := by rw [hi]; rfl
      change 1 - ((p i : unitInterval) : ℝ) = 1
      linarith
    · refine ⟨i, Or.inl ?_⟩
      apply Subtype.ext
      rw [hc i]
      have h : ((p i : unitInterval) : ℝ) = 1 := by rw [hi]; rfl
      change 1 - ((p i : unitInterval) : ℝ) = 0
      linarith

theorem squareReflect_northEast : squareReflect squareNorthEast = squareOrigin := by
  funext i
  fin_cases i
  · apply Subtype.ext
    simp only [squareReflect, squareReflectCoord_val, squareNorthEast, squareOrigin,
      squarePoint]
    norm_num
  · apply Subtype.ext
    simp only [squareReflect, squareReflectCoord_val, squareNorthEast, squareOrigin,
      squarePoint]
    norm_num

theorem squareReflect_origin : squareReflect squareOrigin = squareNorthEast := by
  funext i
  fin_cases i
  · apply Subtype.ext
    simp only [squareReflect, squareReflectCoord_val, squareNorthEast, squareOrigin,
      squarePoint]
    norm_num
  · apply Subtype.ext
    simp only [squareReflect, squareReflectCoord_val, squareNorthEast, squareOrigin,
      squarePoint]
    norm_num

theorem squareReflect_mem_originPuncture_iff (p : Square) :
    squareReflect p ∈ squareBoundaryOriginPuncture ↔ p ∈ squareBoundaryPuncture := by
  constructor
  · rintro ⟨hb, hne⟩
    refine ⟨(squareReflect_mem_boundary_iff p).mp hb, ?_⟩
    intro hp
    have hne' : squareReflect p ≠ squareOrigin := hne
    exact hne' (by rw [hp, squareReflect_northEast])
  · rintro ⟨hb, hne⟩
    refine ⟨(squareReflect_mem_boundary_iff p).mpr hb, ?_⟩
    intro hp
    have hne' : p ≠ squareNorthEast := hne
    exact hne' (by rw [← squareReflect_involutive p, hp, squareReflect_origin])

theorem squareReflect_mem_puncture_iff (p : Square) :
    squareReflect p ∈ squareBoundaryPuncture ↔ p ∈ squareBoundaryOriginPuncture := by
  have h := squareReflect_mem_originPuncture_iff (squareReflect p)
  rw [squareReflect_involutive p] at h
  exact h.symm

def squareBoundaryPunctureReflectHomeomorph :
    ↥squareBoundaryPuncture ≃ₜ ↥squareBoundaryOriginPuncture where
  toFun p := ⟨squareReflect p.val, (squareReflect_mem_originPuncture_iff p.val).mpr p.property⟩
  invFun p := ⟨squareReflect p.val, (squareReflect_mem_puncture_iff p.val).mpr p.property⟩
  left_inv p := Subtype.ext (squareReflect_involutive p.val)
  right_inv p := Subtype.ext (squareReflect_involutive p.val)
  continuous_toFun := Continuous.subtype_mk
    (continuous_squareReflect.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_squareReflect.comp continuous_subtype_val) _

theorem squareBoundaryOriginPuncture_contractible :
    ContractibleSpace ↥squareBoundaryOriginPuncture :=
  haveI := squareBoundaryPuncture_contractible
  squareBoundaryPunctureReflectHomeomorph.symm.contractibleSpace

theorem subsingleton_integralSingularHomology_squareBoundaryOriginPuncture (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (integralSingularHomology n ↥squareBoundaryOriginPuncture) :=
  haveI := squareBoundaryOriginPuncture_contractible
  integralSingularHomology_subsingleton_of_contractible n hn _

theorem squareNorth_mem_boundary : squareNorth ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inl rfl⟩

theorem squareNorth_ne_origin : squareNorth ≠ squareOrigin := by
  intro h
  have hc := congrArg (fun p : Square => ((p 1 : unitInterval) : ℝ)) h
  simp [squareNorth, squareOrigin, squarePoint] at hc

theorem squareNorthEast_ne_origin : squareNorthEast ≠ squareOrigin := by
  intro h
  have hc := congrArg (fun p : Square => ((p 1 : unitInterval) : ℝ)) h
  simp [squareNorthEast, squareOrigin, squarePoint] at hc

theorem squareBoundaryOriginPuncture_nonempty : squareBoundaryOriginPuncture.Nonempty :=
  ⟨squareNorth, squareNorth_mem_boundary, squareNorth_ne_origin⟩

theorem squareBoundary_eq_punctures_union :
    squareBoundaryPuncture ∪ squareBoundaryOriginPuncture = Cube.boundary (Fin 2) := by
  ext p
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hx
    by_cases h : p = squareNorthEast
    · subst h
      exact Or.inr ⟨hx, squareNorthEast_ne_origin⟩
    · exact Or.inl ⟨hx, h⟩

end DifferentialGeometry.Topology
