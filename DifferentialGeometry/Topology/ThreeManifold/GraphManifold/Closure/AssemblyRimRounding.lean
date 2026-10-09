import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# Chapter-14 assembly, item L1: the ONE standard rim rounding function

The frozen interface V2 (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:86–107`; review item 2,
disposition D3) replaces the V1 structure `RimRounding` by one fixed function
`standardRimRounding (x, y) = roundedMin (1/4) x y` (defined in `AssemblyCertificateParts.lean`).
This file proves its four frozen facts and the band facts the later L1 steps use.

* `contDiff_standardRimRounding`: smooth (V2 verbatim).
* `fderiv_standardRimRounding_ne_zero`: the differential never vanishes. STRENGTHENING of the V2
  statement `standardRimRounding_regular`, whose hypothesis `standardRimRounding v = 0` is not
  needed: along the diagonal `(1, 1)` the function grows with slope one
  (`standardRimRounding_add_diag`). The verbatim V2 form is kept as an `example`.
* `standardRimRounding_nonpos_iff`, `standardRimRounding_nonneg_iff` (the point `v` is implicit, for
  the `explicitVarsOfIff` linter; otherwise V2 verbatim): outside the open unit box the
  ball–handle side `{ψ ≤ 0}` is the concave union `{y ≤ 0} ∪ {x ≤ 0}` and the circle-region side
  `{ψ ≥ 0}` is the quadrant (V2 verbatim).
* band facts: `{ψ ≤ 0}` contains `{y ≤ 0} ∪ {x ≤ 0}` everywhere, and its extra points (the fillet)
  lie in `{0 < x, 0 < y, x + y < 3/4}`, inside the open unit box.
* `rimBall`: the explicit endpoint label of rim `(k, b)` (V2 verbatim).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Topology.Manifold.CornerRounding
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-! ## Smoothness and regularity -/

theorem contDiff_standardRimRounding : ContDiff ℝ ∞ standardRimRounding :=
  contDiff_roundedMin rimRoundingWidth

theorem rimRoundingWidth_pos : 0 < rimRoundingWidth := by
  norm_num [rimRoundingWidth]

/-- Translation along the diagonal adds the translation length. -/
theorem standardRimRounding_add_diag (v : ℝ × ℝ) (t : ℝ) :
    standardRimRounding (v + (t, t)) = standardRimRounding v + t := by
  simp only [standardRimRounding, roundedMin, Prod.fst_add, Prod.snd_add]
  have h : v.1 + t - (v.2 + t) = v.1 - v.2 := by ring
  rw [h]
  ring

/-- The derivative of the standard rim rounding along the diagonal is one. -/
theorem fderiv_standardRimRounding_diag (v : ℝ × ℝ) :
    fderiv ℝ standardRimRounding v (1, 1) = 1 := by
  have hdiff : DifferentiableAt ℝ standardRimRounding v :=
    (contDiff_standardRimRounding.differentiable (by simp)) v
  have hline : HasDerivAt (fun t : ℝ => v + t • ((1 : ℝ), (1 : ℝ))) ((1 : ℝ), (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((1 : ℝ), (1 : ℝ))).const_add v
  have hcomp : HasDerivAt (fun t : ℝ => standardRimRounding (v + t • ((1 : ℝ), (1 : ℝ))))
      (fderiv ℝ standardRimRounding v (1, 1)) 0 := by
    have hd : HasFDerivAt standardRimRounding (fderiv ℝ standardRimRounding v)
        (v + (0 : ℝ) • ((1 : ℝ), (1 : ℝ))) := by
      simpa using hdiff.hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) hline
  have hfun : (fun t : ℝ => standardRimRounding (v + t • ((1 : ℝ), (1 : ℝ)))) =
      fun t => standardRimRounding v + t := by
    funext t
    have ht : t • ((1 : ℝ), (1 : ℝ)) = (t, t) := by simp
    rw [ht, standardRimRounding_add_diag]
  rw [hfun] at hcomp
  have hid : HasDerivAt (fun t : ℝ => standardRimRounding v + t) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add (standardRimRounding v)
  exact hcomp.unique hid

/-- **Regularity, strengthened.** The differential of `standardRimRounding` vanishes nowhere. -/
theorem fderiv_standardRimRounding_ne_zero (v : ℝ × ℝ) : fderiv ℝ standardRimRounding v ≠ 0 := by
  intro h
  have h1 := fderiv_standardRimRounding_diag v
  rw [h] at h1
  simp at h1

/-- The V2 statement `standardRimRounding_regular`, verbatim (its hypothesis is not needed). -/
example (v : ℝ × ℝ) (hv : standardRimRounding v = 0) :
    fderiv ℝ standardRimRounding v ≠ 0 :=
  (fun _ => fderiv_standardRimRounding_ne_zero v) hv

/-! ## Sign facts -/

theorem standardRimRounding_le_min (v : ℝ × ℝ) : standardRimRounding v ≤ min v.1 v.2 :=
  roundedMin_le_min rimRoundingWidth_pos v.1 v.2

theorem standardRimRounding_nonpos_of (v : ℝ × ℝ) (h : v.2 ≤ 0 ∨ v.1 ≤ 0) :
    standardRimRounding v ≤ 0 :=
  roundedMin_nonpos_of_nonpos rimRoundingWidth_pos h.symm

theorem nonneg_of_standardRimRounding_nonneg (v : ℝ × ℝ) (h : 0 ≤ standardRimRounding v) :
    0 ≤ v.1 ∧ 0 ≤ v.2 :=
  nonneg_of_roundedMin_nonneg rimRoundingWidth_pos h

/-- The fillet: a point of `{ψ ≤ 0}` off `{y ≤ 0} ∪ {x ≤ 0}` lies in the thin corner band. -/
theorem band_of_standardRimRounding_nonpos (v : ℝ × ℝ) (hx : 0 < v.1) (hy : 0 < v.2)
    (h : standardRimRounding v ≤ 0) : v.1 + v.2 < 3 / 4 := by
  have hb := (band_of_roundedMin_nonpos rimRoundingWidth_pos hx hy h).2
  norm_num [rimRoundingWidth] at hb
  linarith

/-- A removed point of the quadrant lies in the thin corner band. -/
theorem band_of_standardRimRounding_neg (v : ℝ × ℝ) (hx : 0 ≤ v.1) (hy : 0 ≤ v.2)
    (h : standardRimRounding v < 0) : v.1 + v.2 < 3 / 4 := by
  have hb := (band_of_roundedMin_neg rimRoundingWidth_pos hx hy h).2
  norm_num [rimRoundingWidth] at hb
  linarith

theorem mem_rimBox_of_band {v : ℝ × ℝ} (hx : 0 ≤ v.1) (hy : 0 ≤ v.2) (hs : v.1 + v.2 < 3 / 4) :
    v ∈ rimBox 1 := by
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg hx]
    linarith
  · rw [abs_of_nonneg hy]
    linarith

theorem rimBox_mono {r s : ℝ} (h : r ≤ s) : rimBox r ⊆ rimBox s :=
  fun _ hv => ⟨hv.1.trans_le h, hv.2.trans_le h⟩

theorem one_le_of_not_mem_rimBox_one {v : ℝ × ℝ} (hv : v ∉ rimBox 1) (hx : 0 ≤ v.1)
    (hy : 0 ≤ v.2) : 1 ≤ v.1 + v.2 := by
  by_contra hlt
  refine hv ⟨?_, ?_⟩
  · rw [abs_of_nonneg hx]
    linarith
  · rw [abs_of_nonneg hy]
    linarith

/-- V2 verbatim: outside the open unit box, the ball–handle side is the concave union. -/
theorem standardRimRounding_nonpos_iff {v : ℝ × ℝ} (hv : v ∉ rimBox 1) :
    standardRimRounding v ≤ 0 ↔ (v.2 ≤ 0 ∨ v.1 ≤ 0) := by
  refine ⟨fun h => ?_, standardRimRounding_nonpos_of v⟩
  by_contra hne
  simp only [not_or, not_le] at hne
  have hb := band_of_standardRimRounding_nonpos v hne.2 hne.1 h
  have h1 := one_le_of_not_mem_rimBox_one hv hne.2.le hne.1.le
  linarith

/-- V2 verbatim: outside the open unit box, the circle-region side is the quadrant. -/
theorem standardRimRounding_nonneg_iff {v : ℝ × ℝ} (hv : v ∉ rimBox 1) :
    0 ≤ standardRimRounding v ↔ (0 ≤ v.1 ∧ 0 ≤ v.2) := by
  refine ⟨nonneg_of_standardRimRounding_nonneg v, fun h => ?_⟩
  by_contra hneg
  have hb := band_of_standardRimRounding_neg v h.1 h.2 (not_le.mp hneg)
  have h1 := one_le_of_not_mem_rimBox_one hv h.1 h.2
  linarith

/-- The ball–handle side `{ψ ≤ 0}` is the concave union plus the fillet inside the unit box. -/
theorem standardRimRounding_nonpos_iff_or_fillet {v : ℝ × ℝ} :
    standardRimRounding v ≤ 0 ↔
      (v.2 ≤ 0 ∨ v.1 ≤ 0 ∨ (0 < v.1 ∧ 0 < v.2 ∧ v ∈ rimBox 1 ∧ standardRimRounding v ≤ 0)) := by
  constructor
  · intro h
    by_cases hy : v.2 ≤ 0
    · exact Or.inl hy
    by_cases hx : v.1 ≤ 0
    · exact Or.inr (Or.inl hx)
    simp only [not_le] at hx hy
    exact Or.inr (Or.inr ⟨hx, hy, mem_rimBox_of_band hx.le hy.le
      (band_of_standardRimRounding_nonpos v hx hy h), h⟩)
  · rintro (h | h | h)
    · exact standardRimRounding_nonpos_of v (Or.inl h)
    · exact standardRimRounding_nonpos_of v (Or.inr h)
    · exact h.2.2.2

/-! ## Rim labels -/

/-- V2 verbatim (review item 2, D3): the explicit endpoint label of rim `(k, b)`: the ball at the
end `b` of handle `k` (`k` at `b = false`, `k + 1 mod len` at `b = true`). -/
def rimBall (len : ℕ) (k : Fin len) (b : Bool) : Fin len :=
  if b then finRotate len k else k

@[simp] theorem rimBall_false (len : ℕ) (k : Fin len) : rimBall len k false = k := rfl

@[simp] theorem rimBall_true (len : ℕ) (k : Fin len) : rimBall len k true = finRotate len k := rfl

end GC.GraphManifold.Assembly
