import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import Mathlib.Topology.Homotopy.Contractible

/-!
# Circle bundles over planar bases

Chapter 6, lane MD5 of the P1 Morse-decomposition plan
(`docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md`, §3, with the errata
after review 8: the row sweep is given as an explicit finite relative open cover that handles the
tangency heights `Im z = ±1/2`, with proved simple connectivity of every overlap piece).

(1) Contractibility criteria. A set `S ⊆ ℂ` whose vertical segments to a continuous spine
`x ↦ x + s(x) i` lie in `S`, and whose spine over the segment from `re z` to `x₀` lies in `S`, is
contractible (`contractibleSpace_of_verticalSlices`); the same with `re` and `im` exchanged
(`contractibleSpace_of_horizontalSlices`, through `swapReIm z = i z̄`). An open box
`planarBox x₁ x₂ y₁ y₂` minus the open disc of radius `1/2` about `a + b i` (`holeOut a b`) is
contractible when nonempty if the box lies above the centre line and either clears the disc or is
narrower than the chord at its top height (`contractibleSpace_planarBox_inter_holeOut`, spine
`(max y₁ (holeHeight a b x) + y₂) / 2`), and likewise below, right or left of the centre
(`_below`, `_right`, `_left`, by `conj`, `swapReIm` and the reflection `reflectAt`).

(2) The grid. For `h = gridH n = 1/(8n)` the grid points are `gridPt n i = (i + 3/4) h`; the
centres `0`, `±3/2` of the holes of `planarModel k` and the tangency heights `0`, `±1/2` lie in
`hℤ`, so they keep the margin `h/4` from every grid edge. Every `gridBox n i j` (abscissae
`(s - h/2, s)`, ordinates `(t - h/2, t + h)`, `s = gridPt n i`, `t = gridPt n j`) meets
`planarModel k` in the empty set or a contractible set
(`contractibleSpace_gridBox_inter_planarModel`: a box meeting a hole lies within distance `1` of its
centre, hence inside the disc and away from the other hole, and the four position cases are
decided by `i, j` against the integer centre index). A horizontal overlap strip
`(t - h/2, t)` either lies in `|Im z| > 1/2`, where the model is the disc, or in
`|Im z| < 1/2`, where it splits at the hole centres into `k` pieces, each contractible by
horizontal slices to the spines `∓2` (`k = 2`) or `-5/2, 0, 5/2` (`k = 3`)
(`HSliceGood`, `gridStrip_decomp`).

(3) The sweep. `planarSweep` is an induction principle: for a smooth embedding `ε : B → ℂ` of a
compact manifold onto `planarModel k`, `k ∈ {1, 2, 3}`, and a property `Good` of open sets that
is inherited by open subsets, holds near every point, and passes to `V₁ ∪ V₂` given a smooth
cutoff `0 ≤ ρ ≤ 1` that is `0` near `V₁ \ V₂` and `1` near `V₂ \ V₁` and a decomposition of
`V₁ ∩ V₂` into finitely many disjoint open pieces each empty or simply connected, `Good` holds on
all of `B`. The proof sweeps each row `t - h/2 < Im z < t + h` from left to right by grid boxes
(pieces of diameter `3h` below a Lebesgue number of the cover, overlaps `gridBox`), then sweeps
the rows from bottom to top (overlaps the strips of (2)); every step is `planarSweep_step` with the
cutoff `discSweepCutoff c (h/2)` of the coordinate.
-/

set_option autoImplicit false

noncomputable section
open Set
open Complex (I)
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def spinePoint (s : ℝ → ℝ) (x : ℝ) : ℂ := (x : ℂ) + (s x : ℂ) * I

theorem continuous_spinePoint {s : ℝ → ℝ} (hs : Continuous s) : Continuous (spinePoint s) := by
  unfold spinePoint
  fun_prop

theorem contractibleSpace_of_verticalSlices {S : Set ℂ} (hne : S.Nonempty) {s : ℝ → ℝ}
    (hs : Continuous s) (x₀ : ℝ)
    (hvert : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      (z.re : ℂ) + (((1 - t) * z.im + t * s z.re : ℝ) : ℂ) * I ∈ S)
    (hspine : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, spinePoint s ((1 - t) * z.re + t * x₀) ∈ S) :
    ContractibleSpace S := by
  have : Nonempty S := hne.to_subtype
  rw [contractible_iff_id_nullhomotopic]
  have hz₀ : spinePoint s x₀ ∈ S := by
    obtain ⟨z, hz⟩ := hne
    have h := hspine z hz 1 ⟨zero_le_one, le_rfl⟩
    simpa using h
  let F₁ : C(S, S) := ⟨fun z => ⟨spinePoint s z.1.re, by
      have h := hvert z.1 z.2 1 ⟨zero_le_one, le_rfl⟩
      simpa [spinePoint] using h⟩, by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_spinePoint hs).comp (Complex.continuous_re.comp continuous_subtype_val)⟩
  have h1 : (ContinuousMap.id S).Homotopic F₁ := by
    refine ⟨{
      toFun := fun p => ⟨(p.2.1.re : ℂ) + (((1 - (p.1 : ℝ)) * p.2.1.im + (p.1 : ℝ) *
        s p.2.1.re : ℝ) : ℂ) * I, hvert p.2.1 p.2.2 p.1 p.1.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        have hre : Continuous fun p : unitInterval × S => p.2.1.re :=
          Complex.continuous_re.comp (continuous_subtype_val.comp continuous_snd)
        have him : Continuous fun p : unitInterval × S => p.2.1.im :=
          Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)
        have ht : Continuous fun p : unitInterval × S => (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have hsr : Continuous fun p : unitInterval × S => s p.2.1.re := hs.comp hre
        fun_prop
      map_zero_left := fun z => by
        apply Subtype.ext
        simp [Complex.re_add_im]
      map_one_left := fun z => by
        apply Subtype.ext
        simp [F₁, spinePoint] }⟩
  have h2 : F₁.Homotopic (ContinuousMap.const S ⟨spinePoint s x₀, hz₀⟩) := by
    refine ⟨{
      toFun := fun p => ⟨spinePoint s ((1 - (p.1 : ℝ)) * p.2.1.re + (p.1 : ℝ) * x₀),
        hspine p.2.1 p.2.2 p.1 p.1.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        have hre : Continuous fun p : unitInterval × S => p.2.1.re :=
          Complex.continuous_re.comp (continuous_subtype_val.comp continuous_snd)
        have ht : Continuous fun p : unitInterval × S => (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        exact (continuous_spinePoint hs).comp (by fun_prop)
      map_zero_left := fun z => by
        apply Subtype.ext
        simp [F₁]
      map_one_left := fun z => by
        apply Subtype.ext
        simp }⟩
  exact ⟨_, h1.trans h2⟩

def swapReIm (z : ℂ) : ℂ := I * (starRingEnd ℂ) z

theorem swapReIm_re (z : ℂ) : (swapReIm z).re = z.im := by simp [swapReIm]

theorem swapReIm_im (z : ℂ) : (swapReIm z).im = z.re := by simp [swapReIm]

theorem swapReIm_swapReIm (z : ℂ) : swapReIm (swapReIm z) = z := by
  apply Complex.ext <;> simp [swapReIm_re, swapReIm_im]

def swapReImHomeomorph : ℂ ≃ₜ ℂ where
  toFun := swapReIm
  invFun := swapReIm
  left_inv := swapReIm_swapReIm
  right_inv := swapReIm_swapReIm
  continuous_toFun := by unfold swapReIm; fun_prop
  continuous_invFun := by unfold swapReIm; fun_prop

theorem contractibleSpace_of_horizontalSlices {S : Set ℂ} (hne : S.Nonempty) {s : ℝ → ℝ}
    (hs : Continuous s) (y₀ : ℝ)
    (hhor : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      (((1 - t) * z.re + t * s z.im : ℝ) : ℂ) + (z.im : ℂ) * I ∈ S)
    (hspine : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ((s ((1 - t) * z.im + t * y₀) : ℝ) : ℂ) + (((1 - t) * z.im + t * y₀ : ℝ) : ℂ) * I ∈ S) :
    ContractibleSpace S := by
  have hS' : ContractibleSpace (swapReImHomeomorph '' S) := by
    have hmem : ∀ w, w ∈ swapReImHomeomorph '' S ↔ swapReIm w ∈ S := by
      intro w
      constructor
      · rintro ⟨z, hz, rfl⟩
        change swapReIm (swapReIm z) ∈ S
        rwa [swapReIm_swapReIm]
      · intro hw
        exact ⟨swapReIm w, hw, swapReIm_swapReIm w⟩
    refine contractibleSpace_of_verticalSlices (hne.image _) hs y₀ (fun w hw t ht => ?_)
      (fun w hw t ht => ?_)
    · rw [hmem] at hw ⊢
      have h := hhor _ hw t ht
      rw [swapReIm_re, swapReIm_im] at h
      convert h using 1
      apply Complex.ext <;> simp [swapReIm]
    · rw [hmem] at hw ⊢
      have h := hspine _ hw t ht
      rw [swapReIm_im] at h
      convert h using 1
      apply Complex.ext <;> simp [swapReIm, spinePoint]
  exact (swapReImHomeomorph.image S).contractibleSpace

def planarBox (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := {z | x₁ < z.re ∧ z.re < x₂ ∧ y₁ < z.im ∧ z.im < y₂}

def holeOut (a b : ℝ) : Set ℂ := {z | 1 / 4 ≤ (z.re - a) ^ 2 + (z.im - b) ^ 2}

def holeHeight (a b x : ℝ) : ℝ := b + Real.sqrt (1 / 4 - (x - a) ^ 2)

theorem continuous_holeHeight (a b : ℝ) : Continuous (holeHeight a b) := by
  unfold holeHeight
  fun_prop

theorem le_holeHeight (a b x : ℝ) : b ≤ holeHeight a b x :=
  le_add_of_nonneg_right (Real.sqrt_nonneg _)

theorem holeHeight_le (a b x : ℝ) : holeHeight a b x ≤ b + 1 / 2 := by
  unfold holeHeight
  have h : Real.sqrt (1 / 4 - (x - a) ^ 2) ≤ Real.sqrt (1 / 4) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x - a)])
  have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

theorem holeOut_iff_holeHeight_le {a b x y : ℝ} (hy : b ≤ y) :
    1 / 4 ≤ (x - a) ^ 2 + (y - b) ^ 2 ↔ holeHeight a b x ≤ y := by
  unfold holeHeight
  constructor
  · intro h
    have h1 : Real.sqrt (1 / 4 - (x - a) ^ 2) ≤ Real.sqrt ((y - b) ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_sq (by linarith)] at h1
    linarith
  · intro h
    have h1 : Real.sqrt (1 / 4 - (x - a) ^ 2) ≤ y - b := by linarith
    by_cases h2 : 0 ≤ 1 / 4 - (x - a) ^ 2
    · have h3 := Real.sq_sqrt h2
      have h4 : Real.sqrt (1 / 4 - (x - a) ^ 2) ^ 2 ≤ (y - b) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      linarith
    · nlinarith [sq_nonneg (y - b)]

theorem holeHeight_lt_iff {a b x y : ℝ} (hy : b < y) :
    holeHeight a b x < y ↔ 1 / 4 - (y - b) ^ 2 < (x - a) ^ 2 := by
  unfold holeHeight
  rw [← lt_sub_iff_add_lt', Real.sqrt_lt' (by linarith)]
  constructor <;> intro h <;> linarith

private theorem sq_between {u u₀ A t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : A < u ^ 2)
    (hu₀ : A < u₀ ^ 2) (hd : (u - u₀) ^ 2 < 4 * A) : A < ((1 - t) * u + t * u₀) ^ 2 := by
  obtain ⟨ht0, ht1⟩ := ht
  have hA : 0 < A := by nlinarith [sq_nonneg (u - u₀)]
  rcases le_total 0 u with hu0 | hu0 <;> rcases le_total 0 u₀ with hv0 | hv0
  · have hm : min u u₀ ≤ (1 - t) * u + t * u₀ := by
      rcases le_total u u₀ with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    have hm0 : 0 ≤ min u u₀ := le_min hu0 hv0
    have hmA : A < min u u₀ ^ 2 := by
      rcases le_total u u₀ with h | h
      · rwa [min_eq_left h]
      · rwa [min_eq_right h]
    nlinarith
  · exfalso
    have h1 : A < u * (-u₀) := by
      have h2 : A ^ 2 < (u * (-u₀)) ^ 2 := by nlinarith
      nlinarith [mul_nonneg hu0 (neg_nonneg.mpr hv0)]
    nlinarith
  · exfalso
    have h1 : A < (-u) * u₀ := by
      have h2 : A ^ 2 < ((-u) * u₀) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (neg_nonneg.mpr hu0) hv0]
    nlinarith
  · have hm : (1 - t) * u + t * u₀ ≤ max u u₀ := by
      rcases le_total u u₀ with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    have hm0 : max u u₀ ≤ 0 := max_le hu0 hv0
    have hmA : A < max u u₀ ^ 2 := by
      rcases le_total u u₀ with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    nlinarith

private theorem lt_convex_comb {c u v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : c < u)
    (hv : c < v) : c < (1 - t) * u + t * v := by
  have h : c = (1 - t) * c + t * c := by ring
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0; simpa using hu
  · nlinarith

private theorem convex_comb_lt {c u v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : u < c)
    (hv : v < c) : (1 - t) * u + t * v < c := by
  have h := lt_convex_comb (c := -c) (u := -u) (v := -v) ht0 ht1 (by linarith) (by linarith)
  linarith

theorem contractibleSpace_planarBox_inter_holeOut {a b x₁ x₂ y₁ y₂ : ℝ} (hy₁ : b ≤ y₁)
    (hw : b + 1 / 2 < y₂ ∨ (x₂ - x₁) ^ 2 < 4 * (1 / 4 - (y₂ - b) ^ 2))
    (hne : (planarBox x₁ x₂ y₁ y₂ ∩ holeOut a b).Nonempty) :
    ContractibleSpace ↥(planarBox x₁ x₂ y₁ y₂ ∩ holeOut a b) := by
  obtain ⟨z₀, hz₀⟩ := hne
  let s : ℝ → ℝ := fun x => (max y₁ (holeHeight a b x) + y₂) / 2
  have hs : Continuous s := by
    have := continuous_holeHeight a b
    fun_prop
  have hmem : ∀ z ∈ planarBox x₁ x₂ y₁ y₂ ∩ holeOut a b,
      holeHeight a b z.re ≤ z.im ∧ y₁ < y₂ := by
    rintro z ⟨⟨-, -, h1, h2⟩, h3⟩
    exact ⟨(holeOut_iff_holeHeight_le (by linarith)).mp h3, by linarith⟩
  have hgood : ∀ x, holeHeight a b x < y₂ → y₁ < y₂ → ∀ y, max y₁ (holeHeight a b x) ≤ y →
      y < y₂ → y₁ < y → (x : ℂ) + (y : ℂ) * I ∈ holeOut a b := by
    intro x hx hy y hy1 hy2 hy3
    change 1 / 4 ≤ (((x : ℂ) + (y : ℂ) * I).re - a) ^ 2 + (((x : ℂ) + (y : ℂ) * I).im - b) ^ 2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    exact (holeOut_iff_holeHeight_le (le_trans (le_holeHeight a b x)
      (le_trans (le_max_right _ _) hy1))).mpr (le_trans (le_max_right _ _) hy1)
  refine contractibleSpace_of_verticalSlices ⟨z₀, hz₀⟩ hs z₀.re (fun z hz t ht => ?_)
    (fun z hz t ht => ?_)
  · obtain ⟨hg, hyy⟩ := hmem z hz
    obtain ⟨⟨hx1, hx2, hz1, hz2⟩, -⟩ := hz
    obtain ⟨ht0, ht1⟩ := ht
    have hmax : max y₁ (holeHeight a b z.re) < y₂ := max_lt hyy (lt_of_le_of_lt hg hz2)
    have hmz : max y₁ (holeHeight a b z.re) ≤ z.im := max_le hz1.le hg
    have hsm : max y₁ (holeHeight a b z.re) ≤ s z.re := by
      change _ ≤ (_ + _) / 2
      linarith
    have hsy : s z.re < y₂ := by
      change (_ + _) / 2 < _
      linarith
    have hlow : max y₁ (holeHeight a b z.re) ≤ (1 - t) * z.im + t * s z.re := by nlinarith
    have hup : (1 - t) * z.im + t * s z.re < y₂ := convex_comb_lt ht0 ht1 hz2 hsy
    have hy1' : y₁ < (1 - t) * z.im + t * s z.re := by
      have : y₁ < s z.re := by
        change _ < (_ + _) / 2
        linarith [le_max_left y₁ (holeHeight a b z.re)]
      exact lt_convex_comb ht0 ht1 hz1 this
    refine ⟨⟨by simpa using hx1, by simpa using hx2, by simpa using hy1', by simpa using hup⟩,
      ?_⟩
    have h := hgood z.re (lt_of_le_of_lt hg hz2) hyy _ hlow hup hy1'
    exact h
  · obtain ⟨hg, hyy⟩ := hmem z hz
    obtain ⟨hg₀, -⟩ := hmem z₀ hz₀
    obtain ⟨⟨hx1, hx2, hz1, hz2⟩, -⟩ := hz
    obtain ⟨⟨hx01, hx02, hz01, hz02⟩, -⟩ := hz₀
    obtain ⟨ht0, ht1⟩ := ht
    set x := (1 - t) * z.re + t * z₀.re with hxdef
    have hx1' : x₁ < x := lt_convex_comb ht0 ht1 hx1 hx01
    have hx2' : x < x₂ := convex_comb_lt ht0 ht1 hx2 hx02
    have hgx : holeHeight a b x < y₂ := by
      rcases hw with hw | hw
      · exact lt_of_le_of_lt (holeHeight_le a b x) hw
      · have hb : b < y₂ := by linarith
        rw [holeHeight_lt_iff hb]
        have hu := (holeHeight_lt_iff hb).mp (lt_of_le_of_lt hg hz2)
        have hu₀ := (holeHeight_lt_iff hb).mp (lt_of_le_of_lt hg₀ hz02)
        have hd : (z.re - a - (z₀.re - a)) ^ 2 < 4 * (1 / 4 - (y₂ - b) ^ 2) := by
          have h1 : (z.re - z₀.re) ^ 2 < (x₂ - x₁) ^ 2 := by
            have h2 : |z.re - z₀.re| < x₂ - x₁ := abs_lt.mpr ⟨by linarith, by linarith⟩
            have h3 : 0 ≤ |z.re - z₀.re| := abs_nonneg _
            calc (z.re - z₀.re) ^ 2 = |z.re - z₀.re| ^ 2 := (sq_abs _).symm
              _ < (x₂ - x₁) ^ 2 := by nlinarith
          have h4 : z.re - a - (z₀.re - a) = z.re - z₀.re := by ring
          rw [h4]
          linarith
        have h := sq_between ⟨ht0, ht1⟩ hu hu₀ hd
        have h5 : (1 - t) * (z.re - a) + t * (z₀.re - a) = x - a := by rw [hxdef]; ring
        rwa [h5] at h
    have hmax : max y₁ (holeHeight a b x) < y₂ := max_lt hyy hgx
    have hsm : max y₁ (holeHeight a b x) ≤ s x := by
      change _ ≤ (_ + _) / 2
      linarith
    have hsy : s x < y₂ := by
      change (_ + _) / 2 < _
      linarith
    have hs1 : y₁ < s x := by
      change _ < (_ + _) / 2
      linarith [le_max_left y₁ (holeHeight a b x)]
    have hre : (spinePoint s x).re = x := by simp [spinePoint]
    have him : (spinePoint s x).im = s x := by simp [spinePoint]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hgood x hgx hyy (s x) hsm hsy hs1⟩
    · rw [hre]
      exact hx1'
    · rw [hre]
      exact hx2'
    · rw [him]
      exact hs1
    · rw [him]
      exact hsy

theorem contractibleSpace_of_mem_iff (φ : ℂ ≃ₜ ℂ) {S S' : Set ℂ} (h : ∀ z, z ∈ S ↔ φ z ∈ S')
    [ContractibleSpace S'] : ContractibleSpace S := by
  have hS : S = φ.symm '' S' := by
    ext z
    rw [h]
    constructor
    · intro hz
      exact ⟨φ z, hz, φ.symm_apply_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      rwa [φ.apply_symm_apply]
  subst hS
  exact (φ.symm.image S').symm.contractibleSpace

theorem nonempty_of_mem_iff (φ : ℂ ≃ₜ ℂ) {S S' : Set ℂ} (h : ∀ z, z ∈ S ↔ φ z ∈ S')
    (hne : S.Nonempty) : S'.Nonempty := by
  obtain ⟨z, hz⟩ := hne
  exact ⟨φ z, (h z).mp hz⟩

def reflectAt (c : ℝ) : ℂ ≃ₜ ℂ :=
  Complex.conjCLE.toHomeomorph.trans (Homeomorph.subLeft ((2 * c : ℝ) : ℂ))

theorem reflectAt_re (c : ℝ) (z : ℂ) : (reflectAt c z).re = 2 * c - z.re := by
  simp [reflectAt]

theorem reflectAt_im (c : ℝ) (z : ℂ) : (reflectAt c z).im = z.im := by
  simp [reflectAt]

theorem conj_re' (z : ℂ) : (Complex.conjCLE.toHomeomorph z).re = z.re := by simp

theorem conj_im' (z : ℂ) : (Complex.conjCLE.toHomeomorph z).im = -z.im := by simp

theorem contractibleSpace_planarBox_inter_holeOut_below {c x₁ x₂ y₁ y₂ : ℝ} (hy₂ : y₂ ≤ 0)
    (hw : y₁ < -(1 / 2) ∨ (x₂ - x₁) ^ 2 < 4 * (1 / 4 - y₁ ^ 2))
    (hne : (planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0).Nonempty) :
    ContractibleSpace ↥(planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0) := by
  have h : ∀ z, z ∈ planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0 ↔
      Complex.conjCLE.toHomeomorph z ∈ planarBox x₁ x₂ (-y₂) (-y₁) ∩ holeOut c 0 := by
    intro z
    simp only [planarBox, holeOut, mem_inter_iff, mem_ofPred_eq, conj_re', conj_im']
    constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
      refine ⟨⟨h1, h2, by linarith, by linarith⟩, by nlinarith⟩
  have : ContractibleSpace ↥(planarBox x₁ x₂ (-y₂) (-y₁) ∩ holeOut c 0) :=
    contractibleSpace_planarBox_inter_holeOut (by linarith)
      (by rcases hw with hw | hw
          · exact Or.inl (by linarith)
          · exact Or.inr (by nlinarith))
      (nonempty_of_mem_iff _ h hne)
  exact contractibleSpace_of_mem_iff _ h

theorem contractibleSpace_planarBox_inter_holeOut_right {c x₁ x₂ y₁ y₂ : ℝ} (hx₁ : c ≤ x₁)
    (hw : c + 1 / 2 < x₂ ∨ (y₂ - y₁) ^ 2 < 4 * (1 / 4 - (x₂ - c) ^ 2))
    (hne : (planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0).Nonempty) :
    ContractibleSpace ↥(planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0) := by
  have h : ∀ z, z ∈ planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0 ↔
      swapReImHomeomorph z ∈ planarBox y₁ y₂ x₁ x₂ ∩ holeOut 0 c := by
    intro z
    change _ ↔ swapReIm z ∈ _
    simp only [planarBox, holeOut, mem_inter_iff, mem_ofPred_eq, swapReIm_re, swapReIm_im]
    constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
      refine ⟨⟨by assumption, by assumption, by assumption, by assumption⟩, by nlinarith⟩
  have : ContractibleSpace ↥(planarBox y₁ y₂ x₁ x₂ ∩ holeOut 0 c) :=
    contractibleSpace_planarBox_inter_holeOut hx₁ hw (nonempty_of_mem_iff _ h hne)
  exact contractibleSpace_of_mem_iff _ h

theorem contractibleSpace_planarBox_inter_holeOut_left {c x₁ x₂ y₁ y₂ : ℝ} (hx₂ : x₂ ≤ c)
    (hw : x₁ < c - 1 / 2 ∨ (y₂ - y₁) ^ 2 < 4 * (1 / 4 - (x₁ - c) ^ 2))
    (hne : (planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0).Nonempty) :
    ContractibleSpace ↥(planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0) := by
  have h : ∀ z, z ∈ planarBox x₁ x₂ y₁ y₂ ∩ holeOut c 0 ↔
      reflectAt c z ∈ planarBox (2 * c - x₂) (2 * c - x₁) y₁ y₂ ∩ holeOut c 0 := by
    intro z
    simp only [planarBox, holeOut, mem_inter_iff, mem_ofPred_eq, reflectAt_re, reflectAt_im]
    constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
      refine ⟨⟨by linarith, by linarith, h3, h4⟩, by nlinarith⟩
  have : ContractibleSpace ↥(planarBox (2 * c - x₂) (2 * c - x₁) y₁ y₂ ∩ holeOut c 0) :=
    contractibleSpace_planarBox_inter_holeOut_right (by linarith)
      (by rcases hw with hw | hw
          · exact Or.inl (by linarith)
          · exact Or.inr (by nlinarith))
      (nonempty_of_mem_iff _ h hne)
  exact contractibleSpace_of_mem_iff _ h

theorem mem_holeOut_iff (c : ℝ) (z : ℂ) : z ∈ holeOut c 0 ↔ 1 / 2 ≤ ‖z - c‖ := by
  have h : ‖z - c‖ ^ 2 = (z.re - c) ^ 2 + (z.im - 0) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  change 1 / 4 ≤ (z.re - c) ^ 2 + (z.im - 0) ^ 2 ↔ _
  rw [← h]
  have h0 := norm_nonneg (z - c)
  constructor
  · intro h1
    nlinarith
  · intro h1
    nlinarith

theorem planarModel_two : planarModel 2 = Metric.closedBall (0 : ℂ) 3 ∩ holeOut 0 0 := by
  ext z
  simp only [planarModel, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
    mem_holeOut_iff, Fin.forall_fin_two]
  simp [planarCenter]

theorem planarModel_three : planarModel 3 =
    Metric.closedBall (0 : ℂ) 3 ∩ holeOut (3 / 2) 0 ∩ holeOut (-(3 / 2)) 0 := by
  ext z
  simp only [planarModel, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
    mem_holeOut_iff, Fin.forall_fin_succ]
  simp only [planarCenter, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ne_eq,
    not_true_eq_false, one_div, IsEmpty.forall_iff, Fin.succ_zero_eq_one, Nat.one_mod,
    one_ne_zero, not_false_eq_true, forall_const, Fin.succ_one_eq_two, Nat.mod_succ,
    OfNat.ofNat_ne_zero, Fin.val_succ, Fin.val_eq_zero, zero_add, Nat.reduceAdd, and_true,
    true_and, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg, sub_neg_eq_add,
    ↓reduceIte, Nat.reduceEqDiff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩

def gridH (n : ℕ) : ℝ := 1 / (8 * n)

def gridPt (n : ℕ) (i : ℤ) : ℝ := (i + 3 / 4) * gridH n

def gridBox (n : ℕ) (i j : ℤ) : Set ℂ :=
  planarBox (gridPt n i - gridH n / 2) (gridPt n i) (gridPt n j - gridH n / 2)
    (gridPt n j + gridH n)

theorem gridH_pos {n : ℕ} (hn : 0 < n) : 0 < gridH n := by
  unfold gridH
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem four_mul_gridH {n : ℕ} (hn : 0 < n) : ((4 * n : ℕ) : ℝ) * gridH n = 1 / 2 := by
  unfold gridH
  have : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  field_simp
  ring

private theorem sq_le_of_mem {y A : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ A) : y ^ 2 ≤ A ^ 2 :=
  pow_le_pow_left₀ h0 h1 2

private theorem contractibleSpace_box_aux {h : ℝ} (hh : 0 < h) (hh8 : h ≤ 1 / 8) {N : ℤ}
    (hN' : (N : ℝ) * h = 1 / 2) (g i j : ℤ)
    (hne : (planarBox ((i + 3 / 4) * h - h / 2) ((i + 3 / 4) * h) ((j + 3 / 4) * h - h / 2)
      ((j + 3 / 4) * h + h) ∩ holeOut (g * h) 0).Nonempty) :
    ContractibleSpace ↥(planarBox ((i + 3 / 4) * h - h / 2) ((i + 3 / 4) * h)
      ((j + 3 / 4) * h - h / 2) ((j + 3 / 4) * h + h) ∩ holeOut (g * h) 0) := by
  rcases le_or_gt 0 j with hj | hj
  · refine contractibleSpace_planarBox_inter_holeOut ?_ ?_ hne
    · have : (0 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith
    · rcases le_or_gt (N - 1) j with hj' | hj'
      · left
        have : (N : ℝ) - 1 ≤ j := by exact_mod_cast hj'
        nlinarith
      · right
        have h1 : (j : ℝ) ≤ N - 2 := by
          have : j ≤ N - 2 := by omega
          exact_mod_cast this
        have h0 : (0 : ℝ) ≤ j := by exact_mod_cast hj
        have h2 := sq_le_of_mem (y := (j + 3 / 4) * h + h - 0) (A := 1 / 2 - h / 4)
          (by nlinarith) (by nlinarith)
        nlinarith
  rcases le_or_gt j (-2) with hj2 | hj2
  · refine contractibleSpace_planarBox_inter_holeOut_below ?_ ?_ hne
    · have : (j : ℝ) ≤ -2 := by exact_mod_cast hj2
      nlinarith
    · rcases le_or_gt j (-N - 1) with hj' | hj'
      · left
        have : (j : ℝ) ≤ -N - 1 := by exact_mod_cast hj'
        nlinarith
      · right
        have h1 : (-N : ℝ) ≤ j := by
          have : -N ≤ j := by omega
          exact_mod_cast this
        have h0 : (j : ℝ) ≤ -2 := by exact_mod_cast hj2
        have h2 := sq_le_of_mem (y := -((j + 3 / 4) * h - h / 2)) (A := 1 / 2 - h / 4)
          (by nlinarith) (by nlinarith)
        nlinarith
  have hjm : j = -1 := by omega
  subst hjm
  rcases le_or_gt g i with hi | hi
  · refine contractibleSpace_planarBox_inter_holeOut_right ?_ ?_ hne
    · have : (g : ℝ) ≤ i := by exact_mod_cast hi
      nlinarith
    · rcases le_or_gt (g + N) i with hi' | hi'
      · left
        have : (g : ℝ) + N ≤ i := by exact_mod_cast hi'
        nlinarith
      · right
        have h1 : (i : ℝ) ≤ g + N - 1 := by
          have : i ≤ g + N - 1 := by omega
          exact_mod_cast this
        have h0 : (g : ℝ) ≤ i := by exact_mod_cast hi
        have h2 := sq_le_of_mem (y := (i + 3 / 4) * h - g * h) (A := 1 / 2 - h / 4)
          (by nlinarith) (by nlinarith)
        push_cast
        nlinarith
  · refine contractibleSpace_planarBox_inter_holeOut_left ?_ ?_ hne
    · have : (i : ℝ) ≤ g - 1 := by
        have : i ≤ g - 1 := by omega
        exact_mod_cast this
      nlinarith
    · rcases le_or_gt i (g - N - 1) with hi' | hi'
      · left
        have : (i : ℝ) ≤ g - N - 1 := by exact_mod_cast hi'
        nlinarith
      · right
        have h1 : (g : ℝ) - N ≤ i := by
          have : g - N ≤ i := by omega
          exact_mod_cast this
        have h0 : (i : ℝ) ≤ g - 1 := by
          have : i ≤ g - 1 := by omega
          exact_mod_cast this
        have h2 := sq_le_of_mem (y := g * h - ((i + 3 / 4) * h - h / 2)) (A := 1 / 2 - h / 4)
          (by nlinarith) (by nlinarith)
        push_cast
        nlinarith

theorem contractibleSpace_gridBox_inter_holeOut {n : ℕ} (hn : 0 < n) (g i j : ℤ)
    (hne : (gridBox n i j ∩ holeOut (g * gridH n) 0).Nonempty) :
    ContractibleSpace ↥(gridBox n i j ∩ holeOut (g * gridH n) 0) := by
  have hh8 : gridH n ≤ 1 / 8 := by
    unfold gridH
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hN : (((4 * n : ℕ) : ℤ) : ℝ) * gridH n = 1 / 2 := by
    rw [Int.cast_natCast]
    exact four_mul_gridH hn
  exact contractibleSpace_box_aux (gridH_pos hn) hh8 hN g i j hne

theorem convex_planarBox (x₁ x₂ y₁ y₂ : ℝ) : Convex ℝ (planarBox x₁ x₂ y₁ y₂) := by
  have h1 : Convex ℝ {z : ℂ | x₁ < Complex.reCLM z} :=
    convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear x₁
  have h2 : Convex ℝ {z : ℂ | Complex.reCLM z < x₂} :=
    convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear x₂
  have h3 : Convex ℝ {z : ℂ | y₁ < Complex.imCLM z} :=
    convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear y₁
  have h4 : Convex ℝ {z : ℂ | Complex.imCLM z < y₂} :=
    convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear y₂
  exact h1.inter (h2.inter (h3.inter h4))

theorem isOpen_planarBox (x₁ x₂ y₁ y₂ : ℝ) : IsOpen (planarBox x₁ x₂ y₁ y₂) := by
  unfold planarBox
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

theorem norm_sub_lt_of_mem_gridBox {n : ℕ} (hn : 0 < n) {i j : ℤ} {z w : ℂ}
    (hz : z ∈ gridBox n i j) (hw : w ∈ gridBox n i j) : ‖z - w‖ < 1 / 4 := by
  have hh := gridH_pos hn
  have hh8 : gridH n ≤ 1 / 8 := by
    unfold gridH
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < gridH n / 2 + 3 * gridH n / 2 := by
        rw [Complex.sub_re, Complex.sub_im]
        exact add_lt_add (abs_lt.mpr ⟨by linarith, by linarith⟩)
          (abs_lt.mpr ⟨by linarith, by linarith⟩)
    _ ≤ 1 / 4 := by linarith

theorem gridBox_inter_eq_of_hole {n : ℕ} (hn : 0 < n) {i j : ℤ} {γ : ℝ} {T : Set ℂ}
    (hT : ∀ z : ℂ, ‖z - γ‖ < 1 → z ∈ T) {p : ℂ} (hp : p ∈ gridBox n i j)
    (hpγ : ‖p - γ‖ < 1 / 2) :
    gridBox n i j ∩ (T ∩ holeOut γ 0) = gridBox n i j ∩ holeOut γ 0 := by
  ext z
  constructor
  · rintro ⟨hz, -, hz'⟩
    exact ⟨hz, hz'⟩
  · rintro ⟨hz, hz'⟩
    refine ⟨hz, hT z ?_, hz'⟩
    calc ‖z - γ‖ = ‖(z - p) + (p - γ)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - p‖ + ‖p - γ‖ := norm_add_le _ _
      _ < 1 / 4 + 1 / 2 := add_lt_add (norm_sub_lt_of_mem_gridBox hn hz hp) hpγ
      _ ≤ 1 := by norm_num

theorem contractibleSpace_gridBox_inter_ball {n : ℕ} {i j : ℤ}
    (hne : (gridBox n i j ∩ Metric.closedBall (0 : ℂ) 3).Nonempty) :
    ContractibleSpace ↥(gridBox n i j ∩ Metric.closedBall (0 : ℂ) 3) :=
  ((convex_planarBox _ _ _ _).inter (convex_closedBall _ _)).contractibleSpace hne

theorem twelve_mul_gridH {n : ℕ} (hn : 0 < n) : (((12 * n : ℕ) : ℤ) : ℝ) * gridH n = 3 / 2 := by
  unfold gridH
  have : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  field_simp
  ring

theorem contractibleSpace_gridBox_inter_of_hole {n : ℕ} (hn : 0 < n) {i j : ℤ} (g : ℤ)
    {T : Set ℂ} (hT : ∀ z : ℂ, ‖z - ((g * gridH n : ℝ) : ℂ)‖ < 1 → z ∈ T)
    (hp : ∃ p ∈ gridBox n i j, ‖p - ((g * gridH n : ℝ) : ℂ)‖ < 1 / 2)
    (hne : (gridBox n i j ∩ (T ∩ holeOut (g * gridH n) 0)).Nonempty) :
    ContractibleSpace ↥(gridBox n i j ∩ (T ∩ holeOut (g * gridH n) 0)) := by
  obtain ⟨p, hp, hpγ⟩ := hp
  rw [gridBox_inter_eq_of_hole hn hT hp hpγ] at hne ⊢
  exact contractibleSpace_gridBox_inter_holeOut hn g i j hne

theorem gridBox_inter_eq_of_not_hole {n : ℕ} {i j : ℤ} {γ : ℝ} {T : Set ℂ}
    (hp : ¬ ∃ p ∈ gridBox n i j, ‖p - (γ : ℂ)‖ < 1 / 2) :
    gridBox n i j ∩ (T ∩ holeOut γ 0) = gridBox n i j ∩ T := by
  push Not at hp
  ext z
  constructor
  · rintro ⟨hz, hz', -⟩
    exact ⟨hz, hz'⟩
  · rintro ⟨hz, hz'⟩
    exact ⟨hz, hz', (mem_holeOut_iff γ z).mpr (hp z hz)⟩

theorem norm_le_of_norm_sub_lt {z : ℂ} {γ : ℝ} (h : ‖z - γ‖ < 1) : ‖z‖ < |γ| + 1 := by
  have h1 := norm_sub_norm_le z (γ : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

theorem lt_norm_sub_of_norm_sub_lt {z : ℂ} {γ γ' : ℝ} (h : ‖z - γ‖ < 1) :
    |γ - γ'| - 1 < ‖z - γ'‖ := by
  have h1 : ‖((γ - γ' : ℝ) : ℂ)‖ ≤ ‖z - γ'‖ + ‖z - γ‖ := by
    have h2 : ((γ - γ' : ℝ) : ℂ) = (z - γ') - (z - γ) := by push_cast; ring
    rw [h2]
    exact norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

theorem contractibleSpace_gridBox_inter_planarModel {n : ℕ} (hn : 0 < n) {k : ℕ}
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (i j : ℤ) (hne : (gridBox n i j ∩ planarModel k).Nonempty) :
    ContractibleSpace ↥(gridBox n i j ∩ planarModel k) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  have h0 : (((0 : ℤ) : ℝ) * gridH n) = 0 := by simp
  have h32 := twelve_mul_gridH hn
  have hm32 : (((-((12 * n : ℕ) : ℤ)) : ℤ) : ℝ) * gridH n = -(3 / 2) := by
    rw [Int.cast_neg, neg_mul, h32]
  rcases hk with rfl | rfl | rfl
  · rw [planarModel_one] at hne ⊢
    exact contractibleSpace_gridBox_inter_ball hne
  · have he2 : planarModel 2 =
        Metric.closedBall (0 : ℂ) 3 ∩ holeOut (((0 : ℤ) : ℝ) * gridH n) 0 := by
      rw [planarModel_two, h0]
    rw [he2] at hne ⊢
    by_cases hp : ∃ p ∈ gridBox n i j, ‖p - (((0 : ℤ) * gridH n : ℝ) : ℂ)‖ < 1 / 2
    · refine contractibleSpace_gridBox_inter_of_hole hn 0 (fun z hz => ?_) hp hne
      have h1 := norm_le_of_norm_sub_lt hz
      rw [h0, abs_zero] at h1
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    · rw [gridBox_inter_eq_of_not_hole hp] at hne ⊢
      exact contractibleSpace_gridBox_inter_ball hne
  · have he : planarModel 3 = (Metric.closedBall (0 : ℂ) 3 ∩
        holeOut ((-((12 * n : ℕ) : ℤ) : ℤ) * gridH n) 0) ∩
        holeOut (((12 * n : ℕ) : ℤ) * gridH n) 0 := by
      rw [planarModel_three, h32, hm32]
      ext z
      simp only [mem_inter_iff]
      tauto
    rw [he] at hne ⊢
    by_cases hp : ∃ p ∈ gridBox n i j, ‖p - (((((12 * n : ℕ) : ℤ)) * gridH n : ℝ) : ℂ)‖ < 1 / 2
    · refine contractibleSpace_gridBox_inter_of_hole hn _ (fun z hz => ⟨?_, ?_⟩) hp hne
      · have h1 := norm_le_of_norm_sub_lt hz
        rw [h32, abs_of_pos (by norm_num)] at h1
        rw [Metric.mem_closedBall, dist_zero_right]
        linarith
      · rw [mem_holeOut_iff]
        have h1 := lt_norm_sub_of_norm_sub_lt
          (γ' := ((-((12 * n : ℕ) : ℤ) : ℤ) : ℝ) * gridH n) hz
        rw [h32, hm32] at h1
        rw [hm32]
        norm_num at h1 ⊢
        linarith
    rw [gridBox_inter_eq_of_not_hole hp] at hne ⊢
    by_cases hq : ∃ p ∈ gridBox n i j,
        ‖p - ((((-((12 * n : ℕ) : ℤ) : ℤ)) * gridH n : ℝ) : ℂ)‖ < 1 / 2
    · refine contractibleSpace_gridBox_inter_of_hole hn _ (fun z hz => ?_) hq hne
      have h1 := norm_le_of_norm_sub_lt hz
      rw [hm32, abs_of_neg (by norm_num)] at h1
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    rw [gridBox_inter_eq_of_not_hole hq] at hne ⊢
    exact contractibleSpace_gridBox_inter_ball hne

def stripPiece (a b L R : ℝ) : Set ℂ := {z | a < z.im ∧ z.im < b ∧ L < z.re ∧ z.re < R}

def HSliceGood (S : Set ℂ) (x₀ a b : ℝ) : Prop :=
  (∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      (((1 - t) * z.re + t * x₀ : ℝ) : ℂ) + (z.im : ℂ) * I ∈ S) ∧
    ∀ z ∈ S, ∀ y₀ ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1,
      (x₀ : ℂ) + (((1 - t) * z.im + t * y₀ : ℝ) : ℂ) * I ∈ S

theorem HSliceGood.inter {S T : Set ℂ} {x₀ a b : ℝ} (hS : HSliceGood S x₀ a b)
    (hT : HSliceGood T x₀ a b) : HSliceGood (S ∩ T) x₀ a b :=
  ⟨fun z hz t ht => ⟨hS.1 z hz.1 t ht, hT.1 z hz.2 t ht⟩,
    fun z hz y₀ hy₀ t ht => ⟨hS.2 z hz.1 y₀ hy₀ t ht, hT.2 z hz.2 y₀ hy₀ t ht⟩⟩

theorem HSliceGood.contractibleSpace {S : Set ℂ} {x₀ a b : ℝ} (hS : HSliceGood S x₀ a b)
    (hab : ∀ z ∈ S, a < z.im ∧ z.im < b) (hne : S.Nonempty) : ContractibleSpace S := by
  obtain ⟨z₀, hz₀⟩ := hne
  refine contractibleSpace_of_horizontalSlices ⟨z₀, hz₀⟩ (s := fun _ => x₀) continuous_const
    z₀.im (fun z hz t ht => hS.1 z hz t ht) (fun z hz t ht => ?_)
  exact hS.2 z hz z₀.im (hab z₀ hz₀) t ht

private theorem re_im_ofReal_add (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * I).re = x ∧ ((x : ℂ) + (y : ℂ) * I).im = y := by
  simp

private theorem convex_comb_mem_Ioo {a b u v t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Ioo a b)
    (hv : v ∈ Ioo a b) : (1 - t) * u + t * v ∈ Ioo a b :=
  ⟨lt_convex_comb ht.1 ht.2 hu.1 hv.1, convex_comb_lt ht.1 ht.2 hu.2 hv.2⟩

private theorem sq_convex_comb_le {u v t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((1 - t) * u + t * v) ^ 2 ≤ max (u ^ 2) (v ^ 2) := by
  obtain ⟨ht0, ht1⟩ := ht
  have h1 : ((1 - t) * u + t * v) ^ 2 ≤ (1 - t) * u ^ 2 + t * v ^ 2 := by
    nlinarith [sq_nonneg (u - v), mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have h2 : (1 - t) * u ^ 2 + t * v ^ 2 ≤ max (u ^ 2) (v ^ 2) := by
    nlinarith [le_max_left (u ^ 2) (v ^ 2), le_max_right (u ^ 2) (v ^ 2)]
  linarith

private theorem min_sq_le_sq_convex_comb {u v t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (huv : (0 ≤ u ∧ 0 ≤ v) ∨ (u ≤ 0 ∧ v ≤ 0)) :
    min (u ^ 2) (v ^ 2) ≤ ((1 - t) * u + t * v) ^ 2 := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hw : min u v ≤ (1 - t) * u + t * v := by
      nlinarith [min_le_left u v, min_le_right u v]
    have hm : 0 ≤ min u v := le_min hu hv
    have h1 : min u v ^ 2 ≤ ((1 - t) * u + t * v) ^ 2 := pow_le_pow_left₀ hm hw 2
    rcases le_total u v with h | h
    · rw [min_eq_left h] at h1
      exact le_trans (min_le_left _ _) h1
    · rw [min_eq_right h] at h1
      exact le_trans (min_le_right _ _) h1
  · have hw : (1 - t) * u + t * v ≤ max u v := by
      nlinarith [le_max_left u v, le_max_right u v]
    have hm : max u v ≤ 0 := max_le hu hv
    have h1 : (-max u v) ^ 2 ≤ (-((1 - t) * u + t * v)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [neg_sq, neg_sq] at h1
    rcases le_total u v with h | h
    · rw [max_eq_right h] at h1
      exact le_trans (min_le_right _ _) h1
    · rw [max_eq_left h] at h1
      exact le_trans (min_le_left _ _) h1

theorem hSliceGood_stripPiece {a b L R x₀ : ℝ} (hx₀ : x₀ ∈ Ioo L R) :
    HSliceGood (stripPiece a b L R) x₀ a b := by
  refine ⟨fun z hz t ht => ?_, fun z hz y₀ hy₀ t ht => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hz
    have hx := convex_comb_mem_Ioo ht ⟨h3, h4⟩ hx₀
    simp only [stripPiece, mem_ofPred_eq, (re_im_ofReal_add _ _).1, (re_im_ofReal_add _ _).2]
    exact ⟨h1, h2, hx.1, hx.2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hz
    have hy := convex_comb_mem_Ioo ht ⟨h1, h2⟩ hy₀
    simp only [stripPiece, mem_ofPred_eq, (re_im_ofReal_add _ _).1, (re_im_ofReal_add _ _).2]
    exact ⟨hy.1, hy.2, hx₀.1, hx₀.2⟩

theorem ofReal_add_mem_holeOut_iff (x y γ b : ℝ) :
    (x : ℂ) + (y : ℂ) * I ∈ holeOut γ b ↔ 1 / 4 ≤ (x - γ) ^ 2 + (y - b) ^ 2 := by
  change 1 / 4 ≤ (((x : ℂ) + (y : ℂ) * I).re - γ) ^ 2 + (((x : ℂ) + (y : ℂ) * I).im - b) ^ 2 ↔ _
  rw [(re_im_ofReal_add x y).1, (re_im_ofReal_add x y).2]

theorem ofReal_add_mem_closedBall_iff (x y : ℝ) :
    (x : ℂ) + (y : ℂ) * I ∈ Metric.closedBall (0 : ℂ) 3 ↔ x ^ 2 + y ^ 2 ≤ 9 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, (re_im_ofReal_add x y).1, (re_im_ofReal_add x y).2]
    ring
  have h0 := norm_nonneg ((x : ℂ) + (y : ℂ) * I)
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem re_sq_add_im_sq_le_of_mem_closedBall {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 3) :
    z.re ^ 2 + z.im ^ 2 ≤ 9 := by
  have h := (ofReal_add_mem_closedBall_iff z.re z.im).mp (by rwa [Complex.re_add_im])
  exact h

theorem hSliceGood_stripPiece_ball {a b L R x₀ : ℝ} (hx₀ : x₀ ∈ Ioo L R) (ha : -(1 / 2) ≤ a)
    (hb : b ≤ 1 / 2) (hx₀' : x₀ ^ 2 ≤ 35 / 4) :
    HSliceGood (stripPiece a b L R ∩ Metric.closedBall (0 : ℂ) 3) x₀ a b := by
  have hP := hSliceGood_stripPiece (a := a) (b := b) hx₀
  refine ⟨fun z hz t ht => ⟨hP.1 z hz.1 t ht, ?_⟩,
    fun z hz y₀ hy₀ t ht => ⟨hP.2 z hz.1 y₀ hy₀ t ht, ?_⟩⟩
  · have h1 := re_sq_add_im_sq_le_of_mem_closedBall hz.2
    have h2 := sq_convex_comb_le (u := z.re) (v := x₀) ht
    obtain ⟨hz1, hz2, -, -⟩ := hz.1
    rw [ofReal_add_mem_closedBall_iff]
    have h3 : z.im ^ 2 ≤ 1 / 4 := by nlinarith
    rcases le_total (z.re ^ 2) (x₀ ^ 2) with h | h
    · rw [max_eq_right h] at h2
      linarith
    · rw [max_eq_left h] at h2
      linarith
  · obtain ⟨hz1, hz2, -, -⟩ := hz.1
    have hy := convex_comb_mem_Ioo ht ⟨hz1, hz2⟩ hy₀
    rw [ofReal_add_mem_closedBall_iff]
    have h3 : ((1 - t) * z.im + t * y₀) ^ 2 ≤ 1 / 4 := by nlinarith [hy.1, hy.2]
    linarith

theorem hSliceGood_stripPiece_holeOut {a b L R x₀ γ : ℝ} (hx₀ : x₀ ∈ Ioo L R)
    (hγ : γ ≤ L ∨ R ≤ γ) (hx₀γ : 1 / 4 ≤ (x₀ - γ) ^ 2) :
    HSliceGood (stripPiece a b L R ∩ holeOut γ 0) x₀ a b := by
  have hP := hSliceGood_stripPiece (a := a) (b := b) hx₀
  refine ⟨fun z hz t ht => ⟨hP.1 z hz.1 t ht, ?_⟩,
    fun z hz y₀ hy₀ t ht => ⟨hP.2 z hz.1 y₀ hy₀ t ht, ?_⟩⟩
  · obtain ⟨⟨-, -, hz3, hz4⟩, hz5⟩ := hz
    change 1 / 4 ≤ (z.re - γ) ^ 2 + (z.im - 0) ^ 2 at hz5
    rw [ofReal_add_mem_holeOut_iff]
    have hs : (0 ≤ z.re - γ ∧ 0 ≤ x₀ - γ) ∨ (z.re - γ ≤ 0 ∧ x₀ - γ ≤ 0) := by
      rcases hγ with h | h
      · exact Or.inl ⟨by linarith, by linarith [hx₀.1]⟩
      · exact Or.inr ⟨by linarith, by linarith [hx₀.2]⟩
    have h1 := min_sq_le_sq_convex_comb ht hs
    have h2 : (1 - t) * (z.re - γ) + t * (x₀ - γ) = (1 - t) * z.re + t * x₀ - γ := by ring
    rw [h2] at h1
    rcases le_total ((z.re - γ) ^ 2) ((x₀ - γ) ^ 2) with h | h
    · rw [min_eq_left h] at h1
      linarith
    · rw [min_eq_right h] at h1
      nlinarith [sq_nonneg (z.im - 0)]
  · rw [ofReal_add_mem_holeOut_iff]
    nlinarith [sq_nonneg ((1 - t) * z.im + t * y₀ - 0)]

section Sweep

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]

theorem planarSweep_step {ε : B → ℂ} (hε : _root_.Topology.IsEmbedding ε)
    (hεs : ContMDiff I 𝓘(ℝ, ℂ) ∞ ε) (Good : Set B → Prop)
    (hglue : ∀ V₁ V₂ : Set B, IsOpen V₁ → IsOpen V₂ → Good V₁ → Good V₂ →
      ∀ ρ : B → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ → (∀ b, ρ b ∈ Icc (0 : ℝ) 1) →
      (∀ b ∈ V₁, b ∉ V₂ → ρ =ᶠ[𝓝 b] 0) → (∀ b ∈ V₂, b ∉ V₁ → ρ =ᶠ[𝓝 b] 1) →
      ∀ (m : ℕ) (O : Fin m → Set B), (∀ i, IsOpen (O i)) → V₁ ∩ V₂ = ⋃ i, O i →
      Pairwise (Function.onFun Disjoint O) → (∀ i, (O i).Nonempty → IsSimplyConnected (O i)) →
      Good (V₁ ∪ V₂))
    (ℓ : ℂ →L[ℝ] ℝ) {Q : Set ℂ} (hQ : IsOpen Q) {h : ℝ} (hh : 0 < h) (c : ℝ)
    (hS : Good (ε ⁻¹' (Q ∩ {z | ℓ z < c})))
    (hT : Good (ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - h / 2) (c + h))))
    (hO : ∃ (m : ℕ) (O : Fin m → Set B), (∀ i, IsOpen (O i)) ∧
      ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - h / 2) c) = ⋃ i, O i ∧
      Pairwise (Function.onFun Disjoint O) ∧ ∀ i, (O i).Nonempty → IsSimplyConnected (O i)) :
    Good (ε ⁻¹' (Q ∩ {z | ℓ z < c + h})) := by
  obtain ⟨m, O, hOo, hOeq, hOd, hOs⟩ := hO
  have hℓε : Continuous fun y => ℓ (ε y) := ℓ.continuous.comp hε.continuous
  have hSo : IsOpen (ε ⁻¹' (Q ∩ {z | ℓ z < c})) :=
    (hQ.inter (isOpen_lt ℓ.continuous continuous_const)).preimage hε.continuous
  have hTo : IsOpen (ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - h / 2) (c + h))) :=
    (hQ.inter (isOpen_discSweepSlab ℓ _ _)).preimage hε.continuous
  have hST : ε ⁻¹' (Q ∩ {z | ℓ z < c}) ∩ ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - h / 2) (c + h)) =
      ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - h / 2) c) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, discSweepSlab]
    constructor
    · rintro ⟨⟨hq, h1⟩, -, h2, -⟩
      exact ⟨hq, h2, h1⟩
    · rintro ⟨hq, h1, h2⟩
      exact ⟨⟨hq, h2⟩, hq, h1, by linarith⟩
  have hU : ε ⁻¹' (Q ∩ {z | ℓ z < c}) ∪ ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - h / 2) (c + h)) =
      ε ⁻¹' (Q ∩ {z | ℓ z < c + h}) := by
    ext y
    simp only [mem_union, mem_inter_iff, mem_preimage, mem_ofPred_eq, discSweepSlab]
    constructor
    · rintro (⟨hq, h1⟩ | ⟨hq, -, h2⟩)
      · exact ⟨hq, by linarith⟩
      · exact ⟨hq, h2⟩
    · rintro ⟨hq, h1⟩
      by_cases h2 : ℓ (ε y) < c
      · exact Or.inl ⟨hq, h2⟩
      · exact Or.inr ⟨hq, by linarith, h1⟩
  have hh2 : 0 < h / 2 := by positivity
  rw [← hU]
  refine hglue _ _ hSo hTo hS hT (fun y => discSweepCutoff c (h / 2) (ℓ (ε y)))
    ((contDiff_discSweepCutoff c (h / 2)).comp_contMDiff (ℓ.contDiff.comp_contMDiff hεs))
    (fun y => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩) ?_ ?_ m O hOo
    (hST.trans hOeq) hOd hOs
  · intro y hyS hyT
    have hy : ℓ (ε y) ≤ c - h / 2 := by
      by_contra hlt
      exact hyT ⟨hyS.1, by linarith, by linarith [hyS.2.out]⟩
    filter_upwards [(isOpen_lt hℓε continuous_const).mem_nhds
      (show ℓ (ε y) < c - 2 * (h / 2) / 3 by linarith)] with y' hy'
    exact discSweepCutoff_eq_zero hh2 (le_of_lt hy')
  · intro y hyT hyS
    have hy : c ≤ ℓ (ε y) := by
      by_contra hlt
      exact hyS ⟨hyT.1, not_le.mp hlt⟩
    filter_upwards [(isOpen_lt continuous_const hℓε).mem_nhds
      (show c - (h / 2) / 3 < ℓ (ε y) by linarith)] with y' hy'
    exact discSweepCutoff_eq_one hh2 (le_of_lt hy')

end Sweep

section SweepLine

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]

theorem planarSweep_line {ε : B → ℂ} (hε : _root_.Topology.IsEmbedding ε)
    (hεs : ContMDiff I 𝓘(ℝ, ℂ) ∞ ε) (Good : Set B → Prop)
    (hglue : ∀ V₁ V₂ : Set B, IsOpen V₁ → IsOpen V₂ → Good V₁ → Good V₂ →
      ∀ ρ : B → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ → (∀ b, ρ b ∈ Icc (0 : ℝ) 1) →
      (∀ b ∈ V₁, b ∉ V₂ → ρ =ᶠ[𝓝 b] 0) → (∀ b ∈ V₂, b ∉ V₁ → ρ =ᶠ[𝓝 b] 1) →
      ∀ (m : ℕ) (O : Fin m → Set B), (∀ i, IsOpen (O i)) → V₁ ∩ V₂ = ⋃ i, O i →
      Pairwise (Function.onFun Disjoint O) → (∀ i, (O i).Nonempty → IsSimplyConnected (O i)) →
      Good (V₁ ∪ V₂))
    (hempty : Good ∅) (ℓ : ℂ →L[ℝ] ℝ) {Q : Set ℂ} (hQ : IsOpen Q) {h : ℝ} (hh : 0 < h)
    {c₀ R : ℝ} (hc₀ : c₀ ≤ -R) (hR : ∀ y, |ℓ (ε y)| < R)
    (hpiece : ∀ j : ℕ,
      Good (ε ⁻¹' (Q ∩ discSweepSlab ℓ (c₀ + j * h - h / 2) (c₀ + j * h + h))))
    (hover : ∀ j : ℕ, ∃ (m : ℕ) (O : Fin m → Set B), (∀ i, IsOpen (O i)) ∧
      ε ⁻¹' (Q ∩ discSweepSlab ℓ (c₀ + j * h - h / 2) (c₀ + j * h)) = ⋃ i, O i ∧
      Pairwise (Function.onFun Disjoint O) ∧ ∀ i, (O i).Nonempty → IsSimplyConnected (O i)) :
    Good (ε ⁻¹' Q) := by
  have hk : ∀ j : ℕ, Good (ε ⁻¹' (Q ∩ {z | ℓ z < c₀ + j * h})) := by
    intro j
    induction j with
    | zero =>
      have he : ε ⁻¹' (Q ∩ {z | ℓ z < c₀ + ((0 : ℕ) : ℝ) * h}) = ∅ := by
        ext y
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, CharP.cast_eq_zero, zero_mul,
          add_zero, mem_empty_iff_false, iff_false, not_and, not_lt]
        rintro -
        have := (abs_lt.mp (hR y)).1
        linarith
      rw [he]
      exact hempty
    | succ j ih =>
      have h1 := planarSweep_step hε hεs Good hglue ℓ hQ hh _ ih (hpiece j) (hover j)
      have hc : c₀ + (j : ℝ) * h + h = c₀ + ((j + 1 : ℕ) : ℝ) * h := by
        push_cast
        ring
      rwa [hc] at h1
  obtain ⟨N, hN⟩ := exists_nat_ge ((R - c₀) / h)
  have he : ε ⁻¹' (Q ∩ {z | ℓ z < c₀ + N * h}) = ε ⁻¹' Q := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    rintro -
    have h1 := (abs_lt.mp (hR y)).2
    have h2 : R - c₀ ≤ N * h := (div_le_iff₀ hh).mp hN
    linarith
  rw [← he]
  exact hk N

end SweepLine

section Transfer

variable {B : Type*} [TopologicalSpace B]

theorem isSimplyConnected_preimage_of_contractible {ε : B → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) {T M : Set ℂ} (hM : range ε = M)
    (hT : (T ∩ M).Nonempty → ContractibleSpace ↥(T ∩ M)) (hne : (ε ⁻¹' T).Nonempty) :
    IsSimplyConnected (ε ⁻¹' T) := by
  have h1 : ε '' (ε ⁻¹' T) = T ∩ M := by rw [image_preimage_eq_inter_range, hM]
  have h2 : (T ∩ M).Nonempty := by
    rw [← h1]
    exact hne.image ε
  have h3 : ContractibleSpace ↥(ε '' (ε ⁻¹' T)) := by
    rw [h1]
    exact hT h2
  have : ContractibleSpace ↥(ε ⁻¹' T) := (hε.homeomorphImage (ε ⁻¹' T)).contractibleSpace
  exact inferInstanceAs (SimplyConnectedSpace ↥(ε ⁻¹' T))

theorem exists_lebesgue_good [CompactSpace B] {ε : B → ℂ} (hε : _root_.Topology.IsEmbedding ε)
    (Good : Set B → Prop) (hmono : ∀ V W : Set B, IsOpen W → W ⊆ V → Good V → Good W)
    (hempty : Good ∅) (hloc : ∀ b, ∃ V, IsOpen V ∧ b ∈ V ∧ Good V) :
    ∃ δ > 0, ∀ T : Set ℂ, IsOpen T → (∀ z ∈ T, ∀ w ∈ T, ‖z - w‖ < δ) → Good (ε ⁻¹' T) := by
  choose V hVo hbV hV using hloc
  have hc : ∀ b, ∃ t : Set ℂ, IsOpen t ∧ ε ⁻¹' t = V b := fun b =>
    hε.isInducing.isOpen_iff.mp (hVo b)
  choose t hto htV using hc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range hε.continuous) hto
    (by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ ε ⁻¹' t y := by rw [htV]; exact hbV y
      exact mem_iUnion.mpr ⟨y, hy⟩)
  refine ⟨δ, hδ, fun T hTo hT => ?_⟩
  rcases (ε ⁻¹' T).eq_empty_or_nonempty with he | ⟨y, hy⟩
  · rw [he]
    exact hempty
  obtain ⟨b, hb⟩ := hball (ε y) (mem_range_self y)
  refine hmono _ _ (hTo.preimage hε.continuous) (fun y' hy' => ?_) (hV b)
  rw [← htV b]
  apply hb
  rw [Metric.mem_ball, dist_eq_norm]
  exact hT _ hy' _ hy

end Transfer

theorem stripPiece_eq_planarBox (a b L R : ℝ) : stripPiece a b L R = planarBox L R a b := by
  ext z
  simp only [stripPiece, planarBox, mem_ofPred_eq]
  tauto

theorem isOpen_stripPiece (a b L R : ℝ) : IsOpen (stripPiece a b L R) := by
  rw [stripPiece_eq_planarBox]
  exact isOpen_planarBox _ _ _ _

theorem stripOverlap_decomp {B : Type*} [TopologicalSpace B] {ε : B → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) {M : Set ℂ} (hM : range ε = M) {a b : ℝ} {m : ℕ}
    (L R : Fin m → ℝ) (hdisj : ∀ i j, i ≠ j → R i ≤ L j ∨ R j ≤ L i)
    (hcov : ∀ z ∈ M, a < z.im → z.im < b → ∃ i, L i < z.re ∧ z.re < R i)
    (hcon : ∀ i, (stripPiece a b (L i) (R i) ∩ M).Nonempty →
      ContractibleSpace ↥(stripPiece a b (L i) (R i) ∩ M)) :
    ∃ (m' : ℕ) (O : Fin m' → Set B), (∀ i, IsOpen (O i)) ∧
      ε ⁻¹' (univ ∩ discSweepSlab Complex.imCLM a b) = ⋃ i, O i ∧
      Pairwise (Function.onFun Disjoint O) ∧ ∀ i, (O i).Nonempty → IsSimplyConnected (O i) := by
  refine ⟨m, fun i => ε ⁻¹' stripPiece a b (L i) (R i),
    fun i => (isOpen_stripPiece _ _ _ _).preimage hε.continuous, ?_, ?_,
    fun i hne => isSimplyConnected_preimage_of_contractible hε hM (hcon i) hne⟩
  · ext y
    simp only [mem_preimage, mem_inter_iff, mem_univ, true_and, discSweepSlab, mem_ofPred_eq,
      Complex.imCLM_apply, mem_iUnion, stripPiece]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨i, hi1, hi2⟩ := hcov (ε y) (hM ▸ mem_range_self y) h1 h2
      exact ⟨i, h1, h2, hi1, hi2⟩
    · rintro ⟨i, h1, h2, -, -⟩
      exact ⟨h1, h2⟩
  · intro i j hij
    refine Set.disjoint_left.mpr fun y hyi hyj => ?_
    obtain ⟨-, -, hi1, hi2⟩ := hyi
    obtain ⟨-, -, hj1, hj2⟩ := hyj
    rcases hdisj i j hij with h | h <;> linarith

theorem inter_planarModel_eq_of_im {k : ℕ} {T : Set ℂ} (hT : ∀ z ∈ T, 1 / 2 < |z.im|) :
    T ∩ planarModel k = T ∩ Metric.closedBall (0 : ℂ) 3 := by
  ext z
  simp only [mem_inter_iff, planarModel, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨hz, h1, -⟩
    exact ⟨hz, h1⟩
  · rintro ⟨hz, h1⟩
    refine ⟨hz, h1, fun j _ => ?_⟩
    have h2 := Complex.abs_im_le_norm (z - planarCenter k j)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h2
    linarith [hT z hz]

theorem contractibleSpace_stripPiece_inter_ball {a b L R : ℝ}
    (hne : (stripPiece a b L R ∩ Metric.closedBall (0 : ℂ) 3).Nonempty) :
    ContractibleSpace ↥(stripPiece a b L R ∩ Metric.closedBall (0 : ℂ) 3) := by
  rw [stripPiece_eq_planarBox] at hne ⊢
  exact ((convex_planarBox _ _ _ _).inter (convex_closedBall _ _)).contractibleSpace hne

theorem abs_re_le_three_of_mem_planarModel {k : ℕ} {z : ℂ} (hz : z ∈ planarModel k) :
    |z.re| ≤ 3 :=
  le_trans (Complex.abs_re_le_norm z) hz.1

theorem gridStrip_decomp {B : Type*} [TopologicalSpace B] {ε : B → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hM : range ε = planarModel k) {n : ℕ} (hn : 0 < n) (J : ℤ) :
    ∃ (m' : ℕ) (O : Fin m' → Set B), (∀ i, IsOpen (O i)) ∧
      ε ⁻¹' (univ ∩ discSweepSlab Complex.imCLM (gridPt n J - gridH n / 2) (gridPt n J)) =
        ⋃ i, O i ∧
      Pairwise (Function.onFun Disjoint O) ∧ ∀ i, (O i).Nonempty → IsSimplyConnected (O i) := by
  have hh := gridH_pos hn
  have hN : (((4 * n : ℕ) : ℤ) : ℝ) * gridH n = 1 / 2 := by
    rw [Int.cast_natCast]
    exact four_mul_gridH hn
  set N : ℤ := ((4 * n : ℕ) : ℤ) with hNdef
  have hcov1 : ∀ z ∈ planarModel k, gridPt n J - gridH n / 2 < z.im → z.im < gridPt n J →
      ∃ i : Fin 1, (![-4] : Fin 1 → ℝ) i < z.re ∧ z.re < (![4] : Fin 1 → ℝ) i := by
    intro z hz _ _
    have h := abs_le.mp (abs_re_le_three_of_mem_planarModel hz)
    exact ⟨0, by simp; linarith, by simp; linarith⟩
  have hdisj1 : ∀ i j : Fin 1, i ≠ j →
      (![4] : Fin 1 → ℝ) i ≤ (![-4] : Fin 1 → ℝ) j ∨ (![4] : Fin 1 → ℝ) j ≤ (![-4] : Fin 1 → ℝ) i :=
    fun i j hij => absurd (Subsingleton.elim i j) hij
  have hconvex : (∀ z ∈ stripPiece (gridPt n J - gridH n / 2) (gridPt n J) (-4) 4,
      1 / 2 < |z.im|) ∨ k = 1 →
      ∀ i : Fin 1, (stripPiece (gridPt n J - gridH n / 2) (gridPt n J) ((![-4] : Fin 1 → ℝ) i)
        ((![4] : Fin 1 → ℝ) i) ∩ planarModel k).Nonempty →
      ContractibleSpace ↥(stripPiece (gridPt n J - gridH n / 2) (gridPt n J)
        ((![-4] : Fin 1 → ℝ) i) ((![4] : Fin 1 → ℝ) i) ∩ planarModel k) := by
    intro hcase i hne
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change (stripPiece (gridPt n J - gridH n / 2) (gridPt n J) (-4) 4 ∩ planarModel k).Nonempty
      at hne
    change ContractibleSpace ↥(stripPiece (gridPt n J - gridH n / 2) (gridPt n J) (-4) 4 ∩
      planarModel k)
    rcases hcase with hcase | rfl
    · rw [inter_planarModel_eq_of_im hcase] at hne ⊢
      exact contractibleSpace_stripPiece_inter_ball hne
    · rw [planarModel_one] at hne ⊢
      exact contractibleSpace_stripPiece_inter_ball hne
  by_cases hfar : J ≤ -N - 1 ∨ N ≤ J
  · refine stripOverlap_decomp hε hM ![-4] ![4] hdisj1 hcov1 (hconvex (Or.inl ?_))
    intro z hz
    obtain ⟨h1, h2, -, -⟩ := hz
    simp only [gridPt] at h1 h2
    rcases hfar with hJ | hJ
    · have : (J : ℝ) ≤ -N - 1 := by exact_mod_cast hJ
      rw [abs_of_neg (by nlinarith)]
      nlinarith
    · have : (N : ℝ) ≤ J := by exact_mod_cast hJ
      rw [abs_of_pos (by nlinarith)]
      nlinarith
  push Not at hfar
  obtain ⟨hJ1, hJ2⟩ := hfar
  have hJ1' : (-N : ℝ) ≤ J := by
    have : -N ≤ J := by omega
    exact_mod_cast this
  have hJ2' : (J : ℝ) ≤ N - 1 := by
    have : J ≤ N - 1 := by omega
    exact_mod_cast this
  have hlo : -(1 / 2) ≤ gridPt n J - gridH n / 2 := by
    simp only [gridPt]
    nlinarith
  have hhi : gridPt n J ≤ 1 / 2 := by
    simp only [gridPt]
    nlinarith
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact stripOverlap_decomp hε hM ![-4] ![4] hdisj1 hcov1 (hconvex (Or.inr rfl))
  · refine stripOverlap_decomp hε hM ![-4, 0] ![0, 4] ?_ ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · intro z hz h1 h2
      have h := abs_le.mp (abs_re_le_three_of_mem_planarModel hz)
      rw [planarModel_two] at hz
      have h3 : 1 / 4 ≤ (z.re - 0) ^ 2 + (z.im - 0) ^ 2 := hz.2
      have hre : z.re ≠ 0 := by
        intro h0
        rw [h0] at h3
        nlinarith
      rcases lt_or_gt_of_ne hre with h4 | h4
      · exact ⟨0, by simp; linarith, by simp; linarith⟩
      · exact ⟨1, by simp; linarith, by simp; linarith⟩
    · intro i hne
      have hse : ∀ T : Set ℂ, T ∩ planarModel 2 =
          (T ∩ Metric.closedBall (0 : ℂ) 3) ∩ (T ∩ holeOut 0 0) := by
        intro T
        rw [planarModel_two, Set.inter_inter_distrib_left]
      rw [hse] at hne ⊢
      refine HSliceGood.contractibleSpace (x₀ := ![-2, 2] i) ?_
        (fun z hz => ⟨hz.1.1.1, hz.1.1.2.1⟩) hne
      fin_cases i
      · exact (hSliceGood_stripPiece_ball (by norm_num) hlo hhi (by norm_num)).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))
      · exact (hSliceGood_stripPiece_ball (by norm_num) hlo hhi (by norm_num)).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))
  · refine stripOverlap_decomp hε hM ![-4, -(3 / 2), 3 / 2] ![-(3 / 2), 3 / 2, 4] ?_ ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num
    · intro z hz h1 h2
      have h := abs_le.mp (abs_re_le_three_of_mem_planarModel hz)
      rw [planarModel_three] at hz
      have h3 : 1 / 4 ≤ (z.re - 3 / 2) ^ 2 + (z.im - 0) ^ 2 := hz.1.2
      have h4 : 1 / 4 ≤ (z.re - -(3 / 2)) ^ 2 + (z.im - 0) ^ 2 := hz.2
      have hre1 : z.re ≠ 3 / 2 := by
        intro h0
        rw [h0] at h3
        nlinarith
      have hre2 : z.re ≠ -(3 / 2) := by
        intro h0
        rw [h0] at h4
        nlinarith
      rcases lt_or_gt_of_ne hre2 with h5 | h5
      · exact ⟨0, by simp; linarith, by simp; linarith⟩
      rcases lt_or_gt_of_ne hre1 with h6 | h6
      · exact ⟨1, by simp; linarith, by simp; linarith⟩
      · exact ⟨2, by simp; linarith, by simp; linarith⟩
    · intro i hne
      have hse : ∀ T : Set ℂ, T ∩ planarModel 3 = ((T ∩ Metric.closedBall (0 : ℂ) 3) ∩
          (T ∩ holeOut (3 / 2) 0)) ∩ (T ∩ holeOut (-(3 / 2)) 0) := by
        intro T
        rw [planarModel_three]
        ext z
        simp only [mem_inter_iff]
        tauto
      rw [hse] at hne ⊢
      refine HSliceGood.contractibleSpace (x₀ := ![-(5 / 2), 0, 5 / 2] i) ?_
        (fun z hz => ⟨hz.1.1.1.1, hz.1.1.1.2.1⟩) hne
      fin_cases i
      · exact ((hSliceGood_stripPiece_ball (by norm_num) hlo hhi (by norm_num)).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))
      · exact ((hSliceGood_stripPiece_ball (by norm_num) hlo hhi (by norm_num)).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))
      · exact ((hSliceGood_stripPiece_ball (by norm_num) hlo hhi (by norm_num)).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))).inter
          (hSliceGood_stripPiece_holeOut (by norm_num) (by norm_num) (by norm_num))

section PlanarSweep

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]

theorem gridPt_add (n : ℕ) (J : ℤ) (j : ℕ) :
    gridPt n J + (j : ℝ) * gridH n = gridPt n (J + j) := by
  unfold gridPt
  push_cast
  ring

theorem gridPt_le_neg_four {n : ℕ} (hn : 0 < n) :
    gridPt n (-((32 * n : ℕ) : ℤ) - 1) ≤ -4 := by
  unfold gridPt gridH
  have : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  rw [div_eq_mul_inv]
  field_simp
  nlinarith

theorem planarSweep [CompactSpace B] {ε : B → ℂ} (hε : _root_.Topology.IsEmbedding ε)
    (hεs : ContMDiff I 𝓘(ℝ, ℂ) ∞ ε) {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hM : range ε = planarModel k) (Good : Set B → Prop)
    (hmono : ∀ V W : Set B, IsOpen W → W ⊆ V → Good V → Good W)
    (hloc : ∀ b, ∃ V, IsOpen V ∧ b ∈ V ∧ Good V)
    (hglue : ∀ V₁ V₂ : Set B, IsOpen V₁ → IsOpen V₂ → Good V₁ → Good V₂ →
      ∀ ρ : B → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ → (∀ b, ρ b ∈ Icc (0 : ℝ) 1) →
      (∀ b ∈ V₁, b ∉ V₂ → ρ =ᶠ[𝓝 b] 0) → (∀ b ∈ V₂, b ∉ V₁ → ρ =ᶠ[𝓝 b] 1) →
      ∀ (m : ℕ) (O : Fin m → Set B), (∀ i, IsOpen (O i)) → V₁ ∩ V₂ = ⋃ i, O i →
      Pairwise (Function.onFun Disjoint O) → (∀ i, (O i).Nonempty → IsSimplyConnected (O i)) →
      Good (V₁ ∪ V₂)) :
    Good univ := by
  have hk3 : k ≤ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have hk0 : 0 < k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  obtain ⟨b₀, -⟩ : ∃ b₀, ε b₀ = planarCircleMap k ⟨0, hk0⟩ 1 := by
    have h := planarCircleMap_mem_planarModel hk3 ⟨0, hk0⟩ 1
    rw [← hM] at h
    exact h
  have hempty : Good ∅ := by
    obtain ⟨V, -, -, hV⟩ := hloc b₀
    exact hmono V ∅ isOpen_empty (empty_subset _) hV
  obtain ⟨δ, hδ, hleb⟩ := exists_lebesgue_good hε Good hmono hempty hloc
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  have hh := gridH_pos hn0
  have h3h : 3 * gridH n < δ := by
    unfold gridH
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : 1 / (n : ℝ) < δ := by
      rw [div_lt_iff₀ hn']
      rw [div_lt_iff₀ hδ] at hn
      linarith
    calc 3 * (1 / (8 * (n : ℝ))) < 1 / n := by
          rw [mul_one_div, div_lt_div_iff₀ (by positivity) hn']
          nlinarith
      _ < δ := h1
  have hR : ∀ y, ‖ε y‖ ≤ 3 := fun y => by
    have h := (hM ▸ mem_range_self y : ε y ∈ planarModel k).1
    exact h
  have hre : ∀ y, |Complex.reCLM (ε y)| < 4 := fun y =>
    lt_of_le_of_lt (le_trans (Complex.abs_re_le_norm _) (hR y)) (by norm_num)
  have him : ∀ y, |Complex.imCLM (ε y)| < 4 := fun y =>
    lt_of_le_of_lt (le_trans (Complex.abs_im_le_norm _) (hR y)) (by norm_num)
  set J₀ : ℤ := -((32 * n : ℕ) : ℤ) - 1 with hJ₀
  have hc₀ : gridPt n J₀ ≤ -4 := gridPt_le_neg_four hn0
  have hrow : ∀ J : ℤ, Good (ε ⁻¹' (univ ∩ discSweepSlab Complex.imCLM
      (gridPt n J - gridH n / 2) (gridPt n J + gridH n))) := by
    intro J
    rw [univ_inter]
    refine planarSweep_line hε hεs Good hglue hempty Complex.reCLM (isOpen_discSweepSlab _ _ _)
      hh hc₀ hre (fun i => ?_) (fun i => ?_)
    · refine hleb _ ((isOpen_discSweepSlab _ _ _).inter (isOpen_discSweepSlab _ _ _)) ?_
      rintro z ⟨⟨hz1, hz2⟩, hz3, hz4⟩ w ⟨⟨hw1, hw2⟩, hw3, hw4⟩
      simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hz1 hz2 hz3 hz4 hw1 hw2 hw3 hw4
      calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < 3 * gridH n / 2 + 3 * gridH n / 2 := by
          rw [Complex.sub_re, Complex.sub_im]
          exact add_lt_add (abs_lt.mpr ⟨by linarith, by linarith⟩)
            (abs_lt.mpr ⟨by linarith, by linarith⟩)
        _ < δ := by linarith
    · rw [gridPt_add]
      have hset : discSweepSlab Complex.imCLM (gridPt n J - gridH n / 2) (gridPt n J + gridH n) ∩
          discSweepSlab Complex.reCLM (gridPt n (J₀ + i) - gridH n / 2) (gridPt n (J₀ + i)) =
          gridBox n (J₀ + i) J := by
        ext z
        simp only [discSweepSlab, gridBox, planarBox, mem_inter_iff, mem_ofPred_eq,
          Complex.reCLM_apply, Complex.imCLM_apply]
        tauto
      rw [hset]
      refine ⟨1, fun _ => ε ⁻¹' gridBox n (J₀ + i) J,
        fun _ => (isOpen_planarBox _ _ _ _).preimage hε.continuous, (iUnion_const _).symm,
        fun a b hab => absurd (Subsingleton.elim a b) hab, fun _ hne => ?_⟩
      exact isSimplyConnected_preimage_of_contractible hε hM
        (contractibleSpace_gridBox_inter_planarModel hn0 hk _ _) hne
  have h := planarSweep_line hε hεs Good hglue hempty Complex.imCLM isOpen_univ hh hc₀ him
    (fun j => by rw [gridPt_add]; exact hrow _)
    (fun j => by rw [gridPt_add]; exact gridStrip_decomp hε hk hM hn0 _)
  rwa [preimage_univ] at h

end PlanarSweep

section Fibration

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem bijective_mfderiv_planarEmbedding (F : CircleFibration C U) {k : ℕ} (P : PlanarBase.{u} k)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) (x : F.base.Carrier) :
    Function.Bijective (mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℂ)
      (fun y => P.embedding (e y)) x) := by
  have hP := P.isSmoothEmbedding.contMDiff.mdifferentiableAt (x := e x) (by simp)
  have he := e.contMDiff.mdifferentiableAt (x := x) (by simp)
  have h1 : Function.Injective (mfderiv (SurfaceModel.model P.surface.kind) 𝓘(ℝ, ℂ)
      P.embedding (e x)) := P.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) (e x)
  have h2 : Function.Injective (mfderiv (SurfaceModel.model F.base.kind)
      (SurfaceModel.model P.surface.kind) e x) :=
    (e.mfderivToContinuousLinearEquiv (by simp) x).injective
  have hc : mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℂ) (fun y => P.embedding (e y)) x =
      (mfderiv (SurfaceModel.model P.surface.kind) 𝓘(ℝ, ℂ) P.embedding (e x)).comp
        (mfderiv (SurfaceModel.model F.base.kind) (SurfaceModel.model P.surface.kind) e x) :=
    mfderiv_comp x hP he
  have hinj : Function.Injective
      (mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℂ) (fun y => P.embedding (e y)) x) := by
    rw [hc]
    exact h1.comp h2
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank ℝ (TangentSpace (SurfaceModel.model F.base.kind) x) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) (P.embedding (e x))) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ ℂ
    rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

def complexPullbackOrientation {k : SurfaceModel} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (SurfaceModel.Space k) X] [IsManifold (SurfaceModel.model k) ∞ X] {ε : X → ℂ}
    (hεs : ContMDiff (SurfaceModel.model k) 𝓘(ℝ, ℂ) ∞ ε)
    (hbij : ∀ x, Function.Bijective (mfderiv (SurfaceModel.model k) 𝓘(ℝ, ℂ) ε x)) :
    ManifoldOrientation (SurfaceModel.model k) X 2 :=
  Manifold.manifoldOrientationPullback (SurfaceModel.model k) 𝓘(ℝ, ℂ) (by simp) ε hεs hbij
    (Manifold.exists_manifoldOrientation_of_simply_connected (M := ℂ)
      Complex.finrank_real_complex).some

end Fibration

section FibreGood

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

private def FibreGood (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (V : Set F.base.Carrier) : Prop :=
  ∃ hV : IsOpen V, ∃ τ : FibreCoordinate F ⟨V, hV⟩, τ.IsPositive (o.restrictOpen ⟨V, hV⟩)

private theorem fibreGood_mono (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (V W : Set F.base.Carrier) (hW : IsOpen W) (hWV : W ⊆ V) (hV : FibreGood F o V) :
    FibreGood F o W := by
  obtain ⟨hVo, τ, hτ⟩ := hV
  exact ⟨hW, τ.restrict (W := ⟨W, hW⟩) hWV, hτ.restrict (W := ⟨W, hW⟩) hWV⟩

private theorem fibreGood_loc (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (b : F.base.Carrier) : ∃ V, IsOpen V ∧ b ∈ V ∧ FibreGood F o V := by
  have : LocallyPathConnectedSpace (SurfaceModel.Space F.base.kind) :=
    locallyPathConnectedSpace_surfaceModel F.base.kind
  have : LocallyPathConnectedSpace F.base.Carrier :=
    ChartedSpace.locallyPathConnectedSpace (SurfaceModel.Space F.base.kind) F.base.Carrier
  let N : TopologicalSpace.Opens F.base.Carrier := F.neighborhood b
  let W : Set F.base.Carrier := connectedComponentIn (N : Set F.base.Carrier) b
  have hW : IsOpen W := N.isOpen.connectedComponentIn
  have hbW : b ∈ W := mem_connectedComponentIn (F.mem_neighborhood b)
  have hWN : (⟨W, hW⟩ : TopologicalSpace.Opens F.base.Carrier) ≤ N :=
    connectedComponentIn_subset _ _
  have hconn : ConnectedSpace (⟨W, hW⟩ : TopologicalSpace.Opens F.base.Carrier) :=
    Subtype.connectedSpace (isConnected_connectedComponentIn_iff.mpr (F.mem_neighborhood b))
  obtain ⟨τ', hτ', -⟩ := ((FibreCoordinate.ofTrivialization F b).restrict hWN).exists_isPositive
    (o.restrictOpen ⟨W, hW⟩)
  exact ⟨W, hW, hbW, hW, τ', hτ'⟩

private theorem isGloballyTrivial_of_fibreGood_univ (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (h : FibreGood F o univ) : CircleFibration.IsGloballyTrivial F := by
  obtain ⟨hV, τ, -⟩ := h
  let V : TopologicalSpace.Opens F.base.Carrier := ⟨univ, hV⟩
  have hb : ∀ y, y ∈ V := fun y => mem_univ y
  refine ⟨(openDiffeomorphOfForall (TopologicalSpace.Opens.comap F.projection V)
      (fun x => hb (F.projection x))).symm.trans (τ.toDiffeo.trans
        ((openDiffeomorphOfForall V hb).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))),
    fun x => ?_⟩
  exact τ.fst_eq _

end FibreGood

theorem exists_finset_opens_of_fin {X : Type*} [TopologicalSpace X] {V₁ V₂ : Set X} {m : ℕ}
    (O : Fin m → Set X) (hOo : ∀ i, IsOpen (O i)) (hOeq : V₁ ∩ V₂ = ⋃ i, O i)
    (hOd : Pairwise (Function.onFun Disjoint O))
    (hOs : ∀ i, (O i).Nonempty → IsSimplyConnected (O i)) :
    ∃ O' : Finset (TopologicalSpace.Opens X), V₁ ∩ V₂ = ⋃ W ∈ O', (W : Set X) ∧
      (O' : Set (TopologicalSpace.Opens X)).PairwiseDisjoint id ∧
      ∀ W ∈ O', IsSimplyConnected (W : Set X) := by
  classical
  let f : Fin m → TopologicalSpace.Opens X := fun i => ⟨O i, hOo i⟩
  refine ⟨(Finset.univ.filter fun i => (O i).Nonempty).image f, ?_, ?_, ?_⟩
  · rw [hOeq]
    ext x
    simp only [mem_iUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨f i, ⟨i, ⟨x, hi⟩, rfl⟩, hi⟩
    · rintro ⟨W, ⟨i, -, rfl⟩, hx⟩
      exact ⟨i, hx⟩
  · intro W hW W' hW' hne
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, mem_image,
      mem_ofPred_eq] at hW hW'
    obtain ⟨i, -, rfl⟩ := hW
    obtain ⟨j, -, rfl⟩ := hW'
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    have h := hOd hij
    rw [Function.onFun] at h
    change Disjoint (f i) (f j)
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact h
  · intro W hW
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hW
    obtain ⟨i, hi, rfl⟩ := hW
    exact hOs i hi

section FibreGlue

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

private theorem fibreGood_glue (F : CircleFibration C U)
    (o : ManifoldOrientation (SurfaceModel.model F.base.kind) F.base.Carrier 2)
    (V₁ V₂ : Set F.base.Carrier) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (h₁ : FibreGood F o V₁) (h₂ : FibreGood F o V₂) (ρ : F.base.Carrier → ℝ)
    (hρ : ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρ01 : ∀ b, ρ b ∈ Icc (0 : ℝ) 1) (hρ₁ : ∀ b ∈ V₁, b ∉ V₂ → ρ =ᶠ[𝓝 b] 0)
    (hρ₂ : ∀ b ∈ V₂, b ∉ V₁ → ρ =ᶠ[𝓝 b] 1) (m : ℕ) (O : Fin m → Set F.base.Carrier)
    (hOo : ∀ i, IsOpen (O i)) (hOeq : V₁ ∩ V₂ = ⋃ i, O i)
    (hOd : Pairwise (Function.onFun Disjoint O))
    (hOs : ∀ i, (O i).Nonempty → IsSimplyConnected (O i)) : FibreGood F o (V₁ ∪ V₂) := by
  obtain ⟨hV₁', τ₁, hτ₁⟩ := h₁
  obtain ⟨hV₂', τ₂, hτ₂⟩ := h₂
  let W₁ : TopologicalSpace.Opens F.base.Carrier := ⟨V₁, hV₁'⟩
  let W₂ : TopologicalSpace.Opens F.base.Carrier := ⟨V₂, hV₂'⟩
  obtain ⟨O', hO'eq, hO'd, hO's⟩ := exists_finset_opens_of_fin O hOo hOeq hOd hOs
  have hO : ∃ O : Finset (TopologicalSpace.Opens F.base.Carrier), W₁ ⊓ W₂ = ⨆ O' ∈ O, O' ∧
      (O : Set (TopologicalSpace.Opens F.base.Carrier)).PairwiseDisjoint id ∧
      ∀ O' ∈ O, IsSimplyConnected (O' : Set F.base.Carrier) := by
    refine ⟨O', ?_, hO'd, hO's⟩
    apply SetLike.coe_injective
    rw [TopologicalSpace.Opens.coe_inf]
    simp only [TopologicalSpace.Opens.coe_iSup]
    exact hO'eq
  obtain ⟨τ, hτ, -⟩ := FibreCoordinate.glue τ₁ τ₂ o hτ₁ hτ₂ ρ hρ (fun b => hρ01 b) hρ₁ hρ₂ hO
  have hle : (⟨V₁ ∪ V₂, hV₁.union hV₂⟩ : TopologicalSpace.Opens F.base.Carrier) ≤ W₁ ⊔ W₂ := by
    intro x hx
    rw [TopologicalSpace.Opens.mem_sup]
    exact hx
  exact ⟨hV₁.union hV₂, τ.restrict hle, hτ.restrict hle⟩

theorem CircleFibration.isGloballyTrivial_of_planarEmbedding (F : CircleFibration C U) {k : ℕ}
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) {ε : F.base.Carrier → ℂ}
    (hε : _root_.Topology.IsEmbedding ε)
    (hεs : ContMDiff (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℂ) ∞ ε)
    (hbij : ∀ x, Function.Bijective (mfderiv (SurfaceModel.model F.base.kind) 𝓘(ℝ, ℂ) ε x))
    (hrange : range ε = planarModel k) : CircleFibration.IsGloballyTrivial F := by
  let o := complexPullbackOrientation hεs hbij
  have hgood := planarSweep hε hεs hk hrange (FibreGood F o) (fibreGood_mono F o)
    (fibreGood_loc F o) (fibreGood_glue F o)
  exact isGloballyTrivial_of_fibreGood_univ F o hgood

end FibreGlue

theorem circleBundlesOverPlanarBases_planar (C : CompactCarrier.{u})
    (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U) (k : ℕ)
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (P : PlanarBase.{u} k)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) :
    ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model P.surface.kind).prod (𝓡 1)⟯
      P.surface.Carrier × Circle, ∀ x, (Φ x).1 = e (F.projection x) := by
  have hrange : range (fun y => P.embedding (e y)) = planarModel k := by
    rw [← P.range_embedding]
    exact e.surjective.range_comp P.embedding
  exact CircleFibration.exists_product_of_isGloballyTrivial
    (CircleFibration.isGloballyTrivial_of_planarEmbedding F hk
      (P.isSmoothEmbedding.isEmbedding.comp e.toHomeomorph.isEmbedding)
      (P.isSmoothEmbedding.contMDiff.comp e.contMDiff) (bijective_mfderiv_planarEmbedding F P e)
      hrange) P e

end GC.Seifert
