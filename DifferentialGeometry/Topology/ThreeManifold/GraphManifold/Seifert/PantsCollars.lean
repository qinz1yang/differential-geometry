import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFold
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The truncated hexagon and the three cusp collars of the pants group

Packet K16f, tier 1. For a height `h > 1/2` the three horoball regions
`h ≤ cuspHeight j z` (about `1/2`, `0` and `∞`, the heights of `Seifert/PantsFold.lean`) are
pairwise disjoint on all of `ℍ` (`cuspHeight_disjoint`). The ideal triangle is the union of the
truncated hexagon `pantsHexagon h` (all three heights `≤ h`) and the three collars
`pantsCollar h j` (`idealTriangle_eq_union`), and the hexagon is compact
(`isCompact_pantsHexagon`): on it `Im z ≥ 1/(8h)`.

The collar of the cusp `∞` is identified with `S¹ × [h, ∞)`: for `h > 1/4` an element of
`pantsGroup` moving a point of the horoball `h ≤ Im z` into it acts as a power of `T`
(`exists_zpow_T_smul_eq_of_mem_horoball`), so `horoCoord z = (exp (2πi Re z), Im z)` takes
equal values exactly on `pantsGroup`-orbits of the horoball (`horoCoord_eq_iff`) and maps it
onto `S¹ × [h, ∞)` (`horoCoord_surjOn`).
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix
open scoped MatrixGroups

namespace GC.Seifert

theorem cuspHeight_zero_eq (z : ℂ) :
    cuspHeight 0 z = z.im / (4 * ((z.re - 1 / 2) ^ 2 + z.im ^ 2)) := by
  rw [cuspHeight, cuspCoord_zero_im, show (4 * z.re - 2) ^ 2 + (4 * z.im) ^ 2 =
    4 * (4 * ((z.re - 1 / 2) ^ 2 + z.im ^ 2)) by ring, mul_div_mul_left _ _ four_ne_zero]

theorem cuspHeight_one_eq (z : ℂ) : cuspHeight 1 z = z.im / (4 * (z.re ^ 2 + z.im ^ 2)) := by
  rw [cuspHeight, cuspCoord_one_im, show (4 * z.re) ^ 2 + (4 * z.im) ^ 2 =
    4 * (4 * (z.re ^ 2 + z.im ^ 2)) by ring, mul_div_mul_left _ _ four_ne_zero]

theorem cuspHeight_two_eq (z : ℂ) : cuspHeight 2 z = z.im := by
  rw [cuspHeight, cuspCoord_two_im]

theorem le_cuspHeight_zero_iff {h : ℝ} (z : ℍ) :
    h ≤ cuspHeight 0 z ↔ 4 * h * ((z.re - 1 / 2) ^ 2 + z.im ^ 2) ≤ z.im := by
  have hp : 0 < 4 * ((z.re - 1 / 2) ^ 2 + z.im ^ 2) := by have := z.im_pos; positivity
  rw [cuspHeight_zero_eq, coe_re, coe_im, le_div_iff₀ hp]
  constructor <;> intro h' <;> linarith

theorem le_cuspHeight_one_iff {h : ℝ} (z : ℍ) :
    h ≤ cuspHeight 1 z ↔ 4 * h * (z.re ^ 2 + z.im ^ 2) ≤ z.im := by
  have hp : 0 < 4 * (z.re ^ 2 + z.im ^ 2) := by have := z.im_pos; positivity
  rw [cuspHeight_one_eq, coe_re, coe_im, le_div_iff₀ hp]
  constructor <;> intro h' <;> linarith

theorem cuspHeight_le_zero_iff {h : ℝ} (z : ℍ) :
    cuspHeight 0 z ≤ h ↔ z.im ≤ 4 * h * ((z.re - 1 / 2) ^ 2 + z.im ^ 2) := by
  have hp : 0 < 4 * ((z.re - 1 / 2) ^ 2 + z.im ^ 2) := by have := z.im_pos; positivity
  rw [cuspHeight_zero_eq, coe_re, coe_im, div_le_iff₀ hp]
  constructor <;> intro h' <;> linarith

theorem cuspHeight_le_one_iff {h : ℝ} (z : ℍ) :
    cuspHeight 1 z ≤ h ↔ z.im ≤ 4 * h * (z.re ^ 2 + z.im ^ 2) := by
  have hp : 0 < 4 * (z.re ^ 2 + z.im ^ 2) := by have := z.im_pos; positivity
  rw [cuspHeight_one_eq, coe_re, coe_im, div_le_iff₀ hp]
  constructor <;> intro h' <;> linarith

private theorem disjoint_inf {h y a : ℝ} (hh : 1 / 2 < h) (hy : 0 < y) (h1 : h ≤ y)
    (h2 : 4 * h * (a ^ 2 + y ^ 2) ≤ y) : False := by
  have : 4 * h * y ^ 2 ≤ y := by nlinarith [sq_nonneg a]
  have : 4 * h * y ≤ 1 := by nlinarith
  nlinarith

private theorem disjoint_fin {h x y : ℝ} (hh : 1 / 2 < h)
    (h1 : 4 * h * ((x - 1 / 2) ^ 2 + y ^ 2) ≤ y) (h2 : 4 * h * (x ^ 2 + y ^ 2) ≤ y) : False := by
  have hs : 4 * h * (2 * y ^ 2 + 1 / 8) ≤ 2 * y := by nlinarith [sq_nonneg (x - 1 / 4)]
  have h8 := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 8 * h)
  nlinarith [sq_nonneg (8 * h * y - 1)]

theorem cuspHeight_disjoint {h : ℝ} (hh : 1 / 2 < h) {i j : Fin 3} (hij : i ≠ j) (z : ℍ) :
    ¬ (h ≤ cuspHeight i z ∧ h ≤ cuspHeight j z) := by
  rintro ⟨hi, hj⟩
  have hy := z.im_pos
  have A0 : h ≤ cuspHeight 0 z → 4 * h * ((z.re - 1 / 2) ^ 2 + z.im ^ 2) ≤ z.im :=
    (le_cuspHeight_zero_iff z).1
  have A0' : h ≤ cuspHeight 0 z → 4 * h * ((1 / 2 - z.re) ^ 2 + z.im ^ 2) ≤ z.im :=
    fun H => by nlinarith [A0 H]
  have A1 : h ≤ cuspHeight 1 z → 4 * h * (z.re ^ 2 + z.im ^ 2) ≤ z.im :=
    (le_cuspHeight_one_iff z).1
  have A2 : h ≤ cuspHeight 2 z → h ≤ z.im := fun H => by rwa [cuspHeight_two_eq] at H
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hij rfl
    | exact disjoint_fin hh (A0 hi) (A1 hj)
    | exact disjoint_fin hh (A0 hj) (A1 hi)
    | exact disjoint_inf hh hy (A2 hj) (A0' hi)
    | exact disjoint_inf hh hy (A2 hi) (A0' hj)
    | exact disjoint_inf hh hy (A2 hj) (A1 hi)
    | exact disjoint_inf hh hy (A2 hi) (A1 hj)

def pantsCollar (h : ℝ) (j : Fin 3) : Set ℍ :=
  {z | z ∈ idealTriangle ∧ h ≤ cuspHeight j z}

def pantsHexagon (h : ℝ) : Set ℍ :=
  {z | z ∈ idealTriangle ∧ ∀ j, cuspHeight j z ≤ h}

theorem idealTriangle_eq_union (h : ℝ) :
    idealTriangle = pantsHexagon h ∪ ⋃ j, pantsCollar h j := by
  ext z
  simp only [Set.mem_union, Set.mem_iUnion, pantsHexagon, pantsCollar, Set.mem_ofPred_eq]
  constructor
  · intro hz
    by_cases hj : ∀ j, cuspHeight j z ≤ h
    · exact Or.inl ⟨hz, hj⟩
    · push Not at hj
      obtain ⟨j, hj⟩ := hj
      exact Or.inr ⟨j, hz, hj.le⟩
  · rintro (⟨hz, -⟩ | ⟨j, hz, -⟩) <;> exact hz

theorem pantsCollar_disjoint {h : ℝ} (hh : 1 / 2 < h) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (pantsCollar h i) (pantsCollar h j) :=
  Set.disjoint_left.2 fun z hi hj => cuspHeight_disjoint hh hij z ⟨hi.2, hj.2⟩

theorem mem_pantsHexagon_iff (h : ℝ) (z : ℍ) : z ∈ pantsHexagon h ↔
    0 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 0 ≤ z.re ^ 2 + z.im ^ 2 - z.re / 2 ∧
      z.im ≤ 4 * h * ((z.re - 1 / 2) ^ 2 + z.im ^ 2) ∧ z.im ≤ 4 * h * (z.re ^ 2 + z.im ^ 2) ∧
        z.im ≤ h := by
  constructor
  · rintro ⟨⟨a, b, c⟩, hj⟩
    refine ⟨a, b, ?_, (cuspHeight_le_zero_iff z).1 (hj 0), (cuspHeight_le_one_iff z).1 (hj 1),
      ?_⟩
    · rw [← wallSide_two]
      exact (quarter_le_norm_iff z).1 c
    · have := hj 2
      rwa [cuspHeight_two_eq] at this
  · rintro ⟨a, b, c, d, e, f⟩
    refine ⟨⟨a, b, (quarter_le_norm_iff z).2 (by rw [wallSide_two]; exact c)⟩, fun j => ?_⟩
    fin_cases j
    · exact (cuspHeight_le_zero_iff z).2 d
    · exact (cuspHeight_le_one_iff z).2 e
    · change cuspHeight 2 z ≤ h
      rwa [cuspHeight_two_eq]

private theorem hexagon_im_bound {h x y : ℝ} (hh : 1 / 2 ≤ h) (hy : 0 < y) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 4) (hw : 0 ≤ x ^ 2 + y ^ 2 - x / 2) (hc : y ≤ 4 * h * (x ^ 2 + y ^ 2)) :
    1 / (8 * h) ≤ y := by
  by_contra H
  push Not at H
  have hh8 : 0 < 8 * h := by linarith
  have hy8 : 8 * h * y < 1 := by rwa [lt_div_iff₀ hh8, mul_comm] at H
  have hy4 : y ≤ 1 / 4 := by nlinarith
  have hx4 : x ≤ 4 * y ^ 2 := by nlinarith
  have hx2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have h2 : y ≤ 8 * h * y ^ 2 := by nlinarith
  nlinarith

theorem one_div_le_im_of_mem_pantsHexagon {h : ℝ} (hh : 1 / 2 ≤ h) {z : ℍ}
    (hz : z ∈ pantsHexagon h) : 1 / (8 * h) ≤ z.im := by
  obtain ⟨a, b, c, d, e, -⟩ := (mem_pantsHexagon_iff h z).1 hz
  rcases le_total z.re (1 / 4) with hx | hx
  · exact hexagon_im_bound hh z.im_pos a hx c e
  · have c' : 0 ≤ (1 / 2 - z.re) ^ 2 + z.im ^ 2 - (1 / 2 - z.re) / 2 := by
      have : (1 / 2 - z.re) ^ 2 + z.im ^ 2 - (1 / 2 - z.re) / 2 =
          z.re ^ 2 + z.im ^ 2 - z.re / 2 := by ring
      rw [this]
      exact c
    have d' : z.im ≤ 4 * h * ((1 / 2 - z.re) ^ 2 + z.im ^ 2) := by
      rw [show (1 / 2 - z.re) ^ 2 = (z.re - 1 / 2) ^ 2 by ring]
      exact d
    exact hexagon_im_bound hh z.im_pos (by linarith) (by linarith) c' d'

def hexagonSet (h : ℝ) : Set ℂ :=
  {w | 1 / (8 * h) ≤ w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1 / 2 ∧ 0 ≤ w.re ^ 2 + w.im ^ 2 - w.re / 2 ∧
    w.im ≤ 4 * h * ((w.re - 1 / 2) ^ 2 + w.im ^ 2) ∧ w.im ≤ 4 * h * (w.re ^ 2 + w.im ^ 2) ∧
      w.im ≤ h}

theorem coe_image_pantsHexagon {h : ℝ} (hh : 1 / 2 ≤ h) :
    ((↑) : ℍ → ℂ) '' pantsHexagon h = hexagonSet h := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, b, c, d, e, f⟩ := (mem_pantsHexagon_iff h z).1 hz
    exact ⟨one_div_le_im_of_mem_pantsHexagon hh hz, a, b, c, d, e, f⟩
  · rintro ⟨hy, a, b, c, d, e, f⟩
    have hp : 0 < w.im := lt_of_lt_of_le (by positivity) hy
    exact ⟨⟨w, hp⟩, (mem_pantsHexagon_iff h _).2 ⟨a, b, c, d, e, f⟩, rfl⟩

theorem isCompact_hexagonSet (h : ℝ) : IsCompact (hexagonSet h) := by
  have hbox : IsCompact (Set.Icc (0 : ℝ) (1 / 2) ×ℂ Set.Icc (1 / (8 * h)) h) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine hbox.of_isClosed_subset ?_ fun w hw => ⟨⟨hw.2.1, hw.2.2.1⟩, ⟨hw.1, hw.2.2.2.2.2.2⟩⟩
  have hre : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have him : Continuous fun w : ℂ => w.im := Complex.continuous_im
  have hq : Continuous fun w : ℂ => w.re ^ 2 + w.im ^ 2 - w.re / 2 := by fun_prop
  have h0 : Continuous fun w : ℂ => 4 * h * ((w.re - 1 / 2) ^ 2 + w.im ^ 2) := by fun_prop
  have h1 : Continuous fun w : ℂ => 4 * h * (w.re ^ 2 + w.im ^ 2) := by fun_prop
  rw [hexagonSet]
  simp only [Set.ofPred_and]
  exact (isClosed_le continuous_const him).inter ((isClosed_le continuous_const hre).inter
    ((isClosed_le hre continuous_const).inter ((isClosed_le continuous_const hq).inter
    ((isClosed_le him h0).inter ((isClosed_le him h1).inter (isClosed_le him continuous_const))))))

theorem isCompact_pantsHexagon {h : ℝ} (hh : 1 / 2 ≤ h) : IsCompact (pantsHexagon h) := by
  rw [isEmbedding_coe.isInducing.isCompact_iff, coe_image_pantsHexagon hh]
  exact isCompact_hexagonSet h

private theorem four_dvd_of_zmod {a : ℤ} (h : ((a : ℤ) : ZMod 4) = 0) : (4 : ℤ) ∣ a :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a 4).1 h

theorem exists_zpow_T_smul_eq_of_mem_horoball {h : ℝ} (hh : 1 / 4 < h) {γ : SL(2, ℤ)}
    (hγ : γ ∈ pantsGroup) {z : ℍ} (hz : h ≤ z.im) (hγz : h ≤ (γ • z).im) :
    ∃ n : ℤ, γ • z = ModularGroup.T ^ n • z := by
  by_cases hc : γ 1 0 = 0
  · obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
    exact ⟨n, hn z⟩
  · exfalso
    obtain ⟨-, -, hc4⟩ := (CongruenceSubgroup.Gamma1_mem 4 γ).1 (pantsGroup_le_gamma1 hγ)
    have h4 : (4 : ℤ) ∣ γ 1 0 := four_dvd_of_zmod (by exact_mod_cast hc4)
    obtain ⟨k, hk⟩ := h4
    have hk0 : k ≠ 0 := by rintro rfl; exact hc (by simpa using hk)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ k ^ 2 := by
        have := sq_pos_of_ne_zero hk0
        lia
      exact_mod_cast this
    have hy := z.im_pos
    have hns : ((16 : ℝ) * k ^ 2) * z.im ^ 2 ≤ Complex.normSq (denom γ z) := by
      rw [ModularGroup.denom_apply, Complex.normSq_apply]
      have hc' : ((γ 1 0 : ℤ) : ℂ) = ((4 * k : ℝ) : ℂ) := by rw [hk]; push_cast; ring
      have hd' : ((γ 1 1 : ℤ) : ℂ) = ((γ 1 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc', hd']
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, coe_re, coe_im]
      nlinarith [sq_nonneg ((4 * (k : ℝ)) * z.re + (γ 1 1 : ℝ))]
    have him := ModularGroup.im_smul_eq_div_normSq γ z
    have hpos : 0 < Complex.normSq (denom γ z) :=
      Complex.normSq_pos.2 (denom_ne_zero _ z)
    rw [him, le_div_iff₀ hpos] at hγz
    nlinarith [mul_le_mul_of_nonneg_left hns (by linarith : (0 : ℝ) ≤ h)]

def horoCoord (z : ℍ) : Circle × ℝ := (Circle.exp (2 * Real.pi * z.re), z.im)

theorem horoCoord_zpow_T_smul (n : ℤ) (z : ℍ) :
    horoCoord (ModularGroup.T ^ n • z) = horoCoord z := by
  rw [horoCoord, horoCoord, ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul]
  refine Prod.ext (Circle.exp_eq_exp.2 ⟨n, by ring⟩) rfl

theorem horoCoord_eq_iff {h : ℝ} (hh : 1 / 4 < h) {z w : ℍ} (hz : h ≤ z.im) (hw : h ≤ w.im) :
    horoCoord z = horoCoord w ↔ ∃ γ ∈ pantsGroup, γ • z = w := by
  constructor
  · intro hzw
    simp only [horoCoord, Prod.mk.injEq] at hzw
    obtain ⟨h1, h2⟩ := hzw
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h1
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hre : w.re = z.re + (-m : ℤ) := by
      push_cast
      have : 2 * Real.pi * z.re = 2 * Real.pi * (w.re + m) := by rw [hm]; ring
      linarith [mul_left_cancel₀ hpi this]
    have hT : ModularGroup.T ∈ pantsGroup := Subgroup.subset_closure (Set.mem_insert _ _)
    refine ⟨ModularGroup.T ^ (-m), Subgroup.zpow_mem _ hT _, ?_⟩
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq]
    apply Complex.ext
    · simp only [Complex.add_re, coe_re, Complex.intCast_re]
      rw [hre]
    · simp only [Complex.add_im, coe_im, Complex.intCast_im, add_zero]
      exact h2
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨n, hn⟩ := exists_zpow_T_smul_eq_of_mem_horoball hh hγ hz hw
    rw [hn, horoCoord_zpow_T_smul]

theorem horoCoord_surjOn {h : ℝ} (hh : 0 < h) :
    Set.SurjOn horoCoord {z : ℍ | h ≤ z.im} (Set.univ ×ˢ Set.Ici h) := by
  rintro ⟨u, t⟩ ⟨-, ht⟩
  have ht0 : 0 < t := lt_of_lt_of_le hh ht
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective u
  obtain ⟨a, ha⟩ : ∃ a : ℝ, 2 * Real.pi * a = θ :=
    ⟨θ / (2 * Real.pi), by field_simp⟩
  have him : ((a : ℂ) + t * Complex.I).im = t := by simp
  have hre : ((a : ℂ) + t * Complex.I).re = a := by simp
  refine ⟨⟨(a : ℂ) + t * Complex.I, by rw [him]; exact ht0⟩, ?_, ?_⟩
  · change h ≤ ((a : ℂ) + t * Complex.I).im
    rw [him]
    exact ht
  · refine Prod.ext ?_ ?_
    · change Circle.exp (2 * Real.pi * ((a : ℂ) + t * Complex.I).re) = _
      rw [hre, ha]
    · exact him

end GC.Seifert
