import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.LevelSet
import DifferentialGeometry.Topology.Morse.ModifiedFunction
import Mathlib.Topology.Order.IntermediateValue

namespace DifferentialGeometry.Topology.Morse.CellAttachment

open Set
open Filter
open Manifold

open scoped BigOperators Topology ContDiff
open scoped Manifold

noncomputable section

def modelModifiedDip {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ) (y : MorseModel n) : ℝ :=
  modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖

theorem modelModifiedDip_nonneg {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ) (hε : 0 ≤ ε)
    (y : MorseModel n) : 0 ≤ modelModifiedDip hk ε δ y := by
  dsimp [modelModifiedDip]
  exact mul_nonneg (modMu_nonneg (ε := ε) (t := ‖negPart hk y‖ ^ 2) hε)
    (modGamma_nonneg δ ‖posPart hk y‖)

theorem modifiedNormalForm_eq_sub_dip {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y = morseNormalForm hk c y - modelModifiedDip hk ε δ y := by
  simp [modifiedNormalForm, modelModifiedDip]

theorem modifiedNormalForm_sublevel_iff {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y ≤ c - ε ↔
      ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  rw [morseNormalForm_split]
  dsimp [modelModifiedDip]
  constructor <;> intro h <;> nlinarith

theorem modelModifiedDip_sublevel_denom_pos {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n} (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    (modifiedNormalForm_sublevel_iff hk c ε δ y).1 hy
  by_contra hnot
  have hden : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε ≤ 0 := le_of_not_gt hnot
  have hpos0 : ‖posPart hk y‖ ^ 2 = 0 := by nlinarith
  have hb0 : posPart hk y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hpos0)
  have hDnonneg : 0 ≤ modelModifiedDip hk ε δ y := modelModifiedDip_nonneg hk ε δ (le_of_lt hε) y
  have hmu : modMu ε (‖negPart hk y‖ ^ 2) = 3 / 2 * ε := by
    exact modMu_const hε (by nlinarith [hden, hDnonneg])
  have hs : ‖posPart hk y‖ ≤ δ / 2 := by
    rw [hb0]
    exact by
      have hz : (‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖) = 0 := by simp
      rw [hz]
      exact le_of_lt (half_pos hδ)
  have hga : modGamma δ ‖posPart hk y‖ = 1 := modGamma_one hδ hs
  have hden' : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε =
      ‖negPart hk y‖ ^ 2 + ε := by
    dsimp [modelModifiedDip]
    rw [hmu, hga]
    ring
  nlinarith [hden, hden', sq_nonneg ‖negPart hk y‖]

noncomputable def modelModifiedStretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε))) • posPart hk y)

theorem modelModifiedStretchMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelModifiedStretchMap hk ε r δ y) = negPart hk y := by
  dsimp [modelModifiedStretchMap]
  rw [negPart_recombine]

theorem modelModifiedStretchMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    posPart hk (modelModifiedStretchMap hk ε r δ y) =
      (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε))) • posPart hk y := by
  dsimp [modelModifiedStretchMap]
  rw [posPart_recombine]

theorem modelModifiedStretchMap_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (y : MorseModel n)
    (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 =
      ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) /
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
  rw [modelModifiedStretchMap_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt]
  · field_simp
  · have hpos := modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
    have hnum : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      nlinarith [sq_nonneg ‖negPart hk y‖, sq_nonneg r]
    exact div_nonneg hnum (le_of_lt hpos)

theorem modelModifiedStretchMap_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    {y : MorseModel n} (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    morseNormalForm hk c (modelModifiedStretchMap hk ε r δ y) ≤ c + r ^ 2 / 2 := by
  have hsq := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hy
  rw [morseNormalForm_split]
  rw [modelModifiedStretchMap_negPart]
  have hle : ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
      modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
    have hnonneg : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      nlinarith [sq_nonneg ‖negPart hk y‖, sq_nonneg r]
    have hle' : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
      (modifiedNormalForm_sublevel_iff hk c ε δ y).1 hy
    rw [hsq]
    have hmul : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) ≤
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) *
          (‖negPart hk y‖ ^ 2 + r ^ 2) := by
      exact mul_le_mul_of_nonneg_right hle' hnonneg
    rw [div_le_iff₀ hd]
    nlinarith [hmul]
  nlinarith [hle]

theorem modelModifiedStretchMap_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : modifiedNormalForm hk c ε δ y = c - ε) :
    morseNormalForm hk c (modelModifiedStretchMap hk ε r δ y) = c + r ^ 2 / 2 := by
  have hmem : modifiedNormalForm hk c ε δ y ≤ c - ε := le_of_eq hy
  have hsq := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hmem
  rw [morseNormalForm_split]
  rw [modelModifiedStretchMap_negPart]
  have hle' : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
    have hiff := modifiedNormalForm_sublevel_iff hk c ε δ y
    have hge : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε ≤
        ‖posPart hk y‖ ^ 2 := by
      rw [modifiedNormalForm_eq_sub_dip, morseNormalForm_split] at hy
      dsimp [modelModifiedDip] at hy ⊢
      nlinarith
    exact le_antisymm (hiff.1 (le_of_eq hy)) hge
  have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hmem
  have hnorm : ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [hsq, hle']
    field_simp [ne_of_gt hd]
  rw [hnorm]
  ring

theorem modelModifiedStretchMap_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : 0 < r ^ 2) {y : MorseModel n}
    (hy : modifiedNormalForm hk c ε δ y < c - ε) :
    morseNormalForm hk c (modelModifiedStretchMap hk ε r δ y) < c + r ^ 2 / 2 := by
  have hmem : modifiedNormalForm hk c ε δ y ≤ c - ε := le_of_lt hy
  have hsq := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hmem
  rw [morseNormalForm_split]
  rw [modelModifiedStretchMap_negPart]
  have hle' : ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
    rw [modifiedNormalForm_eq_sub_dip, morseNormalForm_split] at hy
    dsimp [modelModifiedDip] at hy ⊢
    nlinarith
  have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hmem
  have hnorm : ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 <
      ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [hsq]
    have hpos : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by nlinarith [sq_nonneg ‖negPart hk y‖, hr]
    have hmul : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) <
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) *
          (‖negPart hk y‖ ^ 2 + r ^ 2) := by
      exact mul_lt_mul_of_pos_right hle' hpos
    rw [div_lt_iff₀ hd]
    nlinarith [hmul]
  nlinarith [hnorm]


def modGammaSqrt (δ : ℝ) (u : ℝ) : ℝ := modGamma δ (Real.sqrt u)

theorem modGammaSqrt_antitone {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (modGammaSqrt δ) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  dsimp [modGammaSqrt]
  exact modGamma_antitone hδ (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) (Real.sqrt_monotone hab)

def modelModifiedFiberDip (ε δ s u : ℝ) : ℝ := modMu ε s * modGammaSqrt δ u

theorem modelModifiedFiberDip_nonneg {ε δ s u : ℝ} (hε : 0 ≤ ε) :
    0 ≤ modelModifiedFiberDip ε δ s u := by
  dsimp [modelModifiedFiberDip]
  exact mul_nonneg (modMu_nonneg hε) (modGamma_nonneg δ (Real.sqrt u))

theorem modelModifiedFiberDip_antitone {ε δ s : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    AntitoneOn (modelModifiedFiberDip ε δ s) (Ici (0 : ℝ)) := by
  intro u hu v hv huv
  dsimp [modelModifiedFiberDip]
  exact mul_le_mul_of_nonneg_left (modGammaSqrt_antitone hδ hu hv huv) (modMu_nonneg hε)

theorem modelModifiedFiberDip_le {ε δ s u : ℝ} (hε : 0 ≤ ε) :
    modelModifiedFiberDip ε δ s u ≤ 3 / 2 * ε := by
  dsimp [modelModifiedFiberDip]
  have h1 : modMu ε s * modGammaSqrt δ u ≤ modMu ε s * 1 := by
    exact mul_le_mul_of_nonneg_left (modGamma_le_one δ (Real.sqrt u)) (modMu_nonneg hε)
  have h2 : modMu ε s ≤ 3 / 2 * ε := modMu_le (ε := ε) (t := s) hε
  nlinarith [h1, h2]

theorem modMu_denom_lower {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ s + 2 * modMu ε s - 2 * ε := by
  by_cases hs2 : s ≤ 2 * ε
  · have hmu : modMu ε s = 3 / 2 * ε := modMu_const hε hs2
    rw [hmu]
    nlinarith [hs]
  · have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
    nlinarith [hs, hmu]

theorem modelModifiedFiberDip_zero {ε δ s : ℝ} (hδ : 0 < δ) :
    modelModifiedFiberDip ε δ s 0 = modMu ε s := by
  dsimp [modelModifiedFiberDip, modGammaSqrt]
  have hz : Real.sqrt (0 : ℝ) = 0 := by simp
  rw [hz]
  have hg : modGamma δ 0 = 1 := modGamma_one hδ (by positivity)
  rw [hg]
  ring

theorem modelModifiedFiberRoot_exists (ε δ r s w2 : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    ∃ u : ℝ, 0 ≤ u ∧
      u * (s + r ^ 2) = w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) := by
  let F : ℝ → ℝ := fun u => u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε)
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hs, hr2]
  have hF0 : F 0 ≤ 0 := by
    dsimp [F]
    rw [modelModifiedFiberDip_zero hδ]
    have hden : 0 ≤ s + 2 * modMu ε s - 2 * ε := modMu_denom_lower hε hs
    nlinarith [hw, hden]
  have hq : 0 ≤ w2 * (s + ε) / (s + r ^ 2) := by
    have hsε : 0 ≤ s + ε := by nlinarith [hs, hε]
    exact div_nonneg (mul_nonneg hw hsε) (le_of_lt hsr)
  obtain ⟨M, hM⟩ := exists_gt (w2 * (s + ε) / (s + r ^ 2))
  let U : ℝ := M + 1
  have hFUp : 0 < F U := by
    dsimp [F, U]
    have hbd : s + 2 * modelModifiedFiberDip ε δ s U - 2 * ε ≤ s + ε := by
      have hDle : modelModifiedFiberDip ε δ s U ≤ 3 / 2 * ε := modelModifiedFiberDip_le (le_of_lt hε)
      nlinarith
    have hstep : w2 * (s + ε) < M * (s + r ^ 2) := (div_lt_iff₀ hsr).mp hM
    have h1 : (M + 1) * (s + r ^ 2) - w2 * (s + ε) > 0 := by nlinarith [hstep, hsr]
    nlinarith [hbd, h1]
  have hcont : ContinuousOn F (Icc 0 U) := by
    have hcd : Continuous (fun u : ℝ => modelModifiedFiberDip ε δ s u) := by
      dsimp [modelModifiedFiberDip, modGammaSqrt]
      have hc1 : Continuous (fun u : ℝ => modMu ε s) := continuous_const
      have hc2 : Continuous (fun u : ℝ => modGamma δ (Real.sqrt u)) :=
        (contDiff_modGamma (δ := δ)).continuous.comp Real.continuous_sqrt
      exact hc1.mul hc2
    dsimp [F]
    fun_prop
  have himg : (0 : ℝ) ∈ F '' Icc 0 U := by
    have hUpos : 0 < U := by
      dsimp [U]
      have hMpos : 0 < M := lt_of_le_of_lt hq hM
      linarith
    exact intermediate_value_Icc (le_of_lt hUpos) hcont ⟨hF0, le_of_lt hFUp⟩
  rcases himg with ⟨u, hu, hFu⟩
  refine ⟨u, hu.1, ?_⟩
  dsimp [F] at hFu
  linarith

theorem modelModifiedFiberRoot_unique (ε δ r s w2 : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu' : u * (s + r ^ 2) = w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε))
    (hv' : v * (s + r ^ 2) = w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε)) :
    u = v := by
  by_contra huv
  have hlt := lt_or_gt_of_ne huv
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hs, hr2]
  rcases hlt with hlt | hgt
  · have hmono : u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) <
      v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) := by
      have hD : modelModifiedFiberDip ε δ s v ≤ modelModifiedFiberDip ε δ s u :=
        modelModifiedFiberDip_antitone (le_of_lt hε) (le_of_lt hδ) hu hv (le_of_lt hlt)
      have hd : 0 < (v - u) * (s + r ^ 2) := mul_pos (sub_pos.mpr hlt) hsr
      nlinarith
    have heq : u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) =
        v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) := by
      rw [hu', hv']
      ring
    exact (not_lt_of_ge (le_of_eq heq.symm)) hmono
  · have hmono : v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) <
      u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) := by
      have hD : modelModifiedFiberDip ε δ s u ≤ modelModifiedFiberDip ε δ s v :=
        modelModifiedFiberDip_antitone (le_of_lt hε) (le_of_lt hδ) hv hu (le_of_lt hgt)
      have hd : 0 < (u - v) * (s + r ^ 2) := mul_pos (sub_pos.mpr hgt) hsr
      nlinarith
    have heq : v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) =
        u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) := by
      rw [hv', hu']
      ring
    exact (not_lt_of_ge (le_of_eq heq.symm)) hmono

noncomputable def modelModifiedFiberRoot (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (s w2 : ℝ) : ℝ :=
  if hs₀ : 0 ≤ s then
    if hw₀ : 0 ≤ w2 then
      Classical.choose (modelModifiedFiberRoot_exists ε δ r s w2 hε hδ hr hs₀ hw₀)
    else 0
  else 0

theorem modelModifiedFiberRoot_nonneg {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 ≤ modelModifiedFiberRoot ε δ r hε hδ hr s w2 := by
  rw [modelModifiedFiberRoot, dif_pos hs, dif_pos hw]
  exact (Classical.choose_spec (modelModifiedFiberRoot_exists ε δ r s w2 hε hδ hr hs hw)).1

theorem modelModifiedFiberRoot_eq {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) =
      w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) := by
  rw [modelModifiedFiberRoot, dif_pos hs, dif_pos hw]
  exact (Classical.choose_spec (modelModifiedFiberRoot_exists ε δ r s w2 hε hδ hr hs hw)).2



noncomputable def modelModifiedUnstretchFactor (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (s w2 : ℝ) : ℝ :=
  Real.sqrt ((s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
      - 2 * ε) / (s + r ^ 2))

noncomputable def modelModifiedUnstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) • posPart hk y)

theorem modelModifiedUnstretchMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    negPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) = negPart hk y := by
  dsimp [modelModifiedUnstretchMap]
  rw [negPart_recombine]

theorem modelModifiedUnstretchMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) =
      (modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) • posPart hk y := by
  dsimp [modelModifiedUnstretchMap]
  rw [posPart_recombine]

theorem modelModifiedDip_eq_fiber {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ) (y : MorseModel n) :
    modelModifiedDip hk ε δ y = modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
  dsimp [modelModifiedDip, modelModifiedFiberDip, modGammaSqrt]
  congr 1
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]


theorem modifiedSublevel_norm_sq_le {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 ≤ ε) {z : MorseModel n} (hz : modifiedNormalForm hk c ε δ z ≤ c - ε) :
    morseNorm n z ^ 2 ≤ 2 * ‖negPart hk z‖ ^ 2 + ε := by
  have hpos : ‖posPart hk z‖ ^ 2 ≤ ‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε :=
    (modifiedNormalForm_sublevel_iff hk c ε δ z).1 hz
  have hdip : modelModifiedDip hk ε δ z ≤ 3 / 2 * ε := by
    rw [modelModifiedDip_eq_fiber]
    exact modelModifiedFiberDip_le hε
  have hnorm : morseNorm n z ^ 2 = ‖negPart hk z‖ ^ 2 + ‖posPart hk z‖ ^ 2 := by
    calc
      morseNorm n z ^ 2 = morseNorm n (recombine hk (negPart hk z) (posPart hk z)) ^ 2 := by
        rw [recombine_decompose hk z]
      _ = ‖negPart hk z‖ ^ 2 + ‖posPart hk z‖ ^ 2 :=
        morseNorm_recombine_sq hk (negPart hk z) (posPart hk z)
  nlinarith [hpos, hdip, hnorm]


theorem modelModifiedFiberDenom_root_nonneg {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 ≤ s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
      - 2 * ε := by
  by_cases hu : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = 0
  · rw [hu]
    have hg0 : modGammaSqrt δ 0 = 1 := by
      dsimp [modGammaSqrt]
      have hz : Real.sqrt (0 : ℝ) = 0 := by simp
      rw [hz]
      exact modGamma_one hδ (le_of_lt (half_pos hδ))
    have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
    have hga : 0 ≤ modGammaSqrt δ 0 := modGamma_nonneg δ (Real.sqrt 0)
    have hd : 0 ≤ s + 2 * modMu ε s - 2 * ε := modMu_denom_lower hε hs
    dsimp [modelModifiedFiberDip]
    rw [hg0]
    nlinarith [hmu, hd]
  · have hpos : 0 < modelModifiedFiberRoot ε δ r hε hδ hr s w2 :=
      lt_of_le_of_ne (modelModifiedFiberRoot_nonneg (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw) (Ne.symm hu)
    have hroot' := modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw
    have hsr : 0 < s + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [hs, hr2]
    have hmul : 0 ≤ modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) :=
      mul_nonneg (le_of_lt hpos) (le_of_lt hsr)
    have hrew : modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) =
        w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
          - 2 * ε) := by
      simpa [modelModifiedFiberDip] using hroot'
    nlinarith [hmul, hrew, hw]

theorem modelModifiedUnstretchMap_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 =
      ‖posPart hk y‖ ^ 2 *
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
          (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) /
        (‖negPart hk y‖ ^ 2 + r ^ 2) := by
  dsimp [modelModifiedUnstretchMap, modelModifiedUnstretchFactor]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt]
  · field_simp
  · have hsr : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [sq_nonneg ‖negPart hk y‖, hr2]
    have hden : 0 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
        (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε :=
      modelModifiedFiberDenom_root_nonneg hε hδ hr (sq_nonneg ‖negPart hk y‖)
        (sq_nonneg ‖posPart hk y‖)
    exact div_nonneg hden (le_of_lt hsr)

theorem modelModifiedUnstretchMap_mem_modified {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : morseNormalForm hk c y ≤ c + r ^ 2 / 2) :
    modifiedNormalForm hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) ≤ c - ε := by
  set s : ℝ := ‖negPart hk y‖ ^ 2 with hs_def
  set w2 : ℝ := ‖posPart hk y‖ ^ 2 with hw2_def
  set u : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2 with hu_def
  set D : ℝ := s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε with hD_def
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    rw [hs_def]
    nlinarith [hr2]
  have hroot' : u * (s + r ^ 2) = w2 * D := by
    rw [hu_def, hD_def]
    simpa using (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2)
      hε hδ hr (by rw [hs_def]; exact sq_nonneg _) (by rw [hw2_def]; exact sq_nonneg _))
  have hw2le : w2 ≤ s + r ^ 2 := by
    rw [hs_def, hw2_def]
    rw [morseNormalForm_split] at hy
    nlinarith
  have hD0 : 0 ≤ D := by
    rw [hD_def]
    simpa using (modelModifiedFiberDenom_root_nonneg hε hδ hr (by rw [hs_def]; exact sq_nonneg _)
      (by rw [hw2_def]; exact sq_nonneg _))
  have huleD : u ≤ D := by
    have hmul : u * (s + r ^ 2) ≤ D * (s + r ^ 2) := by
      rw [hroot']
      calc
        w2 * D ≤ (s + r ^ 2) * D := mul_le_mul_of_nonneg_right hw2le hD0
        _ = D * (s + r ^ 2) := by ring
    exact (mul_le_mul_iff_of_pos_right hsr).mp hmul
  have hsq' : ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 = u := by
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : w2 * D / (s + r ^ 2) = u := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    simpa [hs_def, hw2_def, hD_def, hu_def] using hdiv
  exact (modifiedNormalForm_sublevel_iff hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)).2 (by
    rw [modelModifiedDip_eq_fiber]
    rw [modelModifiedUnstretchMap_negPart]
    rw [hsq']
    rw [← hs_def]
    exact huleD)



theorem modifiedNormalForm_eq_iff {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y = c - ε ↔
      ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  rw [morseNormalForm_split]
  dsimp [modelModifiedDip]
  constructor <;> intro h <;> nlinarith

theorem modifiedNormalForm_lt_iff {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y < c - ε ↔
      ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  rw [morseNormalForm_split]
  dsimp [modelModifiedDip]
  constructor <;> intro h <;> nlinarith

theorem modelModifiedFiberDenom_root_pos {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 < s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
      - 2 * ε := by
  have hroot_nonneg := modelModifiedFiberRoot_nonneg (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw
  by_cases hu : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = 0
  · rw [hu]
    have hg0 : modGammaSqrt δ 0 = 1 := by
      dsimp [modGammaSqrt]
      have hz : Real.sqrt (0 : ℝ) = 0 := by simp
      rw [hz]
      exact modGamma_one hδ (le_of_lt (half_pos hδ))
    have hmain : 0 < s + 2 * modMu ε s - 2 * ε := by
      by_cases hs2 : s ≤ 2 * ε
      · have hmu : modMu ε s = 3 / 2 * ε := modMu_const hε hs2
        rw [hmu]
        nlinarith [hs]
      · have hgt : 2 * ε < s := lt_of_not_ge hs2
        have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
        nlinarith [hmu]
    dsimp [modelModifiedFiberDip]
    rw [hg0]
    nlinarith [hmain]
  · have hpos : 0 < modelModifiedFiberRoot ε δ r hε hδ hr s w2 :=
      lt_of_le_of_ne hroot_nonneg (Ne.symm hu)
    have hroot' := modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw
    have hsr : 0 < s + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [hs, hr2]
    have hden_nonneg : 0 ≤ s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε :=
      modelModifiedFiberDenom_root_nonneg hε hδ hr hs hw
    have hw2pos : 0 < w2 := by
      by_contra hw0
      have hw2le : w2 ≤ 0 := le_of_not_gt hw0
      have hz : w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) = 0 := by
        have hmul : w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hw2le hden_nonneg
        have hge : 0 ≤ w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) := by
          exact mul_nonneg hw hden_nonneg
        exact le_antisymm hmul hge
      have hz' : modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) = 0 := by
        rw [hroot']
        exact hz
      have hz'' : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = 0 := by
        exact (mul_eq_zero.mp hz').resolve_right (ne_of_gt hsr)
      exact hu hz''
    have hden : 0 < s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε := by
      have heq : modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) =
          w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) := hroot'
      have hmul : 0 < modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) :=
        mul_pos hpos hsr
      rw [heq] at hmul
      exact (pos_of_mul_pos_right hmul (le_of_lt hw2pos))
    exact hden

theorem modelModifiedUnstretchMap_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : morseNormalForm hk c y = c + r ^ 2 / 2) :
    modifiedNormalForm hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) = c - ε := by
  set s : ℝ := ‖negPart hk y‖ ^ 2 with hs_def
  set w2 : ℝ := ‖posPart hk y‖ ^ 2 with hw2_def
  set u : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2 with hu_def
  set D : ℝ := s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε with hD_def
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    rw [hs_def]
    nlinarith [hr2]
  have hroot' : u * (s + r ^ 2) = w2 * D := by
    rw [hu_def, hD_def]
    simpa using (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2)
      hε hδ hr (by rw [hs_def]; exact sq_nonneg _) (by rw [hw2_def]; exact sq_nonneg _))
  have hw2eq : w2 = s + r ^ 2 := by
    rw [hs_def, hw2_def]
    rw [morseNormalForm_split] at hy
    nlinarith
  have hEqD : u = D := by
    have hmul : u * (s + r ^ 2) = D * (s + r ^ 2) := by
      rw [hroot', hw2eq]
      ring
    exact (mul_right_cancel₀ (ne_of_gt hsr)) hmul
  have hsq' : ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 = u := by
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : w2 * D / (s + r ^ 2) = u := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    simpa [hs_def, hw2_def, hD_def, hu_def] using hdiv
  exact (modifiedNormalForm_eq_iff hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)).2 (by
    rw [modelModifiedDip_eq_fiber]
    rw [modelModifiedUnstretchMap_negPart]
    rw [hsq']
    rw [← hs_def]
    exact hEqD)

theorem modelModifiedUnstretchMap_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : morseNormalForm hk c y < c + r ^ 2 / 2) :
    modifiedNormalForm hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) < c - ε := by
  set s : ℝ := ‖negPart hk y‖ ^ 2 with hs_def
  set w2 : ℝ := ‖posPart hk y‖ ^ 2 with hw2_def
  set u : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2 with hu_def
  set D : ℝ := s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε with hD_def
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    rw [hs_def]
    nlinarith [hr2]
  have hroot' : u * (s + r ^ 2) = w2 * D := by
    rw [hu_def, hD_def]
    simpa using (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2)
      hε hδ hr (by rw [hs_def]; exact sq_nonneg _) (by rw [hw2_def]; exact sq_nonneg _))
  have hw2lt : w2 < s + r ^ 2 := by
    rw [hs_def, hw2_def]
    rw [morseNormalForm_split] at hy
    nlinarith
  have hDpos : 0 < D := by
    rw [hD_def]
    simpa using (modelModifiedFiberDenom_root_pos hε hδ hr (by rw [hs_def]; exact sq_nonneg _)
      (by rw [hw2_def]; exact sq_nonneg _))
  have hltD : u < D := by
    have hmul : u * (s + r ^ 2) < D * (s + r ^ 2) := by
      rw [hroot']
      calc
        w2 * D < (s + r ^ 2) * D := mul_lt_mul_of_pos_right hw2lt hDpos
        _ = D * (s + r ^ 2) := by ring
    exact (mul_lt_mul_iff_of_pos_right hsr).mp hmul
  have hsq' : ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 = u := by
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : w2 * D / (s + r ^ 2) = u := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    simpa [hs_def, hw2_def, hD_def, hu_def] using hdiv
  exact (modifiedNormalForm_lt_iff hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)).2 (by
    rw [modelModifiedDip_eq_fiber]
    rw [modelModifiedUnstretchMap_negPart]
    rw [hsq']
    rw [← hs_def]
    exact hltD)




theorem sqrt_div_mul_sqrt_rev {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
  have h1 : 0 ≤ a / b := div_nonneg (le_of_lt ha) (le_of_lt hb)
  rw [← Real.sqrt_mul h1]
  have hprod : (a / b) * (b / a) = 1 := by field_simp [ne_of_gt ha, ne_of_gt hb]
  rw [hprod, Real.sqrt_one]

theorem modelModifiedUnstretchFactor_of_root {ε δ r s w2 u : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0)
    (hroot : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = u) :
    modelModifiedUnstretchFactor ε δ r hε hδ hr s w2 =
      Real.sqrt ((s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) / (s + r ^ 2)) := by
  dsimp [modelModifiedUnstretchFactor]
  rw [hroot]

theorem modelModifiedUnstretchMap_stretchMap {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    modelModifiedUnstretchMap hk ε r δ hε hδ hr (modelModifiedStretchMap hk ε r δ y) = y := by
  let z : MorseModel n := modelModifiedStretchMap hk ε r δ y
  have hzneg : negPart hk z = negPart hk y := modelModifiedStretchMap_negPart hk ε r δ y
  have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
  have hsr : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hr2, sq_nonneg ‖negPart hk y‖]
  have hdeq : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε =
      ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)
        - 2 * ε := by
    rw [modelModifiedDip_eq_fiber]
  have hroot : modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2)
      (‖posPart hk z‖ ^ 2) = ‖posPart hk y‖ ^ 2 := by
    have hsqz := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hy
    have hrootEq2 : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) =
        ‖posPart hk z‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
          (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) := by
      calc
        ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2)
            = (‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) /
                (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε)) *
                (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
              field_simp [ne_of_gt hd]
        _ = ‖posPart hk z‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
              rw [hsqz]
        _ = ‖posPart hk z‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
              (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) := by
              rw [hdeq]
    exact modelModifiedFiberRoot_unique ε δ r (‖negPart hk y‖ ^ 2) (‖posPart hk z‖ ^ 2)
      hε hδ hr (sq_nonneg _) (sq_nonneg _)
      (modelModifiedFiberRoot_nonneg (ε := ε) (δ := δ) (r := r) (s := ‖negPart hk y‖ ^ 2)
        (w2 := ‖posPart hk z‖ ^ 2) hε hδ hr (sq_nonneg _) (sq_nonneg _))
      (sq_nonneg _)
      (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := ‖negPart hk y‖ ^ 2)
        (w2 := ‖posPart hk z‖ ^ 2) hε hδ hr (sq_nonneg _) (sq_nonneg _))
      hrootEq2
  calc
    modelModifiedUnstretchMap hk ε r δ hε hδ hr z
        = recombine hk (negPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr z))
            (posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr z)) :=
      (recombine_decompose hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr z)).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · rw [modelModifiedUnstretchMap_negPart, hzneg]
      · rw [modelModifiedUnstretchMap_posPart]
        rw [hzneg]
        have hfactor : modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk y‖ ^ 2)
            (‖posPart hk z‖ ^ 2) =
            Real.sqrt ((‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
              (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) / (‖negPart hk y‖ ^ 2 + r ^ 2)) := by
          exact modelModifiedUnstretchFactor_of_root hε hδ hr hroot
        rw [hfactor]
        rw [modelModifiedStretchMap_posPart]
        rw [hdeq]
        rw [smul_smul]
        have hDpos' : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
            (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε := by
          simpa [hdeq] using hd
        have hscalar : Real.sqrt ((‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
              (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / (‖negPart hk y‖ ^ 2 + 2 *
              modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε)) = 1 :=
          sqrt_div_mul_sqrt_rev hDpos' hsr
        calc
          (Real.sqrt ((‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
                (‖posPart hk y‖ ^ 2) - 2 * ε) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / (‖negPart hk y‖ ^ 2 + 2 *
                modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε))) •
              posPart hk y
              = (1 : ℝ) • posPart hk y := congrArg (fun t : ℝ => t • posPart hk y) hscalar
          _ = posPart hk y := by simp
    _ = y := recombine_decompose hk y


theorem modelModifiedStretchMap_unstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (y : MorseModel n) :
    modelModifiedStretchMap hk ε r δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) = y := by
  let z : MorseModel n := modelModifiedUnstretchMap hk ε r δ hε hδ hr y
  have hzneg : negPart hk z = negPart hk y := modelModifiedUnstretchMap_negPart hk ε r δ hε hδ hr y
  have hsr : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hr2, sq_nonneg ‖negPart hk y‖]
  have hroot' : modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) * (‖negPart hk y‖ ^ 2 + r ^ 2) =
      ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
        (‖negPart hk y‖ ^ 2)
        (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) :=
    modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := ‖negPart hk y‖ ^ 2)
      (w2 := ‖posPart hk y‖ ^ 2) hε hδ hr (sq_nonneg ‖negPart hk y‖)
      (sq_nonneg ‖posPart hk y‖)
  have hDpos : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
      (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε :=
    modelModifiedFiberDenom_root_pos hε hδ hr (sq_nonneg ‖negPart hk y‖)
      (sq_nonneg ‖posPart hk y‖)
  have hsqz : ‖posPart hk z‖ ^ 2 =
      modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
    dsimp [z]
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
          (‖negPart hk y‖ ^ 2)
          (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) /
          (‖negPart hk y‖ ^ 2 + r ^ 2) =
        modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    exact hdiv
  have hDpos : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
      (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε :=
    modelModifiedFiberDenom_root_pos hε hδ hr (sq_nonneg ‖negPart hk y‖)
      (sq_nonneg ‖posPart hk y‖)
  have hsqz : ‖posPart hk z‖ ^ 2 =
      modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
    dsimp [z]
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
          (‖negPart hk y‖ ^ 2)
          (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) /
          (‖negPart hk y‖ ^ 2 + r ^ 2) =
        modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    exact hdiv
  calc
    modelModifiedStretchMap hk ε r δ z
        = recombine hk (negPart hk (modelModifiedStretchMap hk ε r δ z))
            (posPart hk (modelModifiedStretchMap hk ε r δ z)) :=
      (recombine_decompose hk (modelModifiedStretchMap hk ε r δ z)).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · rw [modelModifiedStretchMap_negPart, hzneg]
      · rw [modelModifiedStretchMap_posPart]
        rw [modelModifiedUnstretchMap_posPart]
        rw [hzneg]
        rw [modelModifiedDip_eq_fiber]
        rw [hzneg]
        rw [hsqz]
        rw [smul_smul]
        dsimp [modelModifiedUnstretchFactor]
        set D : ℝ := ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
            (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε with hD_def
        have hDpos' : 0 < D := by
          rw [hD_def]
          exact hDpos
        have hscalar2 : Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / D) *
            Real.sqrt (D / (‖negPart hk y‖ ^ 2 + r ^ 2)) = 1 :=
          sqrt_div_mul_sqrt_rev hsr hDpos'
        calc
          (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / D) *
            Real.sqrt (D / (‖negPart hk y‖ ^ 2 + r ^ 2))) • posPart hk y
              = (1 : ℝ) • posPart hk y := congrArg (fun t : ℝ => t • posPart hk y) hscalar2
          _ = posPart hk y := by simp
    _ = y := recombine_decompose hk y





theorem recombine_contDiff_generic {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2 i) = fun p => p.1 ⟨i.val, hi⟩ := by
      funext p
      dsimp [recombine]
      rw [dif_pos hi]
    rw [hcomp]
    fun_prop
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2 i) = fun p => p.2 ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩ := by
      funext p
      dsimp [recombine]
      rw [dif_neg hi]
    rw [hcomp]
    fun_prop

theorem contDiffAt_modelModifiedStretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) :
    ContDiffAt ℝ (⊤ : ℕ∞) (modelModifiedStretchMap hk ε r δ) y := by
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun z : MorseModel n => recombine hk (negPart hk z)
      ((Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) • posPart hk z)) y
  have hnum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 + r ^ 2) y := by
    have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
      ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
    exact (hns.contDiffAt.add (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => r ^ 2) y))
  have hdipG : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => modelModifiedDip hk ε δ z) := by
    have hmu : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : MorseModel n => modMu ε (‖negPart hk z‖ ^ 2)) := by
      have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
        ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
      simpa [Function.comp_def] using (ContDiff.comp (contDiff_modMu (ε := ε)) hns)
    have hga : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => modGamma δ ‖posPart hk z‖) :=
      contDiff_modGamma_norm hk δ hδ
    simpa [modelModifiedDip] using hmu.mul hga
  have hden : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε) y := by
    have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
      ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
    have hdenG : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε) := by
      exact (hns.add ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (2 : ℝ))).mul hdipG)).sub
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => 2 * ε))
    exact hdenG.contDiffAt
  have hden0 : (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) ≠ 0 := ne_of_gt hy
  have hratio : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε)) y :=
    ContDiffAt.div hnum hden hden0
  have hratio0 : 0 < (‖negPart hk y‖ ^ 2 + r ^ 2) /
      (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
    have hnum0 : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [sq_nonneg ‖negPart hk y‖, hr2]
    exact div_pos hnum0 hy
  have hsqrtAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t)
      ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε)) :=
    (Real.deriv_sqrt_aux (ne_of_gt hratio0)).2 (⊤ : ℕ∞)
  have hfactor : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) y :=
    ContDiffAt.comp y hsqrtAt hratio
  have hneg : ContDiffAt ℝ (⊤ : ℕ∞) (negPart hk) y :=
    (negPartCLM hk).contDiff.contDiffAt
  have hpos : ContDiffAt ℝ (⊤ : ℕ∞) (posPart hk) y :=
    (posPartCLM hk).contDiff.contDiffAt
  have hsmul : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) • posPart hk z) y :=
    ContDiffAt.smul hfactor hpos
  have hrec : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := recombine_contDiff_generic hk
  have hpair2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (negPart hk z, (Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) • posPart hk z)) y :=
    hneg.prodMk hsmul
  exact ContDiffAt.comp y (ContDiff.contDiffAt hrec) hpair2

theorem contDiffOn_modelModifiedStretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (hδ : 0 < δ) (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelModifiedStretchMap hk ε r δ)
      {y : MorseModel n | 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε} := by
  intro y hy
  exact (contDiffAt_modelModifiedStretchMap hk ε r δ hδ hr hy).contDiffWithinAt



theorem contMDiff_modelModifiedStretchMap_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₁.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε) =>
        (⟨modelModifiedStretchMap hk ε r δ y.1,
          modelModifiedStretchMap_mem_upper hk c ε r δ hε hδ y.2⟩ :
          SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2))) := by
  let denomFun : MorseModel (m + 1) → ℝ :=
    fun y => ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε
  let U : Set (MorseModel (m + 1)) := {y | 0 < denomFun y}
  have hUopen : IsOpen U := by
    have hden : ContDiff ℝ (⊤ : ℕ∞) denomFun := by
      have hns : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => ‖negPart hk y‖ ^ 2) :=
        ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
      have hdipG : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => modelModifiedDip hk ε δ y) := by
        have hmu : ContDiff ℝ (⊤ : ℕ∞)
            (fun y : MorseModel (m + 1) => modMu ε (‖negPart hk y‖ ^ 2)) := by
          have hns' : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => ‖negPart hk y‖ ^ 2) :=
            ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
          simpa [Function.comp_def] using (ContDiff.comp (contDiff_modMu (ε := ε)) hns')
        have hga : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => modGamma δ ‖posPart hk y‖) :=
          contDiff_modGamma_norm hk δ hδ
        simpa [modelModifiedDip] using hmu.mul hga
      exact (hns.add ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel (m + 1) => (2 : ℝ))).mul hdipG)).sub
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel (m + 1) => 2 * ε))
    change IsOpen {y : MorseModel (m + 1) | 0 < denomFun y}
    exact isOpen_lt continuous_const hden.continuous
  have hUsub : ∀ y : MorseModel (m + 1), modifiedNormalForm hk c ε δ y ≤ c - ε → y ∈ U := by
    intro y hy
    dsimp [U]
    exact modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (modelModifiedStretchMap hk ε r δ) U := by
    exact contDiffOn_modelModifiedStretchMap hk ε r δ hδ hr
  exact contMDiff_sublevelMap_on (m := m) (modifiedNormalForm hk c ε δ) (morseNormalForm hk c)
    (c - ε) (c + r ^ 2 / 2)
    (contDiff_modifiedNormalForm hk c ε δ hδ) (contDiff_morseNormalForm hk c)
    (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
      ⟨le_of_eq hy.symm, by linarith⟩)
    (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (modelModifiedStretchMap hk ε r δ) U hUopen hUsub hΦ
    (fun y hy => modelModifiedStretchMap_mem_upper hk c ε r δ hε hδ hy)
    (fun y hy => modelModifiedStretchMap_boundary hk c ε r δ hε hδ hy)
    (fun y hy => modelModifiedStretchMap_strict hk c ε r δ hε hδ (sq_pos_of_ne_zero hr) hy)
    (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)



theorem contDiff_modGammaSqrt {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ (⊤ : ℕ∞) (modGammaSqrt δ) := by
  let s : Set ℝ := {u | u < δ ^ 2 / 4}
  let t : Set ℝ := {u | 0 < u}
  have hconstOn : ContDiffOn ℝ (⊤ : ℕ∞) (modGammaSqrt δ) s := by
    rintro u hu
    have hconst : (fun z : ℝ => modGammaSqrt δ z) =ᶠ[nhds u] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_lt continuous_id (continuous_const : Continuous fun _ : ℝ => δ ^ 2 / 4) |>.mem_nhds hu] with z hz
      dsimp [modGammaSqrt]
      have hz' : Real.sqrt z ≤ δ / 2 := by
        have hsq : (Real.sqrt z) ^ 2 ≤ (δ / 2) ^ 2 := by
          have hz2 : z ≤ δ ^ 2 / 4 := le_of_lt hz
          by_cases hz3 : 0 ≤ z
          · rw [Real.sq_sqrt hz3]
            nlinarith
          · have hsqrt0 : Real.sqrt z = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hz3)
            rw [hsqrt0]
            simpa using (sq_nonneg (δ / 2))
        have hnn : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
        exact le_of_sq_le_sq hsq (le_of_lt (half_pos hδ))
      exact modGamma_one hδ hz'
    exact (ContDiffAt.contDiffWithinAt (n := (⊤ : ℕ∞)) (x := u)
      (contDiffAt_const.congr_of_eventuallyEq hconst))
  have hsmOn : ContDiffOn ℝ (⊤ : ℕ∞) (modGammaSqrt δ) t := by
    rintro u hu
    have hsq : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.sqrt x) u :=
      (Real.deriv_sqrt_aux (ne_of_gt hu)).2 (⊤ : ℕ∞)
    have hgamma : ContDiffAt ℝ (⊤ : ℕ∞) (modGamma δ) (Real.sqrt u) :=
      (contDiff_modGamma (δ := δ)).contDiffAt
    exact (ContDiffAt.comp u hgamma hsq).contDiffWithinAt
  have hs : IsOpen s := isOpen_lt continuous_id (continuous_const : Continuous fun _ : ℝ => δ ^ 2 / 4)
  have ht : IsOpen t := isOpen_lt (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)) continuous_id
  have hcov : s ∪ t = Set.univ := by
    ext x
    constructor <;> intro hx
    · trivial
    · by_cases hx' : 0 < x
      · exact Or.inr hx'
      · have hle : x ≤ 0 := le_of_not_gt hx'
        have hmain : x < δ ^ 2 / 4 := by
          have hδ2 : 0 < δ ^ 2 / 4 := div_pos (sq_pos_of_pos hδ) (by norm_num)
          linarith
        exact Or.inl hmain
  exact contDiff_of_contDiffOn_union_of_isOpen hconstOn hsmOn hcov hs ht

theorem contDiff_modelModifiedFiberDip {ε δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelModifiedFiberDip ε δ p.1 p.2) := by
  have hmu : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modMu ε p.1) :=
    (contDiff_modMu (ε := ε)).comp contDiff_fst
  have hga : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modGammaSqrt δ p.2) :=
    (contDiff_modGammaSqrt hδ).comp contDiff_snd
  simpa [modelModifiedFiberDip, Function.comp_def] using hmu.mul hga

noncomputable def modelModifiedFiberEquation (ε δ r : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  p.2 * (p.1.1 + r ^ 2) - p.1.2 * (p.1.1 + 2 * modelModifiedFiberDip ε δ p.1.1 p.2 - 2 * ε)

theorem contDiff_modelModifiedFiberEquation (ε δ r : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelModifiedFiberEquation ε δ r) := by
  have hdip : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => modelModifiedFiberDip ε δ p.1.1 p.2) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelModifiedFiberDip ε δ p.1 p.2) :=
      contDiff_modelModifiedFiberDip hδ
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2)) := by
      fun_prop
    simpa [Function.comp_def] using hd.comp hmap
  have hterm1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => p.2 * (p.1.1 + r ^ 2)) := by
    fun_prop
  have hterm2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => p.1.2 * (p.1.1 + 2 * modelModifiedFiberDip ε δ p.1.1 p.2 - 2 * ε)) := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × ℝ) × ℝ => p.1.1 + 2 * modelModifiedFiberDip ε δ p.1.1 p.2 - 2 * ε) := by
      fun_prop
    have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => p.1.2) := by
      fun_prop
    exact hproj.mul hinner
  simpa [modelModifiedFiberEquation] using hterm1.sub hterm2

theorem differentiableAt_modelModifiedFiberDip_fiber {ε δ : ℝ} (hδ : 0 < δ) (s u : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => modelModifiedFiberDip ε δ s t) u := by
  have hga : DifferentiableAt ℝ (modGammaSqrt δ) u :=
    ((contDiff_modGammaSqrt hδ).differentiable (by norm_num)).differentiableAt
  have hmuC : DifferentiableAt ℝ (fun t : ℝ => modMu ε s) u := by fun_prop
  have hmul := hmuC.mul hga
  dsimp [modelModifiedFiberDip]
  exact hmul

theorem deriv_modelModifiedFiberEquation_fiber {ε δ : ℝ} (hδ : 0 < δ) (s u : ℝ) :
    deriv (fun t : ℝ => modelModifiedFiberDip ε δ s t) u =
      modMu ε s * deriv (modGammaSqrt δ) u := by
  have hga : DifferentiableAt ℝ (modGammaSqrt δ) u :=
    ((contDiff_modGammaSqrt hδ).differentiable (by norm_num)).differentiableAt
  dsimp [modelModifiedFiberDip]
  exact deriv_const_mul (modMu ε s) hga

theorem deriv_modelModifiedFiberEquation {ε δ r : ℝ} (hδ : 0 < δ) (s w2 u : ℝ) :
    deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u =
      (s + r ^ 2) - 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u := by
  have hdipDeriv : deriv (fun t : ℝ => modelModifiedFiberDip ε δ s t) u =
      modMu ε s * deriv (modGammaSqrt δ) u := deriv_modelModifiedFiberEquation_fiber hδ s u
  have hDipDiff : DifferentiableAt ℝ (fun t : ℝ => modelModifiedFiberDip ε δ s t) u :=
    differentiableAt_modelModifiedFiberDip_fiber hδ s u
  have hF1 : deriv (fun t : ℝ => t * (s + r ^ 2)) u = s + r ^ 2 := by
    have hc : DifferentiableAt ℝ (fun t : ℝ => t) u := by fun_prop
    rw [deriv_mul_const hc]
    simp
  have htwo : deriv (fun t : ℝ => 2 * modelModifiedFiberDip ε δ s t) u =
      2 * (modMu ε s * deriv (modGammaSqrt δ) u) := by
    rw [deriv_const_mul (2 : ℝ) hDipDiff]
    rw [hdipDeriv]
  have hinner : deriv (fun t : ℝ => s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε) u =
      2 * (modMu ε s * deriv (modGammaSqrt δ) u) := by
    have h2 : deriv (fun t : ℝ => s + 2 * modelModifiedFiberDip ε δ s t) u =
        2 * (modMu ε s * deriv (modGammaSqrt δ) u) := by
      rw [deriv_const_add]
      rw [htwo]
    rw [deriv_sub_const]
    exact h2
  have hF2 : deriv (fun t : ℝ => w2 * (s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε)) u =
      w2 * (2 * (modMu ε s * deriv (modGammaSqrt δ) u)) := by
    have hinnerDiff : DifferentiableAt ℝ (fun t : ℝ =>
        s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε) u := by
      fun_prop
    rw [deriv_const_mul w2 hinnerDiff]
    rw [hinner]
  have hF : deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u =
      deriv (fun t : ℝ => t * (s + r ^ 2)) u -
        deriv (fun t : ℝ => w2 * (s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε)) u := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => t * (s + r ^ 2)) u := by fun_prop
    have h2 : DifferentiableAt ℝ (fun t : ℝ =>
        w2 * (s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε)) u := by
      fun_prop
    dsimp [modelModifiedFiberEquation]
    exact deriv_sub h1 h2
  rw [hF, hF1, hF2]
  ring

theorem modGammaSqrt_antitone_global {δ : ℝ} (hδ : 0 < δ) : Antitone (modGammaSqrt δ) := by
  intro a b hab
  dsimp [modGammaSqrt]
  exact modGamma_antitone_global hδ (Real.sqrt_monotone hab)

theorem deriv_modGammaSqrt_nonpos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    deriv (modGammaSqrt δ) u ≤ 0 :=
  Antitone.deriv_nonpos (modGammaSqrt_antitone_global hδ)

theorem fderiv_modelModifiedFiberEquation_inr (ε δ r : ℝ) (hδ : 0 < δ) (s w2 u : ℝ) :
    fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ) =
      (s + r ^ 2) - 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u := by
  have hdiff : DifferentiableAt ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) :=
    (contDiff_modelModifiedFiberEquation ε δ r hδ).differentiable (by norm_num) ((s, w2), u)
  have hFder : HasFDerivAt (modelModifiedFiberEquation ε δ r)
      (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u)) ((s, w2), u) :=
    hdiff.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((s, w2), t)) (((0, 0), 1) : (ℝ × ℝ) × ℝ) u := by
    have h1 : HasDerivAt (fun t : ℝ => t • (((0, 0), 1) : (ℝ × ℝ) × ℝ))
        (((0, 0), 1) : (ℝ × ℝ) × ℝ) u := by
      simpa using (hasDerivAt_id u).smul_const (((0, 0), 1) : (ℝ × ℝ) × ℝ)
    have h2 : HasDerivAt (fun t : ℝ => ((s, w2), 0) + t • (((0, 0), 1) : (ℝ × ℝ) × ℝ))
        (((0, 0), 1) : (ℝ × ℝ) × ℝ) u :=
      HasDerivAt.const_add (c := ((s, w2), 0)) h1
    simpa using h2
  have hcomp' : HasDerivAt (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t))
      (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ)) u :=
    HasFDerivAt.comp_hasDerivAt_of_eq (hl := hFder) (hf := hline) (hy := rfl)
  have hd1 : deriv (fun τ : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), τ)) u =
      fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
    simpa using hcomp'.deriv
  calc
    fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ)
        = deriv (fun τ : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), τ)) u := hd1.symm
    _ = (s + r ^ 2) - 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u :=
          deriv_modelModifiedFiberEquation hδ s w2 u

theorem modelModifiedFiberEquation_fiber_deriv_pos (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (s w2 u : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 < deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u := by
  rw [deriv_modelModifiedFiberEquation hδ]
  have hga : deriv (modGammaSqrt δ) u ≤ 0 := deriv_modGammaSqrt_nonpos hδ u
  have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
  have hterm : 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg (by positivity) hw) hmu) hga
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hs, hr2]
  nlinarith

theorem modelModifiedFiberEquation_strictMono (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (s w2 : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    StrictMono (fun u : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), u)) :=
  strictMono_of_deriv_pos (fun u =>
    modelModifiedFiberEquation_fiber_deriv_pos ε δ r hε hδ hr s w2 u hs hw)

theorem modelModifiedFiberRoot_eq_of_modelModifiedFiberEquation {ε δ r : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hr : r ≠ 0) (s w2 u : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w2)
    (hu : modelModifiedFiberEquation ε δ r ((s, w2), u) = 0) :
    u = modelModifiedFiberRoot ε δ r hε hδ hr s w2 := by
  have hroot' : modelModifiedFiberEquation ε δ r
      ((s, w2), modelModifiedFiberRoot ε δ r hε hδ hr s w2) = 0 := by
    dsimp [modelModifiedFiberEquation]
    rw [modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw]
    ring
  exact (modelModifiedFiberEquation_strictMono ε δ r hε hδ hr s w2 hs hw).injective
    (by rw [hu, hroot'])

theorem contDiffWithinAt_modelModifiedFiberRoot (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) {s w2 : ℝ} (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} (s, w2) := by
  let Q : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  let u₀ : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2
  have hFdiff : ContDiffAt ℝ (⊤ : ℕ∞) (modelModifiedFiberEquation ε δ r) ((s, w2), u₀) :=
    (contDiff_modelModifiedFiberEquation ε δ r hδ).contDiffAt
  have hroot : modelModifiedFiberEquation ε δ r ((s, w2), u₀) = 0 := by
    dsimp [u₀, modelModifiedFiberEquation]
    rw [modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw]
    ring
  have hpos : 0 < fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀)
      (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
    rw [fderiv_modelModifiedFiberEquation_inr ε δ r hδ s w2 u₀]
    have hd : 0 < deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u₀ :=
      modelModifiedFiberEquation_fiber_deriv_pos ε δ r hε hδ hr s w2 u₀ hs hw
    rw [deriv_modelModifiedFiberEquation hδ s w2 u₀] at hd
    exact hd
  have hinv : (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    let c : ℝ := fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀)
      (((0, 0), 1) : (ℝ × ℝ) × ℝ)
    have hc : c ≠ 0 := ne_of_gt hpos
    let e : ℝ ≃L[ℝ] ℝ :=
      { toFun := fun y => c * y
        invFun := fun y => c⁻¹ * y
        left_inv := fun y => by field_simp [hc]
        right_inv := fun y => by field_simp [hc]
        map_add' := by intro x y; ring
        map_smul' := by
          intro a y
          simp only [smul_eq_mul, RingHom.id_apply]
          ring }
    refine ⟨e, ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    change c * y = (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) y
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
    have harg : ((0, y) : (ℝ × ℝ) × ℝ) = y • (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
      rw [Prod.smul_mk]
      rw [Prod.smul_mk]
      congr 1
      · rw [smul_eq_mul]
        rw [mul_zero]
        rfl
      · rw [smul_eq_mul]
        rw [mul_one]
    have hlin : (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀))
        (y • (((0, 0), 1) : (ℝ × ℝ) × ℝ)) = y * c := by
      rw [map_smul]
      simp only [smul_eq_mul, c]
    rw [harg, hlin]
    rw [mul_comm]
  let ψ : (ℝ × ℝ) → ℝ :=
    hFdiff.implicitFunction (n := (⊤ : ℕ∞)) (by norm_num) hinv
  have hψdiff : ContDiffAt ℝ (⊤ : ℕ∞) ψ (s, w2) := by
    simpa [ψ] using hFdiff.contDiffAt_implicitFunction (n := (⊤ : ℕ∞)) (by norm_num) hinv
  have hψeq : ψ (s, w2) = u₀ := by
    simpa [ψ] using (hFdiff.implicitFunction_apply_self (n := (⊤ : ℕ∞)) (by norm_num) hinv)
  have heq : ∀ᶠ p in nhdsWithin (s, w2) Q,
      modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2 = ψ p := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hFdiff.eventually_apply_implicitFunction (n := (⊤ : ℕ∞)) (by norm_num) hinv]
      with p hp
    intro hpq
    have hp' : modelModifiedFiberEquation ε δ r (p, ψ p) = 0 := by
      simpa [hroot] using hp
    exact (modelModifiedFiberRoot_eq_of_modelModifiedFiberEquation hε hδ hr p.1 p.2 (ψ p)
      hpq.1 hpq.2 hp').symm
  exact hψdiff.contDiffWithinAt.congr_of_eventuallyEq heq (by
    rw [hψeq])

theorem contDiffOn_modelModifiedFiberRoot (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
  intro p hp
  exact contDiffWithinAt_modelModifiedFiberRoot ε δ r hε hδ hr hp.1 hp.2

theorem contDiffOn_modelModifiedUnstretchFactor (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelModifiedUnstretchFactor ε δ r hε hδ hr p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
  intro p hp
  let Q : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun q : ℝ × ℝ => Real.sqrt
      ((q.1 + 2 * modelModifiedFiberDip ε δ q.1
          (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) / (q.1 + r ^ 2))) Q p
  have hrootW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) Q p :=
    contDiffWithinAt_modelModifiedFiberRoot ε δ r hε hδ hr hp.1 hp.2
  have hfstW : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1) Q p :=
    (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1)).contDiffAt.contDiffWithinAt
  have hpairW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (q.1, modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2)) Q p :=
    hfstW.prodMk hrootW
  have hdipC : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2)) Q p := by
    have hdipW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (fun z : ℝ × ℝ => modelModifiedFiberDip ε δ z.1 z.2) Set.univ
        (p.1, modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) :=
      (contDiff_modelModifiedFiberDip hδ).contDiffAt.contDiffWithinAt
    exact ContDiffWithinAt.comp p hdipW hpairW (by intro q hq; trivial)
  have hnumW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => q.1 + 2 * modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) Q p := by
    have hc2 : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => (2 : ℝ)) Q p :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => (2 : ℝ))).contDiffAt.contDiffWithinAt
    have hcε : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => 2 * ε) Q p :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => 2 * ε)).contDiffAt.contDiffWithinAt
    exact (hfstW.add (hc2.mul hdipC)).sub hcε
  have hdenW : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1 + r ^ 2) Q p := by
    have hc : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => r ^ 2) Q p :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => r ^ 2)).contDiffAt.contDiffWithinAt
    exact hfstW.add hc
  have hden0 : p.1 + r ^ 2 ≠ 0 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have hpos : 0 < p.1 + r ^ 2 := by nlinarith [hp.1, hr2]
    exact ne_of_gt hpos
  have hratioW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (q.1 + 2 * modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) / (q.1 + r ^ 2)) Q p :=
    ContDiffWithinAt.div hnumW hdenW hden0
  have hratio0 : 0 < (p.1 + 2 * modelModifiedFiberDip ε δ p.1
      (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε) / (p.1 + r ^ 2) := by
    have hnum0 : 0 < p.1 + 2 * modelModifiedFiberDip ε δ p.1
        (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε :=
      modelModifiedFiberDenom_root_pos hε hδ hr hp.1 hp.2
    have hdenpos : 0 < p.1 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [hp.1, hr2]
    exact div_pos hnum0 hdenpos
  have hsqrtAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t)
      ((p.1 + 2 * modelModifiedFiberDip ε δ p.1
        (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε) / (p.1 + r ^ 2)) :=
    (Real.deriv_sqrt_aux (ne_of_gt hratio0)).2 (⊤ : ℕ∞)
  have hfactorW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => Real.sqrt ((q.1 + 2 * modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) / (q.1 + r ^ 2))) Q p := by
    have hsqrtW : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t) Set.univ
        ((p.1 + 2 * modelModifiedFiberDip ε δ p.1
          (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε) / (p.1 + r ^ 2)) :=
      hsqrtAt.contDiffWithinAt
    exact ContDiffWithinAt.comp p hsqrtW hratioW (by intro q hq; trivial)
  exact hfactorW

theorem contDiffAt_modelModifiedUnstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (modelModifiedUnstretchMap hk ε r δ hε hδ hr) y := by
  let Q : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun z : MorseModel n => recombine hk (negPart hk z)
      ((modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) •
        posPart hk z)) y
  have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
    ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
  have hps : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) :=
    ContDiff.norm_sq ℝ (posPartCLM hk).contDiff
  have hfacOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => modelModifiedUnstretchFactor ε δ r hε hδ hr
        (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) Set.univ := by
    refine ContDiffOn.comp
      (g := fun p : ℝ × ℝ => modelModifiedUnstretchFactor ε δ r hε hδ hr p.1 p.2)
      (f := fun z : MorseModel n => (‖negPart hk z‖ ^ 2, ‖posPart hk z‖ ^ 2))
      (s := Set.univ) (t := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) ?hg ?hf ?st
    · exact contDiffOn_modelModifiedUnstretchFactor ε δ r hε hδ hr
    · exact (hns.prodMk hps).contDiffOn
    · intro z hz
      exact ⟨sq_nonneg _, sq_nonneg _⟩
  have hfacAt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => modelModifiedUnstretchFactor ε δ r hε hδ hr
        (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) y :=
    contDiffWithinAt_univ.mp (hfacOn y trivial)
  have hneg : ContDiffAt ℝ (⊤ : ℕ∞) (negPart hk) y :=
    (negPartCLM hk).contDiff.contDiffAt
  have hpos : ContDiffAt ℝ (⊤ : ℕ∞) (posPart hk) y :=
    (posPartCLM hk).contDiff.contDiffAt
  have hsmul : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n =>
        (modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) •
          posPart hk z) y :=
    ContDiffAt.smul hfacAt hpos
  have hrec : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := recombine_contDiff_generic hk
  have hpair2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (negPart hk z,
        (modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) •
          posPart hk z)) y :=
    hneg.prodMk hsmul
  exact ContDiffAt.comp y (ContDiff.contDiffAt hrec) hpair2

theorem contDiffOn_modelModifiedUnstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelModifiedUnstretchMap hk ε r δ hε hδ hr) Set.univ := by
  intro y hy
  exact (contDiffAt_modelModifiedUnstretchMap hk ε r δ hε hδ hr y).contDiffWithinAt

theorem contMDiff_modelModifiedUnstretchMap_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hchart₁ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₁.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₂.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2) =>
        (⟨modelModifiedUnstretchMap hk ε r δ hε hδ hr y.1,
          modelModifiedUnstretchMap_mem_modified hk c ε r δ hε hδ hr y.2⟩ :
          SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε))) := by
  exact contMDiff_sublevelMap_on (m := m) (morseNormalForm hk c) (modifiedNormalForm hk c ε δ)
    (c + r ^ 2 / 2) (c - ε)
    (contDiff_morseNormalForm hk c) (contDiff_modifiedNormalForm hk c ε δ hδ)
    (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
      ⟨le_of_eq hy.symm, by linarith⟩)
    (modelModifiedUnstretchMap hk ε r δ hε hδ hr) Set.univ isOpen_univ (by intro y hy; trivial)
    (contDiffOn_modelModifiedUnstretchMap hk ε r δ hε hδ hr)
    (fun y hy => modelModifiedUnstretchMap_mem_modified hk c ε r δ hε hδ hr hy)
    (fun y hy => modelModifiedUnstretchMap_boundary hk c ε r δ hε hδ hr hy)
    (fun y hy => modelModifiedUnstretchMap_strict hk c ε r δ hε hδ hr hy)
    (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

noncomputable def modelModifiedSublevelDiffeomorph {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₁.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) _ hcs₁
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) _ hcs₂
      (⊤ : ℕ∞) where
  toEquiv :=
    { toFun := fun y => (⟨modelModifiedStretchMap hk ε r δ y.1,
        modelModifiedStretchMap_mem_upper hk c ε r δ hε hδ y.2⟩ :
        SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2))
      invFun := fun y => (⟨modelModifiedUnstretchMap hk ε r δ hε hδ hr y.1,
        modelModifiedUnstretchMap_mem_modified hk c ε r δ hε hδ hr y.2⟩ :
        SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε))
      left_inv := by
        intro y
        apply Subtype.ext
        exact modelModifiedUnstretchMap_stretchMap hk c ε r δ hε hδ hr y.2
      right_inv := by
        intro y
        apply Subtype.ext
        exact modelModifiedStretchMap_unstretchMap hk ε r δ hε hδ hr y.1 }
  contMDiff_toFun := by
    simpa using (contMDiff_modelModifiedStretchMap_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (hε := hε) (hδ := hδ) (hr := hr) (hcs₁ := hcs₁) (hcs₂ := hcs₂)
      (hchart₁ := hchart₁) (hchart₂ := hchart₂))
  contMDiff_invFun := by
    simpa using (contMDiff_modelModifiedUnstretchMap_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (hε := hε) (hδ := hδ) (hr := hr) (hcs₁ := hcs₂) (hcs₂ := hcs₁)
      (hchart₁ := hchart₂) (hchart₂ := hchart₁))

noncomputable def modelAttachedRegionEquivModified {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    {y : MorseModel (m + 1) // y ∈ modelAttachedRegion hk ε r δ} ≃ₜ
      {y : MorseModel (m + 1) // modifiedNormalForm hk c ε δ y ≤ c - ε} := by
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
    sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
      (contDiff_modifiedNormalForm hk c ε δ hδ)
      (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
        ⟨le_of_eq hy.symm, by linarith⟩)
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
    sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
      (contDiff_morseNormalForm hk c)
      (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
  exact (modelAttachedRegionEquivUpper hk c ε r δ hδ hδr hr).trans
    (modelModifiedSublevelDiffeomorph hk c ε r δ hε hδ hr).toHomeomorph.symm

noncomputable def modelSharpUnionEquivModifiedHomeo {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    {y : MorseModel (m + 1) // y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪
      modelHandle hk ε r} ≃ₜ
      {y : MorseModel (m + 1) // modifiedNormalForm hk c ε δ y ≤ c - ε} := by
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
    sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
      (contDiff_modifiedNormalForm hk c ε δ hδ)
      (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
        ⟨le_of_eq hy.symm, by linarith⟩)
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
    sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
      (contDiff_morseNormalForm hk c)
      (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
  exact (modelSharpUnionToUpperHomeo hk c ε r δ hδ hδr).trans
    (modelModifiedSublevelDiffeomorph hk c ε r δ hε hδ hr).toHomeomorph.symm

noncomputable def modelRoundedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (y : MorseModel n) : ℝ :=
  modelAttachedFunction hk c ε r δ y +
    (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) *
      Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))

theorem modelRoundedFunction_eq_attached_of_norm_le {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : morseNorm n y ≤ R₀) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = modelAttachedFunction hk c ε r δ y := by
  dsimp [modelRoundedFunction]
  have harg : (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) ≤ 0 := by
    have hsq : morseNorm n y ^ 2 ≤ R₀ ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hnon, hR0]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) (le_of_lt hden)
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem modelRoundedFunction_eq_morse_add_eps_of_norm_ge {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n}
    (hy : R₁ ≤ morseNorm n y) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = morseNormalForm hk c y + ε := by
  dsimp [modelRoundedFunction]
  have harg : 1 ≤ (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hR0, hR]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (one_le_div hden).mpr (by nlinarith [hsq])
  rw [Real.smoothTransition.one_of_one_le harg]
  ring

theorem contDiff_modelRoundedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundedFunction hk c ε r δ R₀ R₁) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
    modelAttachedFunction hk c ε r δ y +
      (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) *
        Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hnormSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
    dsimp [morseNorm]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) := by
      simpa using ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff)
    exact hlin.norm_sq ℝ
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
    exact ((hnormSq.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => R₀ ^ 2))).div_const (R₁ ^ 2 - R₀ ^ 2))
  have htrans : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp harg
  have hF₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y) :=
    contDiff_modelAttachedFunction hk c ε r δ
  have hF₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y + ε) :=
    (contDiff_morseNormalForm hk c).add contDiff_const
  exact (hF₁.add ((hF₂.sub hF₁).mul htrans))

noncomputable def modelCapRoundedLowerFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ θ R₀ R₁ : ℝ)
    (y : MorseModel n) : ℝ :=
  modelCapRoundedLowerFunctionInner hk c ε r δ θ y +
    (morseNormalForm hk c y + ε - modelCapRoundedLowerFunctionInner hk c ε r δ θ y) *
      Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))

theorem modelCapRoundedLowerFunction_eq_inner_of_norm_le {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n}
    (hy : morseNorm n y ≤ R₀) :
    modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y =
      modelCapRoundedLowerFunctionInner hk c ε r δ θ y := by
  dsimp [modelCapRoundedLowerFunction]
  have harg : (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) ≤ 0 := by
    have hsq : morseNorm n y ^ 2 ≤ R₀ ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hnon, hR0]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) (le_of_lt hden)
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem modelCapRoundedLowerFunction_eq_morse_add_eps_of_norm_ge {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n}
    (hy : R₁ ≤ morseNorm n y) :
    modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y = morseNormalForm hk c y + ε := by
  dsimp [modelCapRoundedLowerFunction]
  have harg : 1 ≤ (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hR0, hR]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (one_le_div hden).mpr (by nlinarith [hsq])
  rw [Real.smoothTransition.one_of_one_le harg]
  ring

theorem contDiff_modelCapRoundedLowerFunction {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
    modelCapRoundedLowerFunctionInner hk c ε r δ θ y +
      (morseNormalForm hk c y + ε - modelCapRoundedLowerFunctionInner hk c ε r δ θ y) *
        Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hnormSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
    dsimp [morseNorm]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) := by
      simpa using ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff)
    exact hlin.norm_sq ℝ
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
    exact ((hnormSq.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => R₀ ^ 2))).div_const (R₁ ^ 2 - R₀ ^ 2))
  have htrans : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp harg
  have hF₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      modelCapRoundedLowerFunctionInner hk c ε r δ θ y) :=
    contDiff_modelCapRoundedLowerFunctionInner hk c ε r δ θ hθ hδ hδr hθr
  have hF₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y + ε) :=
    (contDiff_morseNormalForm hk c).add contDiff_const
  exact (hF₁.add ((hF₂.sub hF₁).mul htrans))

theorem modelCapRoundedLowerFunction_eq_morse_add_eps_of_negPart_large {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) {y : MorseModel n}
    (hy : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y = morseNormalForm hk c y + ε := by
  have hinner : modelCapRoundedLowerFunctionInner hk c ε r δ θ y = morseNormalForm hk c y + ε := by
    have hsc : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) = 1 :=
      modelRoundScale_eq_one_of_ge hθ hδ hy
    dsimp [modelCapRoundedLowerFunctionInner]
    rw [morseNormalForm_split]
    have hL : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
      dsimp [modelLowerRoundBound]
      rw [hsc]
      ring
    rw [hL]
    ring
  dsimp [modelCapRoundedLowerFunction]
  rw [hinner]
  ring

theorem modelCapRoundedLowerFunctionInner_eq_morse_add_eps_of_negPart_large {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) {y : MorseModel n}
    (hy : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelCapRoundedLowerFunctionInner hk c ε r δ θ y = morseNormalForm hk c y + ε := by
  have hsc : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) = 1 :=
    modelRoundScale_eq_one_of_ge hθ hδ hy
  dsimp [modelCapRoundedLowerFunctionInner]
  rw [morseNormalForm_split]
  have hL : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [modelLowerRoundBound]
    rw [hsc]
    ring
  rw [hL]
  ring

theorem modelCapRoundedLowerFunction_le_c_iff_of_norm_le {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : morseNorm n y ≤ R₀) :
    modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y ≤ c ↔
      y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)) := by
  rw [modelCapRoundedLowerFunction_eq_inner_of_norm_le hk c ε r δ θ R₀ R₁ hR hR0 hy]
  exact modelCapRoundedLowerFunctionInner_le_c_iff hk c ε r δ θ hθ hδ hδr hθr y

theorem modelRoundedFunction_eq_morse_add_eps_of_negPart_large {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hδ : 0 < δ) {y : MorseModel n}
    (hy : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = morseNormalForm hk c y + ε := by
  dsimp [modelRoundedFunction]
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
    smoothCap_upper hδ hy
  have hf : modelAttachedFunction hk c ε r δ y = morseNormalForm hk c y + ε := by
    dsimp [modelAttachedFunction]
    rw [morseNormalForm_split]
    rw [hcap]
    ring
  rw [hf]
  ring

theorem modelLowerSublevel_norm_sq_lt_of_negPart_lt {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    {y : MorseModel n} (hy : morseNormalForm hk c y ≤ c - ε)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    morseNorm n y ^ 2 < 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε := by
  have hpos : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    rw [morseNormalForm_split] at hy
    nlinarith
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
    calc
      morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
        rw [recombine_decompose hk y]
      _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
        morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
  nlinarith [hneg, hpos, hnorm]

theorem modelAttached_norm_sq_lt_of_negPart_lt {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    morseNorm n y ^ 2 < 2 * (r ^ 2 + 2 * ε + δ) := by
  have hpos : ‖posPart hk y‖ ^ 2 ≤ max (r ^ 2) (‖negPart hk y‖ ^ 2) := by
    dsimp [modelAttachedRegion] at hy
    exact le_trans hy (smoothCap_le_max (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hε hδ)
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
    calc
      morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
        rw [recombine_decompose hk y]
      _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
        morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
  have hle : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2) < 2 * (r ^ 2 + 2 * ε + δ) := by
    by_cases hle' : ‖negPart hk y‖ ^ 2 ≤ r ^ 2
    · have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2) = r ^ 2 := max_eq_left hle'
      nlinarith [hneg, hle', hmax]
    · have hgt : r ^ 2 < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hle'
      have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 := max_eq_right (le_of_lt hgt)
      nlinarith [hneg, hgt, hmax]
  nlinarith [hpos, hnorm, hle]

theorem smoothCap_le_max_sub {ε r δ t : ℝ} :
    smoothCap ε r δ t ≤ max (r ^ 2) (t - 2 * ε) := by
  dsimp [smoothCap]
  let σ : ℝ := Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))
  have hσ : 0 ≤ σ := by dsimp [σ]; exact Real.smoothTransition.nonneg _
  have hσ₁ : σ ≤ 1 := by dsimp [σ]; exact Real.smoothTransition.le_one _
  by_cases hle : t - 2 * ε - r ^ 2 ≤ 0
  · have hmain : r ^ 2 + (t - 2 * ε - r ^ 2) * σ ≤ r ^ 2 := by nlinarith [hσ, hle]
    have hmax : r ^ 2 ≤ max (r ^ 2) (t - 2 * ε) := le_max_left _ _
    nlinarith
  · have hpos : 0 < t - 2 * ε - r ^ 2 := lt_of_not_ge hle
    have hmain : r ^ 2 + (t - 2 * ε - r ^ 2) * σ ≤ t - 2 * ε := by nlinarith [hσ₁, hpos]
    have hmax : t - 2 * ε ≤ max (r ^ 2) (t - 2 * ε) := le_max_right _ _
    nlinarith

theorem modelLowerRoundBound_le_max_sub {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) :
    modelLowerRoundBound ε r δ θ t ≤ max (r ^ 2) (t - 2 * ε) := by
  by_cases ht : 2 * ε < t
  · have hsc := modelRoundScale_sq_le_ratio hδ hθ hδr ht
    have hden : 0 < t - 2 * ε := by linarith [ht]
    have hratio : modelRoundRatio ε r δ t * (t - 2 * ε) = smoothCap ε r δ t := by
      dsimp [modelRoundRatio]
      rw [div_mul_cancel₀ _ (ne_of_gt hden)]
    have hle : modelLowerRoundBound ε r δ θ t ≤ smoothCap ε r δ t := by
      dsimp [modelLowerRoundBound]
      nlinarith [hsc, hratio]
    exact le_trans hle (smoothCap_le_max_sub (ε := ε) (r := r) (δ := δ) (t := t))
  · have htle : t ≤ 2 * ε := le_of_not_gt ht
    have hL : modelLowerRoundBound ε r δ θ t ≤ 0 := by
      dsimp [modelLowerRoundBound]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith [htle])
    have hmax : 0 ≤ max (r ^ 2) (t - 2 * ε) := le_trans (sq_nonneg r) (le_max_left _ _)
    nlinarith

theorem modelCapRoundedLowerFunction_gt_c_of_norm_gt_negPart_lt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ < morseNorm n y)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    c < modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y := by
  by_cases hy₁ : R₁ ≤ morseNorm n y
  · rw [modelCapRoundedLowerFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ θ R₀ R₁ hR hR0 hy₁]
    rw [morseNormalForm_split]
    have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      calc
        morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
          rw [recombine_decompose hk y]
        _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
          morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      exact sq_le_sq' (by nlinarith [hR0, hR]) hy₁
    have hbig' : r ^ 2 + 2 * ε + δ < R₁ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      have hb' : 2 * (r ^ 2 + 2 * ε + δ) < R₁ ^ 2 := by nlinarith [hbig, h01]
      nlinarith
    have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by
      nlinarith [hnorm, hsq, hbig', hneg]
    nlinarith
  · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
    let σ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
    have hσ : 0 ≤ σ := by dsimp [σ]; exact Real.smoothTransition.nonneg _
    have hσ₁ : σ ≤ 1 := by dsimp [σ]; exact Real.smoothTransition.le_one _
    have hpos : R₀ ^ 2 < morseNorm n y ^ 2 := by
      exact sq_lt_sq' (by nlinarith [hR0, norm_nonneg (morseNorm n y)]) hy₀
    have hpos2 : ‖posPart hk y‖ ^ 2 > max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) := by
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) < R₀ ^ 2 := by
        have h1 : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ r ^ 2 + 2 * ε + δ := by
          exact max_le (by nlinarith) (by nlinarith [hneg])
        nlinarith [hbig, h1, hneg]
      nlinarith [hnorm, hpos, hb]
    have hF₁ : c < modelCapRoundedLowerFunctionInner hk c ε r δ θ y := by
      dsimp [modelCapRoundedLowerFunctionInner]
      have hL : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) ≤
          max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) :=
        modelLowerRoundBound_le_max_sub hδ hθ hδr
      nlinarith [hpos2, hL]
    have hF₂ : c < morseNormalForm hk c y + ε := by
      rw [morseNormalForm_split]
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by nlinarith [hpos2, hnorm]
      nlinarith
    dsimp [modelCapRoundedLowerFunction]
    have hmain : c < modelCapRoundedLowerFunctionInner hk c ε r δ θ y +
        (morseNormalForm hk c y + ε - modelCapRoundedLowerFunctionInner hk c ε r δ θ y) * σ := by
      have hσlt : σ < 1 := by
        dsimp [σ]
        exact Real.smoothTransition.lt_one_of_lt_one (by
          have hsq : morseNorm n y ^ 2 < R₁ ^ 2 := by
            have hnon : 0 ≤ morseNorm n y := by
              dsimp [morseNorm]
              exact norm_nonneg _
            exact sq_lt_sq' (by nlinarith [hR0, hR, hnon]) hy₁'
          have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by nlinarith [hR, hR0]
          exact (div_lt_one hden).mpr (by nlinarith [hsq]))
      have hpos1 : 0 < modelCapRoundedLowerFunctionInner hk c ε r δ θ y - c := by linarith [hF₁]
      have hpos2' : 0 < morseNormalForm hk c y + ε - c := by linarith [hF₂]
      have hmain' : 0 < (1 - σ) * (modelCapRoundedLowerFunctionInner hk c ε r δ θ y - c) +
          σ * (morseNormalForm hk c y + ε - c) := by
        have h₁ : 0 < (1 - σ) * (modelCapRoundedLowerFunctionInner hk c ε r δ θ y - c) :=
          mul_pos (by linarith [hσlt]) hpos1
        have h₂ : 0 ≤ σ * (morseNormalForm hk c y + ε - c) :=
          mul_nonneg hσ (le_of_lt hpos2')
        nlinarith
      have hrew : modelCapRoundedLowerFunctionInner hk c ε r δ θ y +
          (morseNormalForm hk c y + ε - modelCapRoundedLowerFunctionInner hk c ε r δ θ y) * σ - c =
          (1 - σ) * (modelCapRoundedLowerFunctionInner hk c ε r δ θ y - c) +
            σ * (morseNormalForm hk c y + ε - c) := by
        ring
      rw [← hrew] at hmain'
      linarith
    exact hmain

theorem modelRoundedFunction_gt_c_of_norm_gt_negPart_lt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ < morseNorm n y)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    c < modelRoundedFunction hk c ε r δ R₀ R₁ y := by
  by_cases hy₁ : R₁ ≤ morseNorm n y
  · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁]
    rw [morseNormalForm_split]
    have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      calc
        morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
          rw [recombine_decompose hk y]
        _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
          morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      exact sq_le_sq' (by nlinarith [hR0, hR]) hy₁
    have hbig' : r ^ 2 + 2 * ε + δ < R₁ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      have hb' : 2 * (r ^ 2 + 2 * ε + δ) < R₁ ^ 2 := by nlinarith [hbig, h01]
      nlinarith
    have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by
      nlinarith [hnorm, hsq, hbig', hneg]
    nlinarith
  · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
    let σ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
    have hσ : 0 ≤ σ := by dsimp [σ]; exact Real.smoothTransition.nonneg _
    have hσ₁ : σ ≤ 1 := by dsimp [σ]; exact Real.smoothTransition.le_one _
    have hpos : R₀ ^ 2 < morseNorm n y ^ 2 := by
      exact sq_lt_sq' (by nlinarith [hR0, norm_nonneg (morseNorm n y)]) hy₀
    have hpos2 : ‖posPart hk y‖ ^ 2 > max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) := by
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) < R₀ ^ 2 := by
        have h1 : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ r ^ 2 + 2 * ε + δ := by
          exact max_le (by nlinarith) (by nlinarith [hneg])
        nlinarith [hbig, h1, hneg]
      nlinarith [hnorm, hpos, hb]
    have hF₁ : c < modelAttachedFunction hk c ε r δ y := by
      dsimp [modelAttachedFunction]
      have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) :=
        smoothCap_le_max_sub (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2)
      nlinarith [hpos2, hcap]
    have hF₂ : c < morseNormalForm hk c y + ε := by
      rw [morseNormalForm_split]
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by nlinarith [hpos2, hnorm]
      nlinarith
    dsimp [modelRoundedFunction]
    have hmain : c < modelAttachedFunction hk c ε r δ y +
        (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) * σ := by
      have hσlt : σ < 1 := by
        dsimp [σ]
        exact Real.smoothTransition.lt_one_of_lt_one (by
          have hsq : morseNorm n y ^ 2 < R₁ ^ 2 := by
            have hnon : 0 ≤ morseNorm n y := by
              dsimp [morseNorm]
              exact norm_nonneg _
            exact sq_lt_sq' (by nlinarith [hR0, hR, hnon]) hy₁'
          have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by nlinarith [hR, hR0]
          exact (div_lt_one hden).mpr (by nlinarith [hsq]))
      have hpos1 : 0 < modelAttachedFunction hk c ε r δ y - c := by linarith [hF₁]
      have hpos2 : 0 < morseNormalForm hk c y + ε - c := by linarith [hF₂]
      have hmain' : 0 < (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) +
          σ * (morseNormalForm hk c y + ε - c) := by
        have h₁ : 0 < (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) :=
          mul_pos (by linarith [hσlt]) hpos1
        have h₂ : 0 ≤ σ * (morseNormalForm hk c y + ε - c) :=
          mul_nonneg hσ (le_of_lt hpos2)
        nlinarith
      have hrew : modelAttachedFunction hk c ε r δ y +
          (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) * σ - c =
          (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) +
            σ * (morseNormalForm hk c y + ε - c) := by
        ring
      rw [← hrew] at hmain'
      linarith
    exact hmain

theorem modelRoundedFunction_le_c_iff_of_norm_gt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ < morseNorm n y) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c ↔ morseNormalForm hk c y ≤ c - ε := by
  constructor
  · intro hy
    by_cases hy₁ : R₁ ≤ morseNorm n y
    · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁] at hy
      nlinarith
    · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hgt : c < modelRoundedFunction hk c ε r δ R₀ R₁ y :=
          modelRoundedFunction_gt_c_of_norm_gt_negPart_lt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hy₀ hlt
        exact (not_lt_of_ge hy) hgt
      rw [modelRoundedFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ R₀ R₁ hδ hnegl] at hy
      nlinarith
  · intro hy
    by_cases hy₁ : R₁ ≤ morseNorm n y
    · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁]
      nlinarith
    · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have h1 := modelLowerSublevel_norm_sq_lt_of_negPart_lt hk c ε r δ hy hlt
          have h2 : 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε < R₀ ^ 2 := by nlinarith [hbig]
          nlinarith [h1, h2]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
          have h2 : |R₀| = R₀ := abs_of_nonneg hR0
          rw [h1, h2] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hy₀
      rw [modelRoundedFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ R₀ R₁ hδ hnegl]
      nlinarith

theorem modelCapRoundedLowerFunction_le_c_iff_of_norm_gt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ < morseNorm n y) :
    modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y ≤ c ↔ morseNormalForm hk c y ≤ c - ε := by
  constructor
  · intro hy
    by_cases hy₁ : R₁ ≤ morseNorm n y
    · rw [modelCapRoundedLowerFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ θ R₀ R₁ hR hR0 hy₁] at hy
      nlinarith
    · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hgt : c < modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y :=
          modelCapRoundedLowerFunction_gt_c_of_norm_gt_negPart_lt hk c ε r δ θ R₀ R₁ hε hδ hθ hδr hR hR0 hbig hy₀ hlt
        exact (not_lt_of_ge hy) hgt
      rw [modelCapRoundedLowerFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ θ R₀ R₁ hθ hδ hnegl] at hy
      nlinarith
  · intro hy
    by_cases hy₁ : R₁ ≤ morseNorm n y
    · rw [modelCapRoundedLowerFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ θ R₀ R₁ hR hR0 hy₁]
      nlinarith
    · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have h1 := modelLowerSublevel_norm_sq_lt_of_negPart_lt hk c ε r δ hy hlt
          have h2 : 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε < R₀ ^ 2 := by nlinarith [hbig]
          nlinarith [h1, h2]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
          have h2 : |R₀| = R₀ := abs_of_nonneg hR0
          rw [h1, h2] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hy₀
      rw [modelCapRoundedLowerFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ θ R₀ R₁ hθ hδ hnegl]
      nlinarith

theorem modelCapRoundedLowerFunction_le_c_iff_inner_le_c {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n} :
    modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y ≤ c ↔
      modelCapRoundedLowerFunctionInner hk c ε r δ θ y ≤ c := by
  constructor
  · intro hg
    by_cases hnorm : morseNorm n y ≤ R₀
    · have hfun : modelCapRoundedLowerFunction hk c ε r δ θ R₀ R₁ y =
          modelCapRoundedLowerFunctionInner hk c ε r δ θ y :=
        modelCapRoundedLowerFunction_eq_inner_of_norm_le hk c ε r δ θ R₀ R₁ hR hR0 hnorm
      rwa [hfun] at hg
    · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
      have hlow : morseNormalForm hk c y ≤ c - ε :=
        (modelCapRoundedLowerFunction_le_c_iff_of_norm_gt hk c ε r δ θ R₀ R₁ hε hδ hθ hδr hR hR0 hbig hnorm').mp hg
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have h1 := modelLowerSublevel_norm_sq_lt_of_negPart_lt hk c ε r δ hlow hlt
          have h2 : 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε < R₀ ^ 2 := by nlinarith [hbig]
          nlinarith [h1, h2]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          rw [abs_of_nonneg hnon, abs_of_nonneg hR0] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hnorm'
      rw [modelCapRoundedLowerFunctionInner_eq_morse_add_eps_of_negPart_large hk c ε r δ θ hθ hδ hnegl]
      nlinarith
  · intro hin
    by_cases hnorm : morseNorm n y ≤ R₀
    · rw [modelCapRoundedLowerFunction_eq_inner_of_norm_le hk c ε r δ θ R₀ R₁ hR hR0 hnorm]
      exact hin
    · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have hpos : ‖posPart hk y‖ ^ 2 ≤ modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) := by
            dsimp [modelCapRoundedLowerFunctionInner] at hin
            nlinarith
          have hbound : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) ≤
              max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) :=
            modelLowerRoundBound_le_max_sub hδ hθ hδr
          have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
            calc
              morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
                rw [recombine_decompose hk y]
              _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
                morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
          have hle1 : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) <
              R₀ ^ 2 := by
            have h1 : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ r ^ 2 + 2 * ε + δ := by
              exact max_le (by nlinarith) (by nlinarith [hlt])
            nlinarith [hbig, h1, hlt]
          nlinarith [hnorm, hpos, hbound, hle1]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          rw [abs_of_nonneg hnon, abs_of_nonneg hR0] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hnorm'
      rw [modelCapRoundedLowerFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ θ R₀ R₁ hθ hδ hnegl]
      rw [modelCapRoundedLowerFunctionInner_eq_morse_add_eps_of_negPart_large hk c ε r δ θ hθ hδ hnegl] at hin
      exact hin

theorem modelRoundedFunction_le_c_iff_of_norm_le {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : morseNorm n y ≤ R₀) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c ↔ y ∈ modelAttachedRegion hk ε r δ := by
  rw [modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hy]
  exact (modelAttachedRegion_iff_sublevel hk c ε r δ y).symm

theorem modelRoundedFunction_sublevel_eq_attached_union_lower {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) :
    {y : MorseModel n | modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c} =
      (modelAttachedRegion hk ε r δ : Set (MorseModel n)) ∪
        {y : MorseModel n | r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 ∧
          morseNormalForm hk c y ≤ c - ε} := by
  ext y
  constructor
  · intro hy
    by_cases hnorm : morseNorm n y ≤ R₀
    · left
      exact (modelRoundedFunction_le_c_iff_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm).mp hy
    · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
      have hlow : morseNormalForm hk c y ≤ c - ε :=
        (modelRoundedFunction_le_c_iff_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hnorm').mp hy
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have h1 := modelLowerSublevel_norm_sq_lt_of_negPart_lt hk c ε r δ hlow hlt
          have h2 : 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε < R₀ ^ 2 := by nlinarith [hbig]
          nlinarith [h1, h2]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
          have h2 : |R₀| = R₀ := abs_of_nonneg hR0
          rw [h1, h2] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hnorm'
      exact Or.inr ⟨hnegl, hlow⟩
  · intro hy
    rcases hy with hatt | hlow
    · by_cases hnorm : morseNorm n y ≤ R₀
      · exact (modelRoundedFunction_le_c_iff_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm).mpr hatt
      · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
        have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
          by_contra hnot
          have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
          have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
            have h1 := modelAttached_norm_sq_lt_of_negPart_lt hk ε r δ (le_of_lt hε) hδ hatt hlt
            nlinarith [hbig, h1]
          have hle : morseNorm n y ≤ R₀ := by
            have habs := sq_lt_sq.mp hnormle
            have hnon : 0 ≤ morseNorm n y := by
              dsimp [morseNorm]
              exact norm_nonneg _
            have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
            have h2 : |R₀| = R₀ := abs_of_nonneg hR0
            rw [h1, h2] at habs
            exact le_of_lt habs
          exact (not_lt_of_ge hle) hnorm'
        have hlow : morseNormalForm hk c y ≤ c - ε := by
          dsimp [modelAttachedRegion] at hatt
          have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
            smoothCap_upper hδ hnegl
          rw [morseNormalForm_split]
          nlinarith [hatt, hcap]
        exact (modelRoundedFunction_le_c_iff_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hnorm').mpr hlow
    · rcases hlow with ⟨hnegl, hlow⟩
      by_cases hnorm : morseNorm n y ≤ R₀
      · have hatt : y ∈ modelAttachedRegion hk ε r δ := by
          dsimp [modelAttachedRegion]
          rw [morseNormalForm_split] at hlow
          have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
            smoothCap_upper hδ hnegl
          nlinarith [hlow, hcap]
        exact (modelRoundedFunction_le_c_iff_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm).mpr hatt
      · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
        exact (modelRoundedFunction_le_c_iff_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hnorm').mpr hlow


end
theorem modelRoundedFunction_gt_c_of_norm_ge_negPart_lt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ ≤ morseNorm n y)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    c < modelRoundedFunction hk c ε r δ R₀ R₁ y := by
  by_cases hy₁ : R₁ ≤ morseNorm n y
  · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁]
    rw [morseNormalForm_split]
    have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      calc
        morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
          rw [recombine_decompose hk y]
        _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
          morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
    have hbig' : r ^ 2 + 2 * ε + δ < R₁ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      have hb' : 2 * (r ^ 2 + 2 * ε + δ) < R₁ ^ 2 := by nlinarith [hbig, h01]
      nlinarith
    have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by
      have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
        exact sq_le_sq' (by nlinarith [hR0, hR]) hy₁
      nlinarith [hnorm, hsq, hbig', hneg]
    nlinarith
  · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
    let σ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
    have hσ : 0 ≤ σ := by dsimp [σ]; exact Real.smoothTransition.nonneg _
    have hσ₁ : σ ≤ 1 := by dsimp [σ]; exact Real.smoothTransition.le_one _
    have hpos : R₀ ^ 2 ≤ morseNorm n y ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hR0, hnon]) hy₀
    have hpos2 : ‖posPart hk y‖ ^ 2 > max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) := by
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) < R₀ ^ 2 := by
        have h1 : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ r ^ 2 + 2 * ε + δ := by
          exact max_le (by nlinarith) (by nlinarith [hneg])
        nlinarith [hbig, h1, hneg]
      nlinarith [hnorm, hpos, hb]
    have hF₁ : c < modelAttachedFunction hk c ε r δ y := by
      dsimp [modelAttachedFunction]
      have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) :=
        smoothCap_le_max_sub (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2)
      nlinarith [hpos2, hcap]
    have hF₂ : c < morseNormalForm hk c y + ε := by
      rw [morseNormalForm_split]
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by nlinarith [hpos2, hnorm]
      nlinarith
    dsimp [modelRoundedFunction]
    have hmain : c < modelAttachedFunction hk c ε r δ y +
        (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) * σ := by
      have hσlt : σ < 1 := by
        dsimp [σ]
        exact Real.smoothTransition.lt_one_of_lt_one (by
          have hsq : morseNorm n y ^ 2 < R₁ ^ 2 := by
            have hnon : 0 ≤ morseNorm n y := by
              dsimp [morseNorm]
              exact norm_nonneg _
            exact sq_lt_sq' (by nlinarith [hR0, hR, hnon]) hy₁'
          have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by nlinarith [hR, hR0]
          exact (div_lt_one hden).mpr (by nlinarith [hsq]))
      have hpos1 : 0 < modelAttachedFunction hk c ε r δ y - c := by linarith [hF₁]
      have hpos2' : 0 < morseNormalForm hk c y + ε - c := by linarith [hF₂]
      have hmain' : 0 < (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) +
          σ * (morseNormalForm hk c y + ε - c) := by
        have h₁ : 0 < (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) :=
          mul_pos (by linarith [hσlt]) hpos1
        have h₂ : 0 ≤ σ * (morseNormalForm hk c y + ε - c) :=
          mul_nonneg hσ (le_of_lt hpos2')
        nlinarith
      have hrew : modelAttachedFunction hk c ε r δ y +
          (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) * σ - c =
          (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) +
            σ * (morseNormalForm hk c y + ε - c) := by
        ring
      rw [← hrew] at hmain'
      linarith
    exact hmain



theorem modelAttachedRegion_of_negPart_large_lower {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ : 0 < δ) {y : MorseModel n}
    (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2)
    (hlow : morseNormalForm hk c y ≤ c - ε) : y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [morseNormalForm_split] at hlow
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
    smoothCap_upper hδ ht
  nlinarith [hlow, hsc]

theorem modelRoundedFunction_le_c_iff_mem_attachedRegion {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (y : MorseModel n) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c ↔ y ∈ modelAttachedRegion hk ε r δ := by
  change y ∈ {z : MorseModel n | modelRoundedFunction hk c ε r δ R₀ R₁ z ≤ c} ↔
    y ∈ modelAttachedRegion hk ε r δ
  rw [modelRoundedFunction_sublevel_eq_attached_union_lower hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig]
  constructor
  · intro hy
    rcases hy with hyatt | hydl
    · exact hyatt
    · exact modelAttachedRegion_of_negPart_large_lower hk c ε r δ hδ hydl.1 hydl.2
  · intro hyatt
    exact Or.inl hyatt

theorem modelRoundedFunction_eq_attached_of_norm_gt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hyatt : y ∈ modelAttachedRegion hk ε r δ) (hy₀ : R₀ < morseNorm n y) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = modelAttachedFunction hk c ε r δ y := by
  have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
    by_contra hnot
    have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
    have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
      have hmain := modelAttached_norm_sq_lt_of_negPart_lt hk ε r δ (le_of_lt hε) hδ hyatt hlt
      nlinarith [hbig, hmain]
    have hle : morseNorm n y ≤ R₀ := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      have habs := sq_lt_sq.mp hnormle
      have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
      have h2 : |R₀| = R₀ := abs_of_nonneg hR0
      rw [h1, h2] at habs
      exact le_of_lt habs
    exact (not_lt_of_ge hle) hy₀
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
    smoothCap_upper hδ hnegl
  dsimp [modelRoundedFunction]
  have hB : morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y = 0 := by
    dsimp [modelAttachedFunction]
    rw [morseNormalForm_split]
    rw [hsc]
    ring
  rw [hB]
  ring

theorem modelRoundedFunction_eq_c_iff_attachedFunction_eq {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (y : MorseModel n) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = c ↔ modelAttachedFunction hk c ε r δ y = c := by
  constructor
  · intro hy
    have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
      (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp
        (le_of_eq hy)
    by_cases hnorm : morseNorm n y ≤ R₀
    · rwa [modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm] at hy
    · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
      rwa [modelRoundedFunction_eq_attached_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR0 hbig hyatt hnorm'] at hy
  · intro hy
    have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
      (modelAttachedRegion_iff_sublevel hk c ε r δ y).mpr (le_of_eq hy)
    by_cases hnorm : morseNorm n y ≤ R₀
    · rw [modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm]
      exact hy
    · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
      rw [modelRoundedFunction_eq_attached_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR0 hbig hyatt hnorm']
      exact hy

theorem modelRoundedFunction_lt_c_iff_attachedFunction_lt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (y : MorseModel n) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y < c ↔ modelAttachedFunction hk c ε r δ y < c := by
  constructor
  · intro hy
    have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
      (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp
        (le_of_lt hy)
    have hle : modelAttachedFunction hk c ε r δ y ≤ c :=
      (modelAttachedRegion_iff_sublevel hk c ε r δ y).mp hyatt
    have hne : modelAttachedFunction hk c ε r δ y ≠ c := by
      intro hc
      have hc' : modelRoundedFunction hk c ε r δ R₀ R₁ y = c :=
        (modelRoundedFunction_eq_c_iff_attachedFunction_eq hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mpr hc
      exact (ne_of_lt hy) hc'
    exact lt_of_le_of_ne hle hne
  · intro hy
    have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
      (modelAttachedRegion_iff_sublevel hk c ε r δ y).mpr (le_of_lt hy)
    have hle : modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c :=
      (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mpr hyatt
    have hne : modelRoundedFunction hk c ε r δ R₀ R₁ y ≠ c := by
      intro hc
      have hc' : modelAttachedFunction hk c ε r δ y = c :=
        (modelRoundedFunction_eq_c_iff_attachedFunction_eq hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp hc
      exact (ne_of_lt hy) hc'
    exact lt_of_le_of_ne hle hne

theorem modelRoundedFunction_lowerRound_lt_c {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (y : MorseModel n) (hy : morseNormalForm hk c y < c - ε) :
    modelRoundedFunction hk c ε r δ R₀ R₁ (modelLowerRoundMap hk ε r δ θ y) < c := by
  exact (modelRoundedFunction_lt_c_iff_attachedFunction_lt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig
    (modelLowerRoundMap hk ε r δ θ y)).mpr
    (modelLowerRoundMap_mem_attached_strict hk c ε r δ θ hδ hθ hδr hθr y hy)

theorem fderiv_modelRoundedFunction_ne_zero {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (y : MorseModel n) (hy : modelRoundedFunction hk c ε r δ R₀ R₁ y = c) :
    fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y ≠ 0 := by
  by_cases hR0' : morseNorm n y < R₀
  · have hlocEq : Filter.Eventually (fun w : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ w = modelAttachedFunction hk c ε r δ w) (nhds y) := by
      have hcontNorm : Continuous (fun w : MorseModel n => morseNorm n w) := by
        dsimp [morseNorm]
        exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ))
      refine Filter.mem_of_superset ((isOpen_lt hcontNorm continuous_const).mem_nhds hR0') ?_
      intro w hw
      exact modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 (le_of_lt hw)
    have hfderiv : fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y =
        fderiv ℝ (modelAttachedFunction hk c ε r δ) y :=
      Filter.EventuallyEq.fderiv_eq (f₁ := modelRoundedFunction hk c ε r δ R₀ R₁)
        (f := modelAttachedFunction hk c ε r δ) (x := y) hlocEq
    have hval' : modelAttachedFunction hk c ε r δ y = c := by
      have hmod := modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 (le_of_lt hR0')
      rwa [hmod] at hy
    rw [hfderiv]
    exact fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ hδr y hval'
  · have hR0ge : R₀ ≤ morseNorm n y := le_of_not_gt hR0'
    have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
      by_contra hnot
      have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
      have hgt : c < modelRoundedFunction hk c ε r δ R₀ R₁ y :=
        modelRoundedFunction_gt_c_of_norm_ge_negPart_lt hk c ε r δ R₀ R₁
          hε hδ hR hR0 hbig hR0ge hlt
      exact (not_lt_of_ge (le_of_eq hy)) hgt
    have hlow : morseNormalForm hk c y = c - ε := by
      have hmod := modelRoundedFunction_eq_morse_add_eps_of_negPart_large
        hk c ε r δ R₀ R₁ hδ hnegl
      rw [hmod] at hy
      nlinarith
    have hneglStrict : r ^ 2 + 2 * ε + δ < ‖negPart hk y‖ ^ 2 := by
      by_contra hnot
      have hle : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ := le_of_not_gt hnot
      have hpos : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - ε := by
        rw [morseNormalForm_split] at hlow
        nlinarith
      have hnormSq : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hsmall : morseNorm n y ^ 2 < R₀ ^ 2 := by
        nlinarith [hle, hpos, hnormSq, hε, hbig]
      have hltR : morseNorm n y < R₀ := by
        have hnon : 0 ≤ morseNorm n y := by
          dsimp [morseNorm]
          exact norm_nonneg _
        have habs : |morseNorm n y| < |R₀| := sq_lt_sq.mp hsmall
        rw [abs_of_nonneg hnon, abs_of_nonneg hR0] at habs
        exact habs
      exact (not_le_of_gt hltR) hR0ge
    have hlocEq : Filter.Eventually (fun w : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ w =
          (fun w : MorseModel n => morseNormalForm hk c w + ε) w) (nhds y) := by
      have hcontNorm' : Continuous (fun w : MorseModel n => ‖negPart hk w‖) := by
        simpa [Function.comp_def] using (continuous_norm.comp (continuous_negPart hk))
      have hcont : Continuous (fun w : MorseModel n => ‖negPart hk w‖ ^ 2) :=
        hcontNorm'.pow 2
      have hopen : IsOpen {w : MorseModel n |
          r ^ 2 + 2 * ε + δ < ‖negPart hk w‖ ^ 2} :=
        isOpen_lt continuous_const hcont
      refine Filter.mem_of_superset (hopen.mem_nhds hneglStrict) ?_
      intro w hw
      exact modelRoundedFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ R₀ R₁ hδ (le_of_lt hw)
    have hfderiv : fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y =
        fderiv ℝ (fun w : MorseModel n => morseNormalForm hk c w + ε) y :=
      Filter.EventuallyEq.fderiv_eq (f₁ := modelRoundedFunction hk c ε r δ R₀ R₁)
        (f := fun w : MorseModel n => morseNormalForm hk c w + ε) (x := y) hlocEq
    have hder : fderiv ℝ (morseNormalForm hk c) y ≠ 0 :=
      fderiv_morseNormalForm_ne_zero_lower hk c ε hε y hlow
    have hderε : fderiv ℝ (fun w : MorseModel n => morseNormalForm hk c w + ε) y ≠ 0 := by
      intro hzero
      have hz : fderiv ℝ (fun w : MorseModel n => morseNormalForm hk c w + ε) y =
          fderiv ℝ (morseNormalForm hk c) y := by
        simp
      rw [hz] at hzero
      exact hder hzero
    rw [hfderiv]
    exact hderε

noncomputable def modelSublevelFamily {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (s : ℝ) (y : MorseModel n) : ℝ :=
  (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ y - c) +
    s * (morseNormalForm hk c y - c - ε)

theorem smoothCap_ge_sub_two_mul_eps {ε r δ t : ℝ} (hδ : 0 < δ) :
    t - 2 * ε - δ ≤ smoothCap ε r δ t := by
  by_cases ht₁ : t ≤ r ^ 2 + 2 * ε - δ
  · rw [smoothCap_lower hδ ht₁]
    nlinarith
  · by_cases ht₂ : r ^ 2 + 2 * ε + δ ≤ t
    · rw [smoothCap_upper hδ ht₂]
      nlinarith
    · have hmid : r ^ 2 + 2 * ε - δ < t ∧ t < r ^ 2 + 2 * ε + δ := by
        constructor <;> linarith
      dsimp [smoothCap]
      have hτ : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
        Real.smoothTransition.nonneg _
      have hτle : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
        Real.smoothTransition.le_one _
      have hw : t - 2 * ε - r ^ 2 ∈ Set.Icc (-δ) δ := by
        constructor <;> nlinarith [hmid.1, hmid.2]
      have hprod : (t - 2 * ε - r ^ 2) * (Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1) ≥ -δ := by
        by_cases hw0 : 0 ≤ t - 2 * ε - r ^ 2
        · have hσm1 : -1 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1 := by linarith [hτle]
          have h1 : (t - 2 * ε - r ^ 2) * (Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1) ≥
              (t - 2 * ε - r ^ 2) * (-1) := mul_le_mul_of_nonneg_left hσm1 hw0
          have hwle : t - 2 * ε - r ^ 2 ≤ δ := hw.2
          nlinarith [h1, hwle]
        · have hσm1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1 ≤ 0 := by linarith [hτle]
          have h1 : 0 ≤ (t - 2 * ε - r ^ 2) * (Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1) :=
            mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hw0) hσm1
          nlinarith [h1, hδ]
      have hb : r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≥
          t - 2 * ε - δ := by
        have hcalc : r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) -
            (t - 2 * ε - δ) = δ + (t - 2 * ε - r ^ 2) * (Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1) := by
          ring
        have hd : 0 ≤ r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) -
            (t - 2 * ε - δ) := by
          rw [hcalc]
          nlinarith [hprod, hδ]
        linarith
      exact hb

theorem deriv_smoothCap_eq_one_of_gt {ε r δ t : ℝ} (hδ : 0 < δ) (ht : r ^ 2 + 2 * ε + δ < t) :
    deriv (smoothCap ε r δ) t = 1 := by
  have hloc : smoothCap ε r δ =ᶠ[nhds t] (fun t : ℝ => t - 2 * ε) := by
    refine Filter.eventuallyEq_of_mem ((isOpen_Ioi : IsOpen {t : ℝ | r ^ 2 + 2 * ε + δ < t}).mem_nhds ht) ?_
    intro t' ht'
    exact smoothCap_upper hδ (le_of_lt ht')
  have hder : deriv (fun t : ℝ => t - 2 * ε) t = 1 := by
    simp
  rw [← hder]
  exact hloc.deriv_eq

theorem smoothTransition_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x := by
  by_cases hx : x ≤ 0 ∨ 1 ≤ x
  · rcases hx with hxle | hxge
    · rw [Real.smoothTransition_deriv_zero_of_nonpos x hxle]
    · rw [Real.smoothTransition_deriv_zero_of_one_le x hxge]
  · have hx0 : 0 < x := by
      rw [not_or] at hx
      exact lt_of_not_ge hx.1
    have hx1 : x < 1 := by
      rw [not_or] at hx
      exact lt_of_not_ge hx.2
    rw [Real.smoothTransition_deriv_eq hx0 hx1]
    have hE1 : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx0
    have hE2 : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
    have hx2 : 0 < x⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero (ne_of_gt hx0))
    have hx3 : 0 < (1 - x)⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero (ne_of_gt (by linarith)))
    have hsum' : 0 < x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 := by linarith
    have hnum : 0 < expNegInvGlue x * expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) :=
      mul_pos (mul_pos hE1 hE2) hsum'
    have hsum : 0 < expNegInvGlue x + expNegInvGlue (1 - x) := by positivity
    have hden : 0 < (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by positivity
    exact div_nonneg hnum.le hden.le

theorem morseNorm_sq_split {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    morseNorm n y ^ 2 = ‖posPart hk y‖ ^ 2 + ‖negPart hk y‖ ^ 2 := by
  calc
    morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
      rw [recombine_decompose hk y]
    _ = ‖posPart hk y‖ ^ 2 + ‖negPart hk y‖ ^ 2 := by
      rw [morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)]
      ring

theorem fderiv_morseNormalForm_direction_pos {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = ‖posPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfun : (fun y : MorseModel n => morseNormalForm hk c y) =
      fun y : MorseModel n => c + (1 / 2 : ℝ) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
    funext y
    unfold morseNormalForm
    have hpos : ∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2 = ‖posPart hk y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq (posPart hk y)]
      simp [posPart]
    have hneg : ∑ i : Fin k, - (y (negIdx hk i)) ^ 2 = -‖negPart hk y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
      simp [negPart]
    rw [hpos, hneg]
    ring
  have hderiv : fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
        fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y) := by
    rw [hfun]
    rw [fderiv_const_add]
    rw [fderiv_const_mul]
    · exact congrArg (fun L : MorseModel n →L[ℝ] ℝ => (1 / 2 : ℝ) • L)
        (fderiv_sub (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
          (g := fun y : MorseModel n => ‖negPart hk y‖ ^ 2)
          (hf := hdiffPos) (hg := hdiffNeg))
    · exact hdiffPos.sub hdiffNeg
  calc
    fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))
        = ((1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
            fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y))
            (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) := by
          rw [hderiv]
    _ = ‖posPart hk y‖ ^ 2 := by
          simp [fderiv_posPart_normSq_self hk y, fderiv_negPart_normSq_zero_direction hk y]

theorem fderiv_morseNormalForm_direction_neg {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = -‖negPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfun : (fun y : MorseModel n => morseNormalForm hk c y) =
      fun y : MorseModel n => c + (1 / 2 : ℝ) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
    funext y
    unfold morseNormalForm
    have hpos : ∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2 = ‖posPart hk y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq (posPart hk y)]
      simp [posPart]
    have hneg : ∑ i : Fin k, - (y (negIdx hk i)) ^ 2 = -‖negPart hk y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
      simp [negPart]
    rw [hpos, hneg]
    ring
  have hderiv : fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
        fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y) := by
    rw [hfun]
    rw [fderiv_const_add]
    rw [fderiv_const_mul]
    · exact congrArg (fun L : MorseModel n →L[ℝ] ℝ => (1 / 2 : ℝ) • L)
        (fderiv_sub (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
          (g := fun y : MorseModel n => ‖negPart hk y‖ ^ 2)
          (hf := hdiffPos) (hg := hdiffNeg))
    · exact hdiffPos.sub hdiffNeg
  calc
    fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y
        (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))
        = ((1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
            fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y))
            (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) := by
          rw [hderiv]
    _ = -‖negPart hk y‖ ^ 2 := by
          simp [fderiv_posPart_normSq_zero_direction hk y, fderiv_negPart_normSq_self hk y]

theorem fderiv_modelAttachedFunction_direction_neg {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (y : MorseModel n) :
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      -(deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)) * ‖negPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffCap : DifferentiableAt ℝ (fun y : MorseModel n =>
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y :=
    ((smoothCap_contDiff ε r δ).comp (contDiff_negPart_normSq hk)).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hderiv : fderiv ℝ (modelAttachedFunction hk c ε r δ) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
        fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y) := by
    unfold modelAttachedFunction
    rw [fderiv_const_add]
    rw [fderiv_const_mul]
    · exact congrArg (fun L : MorseModel n →L[ℝ] ℝ => (1 / 2 : ℝ) • L)
        (fderiv_sub (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
          (g := fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2))
          (hf := hdiffPos) (hg := hdiffCap))
    · exact hdiffPos.sub hdiffCap
  have hcap : fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      (deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)) * (2 * ‖negPart hk y‖ ^ 2) := by
    have hinnerDiff : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
      (contDiff_negPart_normSq hk).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
    have hcapDiff : DifferentiableAt ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) :=
      (smoothCap_contDiff ε r δ).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
    have hcomp : fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y =
        (fderiv ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)).comp
          (fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y) :=
      fderiv_comp (x := y) (f := fun y : MorseModel n => ‖negPart hk y‖ ^ 2)
        (g := smoothCap ε r δ) (hg := hcapDiff) (hf := hinnerDiff)
    calc
      fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y
          (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))
          = ((fderiv ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)).comp
              (fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y))
              (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) := by
            rw [hcomp]
      _ = (deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)) *
            (2 * ‖negPart hk y‖ ^ 2) := by
            simp [fderiv_negPart_normSq_self hk y]
            ring
  calc
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y
        (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))
        = ((1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
            fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y))
            (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) := by
          rw [hderiv]
    _ = -(deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)) * ‖negPart hk y‖ ^ 2 := by
          simp [fderiv_posPart_normSq_zero_direction hk y, hcap]
          ring

theorem fderiv_morseNorm_sq_direction_pos {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 2 * ‖posPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hsplit : (fun y : MorseModel n => morseNorm n y ^ 2) =
      (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    funext y
    exact morseNorm_sq_split hk y
  rw [hsplit]
  rw [fderiv_add (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
    (g := fun y : MorseModel n => ‖negPart hk y‖ ^ 2) (hf := hdiffPos) (hg := hdiffNeg)]
  simp [fderiv_posPart_normSq_self hk y, fderiv_negPart_normSq_zero_direction hk y]

theorem fderiv_morseNorm_sq_direction_neg {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 2 * ‖negPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hsplit : (fun y : MorseModel n => morseNorm n y ^ 2) =
      (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    funext y
    exact morseNorm_sq_split hk y
  rw [hsplit]
  rw [fderiv_add (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
    (g := fun y : MorseModel n => ‖negPart hk y‖ ^ 2) (hf := hdiffPos) (hg := hdiffNeg)]
  simp [fderiv_posPart_normSq_zero_direction hk y, fderiv_negPart_normSq_self hk y]

private theorem fderiv_morseNorm_sq {n k : ℕ} (hk : k ≤ n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y w =
      fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y w +
        fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y w := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hsplit : (fun y : MorseModel n => morseNorm n y ^ 2) =
      (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    funext y
    exact morseNorm_sq_split hk y
  rw [hsplit]
  rw [fderiv_add (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
    (g := fun y : MorseModel n => ‖negPart hk y‖ ^ 2) (hf := hdiffPos) (hg := hdiffNeg)]
  rfl

theorem fderiv_smoothTransitionArg_direction_pos {n k : ℕ} (hk : k ≤ n) (R₀ R₁ : ℝ)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => Real.smoothTransition
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
        (2 * ‖posPart hk y‖ ^ 2 / (R₁ ^ 2 - R₀ ^ 2)) := by
  let f : MorseModel n → ℝ := fun y => (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹
  have hden : (R₁ ^ 2 - R₀ ^ 2) ≠ 0 := by
    have hpos : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have hlt : |R₀| < |R₁| := by
        rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
        exact hR
      have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
      nlinarith
    exact ne_of_gt hpos
  have hdiffNorm : DifferentiableAt ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y := by
    have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        ‖posPart hk y‖ ^ 2 + ‖negPart hk y‖ ^ 2) :=
      (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
    have hsplit : (fun y : MorseModel n => morseNorm n y ^ 2) =
        fun y : MorseModel n => ‖posPart hk y‖ ^ 2 + ‖negPart hk y‖ ^ 2 := by
      funext y
      exact morseNorm_sq_split hk y
    rw [hsplit]
    exact hcont.differentiable (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hc : ContDiff ℝ (⊤ : ℕ∞) f := by
    dsimp [f]
    have hcNorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
      rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
          (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) by
        funext y
        exact morseNorm_sq_split hk y]
      exact (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
    exact (hcNorm.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)))).mul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => ((R₁ ^ 2 - R₀ ^ 2)⁻¹ : ℝ)))
  have hfDiff : DifferentiableAt ℝ f y :=
    hc.differentiable (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hgDiff : DifferentiableAt ℝ Real.smoothTransition (f y) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hcomp := fderiv_comp (x := y) (f := f) (g := Real.smoothTransition) (hg := hgDiff) (hf := hfDiff)
  have hval : fderiv ℝ (fun y : MorseModel n => Real.smoothTransition (f y)) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      fderiv ℝ Real.smoothTransition (f y)
        (fderiv ℝ f y (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))) := by
    simpa [Function.comp_def] using congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))) hcomp
  have hfval : fderiv ℝ f y (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      2 * ‖posPart hk y‖ ^ 2 / (R₁ ^ 2 - R₀ ^ 2) := by
    dsimp [f]
    rw [show (fun y : MorseModel n => (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹) =
        fun y : MorseModel n => (R₁ ^ 2 - R₀ ^ 2)⁻¹ * (morseNorm n y ^ 2 - R₀ ^ 2) by
      funext y
      ring]
    rw [fderiv_const_mul (a := fun y : MorseModel n => morseNorm n y ^ 2 - R₀ ^ 2)
      (b := (R₁ ^ 2 - R₀ ^ 2)⁻¹) (ha := by
        exact hdiffNorm.sub (differentiableAt_const (R₀ ^ 2) : DifferentiableAt ℝ
          (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)) y))]
    rw [ContinuousLinearMap.smul_apply]
    have hsub' : fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2 - R₀ ^ 2) y
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
        fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y
          (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) := by
      simpa using congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)))
        (fderiv_sub (f := fun y : MorseModel n => morseNorm n y ^ 2)
          (g := fun _ : MorseModel n => (R₀ ^ 2 : ℝ)) (hf := hdiffNorm)
          (hg := (differentiableAt_const (R₀ ^ 2) : DifferentiableAt ℝ
            (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)) y)))
    rw [hsub']
    simp [fderiv_morseNorm_sq hk y, fderiv_posPart_normSq_self hk y,
      fderiv_negPart_normSq_zero_direction hk y]
    ring
  rw [show (fun y : MorseModel n => Real.smoothTransition
      ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) =
      fun y : MorseModel n => Real.smoothTransition (f y) by
    funext y
    rfl]
  rw [hval, hfval]
  have hfy : f y = (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    dsimp [f]
    rfl
  rw [hfy]
  simp [fderiv_eq_smul_deriv]
  ring

theorem fderiv_smoothTransitionArg_direction_neg {n k : ℕ} (hk : k ≤ n) (R₀ R₁ : ℝ)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => Real.smoothTransition
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
        (2 * ‖negPart hk y‖ ^ 2 / (R₁ ^ 2 - R₀ ^ 2)) := by
  let f : MorseModel n → ℝ := fun y => (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹
  have hden : (R₁ ^ 2 - R₀ ^ 2) ≠ 0 := by
    have hpos : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have hlt : |R₀| < |R₁| := by
        rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
        exact hR
      have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
      nlinarith
    exact ne_of_gt hpos
  have hdiffNorm : DifferentiableAt ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y := by
    have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        ‖posPart hk y‖ ^ 2 + ‖negPart hk y‖ ^ 2) :=
      (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
    have hsplit : (fun y : MorseModel n => morseNorm n y ^ 2) =
        fun y : MorseModel n => ‖posPart hk y‖ ^ 2 + ‖negPart hk y‖ ^ 2 := by
      funext y
      exact morseNorm_sq_split hk y
    rw [hsplit]
    exact hcont.differentiable (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hc : ContDiff ℝ (⊤ : ℕ∞) f := by
    dsimp [f]
    have hcNorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
      rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
          (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) by
        funext y
        exact morseNorm_sq_split hk y]
      exact (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
    exact (hcNorm.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)))).mul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => ((R₁ ^ 2 - R₀ ^ 2)⁻¹ : ℝ)))
  have hfDiff : DifferentiableAt ℝ f y :=
    hc.differentiable (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hgDiff : DifferentiableAt ℝ Real.smoothTransition (f y) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hcomp := fderiv_comp (x := y) (f := f) (g := Real.smoothTransition) (hg := hgDiff) (hf := hfDiff)
  have hval : fderiv ℝ (fun y : MorseModel n => Real.smoothTransition (f y)) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      fderiv ℝ Real.smoothTransition (f y)
        (fderiv ℝ f y (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))) := by
    simpa [Function.comp_def] using congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))) hcomp
  have hfval : fderiv ℝ f y (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      2 * ‖negPart hk y‖ ^ 2 / (R₁ ^ 2 - R₀ ^ 2) := by
    dsimp [f]
    rw [show (fun y : MorseModel n => (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹) =
        fun y : MorseModel n => (R₁ ^ 2 - R₀ ^ 2)⁻¹ * (morseNorm n y ^ 2 - R₀ ^ 2) by
      funext y
      ring]
    rw [fderiv_const_mul (a := fun y : MorseModel n => morseNorm n y ^ 2 - R₀ ^ 2)
      (b := (R₁ ^ 2 - R₀ ^ 2)⁻¹) (ha := by
        exact hdiffNorm.sub (differentiableAt_const (R₀ ^ 2) : DifferentiableAt ℝ
          (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)) y))]
    rw [ContinuousLinearMap.smul_apply]
    have hsub' : fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2 - R₀ ^ 2) y
        (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
        fderiv ℝ (fun y : MorseModel n => morseNorm n y ^ 2) y
          (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) := by
      simpa using congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L
        (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))))
        (fderiv_sub (f := fun y : MorseModel n => morseNorm n y ^ 2)
          (g := fun _ : MorseModel n => (R₀ ^ 2 : ℝ)) (hf := hdiffNorm)
          (hg := (differentiableAt_const (R₀ ^ 2) : DifferentiableAt ℝ
            (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)) y)))
    rw [hsub']
    simp [fderiv_morseNorm_sq hk y, fderiv_posPart_normSq_zero_direction hk y,
      fderiv_negPart_normSq_self hk y]
    ring
  rw [show (fun y : MorseModel n => Real.smoothTransition
      ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) =
      fun y : MorseModel n => Real.smoothTransition (f y) by
    funext y
    rfl]
  rw [hval, hfval]
  have hfy : f y = (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    dsimp [f]
    rfl
  rw [hfy]
  simp [fderiv_eq_smul_deriv]
  ring

theorem fderiv_modelRoundedFunction_direction {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (y w : MorseModel n) :
    fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y w =
      fderiv ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y w +
        (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
          fderiv ℝ (fun y : MorseModel n => Real.smoothTransition
            ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) y w +
        Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) *
          (fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y - c) y w -
            fderiv ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y w) := by
  let A : MorseModel n → ℝ := fun y => modelAttachedFunction hk c ε r δ y - c
  let N : MorseModel n → ℝ := fun y => morseNormalForm hk c y - c
  let τ : MorseModel n → ℝ := fun y => Real.smoothTransition
    ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
  have hA : DifferentiableAt ℝ A y := by
    dsimp [A]
    exact ((contDiff_modelAttachedFunction hk c ε r δ).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hN : DifferentiableAt ℝ N y := by
    dsimp [N]
    exact ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hτ : DifferentiableAt ℝ τ y := by
    dsimp [τ]
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
      have hcNorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
        rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
            (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) by
          funext y
          exact morseNorm_sq_split hk y]
        exact (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
      change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹)
      exact (hcNorm.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)))).mul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : MorseModel n => ((R₁ ^ 2 - R₀ ^ 2)⁻¹ : ℝ)))
    exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hc).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdef : modelRoundedFunction hk c ε r δ R₀ R₁ =
      A + (N + (fun _ : MorseModel n => ε) - A) * τ + (fun _ : MorseModel n => c) := by
    funext y
    change modelAttachedFunction hk c ε r δ y +
        (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) *
          Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) =
      (modelAttachedFunction hk c ε r δ y - c) +
        (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
          Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) + c
    ring
  have hmid : DifferentiableAt ℝ (N + (fun _ : MorseModel n => ε) - A) y := by
    exact (hN.add (differentiableAt_const ε)).sub hA
  have hmid' : fderiv ℝ (N + (fun _ : MorseModel n => ε) - A) y w =
      fderiv ℝ N y w - fderiv ℝ A y w := by
    have hstep : fderiv ℝ (N + (fun _ : MorseModel n => ε)) y w = fderiv ℝ N y w := by
      rw [fderiv_add (f := N) (g := fun _ : MorseModel n => ε) (hf := hN)
        (hg := differentiableAt_const ε)]
      simp
    rw [fderiv_sub (f := N + (fun _ : MorseModel n => ε)) (g := A)
      (hf := hN.add (differentiableAt_const ε)) (hg := hA)]
    simp [ContinuousLinearMap.sub_apply, hstep]
  have hAτ : DifferentiableAt ℝ ((N + (fun _ : MorseModel n => ε) - A) * τ) y := hmid.mul hτ
  calc
    fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y w
        = fderiv ℝ (A + (N + (fun _ : MorseModel n => ε) - A) * τ + (fun _ : MorseModel n => c)) y w := by
          rw [hdef]
    _ = fderiv ℝ (A + (N + (fun _ : MorseModel n => ε) - A) * τ) y w := by
          rw [fderiv_add (f := A + (N + (fun _ : MorseModel n => ε) - A) * τ)
            (g := fun _ : MorseModel n => c) (hf := hA.add hAτ) (hg := differentiableAt_const c)]
          simp only [fderiv_fun_const, Pi.zero_apply, add_zero]
    _ = fderiv ℝ A y w + fderiv ℝ ((N + (fun _ : MorseModel n => ε) - A) * τ) y w := by
          rw [fderiv_add (f := A) (g := (N + (fun _ : MorseModel n => ε) - A) * τ) (hf := hA)
            (hg := hAτ)]
          simp only [ContinuousLinearMap.add_apply]
    _ = fderiv ℝ A y w +
          ((N y + ε - A y) * fderiv ℝ τ y w + τ y * (fderiv ℝ N y w - fderiv ℝ A y w)) := by
          rw [fderiv_mul hmid hτ]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hmid']
          rfl
    _ = fderiv ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y w +
          (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
            fderiv ℝ (fun y : MorseModel n => Real.smoothTransition
              ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) y w +
          Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) *
            (fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y - c) y w -
              fderiv ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y w) := by
          dsimp [A, N, τ]
          ring

theorem fderiv_modelSublevelFamily_direction_pos {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ s : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n) :
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      ‖posPart hk y‖ ^ 2 *
        (1 + 2 * (1 - s) * (morseNormalForm hk c y - c + ε -
          (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) := by
  let A : MorseModel n → ℝ := fun y => modelAttachedFunction hk c ε r δ y - c
  let N : MorseModel n → ℝ := fun y => morseNormalForm hk c y - c
  let wp : MorseModel n := recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  have hA : DifferentiableAt ℝ A y := by
    dsimp [A]
    exact ((contDiff_modelAttachedFunction hk c ε r δ).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hN : DifferentiableAt ℝ N y := by
    dsimp [N]
    exact ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hτc : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => Real.smoothTransition
      ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
    have hcNorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
      rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
          (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) by
        funext y
        exact morseNorm_sq_split hk y]
      exact (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹)
      exact (hcNorm.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)))).mul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : MorseModel n => ((R₁ ^ 2 - R₀ ^ 2)⁻¹ : ℝ)))
    exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hc
  have hRdiff : DifferentiableAt ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y := by
    have hmid : DifferentiableAt ℝ (N + (fun _ : MorseModel n => ε) - A) y :=
      (hN.add (differentiableAt_const ε)).sub hA
    have hdef' : modelRoundedFunction hk c ε r δ R₀ R₁ =
        A + (N + (fun _ : MorseModel n => ε) - A) *
          (fun y : MorseModel n => Real.smoothTransition
            ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) + (fun _ : MorseModel n => c) := by
      funext z
      dsimp [A, N, modelRoundedFunction]
      ring
    rw [hdef']
    exact (hA.add (hmid.mul (hτc.differentiable (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm)
      |>.differentiableAt))).add (differentiableAt_const c)
  have hdiffR0 : DifferentiableAt ℝ (fun z : MorseModel n =>
      modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y :=
    hRdiff.sub (differentiableAt_const c)
  have hdiffN : DifferentiableAt ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y :=
    hN.sub (differentiableAt_const ε)
  have hAval : fderiv ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y wp =
      ‖posPart hk y‖ ^ 2 := by
    rw [show (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) =
        modelAttachedFunction hk c ε r δ - (fun _ : MorseModel n => c) by rfl]
    rw [fderiv_sub (f := modelAttachedFunction hk c ε r δ) (g := fun _ : MorseModel n => c)
      (hf := (contDiff_modelAttachedFunction hk c ε r δ).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
      (hg := differentiableAt_const c)]
    simp [wp, fderiv_modelAttachedFunction_direction hk c ε r δ y]
  have hN0 : fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y - c) y wp =
      fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y wp := by
    rw [show (fun y : MorseModel n => morseNormalForm hk c y - c) =
        (fun y : MorseModel n => morseNormalForm hk c y) - (fun _ : MorseModel n => c) by rfl]
    rw [fderiv_sub (f := fun y : MorseModel n => morseNormalForm hk c y)
      (g := fun _ : MorseModel n => c) (hf := (contDiff_morseNormalForm hk c).differentiable
        (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
      (hg := differentiableAt_const c)]
    simp
  have hRval : fderiv ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y wp =
      ‖posPart hk y‖ ^ 2 *
        (1 + 2 * (N y + ε - A y) *
          (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
            (R₁ ^ 2 - R₀ ^ 2))) := by
    have hd : fderiv ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y wp =
        fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y wp := by
      rw [show (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) =
          modelRoundedFunction hk c ε r δ R₀ R₁ - (fun _ : MorseModel n => c) by rfl]
      rw [fderiv_sub (f := modelRoundedFunction hk c ε r δ R₀ R₁) (g := fun _ : MorseModel n => c)
        (hf := hRdiff) (hg := differentiableAt_const c)]
      simp
    rw [hd, fderiv_modelRoundedFunction_direction hk c ε r δ R₀ R₁ y wp]
    simp [A, N, wp, hAval, hN0, fderiv_morseNormalForm_direction_pos hk c y,
      fderiv_smoothTransitionArg_direction_pos hk R₀ R₁ hR hR0 y]
    ring_nf
  have hNval : fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y wp =
      ‖posPart hk y‖ ^ 2 := by
    have hd1 : fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c) y wp =
        fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z) y wp := by
      rw [show (fun z : MorseModel n => morseNormalForm hk c z - c) =
          (fun z : MorseModel n => morseNormalForm hk c z) - (fun _ : MorseModel n => c) by rfl]
      rw [fderiv_sub (f := fun z : MorseModel n => morseNormalForm hk c z)
        (g := fun _ : MorseModel n => c) (hf := (contDiff_morseNormalForm hk c).differentiable
          (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
        (hg := differentiableAt_const c)]
      simp
    have hd : fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y wp =
        fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z) y wp := by
      rw [show (fun z : MorseModel n => morseNormalForm hk c z - c - ε) =
          (fun z : MorseModel n => morseNormalForm hk c z - c) - (fun _ : MorseModel n => ε) by rfl]
      rw [fderiv_sub (f := fun z : MorseModel n => morseNormalForm hk c z - c)
        (g := fun _ : MorseModel n => ε) (hf := hN) (hg := differentiableAt_const ε)]
      simp [hd1]
    rw [hd]
    exact fderiv_morseNormalForm_direction_pos hk c y
  calc
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wp
        = (1 - s) * fderiv ℝ (fun z : MorseModel n =>
            modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y wp +
          s * fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y wp := by
          unfold modelSublevelFamily
          rw [show (fun z : MorseModel n => (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ z - c) +
              s * (morseNormalForm hk c z - c - ε)) =
              (fun z : MorseModel n => (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ z - c)) +
                (fun z : MorseModel n => s * (morseNormalForm hk c z - c - ε)) by rfl]
          rw [fderiv_add (f := fun z : MorseModel n => (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ z - c))
            (g := fun z : MorseModel n => s * (morseNormalForm hk c z - c - ε))
            (hf := hdiffR0.const_mul (1 - s)) (hg := hdiffN.const_mul s)]
          simp only [ContinuousLinearMap.add_apply]
          rw [fderiv_const_mul (a := fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c)
            (b := 1 - s) (ha := hdiffR0)]
          rw [fderiv_const_mul (a := fun z : MorseModel n => morseNormalForm hk c z - c - ε)
            (b := s) (ha := hdiffN)]
          simp [ContinuousLinearMap.smul_apply]
    _ = (1 - s) * (‖posPart hk y‖ ^ 2 *
          (1 + 2 * (N y + ε - A y) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2)))) + s * ‖posPart hk y‖ ^ 2 := by
          rw [hRval, hNval]
    _ = ‖posPart hk y‖ ^ 2 *
        (1 + 2 * (1 - s) * (N y + ε - A y) *
          (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
            (R₁ ^ 2 - R₀ ^ 2))) := by
          ring
    _ = ‖posPart hk y‖ ^ 2 *
        (1 + 2 * (1 - s) * (morseNormalForm hk c y - c + ε -
          (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) := by
          dsimp [A, N]

theorem fderiv_modelSublevelFamily_direction_neg {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ s : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n) :
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      ‖negPart hk y‖ ^ 2 *
        (-((1 - s) * (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
              deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) +
            (1 - s) * Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) + s) +
          2 * (1 - s) * (morseNormalForm hk c y - c + ε -
            (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) := by
  let A : MorseModel n → ℝ := fun y => modelAttachedFunction hk c ε r δ y - c
  let N : MorseModel n → ℝ := fun y => morseNormalForm hk c y - c
  let wm : MorseModel n := recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  have hA : DifferentiableAt ℝ A y := by
    dsimp [A]
    exact ((contDiff_modelAttachedFunction hk c ε r δ).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hN : DifferentiableAt ℝ N y := by
    dsimp [N]
    exact ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hRdiff : DifferentiableAt ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y := by
    have hmid : DifferentiableAt ℝ (N + (fun _ : MorseModel n => ε) - A) y :=
      (hN.add (differentiableAt_const ε)).sub hA
    have hdef' : modelRoundedFunction hk c ε r δ R₀ R₁ =
        A + (N + (fun _ : MorseModel n => ε) - A) *
          (fun y : MorseModel n => Real.smoothTransition
            ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) + (fun _ : MorseModel n => c) := by
      funext z
      dsimp [A, N, modelRoundedFunction]
      ring
    rw [hdef']
    have hτ : DifferentiableAt ℝ (fun y : MorseModel n => Real.smoothTransition
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) y := by
      have hcNorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
        rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
            (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) by
          funext y
          exact morseNorm_sq_split hk y]
        exact (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
      have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
          ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
        change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
          (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹)
        exact (hcNorm.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)))).mul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : MorseModel n => ((R₁ ^ 2 - R₀ ^ 2)⁻¹ : ℝ)))
      exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hc).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
    exact (hA.add (hmid.mul hτ)).add (differentiableAt_const c)
  have hdiffR0 : DifferentiableAt ℝ (fun z : MorseModel n =>
      modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y :=
    hRdiff.sub (differentiableAt_const c)
  have hdiffN : DifferentiableAt ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y :=
    hN.sub (differentiableAt_const ε)
  have hAval : fderiv ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y wm =
      -(deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)) * ‖negPart hk y‖ ^ 2 := by
    rw [show (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) =
        modelAttachedFunction hk c ε r δ - (fun _ : MorseModel n => c) by rfl]
    rw [fderiv_sub (f := modelAttachedFunction hk c ε r δ) (g := fun _ : MorseModel n => c)
      (hf := (contDiff_modelAttachedFunction hk c ε r δ).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
      (hg := differentiableAt_const c)]
    simp [wm, fderiv_modelAttachedFunction_direction_neg hk c ε r δ y]
  have hN0 : fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y - c) y wm =
      fderiv ℝ (fun y : MorseModel n => morseNormalForm hk c y) y wm := by
    rw [show (fun y : MorseModel n => morseNormalForm hk c y - c) =
        (fun y : MorseModel n => morseNormalForm hk c y) - (fun _ : MorseModel n => c) by rfl]
    rw [fderiv_sub (f := fun y : MorseModel n => morseNormalForm hk c y)
      (g := fun _ : MorseModel n => c) (hf := (contDiff_morseNormalForm hk c).differentiable
        (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
      (hg := differentiableAt_const c)]
    simp
  have hRval : fderiv ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y wm =
      -(deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)) * ‖negPart hk y‖ ^ 2 -
        Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) *
          ‖negPart hk y‖ ^ 2 +
        Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) *
          deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) * ‖negPart hk y‖ ^ 2 +
        (N y + ε - A y) *
          (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
            (R₁ ^ 2 - R₀ ^ 2)) * (2 * ‖negPart hk y‖ ^ 2) := by
    have hd : fderiv ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y wm =
        fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y wm := by
      rw [show (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) =
          modelRoundedFunction hk c ε r δ R₀ R₁ - (fun _ : MorseModel n => c) by rfl]
      rw [fderiv_sub (f := modelRoundedFunction hk c ε r δ R₀ R₁) (g := fun _ : MorseModel n => c)
        (hf := hRdiff) (hg := differentiableAt_const c)]
      simp
    rw [hd, fderiv_modelRoundedFunction_direction hk c ε r δ R₀ R₁ y wm]
    simp [A, N, wm, hAval, hN0, fderiv_morseNormalForm_direction_neg hk c y,
      fderiv_smoothTransitionArg_direction_neg hk R₀ R₁ hR hR0 y]
    ring
  have hNval : fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y wm =
      -‖negPart hk y‖ ^ 2 := by
    have hd1 : fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c) y wm =
        fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z) y wm := by
      rw [show (fun z : MorseModel n => morseNormalForm hk c z - c) =
          (fun z : MorseModel n => morseNormalForm hk c z) - (fun _ : MorseModel n => c) by rfl]
      rw [fderiv_sub (f := fun z : MorseModel n => morseNormalForm hk c z)
        (g := fun _ : MorseModel n => c) (hf := (contDiff_morseNormalForm hk c).differentiable
          (by exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
        (hg := differentiableAt_const c)]
      simp
    have hd : fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y wm =
        fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z) y wm := by
      rw [show (fun z : MorseModel n => morseNormalForm hk c z - c - ε) =
          (fun z : MorseModel n => morseNormalForm hk c z - c) - (fun _ : MorseModel n => ε) by rfl]
      rw [fderiv_sub (f := fun z : MorseModel n => morseNormalForm hk c z - c)
        (g := fun _ : MorseModel n => ε) (hf := hN) (hg := differentiableAt_const ε)]
      simp [hd1]
    rw [hd]
    exact fderiv_morseNormalForm_direction_neg hk c y
  calc
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wm
        = (1 - s) * fderiv ℝ (fun z : MorseModel n =>
            modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y wm +
          s * fderiv ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y wm := by
          unfold modelSublevelFamily
          rw [show (fun z : MorseModel n => (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ z - c) +
              s * (morseNormalForm hk c z - c - ε)) =
              (fun z : MorseModel n => (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ z - c)) +
                (fun z : MorseModel n => s * (morseNormalForm hk c z - c - ε)) by rfl]
          rw [fderiv_add (f := fun z : MorseModel n => (1 - s) * (modelRoundedFunction hk c ε r δ R₀ R₁ z - c))
            (g := fun z : MorseModel n => s * (morseNormalForm hk c z - c - ε))
            (hf := hdiffR0.const_mul (1 - s)) (hg := hdiffN.const_mul s)]
          simp only [ContinuousLinearMap.add_apply]
          rw [fderiv_const_mul (a := fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c)
            (b := 1 - s) (ha := hdiffR0)]
          rw [fderiv_const_mul (a := fun z : MorseModel n => morseNormalForm hk c z - c - ε)
            (b := s) (ha := hdiffN)]
          simp [ContinuousLinearMap.smul_apply]
    _ = ‖negPart hk y‖ ^ 2 *
        (-((1 - s) * (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
              deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) +
            (1 - s) * Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) + s) +
          2 * (1 - s) * (morseNormalForm hk c y - c + ε -
            (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) := by
          rw [hRval, hNval]
          dsimp [A, N]
          ring_nf

theorem recombine_zero_of_parts_eq_zero {n k : ℕ} (hk : k ≤ n) (y : MorseModel n)
    (hp : posPart hk y = 0) (hm : negPart hk y = 0) : y = 0 := by
  have hdec : y = recombine hk (negPart hk y) (posPart hk y) := (recombine_decompose hk y).symm
  rw [hdec, hm, hp]
  ext i
  dsimp [recombine]
  by_cases hi : i.val < k
  · simp [hi]
  · simp [hi]

theorem smoothTransition_pos_iff (x : ℝ) : 0 < Real.smoothTransition x ↔ 0 < x := by
  constructor
  · intro hpos
    by_contra hnot
    have hle : x ≤ 0 := le_of_not_gt hnot
    have hz : Real.smoothTransition x = 0 := Real.smoothTransition.zero_of_nonpos hle
    rw [hz] at hpos
    linarith
  · intro hx
    by_cases hx1 : 1 ≤ x
    · rw [Real.smoothTransition.one_of_one_le hx1]
      norm_num
    · have hxlt : x < 1 := lt_of_not_ge hx1
      change 0 < expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))
      have hE1 : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx
      have hE2 : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
      have hsum : 0 < expNegInvGlue x + expNegInvGlue (1 - x) := by positivity
      exact div_pos hE1 hsum

theorem differentiableAt_modelRoundedFunction {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (y : MorseModel n) :
    DifferentiableAt ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y := by
  have hA : DifferentiableAt ℝ (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) y :=
    ((contDiff_modelAttachedFunction hk c ε r δ).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hN : DifferentiableAt ℝ (fun y : MorseModel n => morseNormalForm hk c y - c) y :=
    ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt).sub
      (differentiableAt_const c)
  have hmid : DifferentiableAt ℝ ((fun y : MorseModel n => morseNormalForm hk c y - c) +
      (fun _ : MorseModel n => ε) - (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c)) y :=
    (hN.add (differentiableAt_const ε)).sub hA
  have hτ : DifferentiableAt ℝ (fun y : MorseModel n => Real.smoothTransition
      ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) y := by
    have hcNorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
      rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
          (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) + (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) by
        funext y
        exact morseNorm_sq_split hk y]
      exact (contDiff_posPart_normSq hk).add (contDiff_negPart_normSq hk)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        (morseNorm n y ^ 2 - R₀ ^ 2) * (R₁ ^ 2 - R₀ ^ 2)⁻¹)
      exact (hcNorm.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : MorseModel n => (R₀ ^ 2 : ℝ)))).mul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : MorseModel n => ((R₁ ^ 2 - R₀ ^ 2)⁻¹ : ℝ)))
    exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hc).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdef' : modelRoundedFunction hk c ε r δ R₀ R₁ =
      (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c) +
        ((fun y : MorseModel n => morseNormalForm hk c y - c) + (fun _ : MorseModel n => ε) -
          (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y - c)) *
          (fun y : MorseModel n => Real.smoothTransition
            ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) + (fun _ : MorseModel n => c) := by
    funext z
    dsimp [modelRoundedFunction]
    ring
  rw [hdef']
  exact (hA.add (hmid.mul hτ)).add (differentiableAt_const c)

theorem modelSublevelFamily_value_split {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ s : ℝ) (y : MorseModel n)
    (hu : ‖posPart hk y‖ ^ 2 = 0) :
    modelSublevelFamily hk c ε r δ R₀ R₁ s y =
      ε * ((1 - s) * Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) - s) -
        (1 / 2 : ℝ) * ((1 - s) * (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
            smoothCap ε r δ (‖negPart hk y‖ ^ 2) +
          ((1 - s) * Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) + s) *
            ‖negPart hk y‖ ^ 2) := by
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 := by
    rw [morseNorm_sq_split hk y, hu]
    ring
  dsimp [modelSublevelFamily]
  dsimp [modelRoundedFunction, modelAttachedFunction]
  rw [morseNormalForm_split hk c y]
  rw [hu, hnorm]
  ring

theorem fderiv_modelSublevelFamily_ne_zero_of_eq_zero {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (y : MorseModel n)
    (hy : modelSublevelFamily hk c ε r δ R₀ R₁ s y = 0) :
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y ≠ 0 := by
  by_cases hs0 : s = 0
  · have hval : modelRoundedFunction hk c ε r δ R₀ R₁ y = c := by
      have : modelSublevelFamily hk c ε r δ R₀ R₁ 0 y = 0 := by simpa [hs0] using hy
      dsimp [modelSublevelFamily] at this
      nlinarith
    intro hzero
    have hz : fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y ≠ 0 :=
      fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hval
    have hfe : (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ 0 z) =
        fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c := by
      funext z
      dsimp [modelSublevelFamily]
      ring
    have hfm : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ 0 z) y =
        fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y := by
      rw [hfe]
      rw [show (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) =
          modelRoundedFunction hk c ε r δ R₀ R₁ - (fun _ : MorseModel n => c) by rfl]
      rw [fderiv_sub (f := modelRoundedFunction hk c ε r δ R₀ R₁) (g := fun _ : MorseModel n => c)
        (hf := differentiableAt_modelRoundedFunction hk c ε r δ R₀ R₁ y) (hg := differentiableAt_const c)]
      simp
    have hz0 : fderiv ℝ (modelRoundedFunction hk c ε r δ R₀ R₁) y = 0 := by
      rw [← hfm]
      simpa [hs0] using hzero
    exact hz hz0
  · have hs_pos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hden_pos : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have hlt : |R₀| < |R₁| := by
        rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
        exact hR
      have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
      nlinarith
    intro hzero
    let wp : MorseModel n := recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
    let wm : MorseModel n := recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
    let τ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
    let τSlope : ℝ := deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
      (R₁ ^ 2 - R₀ ^ 2)
    let capSlope : ℝ := deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)
    let Nval : ℝ := morseNormalForm hk c y - c
    let Aval : ℝ := modelAttachedFunction hk c ε r δ y - c
    have hτSlope_nonneg : 0 ≤ τSlope := by
      dsimp [τSlope]
      exact div_nonneg (smoothTransition_deriv_nonneg _) (le_of_lt hden_pos)
    have hτSlope_le : τSlope ≤ 40 / (R₁ ^ 2 - R₀ ^ 2) := by
      dsimp [τSlope]
      have hd : deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 40 :=
        Real.smoothTransition_deriv_le_forty _
      exact div_le_div_of_nonneg_right hd (le_of_lt hden_pos)
    have hNεA_ge : -(δ / 2) ≤ Nval + ε - Aval := by
      dsimp [Nval, Aval]
      have hcap : ‖negPart hk y‖ ^ 2 - 2 * ε - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
        smoothCap_ge_sub_two_mul_eps (ε := ε) (δ := δ) hδ
      have hmid : morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c) =
          ε + (1 / 2 : ℝ) * (smoothCap ε r δ (‖negPart hk y‖ ^ 2) - ‖negPart hk y‖ ^ 2) := by
        rw [morseNormalForm_split hk c y]
        unfold modelAttachedFunction
        ring
      rw [hmid]
      nlinarith [hcap]
    have hwp : ‖posPart hk y‖ ^ 2 *
        (1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope) = 0 := by
      have hd : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wp = 0 :=
        congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L wp) hzero
      rw [fderiv_modelSublevelFamily_direction_pos hk c ε r δ R₀ R₁ s hR hR0 y] at hd
      simpa [wp, τSlope, Nval, Aval] using hd
    have hwm : ‖negPart hk y‖ ^ 2 *
        (-((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) +
          2 * (1 - s) * (Nval + ε - Aval) * τSlope) = 0 := by
      have hd : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wm = 0 :=
        congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L wm) hzero
      rw [fderiv_modelSublevelFamily_direction_neg hk c ε r δ R₀ R₁ s hR hR0 y] at hd
      simpa [wm, τ, τSlope, capSlope, Nval, Aval] using hd
    by_cases hpp : ‖posPart hk y‖ ^ 2 = 0
    · by_cases hpm : ‖negPart hk y‖ ^ 2 = 0
      · have hy0 : modelSublevelFamily hk c ε r δ R₀ R₁ s 0 = 0 := by
          have hp : posPart hk y = 0 := by
            have hnon : 0 ≤ ‖posPart hk y‖ := by positivity
            exact norm_eq_zero.mp (sq_eq_zero_iff.mp hpp)
          have hm : negPart hk y = 0 := by
            have hnon : 0 ≤ ‖negPart hk y‖ := by positivity
            exact norm_eq_zero.mp (sq_eq_zero_iff.mp hpm)
          have hy' : y = 0 := recombine_zero_of_parts_eq_zero hk y hp hm
          simpa [hy'] using hy
        have hval0 : modelSublevelFamily hk c ε r δ R₀ R₁ s 0 = -(1 - s) * (r ^ 2 / 2) - s * ε := by
          have hρ : morseNorm n 0 ≤ R₀ := by
            simpa [morseNorm] using hR0
          have hround : modelRoundedFunction hk c ε r δ R₀ R₁ 0 = modelAttachedFunction hk c ε r δ 0 :=
            modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hρ
          have hcap0 : smoothCap ε r δ 0 = r ^ 2 := by
            rw [smoothCap_lower hδ (by nlinarith [hδr, hε] : 0 ≤ r ^ 2 + 2 * ε - δ)]
          dsimp [modelSublevelFamily]
          rw [hround]
          dsimp [modelRoundedFunction, modelAttachedFunction]
          rw [morseNormalForm_split hk c 0]
          have hp0 : posPart hk (0 : MorseModel n) = 0 := by
            ext i
            simp [posPart]
          have hn0 : negPart hk (0 : MorseModel n) = 0 := by
            ext i
            simp [negPart]
          simp [hp0, hn0, hcap0]
          ring
        have hneq : -(1 - s) * (r ^ 2 / 2) - s * ε ≠ 0 := by
          by_cases hs1 : s = 1
          · rw [hs1]
            simp
            linarith [hε]
          · have hs_lt : s < 1 := lt_of_le_of_ne hs.2 hs1
            have h1sp : 0 < 1 - s := by linarith
            have hr2 : 0 < r ^ 2 := by nlinarith [hδ, hδr]
            have hterm1 : 0 < (1 - s) * (r ^ 2 / 2) := by positivity
            have hterm2 : 0 ≤ s * ε := by positivity
            have hpos : 0 < (1 - s) * (r ^ 2 / 2) + s * ε := by linarith
            have hneg : -(1 - s) * (r ^ 2 / 2) - s * ε < 0 := by linarith
            exact ne_of_lt hneg
        exact False.elim (hneq (by
          rw [← hval0]
          exact hy0))
      · have hβ : -((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) +
            2 * (1 - s) * (Nval + ε - Aval) * τSlope = 0 := by
          exact (mul_eq_zero.mp hwm).resolve_left hpm
        have hτpos : 0 < τ := by
          have hvalue : ε * ((1 - s) * τ - s) =
              (1 / 2 : ℝ) * ((1 - s) * (1 - τ) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) +
                ((1 - s) * τ + s) * ‖negPart hk y‖ ^ 2) := by
            have hsplit := modelSublevelFamily_value_split hk c ε r δ R₀ R₁ s y hpp
            have hmain : ε * ((1 - s) * Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) - s) -
                (1 / 2 : ℝ) * ((1 - s) * (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
                    smoothCap ε r δ (‖negPart hk y‖ ^ 2) +
                  ((1 - s) * Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) + s) *
                    ‖negPart hk y‖ ^ 2) = 0 := by
              rw [← hsplit]
              exact hy
            dsimp [τ]
            linarith [hmain]
          have hrhs_nonneg : 0 ≤ (1 / 2 : ℝ) * ((1 - s) * (1 - τ) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) +
              ((1 - s) * τ + s) * ‖negPart hk y‖ ^ 2) := by
            have hcap : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
              smoothCap_pos hδ hδr
            have h1s : 0 ≤ 1 - s := by linarith [hs.2]
            have hτ01 : 0 ≤ τ ∧ τ ≤ 1 := by
              dsimp [τ]
              constructor
              · exact Real.smoothTransition.nonneg _
              · exact Real.smoothTransition.le_one _
            have hτle1 : 1 - τ ≥ 0 := by linarith only [hτ01.2]
            have hnon1 : 0 ≤ (1 - s) * (1 - τ) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by positivity
            have hτs : 0 ≤ (1 - s) * τ + s := by
              have h1 : 0 ≤ (1 - s) * τ := mul_nonneg h1s hτ01.1
              exact add_nonneg h1 hs.1
            have hnon2 : 0 ≤ ((1 - s) * τ + s) * ‖negPart hk y‖ ^ 2 := by positivity
            have hsum : 0 ≤ (1 - s) * (1 - τ) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) +
                ((1 - s) * τ + s) * ‖negPart hk y‖ ^ 2 := add_nonneg hnon1 hnon2
            exact mul_nonneg (by norm_num) hsum
          have hleq : (1 - s) * τ ≥ s := by
            have : ε * ((1 - s) * τ - s) ≥ 0 := by
              rw [hvalue]
              exact hrhs_nonneg
            nlinarith only [this, hε]
          have hτ_nonneg : 0 ≤ τ := by
            dsimp [τ]
            exact Real.smoothTransition.nonneg _
          have hprod_pos : 0 < (1 - s) * τ := by
            nlinarith only [hleq, hs_pos]
          have h1s_pos : 0 < 1 - s := by
            by_contra hnot
            have hle : 1 - s ≤ 0 := le_of_not_gt hnot
            have hprod' : (1 - s) * τ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hτ_nonneg
            nlinarith only [hprod_pos, hprod']
          have hτpos_final : 0 < τ := by
            by_contra hnot
            have hle : τ ≤ 0 := le_of_not_gt hnot
            have hτ0 : τ = 0 := le_antisymm hle hτ_nonneg
            have hzero : (1 - s) * τ = 0 := by rw [hτ0]; ring
            nlinarith only [hleq, hzero, hs_pos]
          exact hτpos_final
        have hvgt : R₀ ^ 2 < ‖negPart hk y‖ ^ 2 := by
          have harg_pos : 0 < (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
            have hτ' : 0 < Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
              simpa [τ] using hτpos
            exact (smoothTransition_pos_iff _).mp hτ'
          have hnorm_gt : R₀ ^ 2 < morseNorm n y ^ 2 := by
            have hden0 : 0 < R₁ ^ 2 - R₀ ^ 2 := hden_pos
            have : 0 < morseNorm n y ^ 2 - R₀ ^ 2 := by
              simpa using (lt_div_iff₀ hden0).mp harg_pos
            nlinarith only [this]
          rw [morseNorm_sq_split hk y, hpp, zero_add] at hnorm_gt
          exact hnorm_gt
        have hcapv : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
          have hge : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by nlinarith only [hvgt, hbig]
          exact smoothCap_upper hδ hge
        have hcapSlope1 : capSlope = 1 := by
          dsimp [capSlope]
          have hge : r ^ 2 + 2 * ε + δ < ‖negPart hk y‖ ^ 2 := by
            have : 2 * (r ^ 2 + 2 * ε + δ) < ‖negPart hk y‖ ^ 2 := by nlinarith only [hvgt, hbig]
            nlinarith only [this]
          exact deriv_smoothCap_eq_one_of_gt hδ hge
        have hNεA_zero : Nval + ε - Aval = 0 := by
          dsimp [Nval, Aval]
          rw [morseNormalForm_split hk c y]
          unfold modelAttachedFunction
          rw [hcapv]
          ring
        have hβ' : -((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) = 0 := by
          rw [hNεA_zero] at hβ
          simpa using hβ
        have hbneq : (1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s ≠ 0 := by
          rw [hcapSlope1]
          have hsum : (1 - s) * (1 - τ) + (1 - s) * τ + s = 1 := by
            ring_nf
          nlinarith only [hsum]
        exact False.elim (by
          have : -((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) = 0 := hβ'
          have hmain : (1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s = 0 := by linarith
          exact hbneq hmain)
    · have hα : 1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope = 0 := by
        exact (mul_eq_zero.mp hwp).resolve_left hpp
      have hNεA_neg : Nval + ε - Aval < 0 := by
        have hα' : 2 * (1 - s) * (Nval + ε - Aval) * τSlope = -1 := by nlinarith only [hα]
        have h1s : 0 ≤ 1 - s := by linarith only [hs.2]
        have hτnon : 0 ≤ τSlope := hτSlope_nonneg
        by_contra hnot
        have hge : 0 ≤ Nval + ε - Aval := le_of_not_gt hnot
        have hprod : 0 ≤ 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
          positivity
        nlinarith only [hα', hprod]
      have hα_lower : 0 < 1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
        have h1s : 0 ≤ 1 - s := by linarith only [hs.2]
        have hle1 : 2 * (1 - s) * (-(δ / 2)) * τSlope ≤ 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
          have hpr : 0 ≤ 2 * (1 - s) * τSlope := by
            positivity
          have hmul := mul_le_mul_of_nonneg_right hNεA_ge hpr
          nlinarith only [hmul]
        have hle2 : -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 2 * (1 - s) * (-(δ / 2)) * τSlope := by
          have hcoef : 2 * (1 - s) * (δ / 2) * τSlope ≤ 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by
            have h1sle : 1 - s ≤ 1 := by linarith only [hs.1]
            have hcoef' : 2 * (1 - s) * (δ / 2) ≤ δ := by nlinarith only [h1sle, hδ]
            have hmain : 2 * (1 - s) * (δ / 2) * τSlope ≤ δ * τSlope :=
              mul_le_mul_of_nonneg_right hcoef' hτSlope_nonneg
            have hdle : τSlope ≤ 40 / (R₁ ^ 2 - R₀ ^ 2) := hτSlope_le
            have hstep : δ * τSlope ≤ 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by
              have hmul := mul_le_mul_of_nonneg_left hdle (le_of_lt hδ)
              have heq : δ * (40 / (R₁ ^ 2 - R₀ ^ 2)) = 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by ring
              rw [← heq]
              exact hmul
            nlinarith only [hmain, hstep]
          have hneg : -(40 * δ / (R₁ ^ 2 - R₀ ^ 2)) ≤ -(2 * (1 - s) * (δ / 2) * τSlope) :=
            neg_le_neg hcoef
          have hrew : -(2 * (1 - s) * (δ / 2) * τSlope) = 2 * (1 - s) * (-(δ / 2)) * τSlope := by ring
          rw [hrew] at hneg
          exact hneg
        have hδR' : 40 * δ / (R₁ ^ 2 - R₀ ^ 2) < 1 := (div_lt_one (by positivity)).2 hδR
        have hA_le_B : -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) ≤
            2 * (1 - s) * (Nval + ε - Aval) * τSlope := le_trans hle2 hle1
        have hlb : 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) ≤
            1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
          have hrew : 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) = 1 + -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) := by ring
          rw [hrew]
          exact add_le_add (le_refl 1) hA_le_B
        have hpos1 : 0 < 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := sub_pos.mpr hδR'
        exact lt_of_lt_of_le hpos1 hlb
      exact False.elim (by
        have : 0 < 1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope := hα_lower
        rw [hα] at this
        exact (not_lt_of_ge le_rfl) this)

theorem modelSublevelFamily_notCritical_of_strip {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀le : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (y : MorseModel n)
    (hy : |modelSublevelFamily hk c ε r δ R₀ R₁ s y| ≤ 2 * ε₀) :
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y ≠ 0 := by
  intro hzero
  have hden_pos : 0 < R₁ ^ 2 - R₀ ^ 2 := by
    have hlt : |R₀| < |R₁| := by
      rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
      exact hR
    have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
    nlinarith
  let wp : MorseModel n := recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  let wm : MorseModel n := recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  let τ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
  let τSlope : ℝ := deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
    (R₁ ^ 2 - R₀ ^ 2)
  let capSlope : ℝ := deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)
  let Nval : ℝ := morseNormalForm hk c y - c
  let Aval : ℝ := modelAttachedFunction hk c ε r δ y - c
  have hτSlope_nonneg : 0 ≤ τSlope := by
    dsimp [τSlope]
    exact div_nonneg (smoothTransition_deriv_nonneg _) (le_of_lt hden_pos)
  have hτSlope_le : τSlope ≤ 40 / (R₁ ^ 2 - R₀ ^ 2) := by
    dsimp [τSlope]
    have hd : deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 40 :=
      Real.smoothTransition_deriv_le_forty _
    exact div_le_div_of_nonneg_right hd (le_of_lt hden_pos)
  have hNεA_ge : -(δ / 2) ≤ Nval + ε - Aval := by
    dsimp [Nval, Aval]
    have hcap : ‖negPart hk y‖ ^ 2 - 2 * ε - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      smoothCap_ge_sub_two_mul_eps (ε := ε) (δ := δ) hδ
    have hmid : morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c) =
        ε + (1 / 2 : ℝ) * (smoothCap ε r δ (‖negPart hk y‖ ^ 2) - ‖negPart hk y‖ ^ 2) := by
      rw [morseNormalForm_split hk c y]
      unfold modelAttachedFunction
      ring
    rw [hmid]
    nlinarith [hcap]
  have hαpos : 0 < 1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
    have h1s : 0 ≤ 1 - s := by linarith only [hs.2]
    have hle1 : 2 * (1 - s) * (-(δ / 2)) * τSlope ≤ 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
      have hpr : 0 ≤ 2 * (1 - s) * τSlope := by positivity
      have hmul := mul_le_mul_of_nonneg_right hNεA_ge hpr
      nlinarith only [hmul]
    have hle2 : -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 2 * (1 - s) * (-(δ / 2)) * τSlope := by
      have hcoef : 2 * (1 - s) * (δ / 2) * τSlope ≤ 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by
        have h1sle : 1 - s ≤ 1 := by linarith only [hs.1]
        have hcoef' : 2 * (1 - s) * (δ / 2) ≤ δ := by nlinarith only [h1sle, hδ]
        have hmain : 2 * (1 - s) * (δ / 2) * τSlope ≤ δ * τSlope :=
          mul_le_mul_of_nonneg_right hcoef' hτSlope_nonneg
        have hdle : τSlope ≤ 40 / (R₁ ^ 2 - R₀ ^ 2) := hτSlope_le
        have hstep : δ * τSlope ≤ 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by
          have hmul := mul_le_mul_of_nonneg_left hdle (le_of_lt hδ)
          have heq : δ * (40 / (R₁ ^ 2 - R₀ ^ 2)) = 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by ring
          rw [← heq]
          exact hmul
        nlinarith only [hmain, hstep]
      have hneg : -(40 * δ / (R₁ ^ 2 - R₀ ^ 2)) ≤ -(2 * (1 - s) * (δ / 2) * τSlope) :=
        neg_le_neg hcoef
      have hrew : -(2 * (1 - s) * (δ / 2) * τSlope) = 2 * (1 - s) * (-(δ / 2)) * τSlope := by ring
      rw [hrew] at hneg
      exact hneg
    have hδR' : 40 * δ / (R₁ ^ 2 - R₀ ^ 2) < 1 := (div_lt_one (by positivity)).2 hδR
    have hA_le_B : -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) ≤
        2 * (1 - s) * (Nval + ε - Aval) * τSlope := le_trans hle2 hle1
    have hlb : 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) ≤
        1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope := by
      have hrew : 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) = 1 + -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) := by ring
      rw [hrew]
      exact add_le_add (le_refl 1) hA_le_B
    have hpos1 : 0 < 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := sub_pos.mpr hδR'
    exact lt_of_lt_of_le hpos1 hlb
  have hwp : ‖posPart hk y‖ ^ 2 *
      (1 + 2 * (1 - s) * (Nval + ε - Aval) * τSlope) = 0 := by
    have hd : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wp = 0 :=
      congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L wp) hzero
    rw [fderiv_modelSublevelFamily_direction_pos hk c ε r δ R₀ R₁ s hR hR0 y] at hd
    simpa [wp, τSlope, Nval, Aval] using hd
  have hwm : ‖negPart hk y‖ ^ 2 *
      (-((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) +
        2 * (1 - s) * (Nval + ε - Aval) * τSlope) = 0 := by
    have hd : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wm = 0 :=
      congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L wm) hzero
    rw [fderiv_modelSublevelFamily_direction_neg hk c ε r δ R₀ R₁ s hR hR0 y] at hd
    simpa [wm, τ, τSlope, capSlope, Nval, Aval] using hd
  have hpp : ‖posPart hk y‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp hwp).resolve_right (ne_of_gt hαpos)
  by_cases hpm0 : ‖negPart hk y‖ ^ 2 = 0
  · have hp : posPart hk y = 0 := by
      have hnon : 0 ≤ ‖posPart hk y‖ := by positivity
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hpp)
    have hm : negPart hk y = 0 := by
      have hnon : 0 ≤ ‖negPart hk y‖ := by positivity
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hpm0)
    have hy0 : y = 0 := recombine_zero_of_parts_eq_zero hk y hp hm
    have hval0 : modelSublevelFamily hk c ε r δ R₀ R₁ s 0 = -(1 - s) * (r ^ 2 / 2) - s * ε := by
      have hρ : morseNorm n 0 ≤ R₀ := by
        simpa [morseNorm] using hR0
      have hround : modelRoundedFunction hk c ε r δ R₀ R₁ 0 = modelAttachedFunction hk c ε r δ 0 :=
        modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hρ
      have hcap0 : smoothCap ε r δ 0 = r ^ 2 := by
        rw [smoothCap_lower hδ (by nlinarith [hδr, hε] : 0 ≤ r ^ 2 + 2 * ε - δ)]
      dsimp [modelSublevelFamily]
      rw [hround]
      dsimp [modelRoundedFunction, modelAttachedFunction]
      rw [morseNormalForm_split hk c 0]
      have hp0 : posPart hk (0 : MorseModel n) = 0 := by
        ext i
        simp [posPart]
      have hn0 : negPart hk (0 : MorseModel n) = 0 := by
        ext i
        simp [negPart]
      simp [hp0, hn0, hcap0]
      ring
    have hval_neg : -(1 - s) * (r ^ 2 / 2) - s * ε < 0 := by
      have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
      have hpos : 0 < (1 - s) * (r ^ 2 / 2) + s * ε := by
        by_cases hs0 : s = 0
        · rw [hs0]
          nlinarith only [hr2]
        · have hsgt : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
          have h1 : 0 < s * ε := mul_pos hsgt hε
          have h2 : 0 ≤ (1 - s) * (r ^ 2 / 2) := by
            exact mul_nonneg (by linarith only [hs.2]) (by nlinarith only [hr2])
          linarith
      linarith
    have hval_abs : |-(1 - s) * (r ^ 2 / 2) - s * ε| = (1 - s) * (r ^ 2 / 2) + s * ε := by
      rw [abs_of_neg hval_neg]
      ring
    have hminle : min ε (r ^ 2 / 2) ≤ (1 - s) * (r ^ 2 / 2) + s * ε := by
      have h1 : min ε (r ^ 2 / 2) ≤ r ^ 2 / 2 := min_le_right _ _
      have h2 : min ε (r ^ 2 / 2) ≤ ε := min_le_left _ _
      have h3 : s * min ε (r ^ 2 / 2) ≤ s * ε := mul_le_mul_of_nonneg_left h2 hs.1
      have h4 : (1 - s) * min ε (r ^ 2 / 2) ≤ (1 - s) * (r ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h1 (by linarith only [hs.2])
      nlinarith only [h3, h4]
    have hgt : 2 * ε₀ < min ε (r ^ 2 / 2) := by
      have hle : min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2) ≤ min ε (r ^ 2 / 2) :=
        min_le_left _ _
      linarith only [hε₀le, hle]
    have hmain : 2 * ε₀ < |-(1 - s) * (r ^ 2 / 2) - s * ε| := by
      rw [hval_abs]
      exact lt_of_lt_of_le hgt hminle
    have hval : modelSublevelFamily hk c ε r δ R₀ R₁ s y = -(1 - s) * (r ^ 2 / 2) - s * ε := by
      simpa [hy0] using hval0
    have hmain' : 2 * ε₀ < |modelSublevelFamily hk c ε r δ R₀ R₁ s y| := by
      rw [hval]
      exact hmain
    exact (not_lt_of_ge hy) hmain'
  · have hβ : -((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) +
        2 * (1 - s) * (Nval + ε - Aval) * τSlope = 0 := by
      exact (mul_eq_zero.mp hwm).resolve_left hpm0
    by_cases hcore : ‖negPart hk y‖ ^ 2 < R₀ ^ 2
    · have hτ0 : τ = 0 := by
        dsimp [τ]
        apply Real.smoothTransition.zero_of_nonpos
        have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 := by
          rw [morseNorm_sq_eq_negPart_add_posPart hk y, hpp, add_zero]
        have harg : (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) ≤ 0 := by
          exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcore, hnorm])
            (le_of_lt hden_pos)
        exact harg
      have hsplit := modelSublevelFamily_value_split hk c ε r δ R₀ R₁ s y hpp
      have hcap : r ^ 2 - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_ge_sub hδ
      have hle : modelSublevelFamily hk c ε r δ R₀ R₁ s y ≤ -min ε ((r ^ 2 - δ) / 2) := by
        have hmain : modelSublevelFamily hk c ε r δ R₀ R₁ s y ≤
            -s * ε - (1 - s) * (r ^ 2 - δ) / 2 := by
          have hsplit' : modelSublevelFamily hk c ε r δ R₀ R₁ s y =
              ε * ((1 - s) * τ - s) -
                (1 / 2 : ℝ) * ((1 - s) * (1 - τ) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) +
                  ((1 - s) * τ + s) * ‖negPart hk y‖ ^ 2) := hsplit
          rw [hsplit', hτ0]
          have h1s : 0 ≤ 1 - s := by linarith only [hs.2]
          have hdiff : 0 ≤ (1 - s) * (smoothCap ε r δ (‖negPart hk y‖ ^ 2) - (r ^ 2 - δ)) := by
            have hcap' : 0 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) - (r ^ 2 - δ) := by
              linarith only [hcap]
            exact mul_nonneg h1s hcap'
          have hst : 0 ≤ s * ‖negPart hk y‖ ^ 2 := mul_nonneg hs.1 (sq_nonneg _)
          nlinarith only [hdiff, hst]
        have hconv : min ε ((r ^ 2 - δ) / 2) ≤ s * ε + (1 - s) * ((r ^ 2 - δ) / 2) := by
          have h1 : min ε ((r ^ 2 - δ) / 2) ≤ (r ^ 2 - δ) / 2 := min_le_right _ _
          have h2 : min ε ((r ^ 2 - δ) / 2) ≤ ε := min_le_left _ _
          have h3 : s * min ε ((r ^ 2 - δ) / 2) ≤ s * ε := mul_le_mul_of_nonneg_left h2 hs.1
          have h4 : (1 - s) * min ε ((r ^ 2 - δ) / 2) ≤ (1 - s) * ((r ^ 2 - δ) / 2) :=
            mul_le_mul_of_nonneg_left h1 (by linarith only [hs.2])
          nlinarith only [h3, h4]
        have hneg : -(s * ε + (1 - s) * ((r ^ 2 - δ) / 2)) ≤ -min ε ((r ^ 2 - δ) / 2) :=
          neg_le_neg hconv
        have hrew : -s * ε - (1 - s) * (r ^ 2 - δ) / 2 = -(s * ε + (1 - s) * ((r ^ 2 - δ) / 2)) := by
          ring
        rw [hrew] at hmain
        exact le_trans hmain hneg
      have hgt : 2 * ε₀ < min ε ((r ^ 2 - δ) / 2) := by
        have hle : min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2) ≤ min ε ((r ^ 2 - δ) / 2) := by
          exact le_min (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
        linarith only [hε₀le, hle]
      have hlt : modelSublevelFamily hk c ε r δ R₀ R₁ s y < -(2 * ε₀) :=
        lt_of_le_of_lt hle (by linarith only [hgt])
      have hhy : -(2 * ε₀) ≤ modelSublevelFamily hk c ε r δ R₀ R₁ s y := (abs_le.mp hy).1
      exact (not_lt_of_ge hhy) hlt
    · have hcore' : R₀ ^ 2 ≤ ‖negPart hk y‖ ^ 2 := le_of_not_gt hcore
      have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
        apply smoothCap_upper hδ
        have hge : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
          have hle2 : r ^ 2 + 2 * ε + δ ≤ R₀ ^ 2 / 2 := by nlinarith only [hbig]
          have hR₀pos : 0 < R₀ ^ 2 := by
            have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
            nlinarith only [hbig, hε, hr2, hδ]
          nlinarith only [hle2, hR₀pos, hcore']
        exact hge
      have hcapSlope1 : capSlope = 1 := by
        dsimp [capSlope]
        apply deriv_smoothCap_eq_one_of_gt hδ
        have hge : r ^ 2 + 2 * ε + δ < ‖negPart hk y‖ ^ 2 := by
          have hle2 : r ^ 2 + 2 * ε + δ ≤ R₀ ^ 2 / 2 := by nlinarith only [hbig]
          have hR₀pos : 0 < R₀ ^ 2 := by
            have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
            nlinarith only [hbig, hε, hr2, hδ]
          have hhalf : R₀ ^ 2 / 2 < R₀ ^ 2 := by nlinarith only [hR₀pos]
          nlinarith only [hle2, hhalf, hcore']
        exact hge
      have hNεA_zero : Nval + ε - Aval = 0 := by
        dsimp [Nval, Aval]
        rw [morseNormalForm_split hk c y]
        unfold modelAttachedFunction
        rw [hcap]
        ring
      have hβ' : -((1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s) = 0 := by
        rw [hNεA_zero] at hβ
        simpa using hβ
      have hbneq : (1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s ≠ 0 := by
        rw [hcapSlope1]
        have hsum : (1 - s) * (1 - τ) + (1 - s) * τ + s = 1 := by ring
        nlinarith only [hsum]
      exact False.elim (by
        have hmain : (1 - s) * (1 - τ) * capSlope + (1 - s) * τ + s = 0 := by linarith
        exact hbneq hmain)

noncomputable def modelSublevelCutoffRatio {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ : ℝ) (y : MorseModel n) : ℝ :=
  (modelRoundedFunction hk c ε r δ R₀ R₁ y - c + ε₀) /
    (modelRoundedFunction hk c ε r δ R₀ R₁ y - c - (morseNormalForm hk c y - c - ε))

noncomputable def modelSublevelFamilyCutoff {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ : ℝ) (θ : ℝ → ℝ) (s : ℝ) (y : MorseModel n) : ℝ :=
  let γ : ℝ := modelRoundedFunction hk c ε r δ R₀ R₁ y - c
  let β : ℝ := morseNormalForm hk c y - c - ε
  let ρ : ℝ := modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y
  (1 - s * θ ρ) * γ + s * θ ρ * β

theorem modelSublevelFamilyCutoff_affine {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ a : ℝ) (θ : ℝ → ℝ) (s : ℝ) (y : MorseModel n)
    (hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
      (morseNormalForm hk c y - c - ε) ≠ 0)
    (hθ : θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) =
      a * modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) :
    modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s y =
      (1 - s * a) * (modelRoundedFunction hk c ε r δ R₀ R₁ y - c) - s * a * ε₀ := by
  dsimp [modelSublevelFamilyCutoff]
  let γ : ℝ := modelRoundedFunction hk c ε r δ R₀ R₁ y - c
  let β : ℝ := morseNormalForm hk c y - c - ε
  let ρ : ℝ := modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y
  have hρ : (γ - β) * modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y = γ + ε₀ := by
    dsimp [modelSublevelCutoffRatio, γ, β]
    field_simp [hden]
  have hmain : (1 - s * θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y)) * γ +
      s * θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) * β =
      (1 - s * a) * γ - s * a * ε₀ := by
    rw [hθ]
    have hring : (1 - s * (a * ρ)) * γ + s * (a * ρ) * β =
        (1 - s * a) * γ - s * a * ((γ - β) * ρ - γ) := by ring
    rw [hring]
    rw [hρ]
    ring
  simpa [γ, β, ρ] using hmain

theorem differentiableAt_modelSublevelFamily {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ s : ℝ) (y : MorseModel n) :
    DifferentiableAt ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y := by
  have h1 : DifferentiableAt ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y :=
    (differentiableAt_modelRoundedFunction hk c ε r δ R₀ R₁ y).sub (differentiableAt_const c)
  have h2 : DifferentiableAt ℝ (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y :=
    ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt.sub
      (differentiableAt_const c)).sub (differentiableAt_const ε)
  dsimp [modelSublevelFamily]
  exact (h1.const_mul (1 - s)).add (h2.const_mul s)

theorem fderiv_modelRoundedFunction_direction_pos_value {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n) :
    fderiv ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      ‖posPart hk y‖ ^ 2 *
        (1 + 2 * (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
          (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
            (R₁ ^ 2 - R₀ ^ 2))) := by
  have hfun : (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ 0 z) =
      fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c := by
    funext z
    dsimp [modelSublevelFamily]
    ring
  have hd := fderiv_modelSublevelFamily_direction_pos hk c ε r δ R₀ R₁ (0 : ℝ) hR hR0 y
  rw [← hfun]
  simpa using hd

theorem fderiv_modelRoundedFunction_direction_neg_value {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n) :
    fderiv ℝ (fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      ‖negPart hk y‖ ^ 2 *
        (-((1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
              deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) +
            Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) +
          2 * (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) := by
  have hfun : (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ 0 z) =
      fun z : MorseModel n => modelRoundedFunction hk c ε r δ R₀ R₁ z - c := by
    funext z
    dsimp [modelSublevelFamily]
    ring
  have hd := fderiv_modelSublevelFamily_direction_neg hk c ε r δ R₀ R₁ (0 : ℝ) hR hR0 y
  rw [← hfun]
  simpa using hd

theorem fderiv_modelSublevelFamilyCutoff_direction_pos {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (θ : ℝ → ℝ) (s : ℝ)
    (y : MorseModel n)
    (hθ : DifferentiableAt ℝ θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y))
    (hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
      (morseNormalForm hk c y - c - ε) ≠ 0) :
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      ‖posPart hk y‖ ^ 2 *
        ((1 - s * θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) -
            s * deriv θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) *
              (1 - modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y)) *
            (1 + 2 * (morseNormalForm hk c y - c + ε -
              (modelAttachedFunction hk c ε r δ y - c)) *
                (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
                  (R₁ ^ 2 - R₀ ^ 2))) +
          s * (θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) -
            modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y *
              deriv θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y))) := by
  let γ : MorseModel n → ℝ := fun z => modelRoundedFunction hk c ε r δ R₀ R₁ z - c
  let β : MorseModel n → ℝ := fun z => morseNormalForm hk c z - c - ε
  let ρ : MorseModel n → ℝ := fun z => modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z
  let wp : MorseModel n := recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  let G : ℝ := morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)
  let τSlope : ℝ := deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
    (R₁ ^ 2 - R₀ ^ 2)
  let q : ℝ := 1 + 2 * G * τSlope
  have hγ : DifferentiableAt ℝ γ y := by
    dsimp [γ]
    exact (differentiableAt_modelRoundedFunction hk c ε r δ R₀ R₁ y).sub (differentiableAt_const c)
  have hβ : DifferentiableAt ℝ β y := by
    dsimp [β]
    exact ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt.sub
      (differentiableAt_const c)).sub (differentiableAt_const ε)
  have hρ : DifferentiableAt ℝ ρ y := by
    dsimp [ρ, modelSublevelCutoffRatio]
    have hden' : γ y - β y ≠ 0 := by
      dsimp [γ, β]
      exact hden
    change DifferentiableAt ℝ (fun z : MorseModel n => (γ z + ε₀) * (γ z - β z)⁻¹) y
    exact (hγ.add (differentiableAt_const ε₀)).mul ((hγ.sub hβ).inv hden')
  have hθρ : DifferentiableAt ℝ (fun z => θ (ρ z)) y := hθ.comp y hρ
  have hsplit : (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) =
      (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) +
        (fun z : MorseModel n => s * (θ (ρ z) - 1) * (β z - γ z)) := by
    funext z
    dsimp [modelSublevelFamilyCutoff, modelSublevelFamily, ρ, β, γ]
    ring
  have hdγ : fderiv ℝ γ y wp = ‖posPart hk y‖ ^ 2 * q := by
    dsimp [γ, wp, q, G, τSlope]
    exact fderiv_modelRoundedFunction_direction_pos_value hk c ε r δ R₀ R₁ hR hR0 y
  have hdβ : fderiv ℝ β y wp = ‖posPart hk y‖ ^ 2 := by
    dsimp [β, wp]
    have hfuneq : (fun z : MorseModel n => morseNormalForm hk c z - c - ε) =
        (fun z : MorseModel n => morseNormalForm hk c z) - (fun _ : MorseModel n => c + ε) := by
      funext z
      change morseNormalForm hk c z - c - ε = morseNormalForm hk c z - (c + ε)
      ring
    rw [hfuneq]
    rw [fderiv_sub (f := fun z : MorseModel n => morseNormalForm hk c z)
      (g := fun _ : MorseModel n => c + ε)
      (hf := (contDiff_morseNormalForm hk c).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
      (hg := differentiableAt_const (c + ε))]
    simp [fderiv_morseNormalForm_direction_pos hk c y]
  have hdγβ : fderiv ℝ (fun z => β z - γ z) y wp = ‖posPart hk y‖ ^ 2 * (1 - q) := by
    rw [show (fun z : MorseModel n => β z - γ z) = β - γ by rfl]
    rw [fderiv_sub (f := β) (g := γ) (hf := hβ) (hg := hγ)]
    simp [ContinuousLinearMap.sub_apply, hdβ, hdγ]
    ring
  have hdρ : fderiv ℝ ρ y wp = ‖posPart hk y‖ ^ 2 * ((1 - ρ y) * q + ρ y) / (γ y - β y) := by
    have hγβ : γ y - β y ≠ 0 := by
      dsimp [γ, β]
      exact hden
    have hγβdiff : DifferentiableAt ℝ (fun z => γ z - β z) y := hγ.sub hβ
    have hγβinv : DifferentiableAt ℝ (fun z => (γ z - β z)⁻¹) y := hγβdiff.inv hγβ
    have hγβinv_val : fderiv ℝ (fun z => (γ z - β z)⁻¹) y wp =
        -(γ y - β y)⁻¹ ^ 2 * (fderiv ℝ (fun z => γ z - β z) y wp) := by
      have hinv := hasFDerivAt_inv (𝕜 := ℝ) hγβ
      have hcomp :=
        HasFDerivAt.comp (g := fun x : ℝ => x⁻¹) (hg := hinv) (f := fun z => γ z - β z)
          (hf := hγβdiff.hasFDerivAt)
      have hcompf : fderiv ℝ (fun z => (γ z - β z)⁻¹) y =
          (ContinuousLinearMap.toSpanSingleton ℝ (-((γ y - β y) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
            (fderiv ℝ (fun z => γ z - β z) y) := by
        simpa using hcomp.fderiv
      calc
        fderiv ℝ (fun z => (γ z - β z)⁻¹) y wp
            = ((ContinuousLinearMap.toSpanSingleton ℝ (-((γ y - β y) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
                (fderiv ℝ (fun z => γ z - β z) y)) wp := by rw [hcompf]
        _ = -(γ y - β y)⁻¹ ^ 2 * (fderiv ℝ (fun z => γ z - β z) y wp) := by
              simp [ContinuousLinearMap.comp_apply]
              field_simp
    have hnum : fderiv ℝ (fun z => γ z + ε₀) y wp = ‖posPart hk y‖ ^ 2 * q := by
      rw [show (fun z : MorseModel n => γ z + ε₀) = γ + (fun _ : MorseModel n => ε₀) by rfl]
      rw [fderiv_add (f := γ) (g := fun _ : MorseModel n => ε₀) (hf := hγ)
        (hg := differentiableAt_const ε₀)]
      simp [hdγ]
    have hdenf : fderiv ℝ (fun z => γ z - β z) y wp = ‖posPart hk y‖ ^ 2 * (q - 1) := by
      rw [show (fun z : MorseModel n => γ z - β z) = γ - β by rfl]
      rw [fderiv_sub (f := γ) (g := β) (hf := hγ) (hg := hβ)]
      simp [ContinuousLinearMap.sub_apply, hdγ, hdβ]
      ring
    have hρdef : (fun z : MorseModel n => ρ z) = fun z => (γ z + ε₀) * (γ z - β z)⁻¹ := by
      funext z
      dsimp [ρ]
      rfl
    have hmain : fderiv ℝ ρ y wp =
        ‖posPart hk y‖ ^ 2 * q * (γ y - β y)⁻¹ +
          (γ y + ε₀) * (-(γ y - β y)⁻¹ ^ 2 * (‖posPart hk y‖ ^ 2 * (q - 1))) := by
      rw [show fderiv ℝ ρ y = fderiv ℝ (fun z : MorseModel n => ρ z) y by rfl]
      rw [hρdef]
      have hprod : (fun z : MorseModel n => (γ z + ε₀) * (γ z - β z)⁻¹) =
          (fun z : MorseModel n => γ z + ε₀) * (fun z : MorseModel n => (γ z - β z)⁻¹) := by
        rfl
      rw [hprod]
      have hγp : DifferentiableAt ℝ (fun z => γ z + ε₀) y := hγ.add (differentiableAt_const ε₀)
      have hmul := fderiv_mul (x := y) (c := fun z => γ z + ε₀)
        (d := fun z => (γ z - β z)⁻¹) (hc := hγp) (hd := hγβinv)
      rw [hmul]
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
      rw [hγβinv_val, hnum, hdenf]
      simp [smul_eq_mul]
      field_simp [hγβ]
      ring
    have hρval : ρ y = (γ y + ε₀) / (γ y - β y) := rfl
    dsimp [ρ] at hρval
    have hlin : (γ y + ε₀) = ρ y * (γ y - β y) := by
      dsimp [ρ]
      rw [hρval]
      field_simp [hγβ]
    have hlin1 : 1 - ρ y = (γ y - β y - (γ y + ε₀)) / (γ y - β y) := by
      rw [hlin]
      field_simp [hγβ]
    have hfinal : ‖posPart hk y‖ ^ 2 * q * (γ y - β y)⁻¹ +
          (γ y + ε₀) * (-(γ y - β y)⁻¹ ^ 2 * (‖posPart hk y‖ ^ 2 * (q - 1))) =
        ‖posPart hk y‖ ^ 2 * ((1 - ρ y) * q + ρ y) / (γ y - β y) := by
      rw [hlin]
      field_simp [hγβ]
      ring
    rw [hmain, hfinal]
  have hdθρ : fderiv ℝ (fun z => θ (ρ z)) y wp =
      deriv θ (ρ y) * (‖posPart hk y‖ ^ 2 * ((1 - ρ y) * q + ρ y) / (γ y - β y)) := by
    have hchain : fderiv ℝ (fun z => θ (ρ z)) y =
        (fderiv ℝ θ (ρ y)).comp (fderiv ℝ ρ y) := by
      have hcomp :=
        HasFDerivAt.comp (g := θ) (hg := hθ.hasFDerivAt) (f := ρ) (hf := hρ.hasFDerivAt)
      exact hcomp.fderiv
    have hθapp : ∀ u : ℝ, (fderiv ℝ θ (ρ y)) u = deriv θ (ρ y) * u := by
      intro u
      have h1 : (fderiv ℝ θ (ρ y)) 1 = deriv θ (ρ y) := by
        simp [fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := θ) (x := ρ y)]
      have hlin : (fderiv ℝ θ (ρ y)) u = u • (fderiv ℝ θ (ρ y)) 1 := by
        calc
          (fderiv ℝ θ (ρ y)) u = (fderiv ℝ θ (ρ y)) (u • (1 : ℝ)) := by
            congr 1
            simp
          _ = u • (fderiv ℝ θ (ρ y)) 1 := map_smul _ _ _
      rw [hlin, h1]
      rw [smul_eq_mul]
      ring
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hθapp, hdρ]
  have hcorr : fderiv ℝ (fun z => s * (θ (ρ z) - 1) * (β z - γ z)) y wp =
      s * ‖posPart hk y‖ ^ 2 *
        ((θ (ρ y) - 1) * (1 - q) - deriv θ (ρ y) * ((1 - ρ y) * q + ρ y)) := by
    have hprod1 : DifferentiableAt ℝ (fun z => θ (ρ z) - 1) y := hθρ.sub (differentiableAt_const 1)
    have hprod2 : DifferentiableAt ℝ (fun z => β z - γ z) y := hβ.sub hγ
    have hmain : fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y wp =
        (θ (ρ y) - 1) * fderiv ℝ (fun z => β z - γ z) y wp +
          (β y - γ y) * fderiv ℝ (fun z => θ (ρ z)) y wp := by
      have hmul := fderiv_mul (x := y) (c := fun z => θ (ρ z) - 1)
        (d := fun z => β z - γ z) (hc := hprod1) (hd := hprod2)
      have hθρ1 : fderiv ℝ (fun z => θ (ρ z) - 1) y = fderiv ℝ (fun z => θ (ρ z)) y := by
        rw [show (fun z : MorseModel n => θ (ρ z) - 1) =
            (fun z : MorseModel n => θ (ρ z)) - (fun _ : MorseModel n => 1) by rfl]
        rw [fderiv_sub (f := fun z => θ (ρ z)) (g := fun _ : MorseModel n => 1)
          (hf := hθρ) (hg := differentiableAt_const 1)]
        simp
      have hmain' : fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y =
          (θ (ρ y) - 1) • fderiv ℝ (fun z => β z - γ z) y +
            (β y - γ y) • fderiv ℝ (fun z => θ (ρ z)) y := by
        rw [show (fun z : MorseModel n => (θ (ρ z) - 1) * (β z - γ z)) =
            (fun z : MorseModel n => θ (ρ z) - 1) * (fun z : MorseModel n => β z - γ z) by rfl]
        rw [hmul, hθρ1]
      rw [hmain']
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    have hval : (β y - γ y) * fderiv ℝ (fun z => θ (ρ z)) y wp =
        ‖posPart hk y‖ ^ 2 * (-(1 - ρ y) * q - ρ y) * deriv θ (ρ y) := by
      have hβγ : β y - γ y = -(γ y - β y) := by ring
      rw [hβγ, hdθρ]
      have hγβ : γ y - β y ≠ 0 := by
        dsimp [γ, β]
        exact hden
      field_simp [hγβ]
      ring
    have hmain' : fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y wp =
        ‖posPart hk y‖ ^ 2 *
          ((θ (ρ y) - 1) * (1 - q) - deriv θ (ρ y) * ((1 - ρ y) * q + ρ y)) := by
      rw [hmain, hdγβ, hval]
      ring
    have hsmul : fderiv ℝ (fun z => s * (θ (ρ z) - 1) * (β z - γ z)) y wp =
        s * fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y wp := by
      have hd : DifferentiableAt ℝ (fun z => s * ((θ (ρ z) - 1) * (β z - γ z))) y :=
        (differentiableAt_const s).mul (hprod1.mul hprod2)
      rw [show (fun z : MorseModel n => s * (θ (ρ z) - 1) * (β z - γ z)) =
          (fun z : MorseModel n => s * ((θ (ρ z) - 1) * (β z - γ z))) by
        funext z
        ring]
      rw [fderiv_const_mul (a := fun z : MorseModel n => (θ (ρ z) - 1) * (β z - γ z))
        (b := s) (ha := hprod1.mul hprod2)]
      simp [ContinuousLinearMap.smul_apply]
    rw [hsmul, hmain']
    ring
  have hnaive : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wp =
      ‖posPart hk y‖ ^ 2 * (1 + 2 * (1 - s) * G * τSlope) := by
    have hd := fderiv_modelSublevelFamily_direction_pos hk c ε r δ R₀ R₁ s hR hR0 y
    dsimp [wp, G, τSlope] at hd ⊢
    simpa using hd
  have htotal : fderiv ℝ (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) y wp =
      ‖posPart hk y‖ ^ 2 *
        ((1 + 2 * (1 - s) * G * τSlope) +
          s * ((θ (ρ y) - 1) * (1 - q) - deriv θ (ρ y) * ((1 - ρ y) * q + ρ y))) := by
    rw [hsplit]
    rw [fderiv_add (f := fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z)
      (g := fun z : MorseModel n => s * (θ (ρ z) - 1) * (β z - γ z))
      (hf := differentiableAt_modelSublevelFamily hk c ε r δ R₀ R₁ s y)
      (hg := ((differentiableAt_const s).mul (hθρ.sub (differentiableAt_const 1))).mul (hβ.sub hγ))]
    simp [ContinuousLinearMap.add_apply, hnaive, hcorr]
    ring
  have hgoal : (1 + 2 * (1 - s) * G * τSlope) +
        s * ((θ (ρ y) - 1) * (1 - q) - deriv θ (ρ y) * ((1 - ρ y) * q + ρ y)) =
      (1 - s * θ (ρ y) - s * deriv θ (ρ y) * (1 - ρ y)) * q +
        s * (θ (ρ y) - ρ y * deriv θ (ρ y)) := by
    dsimp [q]
    ring
  rw [htotal]
  dsimp [wp, ρ, γ, β, G, τSlope, q]
  rw [hgoal]

theorem fderiv_modelSublevelFamilyCutoff_direction_neg {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (θ : ℝ → ℝ) (s : ℝ)
    (y : MorseModel n)
    (hθ : DifferentiableAt ℝ θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y))
    (hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
      (morseNormalForm hk c y - c - ε) ≠ 0) :
    fderiv ℝ (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      ‖negPart hk y‖ ^ 2 *
        ((1 - s * θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) -
            s * deriv θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) *
              (1 - modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y)) *
            (-((1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
                  deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) +
                Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) +
              2 * (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
                (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
                  (R₁ ^ 2 - R₀ ^ 2))) -
          s * (θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y) -
            modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y *
              deriv θ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y))) := by
  let γ : MorseModel n → ℝ := fun z => modelRoundedFunction hk c ε r δ R₀ R₁ z - c
  let β : MorseModel n → ℝ := fun z => morseNormalForm hk c z - c - ε
  let ρ : MorseModel n → ℝ := fun z => modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z
  let wm : MorseModel n := recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  let G : ℝ := morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)
  let τ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
  let capSlope : ℝ := deriv (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)
  let τSlope : ℝ := deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
    (R₁ ^ 2 - R₀ ^ 2)
  let p : ℝ := -((1 - τ) * capSlope + τ) + 2 * G * τSlope
  have hγ : DifferentiableAt ℝ γ y := by
    dsimp [γ]
    exact (differentiableAt_modelRoundedFunction hk c ε r δ R₀ R₁ y).sub (differentiableAt_const c)
  have hβ : DifferentiableAt ℝ β y := by
    dsimp [β]
    exact ((contDiff_morseNormalForm hk c).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt.sub
      (differentiableAt_const c)).sub (differentiableAt_const ε)
  have hρ : DifferentiableAt ℝ ρ y := by
    dsimp [ρ, modelSublevelCutoffRatio]
    have hden' : γ y - β y ≠ 0 := by
      dsimp [γ, β]
      exact hden
    change DifferentiableAt ℝ (fun z : MorseModel n => (γ z + ε₀) * (γ z - β z)⁻¹) y
    exact (hγ.add (differentiableAt_const ε₀)).mul ((hγ.sub hβ).inv hden')
  have hθρ : DifferentiableAt ℝ (fun z => θ (ρ z)) y := hθ.comp y hρ
  have hsplit : (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) =
      (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) +
        (fun z : MorseModel n => s * (θ (ρ z) - 1) * (β z - γ z)) := by
    funext z
    dsimp [modelSublevelFamilyCutoff, modelSublevelFamily, ρ, β, γ]
    ring
  have hdγ : fderiv ℝ γ y wm = ‖negPart hk y‖ ^ 2 * p := by
    dsimp [γ, wm, p, G, τ, capSlope, τSlope]
    exact fderiv_modelRoundedFunction_direction_neg_value hk c ε r δ R₀ R₁ hR hR0 y
  have hdβ : fderiv ℝ β y wm = -‖negPart hk y‖ ^ 2 := by
    dsimp [β, wm]
    have hfuneq : (fun z : MorseModel n => morseNormalForm hk c z - c - ε) =
        (fun z : MorseModel n => morseNormalForm hk c z) - (fun _ : MorseModel n => c + ε) := by
      funext z
      change morseNormalForm hk c z - c - ε = morseNormalForm hk c z - (c + ε)
      ring
    rw [hfuneq]
    rw [fderiv_sub (f := fun z : MorseModel n => morseNormalForm hk c z)
      (g := fun _ : MorseModel n => c + ε)
      (hf := (contDiff_morseNormalForm hk c).differentiable (by
        exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt)
      (hg := differentiableAt_const (c + ε))]
    simp [fderiv_morseNormalForm_direction_neg hk c y]
  have hdγβ : fderiv ℝ (fun z => β z - γ z) y wm = ‖negPart hk y‖ ^ 2 * (-1 - p) := by
    rw [show (fun z : MorseModel n => β z - γ z) = β - γ by rfl]
    rw [fderiv_sub (f := β) (g := γ) (hf := hβ) (hg := hγ)]
    simp [ContinuousLinearMap.sub_apply, hdβ, hdγ]
    ring
  have hdρ : fderiv ℝ ρ y wm = ‖negPart hk y‖ ^ 2 * ((1 - ρ y) * p - ρ y) / (γ y - β y) := by
    have hγβ : γ y - β y ≠ 0 := by
      dsimp [γ, β]
      exact hden
    have hγβdiff : DifferentiableAt ℝ (fun z => γ z - β z) y := hγ.sub hβ
    have hγβinv : DifferentiableAt ℝ (fun z => (γ z - β z)⁻¹) y := hγβdiff.inv hγβ
    have hγβinv_val : fderiv ℝ (fun z => (γ z - β z)⁻¹) y wm =
        -(γ y - β y)⁻¹ ^ 2 * (fderiv ℝ (fun z => γ z - β z) y wm) := by
      have hinv := hasFDerivAt_inv (𝕜 := ℝ) hγβ
      have hcomp :=
        HasFDerivAt.comp (g := fun x : ℝ => x⁻¹) (hg := hinv) (f := fun z => γ z - β z)
          (hf := hγβdiff.hasFDerivAt)
      have hcompf : fderiv ℝ (fun z => (γ z - β z)⁻¹) y =
          (ContinuousLinearMap.toSpanSingleton ℝ (-((γ y - β y) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
            (fderiv ℝ (fun z => γ z - β z) y) := by
        simpa using hcomp.fderiv
      calc
        fderiv ℝ (fun z => (γ z - β z)⁻¹) y wm
            = ((ContinuousLinearMap.toSpanSingleton ℝ (-((γ y - β y) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
                (fderiv ℝ (fun z => γ z - β z) y)) wm := by rw [hcompf]
        _ = -(γ y - β y)⁻¹ ^ 2 * (fderiv ℝ (fun z => γ z - β z) y wm) := by
              simp [ContinuousLinearMap.comp_apply]
              field_simp
    have hnum : fderiv ℝ (fun z => γ z + ε₀) y wm = ‖negPart hk y‖ ^ 2 * p := by
      rw [show (fun z : MorseModel n => γ z + ε₀) = γ + (fun _ : MorseModel n => ε₀) by rfl]
      rw [fderiv_add (f := γ) (g := fun _ : MorseModel n => ε₀) (hf := hγ)
        (hg := differentiableAt_const ε₀)]
      simp [hdγ]
    have hdenf : fderiv ℝ (fun z => γ z - β z) y wm = ‖negPart hk y‖ ^ 2 * (p + 1) := by
      rw [show (fun z : MorseModel n => γ z - β z) = γ - β by rfl]
      rw [fderiv_sub (f := γ) (g := β) (hf := hγ) (hg := hβ)]
      simp [ContinuousLinearMap.sub_apply, hdγ, hdβ]
      ring
    have hρdef : (fun z : MorseModel n => ρ z) = fun z => (γ z + ε₀) * (γ z - β z)⁻¹ := by
      funext z
      dsimp [ρ]
      rfl
    have hmain : fderiv ℝ ρ y wm =
        ‖negPart hk y‖ ^ 2 * p * (γ y - β y)⁻¹ +
          (γ y + ε₀) * (-(γ y - β y)⁻¹ ^ 2 * (‖negPart hk y‖ ^ 2 * (p + 1))) := by
      rw [show fderiv ℝ ρ y = fderiv ℝ (fun z : MorseModel n => ρ z) y by rfl]
      rw [hρdef]
      have hprod : (fun z : MorseModel n => (γ z + ε₀) * (γ z - β z)⁻¹) =
          (fun z : MorseModel n => γ z + ε₀) * (fun z : MorseModel n => (γ z - β z)⁻¹) := by
        rfl
      rw [hprod]
      have hγp : DifferentiableAt ℝ (fun z => γ z + ε₀) y := hγ.add (differentiableAt_const ε₀)
      have hmul := fderiv_mul (x := y) (c := fun z => γ z + ε₀)
        (d := fun z => (γ z - β z)⁻¹) (hc := hγp) (hd := hγβinv)
      rw [hmul]
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
      rw [hγβinv_val, hnum, hdenf]
      simp [smul_eq_mul]
      field_simp [hγβ]
      ring
    have hρval : ρ y = (γ y + ε₀) / (γ y - β y) := rfl
    dsimp [ρ] at hρval
    have hlin : (γ y + ε₀) = ρ y * (γ y - β y) := by
      dsimp [ρ]
      rw [hρval]
      field_simp [hγβ]
    have hfinal : ‖negPart hk y‖ ^ 2 * p * (γ y - β y)⁻¹ +
          (γ y + ε₀) * (-(γ y - β y)⁻¹ ^ 2 * (‖negPart hk y‖ ^ 2 * (p + 1))) =
        ‖negPart hk y‖ ^ 2 * ((1 - ρ y) * p - ρ y) / (γ y - β y) := by
      rw [hlin]
      field_simp [hγβ]
      ring
    rw [hmain, hfinal]
  have hdθρ : fderiv ℝ (fun z => θ (ρ z)) y wm =
      deriv θ (ρ y) * (‖negPart hk y‖ ^ 2 * ((1 - ρ y) * p - ρ y) / (γ y - β y)) := by
    have hchain : fderiv ℝ (fun z => θ (ρ z)) y =
        (fderiv ℝ θ (ρ y)).comp (fderiv ℝ ρ y) := by
      have hcomp :=
        HasFDerivAt.comp (g := θ) (hg := hθ.hasFDerivAt) (f := ρ) (hf := hρ.hasFDerivAt)
      exact hcomp.fderiv
    have hθapp : ∀ u : ℝ, (fderiv ℝ θ (ρ y)) u = deriv θ (ρ y) * u := by
      intro u
      have h1 : (fderiv ℝ θ (ρ y)) 1 = deriv θ (ρ y) := by
        simp [fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := θ) (x := ρ y)]
      have hlin : (fderiv ℝ θ (ρ y)) u = u • (fderiv ℝ θ (ρ y)) 1 := by
        calc
          (fderiv ℝ θ (ρ y)) u = (fderiv ℝ θ (ρ y)) (u • (1 : ℝ)) := by
            congr 1
            simp
          _ = u • (fderiv ℝ θ (ρ y)) 1 := map_smul _ _ _
      rw [hlin, h1]
      rw [smul_eq_mul]
      ring
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hθapp, hdρ]
  have hcorr : fderiv ℝ (fun z => s * (θ (ρ z) - 1) * (β z - γ z)) y wm =
      s * ‖negPart hk y‖ ^ 2 *
        ((θ (ρ y) - 1) * (-1 - p) - deriv θ (ρ y) * ((1 - ρ y) * p - ρ y)) := by
    have hprod1 : DifferentiableAt ℝ (fun z => θ (ρ z) - 1) y := hθρ.sub (differentiableAt_const 1)
    have hprod2 : DifferentiableAt ℝ (fun z => β z - γ z) y := hβ.sub hγ
    have hmain : fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y wm =
        (θ (ρ y) - 1) * fderiv ℝ (fun z => β z - γ z) y wm +
          (β y - γ y) * fderiv ℝ (fun z => θ (ρ z)) y wm := by
      have hmul := fderiv_mul (x := y) (c := fun z => θ (ρ z) - 1)
        (d := fun z => β z - γ z) (hc := hprod1) (hd := hprod2)
      have hθρ1 : fderiv ℝ (fun z => θ (ρ z) - 1) y = fderiv ℝ (fun z => θ (ρ z)) y := by
        rw [show (fun z : MorseModel n => θ (ρ z) - 1) =
            (fun z : MorseModel n => θ (ρ z)) - (fun _ : MorseModel n => 1) by rfl]
        rw [fderiv_sub (f := fun z => θ (ρ z)) (g := fun _ : MorseModel n => 1)
          (hf := hθρ) (hg := differentiableAt_const 1)]
        simp
      have hmain' : fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y =
          (θ (ρ y) - 1) • fderiv ℝ (fun z => β z - γ z) y +
            (β y - γ y) • fderiv ℝ (fun z => θ (ρ z)) y := by
        rw [show (fun z : MorseModel n => (θ (ρ z) - 1) * (β z - γ z)) =
            (fun z : MorseModel n => θ (ρ z) - 1) * (fun z : MorseModel n => β z - γ z) by rfl]
        rw [hmul, hθρ1]
      rw [hmain']
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    have hval : (β y - γ y) * fderiv ℝ (fun z => θ (ρ z)) y wm =
        ‖negPart hk y‖ ^ 2 * (-(1 - ρ y) * p + ρ y) * deriv θ (ρ y) := by
      have hβγ : β y - γ y = -(γ y - β y) := by ring
      rw [hβγ, hdθρ]
      have hγβ : γ y - β y ≠ 0 := by
        dsimp [γ, β]
        exact hden
      field_simp [hγβ]
      ring
    have hmain' : fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y wm =
        ‖negPart hk y‖ ^ 2 *
          ((θ (ρ y) - 1) * (-1 - p) - deriv θ (ρ y) * ((1 - ρ y) * p - ρ y)) := by
      rw [hmain, hdγβ, hval]
      ring
    have hsmul : fderiv ℝ (fun z => s * (θ (ρ z) - 1) * (β z - γ z)) y wm =
        s * fderiv ℝ (fun z => (θ (ρ z) - 1) * (β z - γ z)) y wm := by
      have hd : DifferentiableAt ℝ (fun z => s * ((θ (ρ z) - 1) * (β z - γ z))) y :=
        (differentiableAt_const s).mul (hprod1.mul hprod2)
      rw [show (fun z : MorseModel n => s * (θ (ρ z) - 1) * (β z - γ z)) =
          (fun z : MorseModel n => s * ((θ (ρ z) - 1) * (β z - γ z))) by
        funext z
        ring]
      rw [fderiv_const_mul (a := fun z : MorseModel n => (θ (ρ z) - 1) * (β z - γ z))
        (b := s) (ha := hprod1.mul hprod2)]
      simp [ContinuousLinearMap.smul_apply]
    rw [hsmul, hmain']
    ring
  have hnaive : fderiv ℝ (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y wm =
      ‖negPart hk y‖ ^ 2 * ((1 - s) * p - s) := by
    have hd := fderiv_modelSublevelFamily_direction_neg hk c ε r δ R₀ R₁ s hR hR0 y
    dsimp [wm, G, τ, capSlope, τSlope, p] at hd ⊢
    rw [hd]
    ring
  have htotal : fderiv ℝ (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) y wm =
      ‖negPart hk y‖ ^ 2 *
        (((1 - s) * p - s) +
          s * ((θ (ρ y) - 1) * (-1 - p) - deriv θ (ρ y) * ((1 - ρ y) * p - ρ y))) := by
    rw [hsplit]
    rw [fderiv_add (f := fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z)
      (g := fun z : MorseModel n => s * (θ (ρ z) - 1) * (β z - γ z))
      (hf := differentiableAt_modelSublevelFamily hk c ε r δ R₀ R₁ s y)
      (hg := ((differentiableAt_const s).mul (hθρ.sub (differentiableAt_const 1))).mul (hβ.sub hγ))]
    simp [ContinuousLinearMap.add_apply, hnaive, hcorr]
    ring
  have hgoal : ((1 - s) * p - s) +
        s * ((θ (ρ y) - 1) * (-1 - p) - deriv θ (ρ y) * ((1 - ρ y) * p - ρ y)) =
      (1 - s * θ (ρ y) - s * deriv θ (ρ y) * (1 - ρ y)) * p -
        s * (θ (ρ y) - ρ y * deriv θ (ρ y)) := by
    dsimp [p]
    ring
  rw [htotal]
  dsimp [wm, ρ, γ, β, G, τ, capSlope, τSlope, p]
  rw [hgoal]

noncomputable def cutoffTransition (a ε' w : ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ ε' then
    a * t * Real.smoothTransition ((t / ε') ^ w) else a * t

theorem cutoffTransition_nonpos {a ε' w t : ℝ} (ht : t ≤ 0) :
    cutoffTransition a ε' w t = 0 := by
  dsimp [cutoffTransition]
  rw [if_pos ht]

theorem cutoffTransition_eq_affine {a ε' w t : ℝ} (hε' : 0 < ε') (htε : ε' < t) :
    cutoffTransition a ε' w t = a * t := by
  dsimp [cutoffTransition]
  rw [if_neg (not_le_of_gt (lt_trans hε' htε))]
  rw [if_neg (not_le_of_gt htε)]

theorem cutoffTransition_middle {a ε' w t : ℝ} (ht0 : 0 < t) (htε : t < ε') :
    cutoffTransition a ε' w t = a * t * Real.smoothTransition ((t / ε') ^ w) := by
  dsimp [cutoffTransition]
  rw [if_neg (not_le_of_gt ht0)]
  rw [if_pos (le_of_lt htε)]

theorem cutoffTransition_nonneg {a ε' w t : ℝ} (ha : 0 ≤ a) :
    0 ≤ cutoffTransition a ε' w t := by
  dsimp [cutoffTransition]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
  · rw [if_neg ht]
    by_cases htε : t ≤ ε'
    · rw [if_pos htε]
      have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
      have hσ : 0 ≤ Real.smoothTransition ((t / ε') ^ w) := Real.smoothTransition.nonneg _
      exact mul_nonneg (mul_nonneg ha ht0) hσ
    · rw [if_neg htε]
      exact mul_nonneg ha (le_of_lt (lt_of_not_ge ht))

theorem cutoffTransition_le_one {a ε' w t : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1)
    (ht1 : t ≤ 1) :
    cutoffTransition a ε' w t ≤ 1 := by
  dsimp [cutoffTransition]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    exact zero_le_one
  · rw [if_neg ht]
    have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    by_cases htε : t ≤ ε'
    · rw [if_pos htε]
      have hσ : Real.smoothTransition ((t / ε') ^ w) ≤ 1 := Real.smoothTransition.le_one _
      have hσ0 : 0 ≤ Real.smoothTransition ((t / ε') ^ w) := Real.smoothTransition.nonneg _
      have hat : a * t ≤ 1 := by nlinarith [ha, ht0, ht1]
      have hat0 : 0 ≤ a * t := mul_nonneg ha0 ht0
      have hatσ : a * t * Real.smoothTransition ((t / ε') ^ w) ≤ a * t :=
        by simpa using (mul_le_mul_of_nonneg_left hσ hat0)
      exact le_trans hatσ hat
    · rw [if_neg htε]
      simpa using (mul_le_mul ha ht1 ht0 (by norm_num : 0 ≤ (1 : ℝ)))

theorem cutoffTransition_affine_slope {a ε' w t : ℝ} (hε' : 0 < ε') (htε : ε' < t) :
    deriv (cutoffTransition a ε' w) t = a := by
  have hloc : cutoffTransition a ε' w =ᶠ[nhds t] (fun u : ℝ => a * u) := by
    exact Filter.eventually_of_mem (Ioi_mem_nhds htε) (by
      intro u hu
      dsimp [cutoffTransition]
      have hu0 : 0 < u := lt_trans hε' hu
      rw [if_neg (not_le_of_gt hu0)]
      rw [if_neg (not_le_of_gt hu)])
  have hder : deriv (fun u : ℝ => a * u) t = a := by
    have hd := deriv_const_mul (c := a) (d := fun u : ℝ => u) (x := t)
      (hd := differentiableAt_id)
    rw [hd]
    have hid : deriv (fun u : ℝ => u) t = 1 := by simp
    rw [hid]
    ring
  exact hloc.deriv_eq.trans hder

theorem cutoffTransition_deriv_middle {a ε' w t : ℝ} (hε' : 0 < ε') (ht0 : 0 < t)
    (htε : t < ε') :
    deriv (cutoffTransition a ε' w) t =
      a * (Real.smoothTransition ((t / ε') ^ w) +
        w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w)) := by
  have hloc : cutoffTransition a ε' w =ᶠ[nhds t]
      (fun u : ℝ => a * u * Real.smoothTransition ((u / ε') ^ w)) := by
    exact Filter.eventually_of_mem (Ioo_mem_nhds ht0 htε) (by
      intro u hu
      dsimp [cutoffTransition]
      have hu0 : 0 < u := hu.1
      have huε : u < ε' := hu.2
      rw [if_neg (not_le_of_gt hu0)]
      rw [if_pos (le_of_lt huε)])
  have hder : deriv (fun u : ℝ => a * u * Real.smoothTransition ((u / ε') ^ w)) t =
      a * (Real.smoothTransition ((t / ε') ^ w) +
        w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w)) := by
    have h1diff : DifferentiableAt ℝ (fun u : ℝ => a * u) t :=
      (differentiableAt_const a).mul differentiableAt_id
    have hg : DifferentiableAt ℝ (fun u : ℝ => u / ε') t :=
      differentiableAt_id.div (differentiableAt_const ε') (ne_of_gt hε')
    have hpowdiff : DifferentiableAt ℝ (fun u : ℝ => (u / ε') ^ w) t :=
      hg.rpow_const (Or.inl (ne_of_gt (div_pos ht0 hε')))
    have h2diff : DifferentiableAt ℝ (fun u : ℝ => Real.smoothTransition ((u / ε') ^ w)) t :=
      by fun_prop
    rw [show (fun u : ℝ => a * u * Real.smoothTransition ((u / ε') ^ w)) =
        (fun u : ℝ => a * u) * (fun u : ℝ => Real.smoothTransition ((u / ε') ^ w)) by rfl]
    rw [deriv_mul h1diff h2diff]
    have h1' : deriv (fun u : ℝ => a * u) t = a := by
      rw [deriv_const_mul (c := a) (d := fun u : ℝ => u) (x := t) (hd := differentiableAt_id)]
      have hid : deriv (fun u : ℝ => u) t = 1 := by simp
      rw [hid]
      simp
    have hlin' : deriv (fun u : ℝ => u / ε') t = 1 / ε' := by
      rw [show (fun u : ℝ => u / ε') = id / (fun _ : ℝ => ε') by rfl]
      rw [deriv_div differentiableAt_id (differentiableAt_const ε') (ne_of_gt hε')]
      simp
      field_simp [hε'.ne']
    have hpow' : deriv (fun u : ℝ => (u / ε') ^ w) t = w * (t / ε') ^ (w - 1) / ε' := by
      rw [show (fun u : ℝ => (u / ε') ^ w) =
          (fun x : ℝ => x ^ w) ∘ (fun u : ℝ => u / ε') by rfl]
      rw [deriv_comp (h₂ := fun x : ℝ => x ^ w) (h := fun u : ℝ => u / ε') (x := t)
        (Real.differentiableAt_rpow_const_of_ne w (ne_of_gt (div_pos ht0 hε'))) hg]
      rw [Real.deriv_rpow_const (t / ε') w]
      rw [hlin']
      ring
    have h2' : deriv (fun u : ℝ => Real.smoothTransition ((u / ε') ^ w)) t =
        w * (t / ε') ^ (w - 1) / ε' * deriv Real.smoothTransition ((t / ε') ^ w) := by
      rw [show (fun u : ℝ => Real.smoothTransition ((u / ε') ^ w)) =
          Real.smoothTransition ∘ (fun u : ℝ => (u / ε') ^ w) by rfl]
      have hσdiff : DifferentiableAt ℝ Real.smoothTransition ((t / ε') ^ w) := by
        fun_prop
      rw [deriv_comp (h₂ := Real.smoothTransition) (h := fun u : ℝ => (u / ε') ^ w) (x := t)
        hσdiff hpowdiff]
      rw [hpow']
      ring
    rw [h1', h2']
    have hvt : t * (t / ε') ^ (w - 1) / ε' = (t / ε') ^ w := by
      have htd : 0 < t / ε' := div_pos ht0 hε'
      have hmain : (t / ε') * (t / ε') ^ (w - 1) = (t / ε') ^ w := by
        have hstep : (t / ε') ^ (1 : ℝ) * (t / ε') ^ (w - 1) = (t / ε') ^ (1 + (w - 1)) :=
          (Real.rpow_add htd (1 : ℝ) (w - 1)).symm
        have hmain0 : (t / ε') * (t / ε') ^ (w - 1) = (t / ε') ^ (1 + (w - 1)) := by
          simpa [Real.rpow_one] using hstep
        rw [hmain0]
        ring_nf
      calc
        t * (t / ε') ^ (w - 1) / ε' = (t / ε') * (t / ε') ^ (w - 1) := by
          field_simp [hε'.ne']
        _ = (t / ε') ^ w := hmain
    have hrew : a * Real.smoothTransition ((t / ε') ^ w) +
        (a * t) * (w * (t / ε') ^ (w - 1) / ε' * deriv Real.smoothTransition ((t / ε') ^ w)) =
        a * (Real.smoothTransition ((t / ε') ^ w) +
          w * (t * (t / ε') ^ (w - 1) / ε') * deriv Real.smoothTransition ((t / ε') ^ w)) := by
      ring
    rw [hrew, hvt]
  rw [hloc.deriv_eq]
  exact hder

theorem cutoffTransition_deriv_lt_one {a ε' w t : ℝ} (ha0 : 0 ≤ a) (hε' : 0 < ε')
    (ht0 : 0 < t) (htε : t < ε') (hw : 0 < w) (hslope : a * (1 + 40 * w) < 1) :
    deriv (cutoffTransition a ε' w) t < 1 := by
  have hmid := cutoffTransition_deriv_middle (a := a) (ε' := ε') (w := w) (t := t) hε' ht0 htε
  rw [hmid]
  have hσ : Real.smoothTransition ((t / ε') ^ w) ≤ 1 := Real.smoothTransition.le_one _
  have hσ' : deriv Real.smoothTransition ((t / ε') ^ w) ≤ 40 :=
    Real.smoothTransition_deriv_le_forty _
  have hσ'0 : 0 ≤ deriv Real.smoothTransition ((t / ε') ^ w) := smoothTransition_deriv_nonneg _
  have hv : (t / ε') ^ w ≤ 1 := by
    have htdiv : t / ε' ≤ 1 := div_le_one_of_le₀ (le_of_lt htε) (le_of_lt hε')
    have htd : 0 ≤ t / ε' := div_nonneg (le_of_lt ht0) (le_of_lt hε')
    have hle := Real.rpow_le_rpow htd htdiv (le_of_lt hw)
    have hone : (1 : ℝ) ^ w = 1 := Real.one_rpow w
    rwa [hone] at hle
  have hv0 : 0 ≤ (t / ε') ^ w :=
    Real.rpow_nonneg (div_nonneg (le_of_lt ht0) (le_of_lt hε')) w
  have hterm : w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) ≤ w * 40 := by
    have h1 : (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) ≤ 1 * 40 := by
      exact mul_le_mul hv hσ' hσ'0 (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum : Real.smoothTransition ((t / ε') ^ w) +
      w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) ≤ 1 + 40 * w := by
    nlinarith [hσ, hterm]
  have hmain : a * (Real.smoothTransition ((t / ε') ^ w) +
      w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w)) < 1 := by
    have hle := mul_le_mul_of_nonneg_left hsum ha0
    nlinarith [hle, hslope]
  exact hmain

theorem cutoffTransition_le_mul {a ε' w t : ℝ} (ha0 : 0 ≤ a) (ht0 : 0 ≤ t) :
    cutoffTransition a ε' w t ≤ a * t := by
  dsimp [cutoffTransition]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    have h : 0 ≤ a * t := mul_nonneg ha0 ht0
    exact h
  · rw [if_neg ht]
    by_cases htε : t ≤ ε'
    · rw [if_pos htε]
      have hσ : Real.smoothTransition ((t / ε') ^ w) ≤ 1 := Real.smoothTransition.le_one _
      have ht0' : 0 < t := lt_of_not_ge ht
      have hmain : a * t * Real.smoothTransition ((t / ε') ^ w) ≤ a * t :=
        by simpa using (mul_le_mul_of_nonneg_left hσ (mul_nonneg ha0 (le_of_lt ht0')))
      exact hmain
    · rw [if_neg htε]

theorem cutoffTransition_deriv_le {a ε' w t : ℝ} (ha0 : 0 ≤ a) (hε' : 0 < ε')
    (ht0 : 0 < t) (htε : t < ε') (hw : 0 < w) :
    deriv (cutoffTransition a ε' w) t ≤ a * (1 + 40 * w) := by
  have hmid := cutoffTransition_deriv_middle (a := a) (ε' := ε') (w := w) (t := t) hε' ht0 htε
  rw [hmid]
  have hσ : Real.smoothTransition ((t / ε') ^ w) ≤ 1 := Real.smoothTransition.le_one _
  have hσ' : deriv Real.smoothTransition ((t / ε') ^ w) ≤ 40 :=
    Real.smoothTransition_deriv_le_forty _
  have hσ'0 : 0 ≤ deriv Real.smoothTransition ((t / ε') ^ w) := smoothTransition_deriv_nonneg _
  have hv : (t / ε') ^ w ≤ 1 := by
    have htdiv : t / ε' ≤ 1 := div_le_one_of_le₀ (le_of_lt htε) (le_of_lt hε')
    have htd : 0 ≤ t / ε' := div_nonneg (le_of_lt ht0) (le_of_lt hε')
    have hle := Real.rpow_le_rpow htd htdiv (le_of_lt hw)
    have hone : (1 : ℝ) ^ w = 1 := Real.one_rpow w
    rwa [hone] at hle
  have hv0 : 0 ≤ (t / ε') ^ w :=
    Real.rpow_nonneg (div_nonneg (le_of_lt ht0) (le_of_lt hε')) w
  have hterm : w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) ≤ w * 40 := by
    have h1 : (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) ≤ 1 * 40 := by
      exact mul_le_mul hv hσ' hσ'0 (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum : Real.smoothTransition ((t / ε') ^ w) +
      w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) ≤ 1 + 40 * w := by
    nlinarith [hσ, hterm]
  have hmain : a * (Real.smoothTransition ((t / ε') ^ w) +
      w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w)) ≤ a * (1 + 40 * w) :=
    mul_le_mul_of_nonneg_left hsum ha0
  exact hmain

theorem cutoffTransition_junction_bound {a ε' w t : ℝ} (ha0 : 0 ≤ a) (hε' : 0 < ε')
    (hε'1 : ε' ≤ 1) (ht0 : 0 < t) (htε : t < ε') (hw : 0 < w)
    (hslope : a * (1 + 40 * w + ε') < 1) :
    cutoffTransition a ε' w t + deriv (cutoffTransition a ε' w) t * (1 - t) < 1 := by
  have hle : cutoffTransition a ε' w t ≤ a * t :=
    cutoffTransition_le_mul ha0 (le_of_lt ht0)
  have hder : deriv (cutoffTransition a ε' w) t ≤ a * (1 + 40 * w) :=
    cutoffTransition_deriv_le ha0 hε' ht0 htε hw
  have ht1 : 1 - t ≤ 1 := by linarith [ht0]
  have ht1' : 0 ≤ 1 - t := by nlinarith [hε'1, htε]
  have h1 : deriv (cutoffTransition a ε' w) t * (1 - t) ≤ a * (1 + 40 * w) * 1 := by
    have hder0 : 0 ≤ deriv (cutoffTransition a ε' w) t := by
      have hmid := cutoffTransition_deriv_middle (a := a) (ε' := ε') (w := w) (t := t) hε' ht0 htε
      rw [hmid]
      have h1 : 0 ≤ Real.smoothTransition ((t / ε') ^ w) := Real.smoothTransition.nonneg _
      have h2 : 0 ≤ w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) := by
        have h3 : 0 ≤ (t / ε') ^ w := Real.rpow_nonneg (div_nonneg (le_of_lt ht0) (le_of_lt hε')) w
        have h4 : 0 ≤ deriv Real.smoothTransition ((t / ε') ^ w) := smoothTransition_deriv_nonneg _
        have hw0 : 0 ≤ w := le_of_lt hw
        positivity
      have hsum : 0 ≤ Real.smoothTransition ((t / ε') ^ w) +
          w * (t / ε') ^ w * deriv Real.smoothTransition ((t / ε') ^ w) := by
        nlinarith [h1, h2]
      exact mul_nonneg ha0 hsum
    have hmul := mul_le_mul hder ht1 ht1' (by positivity)
    simpa [mul_assoc] using hmul
  have h2 : a * t + a * (1 + 40 * w) ≤ a * (1 + 40 * w + ε') := by
    have htε' : t < ε' := htε
    nlinarith [htε']
  have hmain : cutoffTransition a ε' w t + deriv (cutoffTransition a ε' w) t * (1 - t) ≤
      a * t + a * (1 + 40 * w) := by
    nlinarith [hle, h1]
  have hfinal : a * (1 + 40 * w + ε') < 1 := hslope
  nlinarith [hmain, h2, hfinal]

noncomputable def cutoffFunction (a ε' w η₁ : ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ ε' then
    a * t * Real.smoothTransition ((t / ε') ^ w)
  else if t ≤ 1 - η₁ then a * t
  else if t ≤ 1 then
    a * t + (1 - a * t) * Real.smoothTransition ((t - (1 - η₁)) / η₁)
  else 1

theorem cutoffFunction_nonpos {a ε' w η₁ t : ℝ} (ht : t ≤ 0) :
    cutoffFunction a ε' w η₁ t = 0 := by
  dsimp [cutoffFunction]
  rw [if_pos ht]

theorem cutoffFunction_eq_affine {a ε' w η₁ t : ℝ} (hε' : 0 < ε') (htε : ε' < t)
    (ht₁ : t ≤ 1 - η₁) :
    cutoffFunction a ε' w η₁ t = a * t := by
  dsimp [cutoffFunction]
  rw [if_neg (not_le_of_gt (lt_trans hε' htε))]
  rw [if_neg (not_le_of_gt htε)]
  rw [if_pos ht₁]

theorem cutoffFunction_eq_one {a ε' w η₁ t : ℝ} (hη₁ : 0 < η₁) (hε'1 : ε' < 1)
    (ht1 : 1 < t) :
    cutoffFunction a ε' w η₁ t = 1 := by
  dsimp [cutoffFunction]
  rw [if_neg (not_le_of_gt (by nlinarith [ht1]))]
  rw [if_neg (not_le_of_gt (by nlinarith [hε'1, ht1]))]
  rw [if_neg (not_le_of_gt (by nlinarith [hη₁, ht1]))]
  rw [if_neg (not_le_of_gt ht1)]

theorem cutoffFunction_nonneg {a ε' w η₁ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ cutoffFunction a ε' w η₁ t := by
  dsimp [cutoffFunction]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
  · rw [if_neg ht]
    have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    by_cases htε : t ≤ ε'
    · rw [if_pos htε]
      have hσ : 0 ≤ Real.smoothTransition ((t / ε') ^ w) := Real.smoothTransition.nonneg _
      exact mul_nonneg (mul_nonneg ha ht0) hσ
    · rw [if_neg htε]
      by_cases ht₁ : t ≤ 1 - η₁
      · rw [if_pos ht₁]
        exact mul_nonneg ha ht0
      · rw [if_neg ht₁]
        by_cases ht₂ : t ≤ 1
        · rw [if_pos ht₂]
          have hσ : 0 ≤ Real.smoothTransition ((t - (1 - η₁)) / η₁) :=
            Real.smoothTransition.nonneg _
          have h1 : 0 ≤ a * t := mul_nonneg ha ht0
          have ht1 : t ≤ 1 := ht₂
          have hat : a * t ≤ 1 := by
            simpa using (mul_le_mul ha1 ht1 ht0 (by norm_num : 0 ≤ (1 : ℝ)))
          have h2 : 0 ≤ 1 - a * t := by linarith
          have hprod := mul_nonneg h2 hσ
          nlinarith [h1, hprod]
        · rw [if_neg ht₂]
          exact zero_le_one

theorem cutoffFunction_le_one {a ε' w η₁ t : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1)
    (ht1 : t ≤ 1) :
    cutoffFunction a ε' w η₁ t ≤ 1 := by
  dsimp [cutoffFunction]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    exact zero_le_one
  · rw [if_neg ht]
    have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    by_cases htε : t ≤ ε'
    · rw [if_pos htε]
      have hσ : Real.smoothTransition ((t / ε') ^ w) ≤ 1 := Real.smoothTransition.le_one _
      have hσ0 : 0 ≤ Real.smoothTransition ((t / ε') ^ w) := Real.smoothTransition.nonneg _
      have hat : a * t ≤ 1 := by
        simpa using (mul_le_mul ha ht1 ht0 (by norm_num : 0 ≤ (1 : ℝ)))
      have hat0 : 0 ≤ a * t := mul_nonneg ha0 ht0
      have hatσ : a * t * Real.smoothTransition ((t / ε') ^ w) ≤ a * t :=
        by simpa using (mul_le_mul_of_nonneg_left hσ hat0)
      exact le_trans hatσ hat
    · rw [if_neg htε]
      by_cases ht₁ : t ≤ 1 - η₁
      · rw [if_pos ht₁]
        simpa using (mul_le_mul ha ht1 ht0 (by norm_num : 0 ≤ (1 : ℝ)))
      · rw [if_neg ht₁]
        by_cases ht₂ : t ≤ 1
        · rw [if_pos ht₂]
          have hσ : Real.smoothTransition ((t - (1 - η₁)) / η₁) ≤ 1 :=
            Real.smoothTransition.le_one _
          have hσ0 : 0 ≤ Real.smoothTransition ((t - (1 - η₁)) / η₁) :=
            Real.smoothTransition.nonneg _
          have hat1 : a * t ≤ 1 := by
            nlinarith [ha, ht1, ht0, ha0]
          have htail : 0 ≤ 1 - a * t := by linarith
          have hmul := mul_le_mul_of_nonneg_left hσ htail
          have hmain : a * t + (1 - a * t) * Real.smoothTransition ((t - (1 - η₁)) / η₁) ≤
              a * t + (1 - a * t) := by
            nlinarith [hmul]
          have hmain' : a * t + (1 - a * t) ≤ 1 := by nlinarith [hat1]
          nlinarith [hmain, hmain']
        · rw [if_neg ht₂]

theorem modelRoundedFunction_value_le_of_posPart_eq_zero {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hp : posPart hk y = 0) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y - c ≤ -(r ^ 2 - δ) / 2 := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hb : ‖posPart hk y‖ ^ 2 = 0 := by
    rw [hp]
    simp
  have hnorm : morseNorm n y ^ 2 = t := by
    dsimp [t]
    rw [morseNorm_sq_eq_negPart_add_posPart hk y, hb, add_zero]
  by_cases hcore : t < R₀ ^ 2
  · have hcap : r ^ 2 - δ ≤ smoothCap ε r δ t := smoothCap_ge_sub hδ
    have hnormR : morseNorm n y < R₀ := by
      have hlt : morseNorm n y ^ 2 < R₀ ^ 2 := by
        rw [hnorm]
        exact hcore
      have hnon : 0 ≤ morseNorm n y := by positivity
      have habs := sq_lt_sq.mp hlt
      rw [abs_of_nonneg hnon, abs_of_nonneg hR0] at habs
      exact habs
    have hval : modelRoundedFunction hk c ε r δ R₀ R₁ y - c =
        -(1 / 2 : ℝ) * smoothCap ε r δ t := by
      have hround : modelRoundedFunction hk c ε r δ R₀ R₁ y =
          modelAttachedFunction hk c ε r δ y := by
        exact modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 (le_of_lt hnormR)
      rw [hround]
      dsimp [modelAttachedFunction]
      have hstep : c + (1 / 2 : ℝ) * (‖posPart hk y‖ ^ 2 -
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - c =
          -(1 / 2 : ℝ) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
        rw [hp]
        simp
      simpa [t] using hstep
    rw [hval]
    have hm : -(1 / 2 : ℝ) * smoothCap ε r δ t ≤ -(1 / 2 : ℝ) * (r ^ 2 - δ) :=
      mul_le_mul_of_nonpos_left hcap (by norm_num)
    nlinarith [hm]
  · have hcore' : R₀ ^ 2 ≤ ‖negPart hk y‖ ^ 2 := by
      simpa [t] using (le_of_not_gt hcore)
    have hcap : smoothCap ε r δ t = t - 2 * ε := by
      apply smoothCap_upper hδ
      have hle2 : r ^ 2 + 2 * ε + δ ≤ R₀ ^ 2 / 2 := by nlinarith only [hbig]
      have hR₀pos : 0 < R₀ ^ 2 := by
        have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
        nlinarith only [hbig, hδ, hr2, hε]
      have hhalf : R₀ ^ 2 / 2 < R₀ ^ 2 := by nlinarith only [hR₀pos]
      calc
        r ^ 2 + 2 * ε + δ ≤ R₀ ^ 2 / 2 := hle2
        _ ≤ R₀ ^ 2 := le_of_lt hhalf
        _ ≤ t := by simpa [t] using hcore'
    have hG : morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c) = 0 := by
      have hcap' : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
        simpa [t] using hcap
      rw [morseNormalForm_split hk c y]
      unfold modelAttachedFunction
      rw [hcap', hp]
      ring
    have hval : modelRoundedFunction hk c ε r δ R₀ R₁ y - c =
        -(1 / 2 : ℝ) * (t - 2 * ε) := by
      have hdef : modelRoundedFunction hk c ε r δ R₀ R₁ y - c =
          (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
            Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) -
          (1 / 2 : ℝ) * smoothCap ε r δ t := by
        dsimp [modelRoundedFunction, modelAttachedFunction, t]
        rw [morseNormalForm_split hk c y, hp]
        simp
        ring
      rw [hdef, hG, hcap]
      dsimp [t]
      ring
    rw [hval]
    have hsq : R₀ ^ 2 ≤ t := hcore'
    have hm : -(1 / 2 : ℝ) * (t - 2 * ε) ≤ -R₀ ^ 2 / 2 + ε := by
      nlinarith [hsq]
    have hR₀big : R₀ ^ 2 ≥ 2 * r ^ 2 + 4 * ε + 2 * δ := by nlinarith only [hbig]
    have hgoal : -R₀ ^ 2 / 2 + ε ≤ -(r ^ 2 - δ) / 2 := by
      nlinarith [hR₀big]
    exact le_trans hm hgoal

theorem modelRoundedFunction_ratio_nonpos_of_posPart_eq_zero {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hr : r ^ 2 = 2 * ε) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hε₀ : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    {y : MorseModel n} (hp : posPart hk y = 0)
    (hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
      (morseNormalForm hk c y - c - ε) ≠ 0) :
    modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y ≤ 0 := by
  have hval := modelRoundedFunction_value_le_of_posPart_eq_zero hk c ε r δ R₀ R₁
    hε hδ hδr hR hR0 hbig hp
  have hγ : modelRoundedFunction hk c ε r δ R₀ R₁ y - c + ε₀ < 0 := by
    have hε₀' : ε₀ < (r ^ 2 - δ) / 2 := by
      have hle : min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2) ≤ (r ^ 2 - δ) / 2 :=
        min_le_right _ _
      nlinarith [hε₀, hle]
    nlinarith [hval, hε₀']
  have hpos : 0 < modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
      (morseNormalForm hk c y - c - ε) := by
    have hge : 0 ≤ modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
        (morseNormalForm hk c y - c - ε) := by
      let t : ℝ := ‖negPart hk y‖ ^ 2
      have hcap : smoothCap ε r δ t ≤ t + 2 * ε := by
        have hcap' : smoothCap ε r δ t ≤ max (r ^ 2) t := smoothCap_le_max (le_of_lt hε) hδ
        have hmax : max (r ^ 2) t ≤ t + 2 * ε := by
          have ht0 : 0 ≤ t := by dsimp [t]; positivity
          have h1 : r ^ 2 ≤ t + 2 * ε := by nlinarith [hr, ht0]
          have h2 : t ≤ t + 2 * ε := by nlinarith [hε]
          exact max_le h1 h2
        exact le_trans hcap' hmax
      have hγβ : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
          (morseNormalForm hk c y - c - ε) =
          (‖negPart hk y‖ ^ 2 + 2 * ε - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) / 2 +
            (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
              Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
        dsimp [modelRoundedFunction, modelAttachedFunction]
        rw [morseNormalForm_split hk c y]
        ring
      rw [hγβ]
      have hG : 0 ≤ (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
          Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
        have htrans : 0 ≤ Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) :=
          Real.smoothTransition.nonneg _
        by_cases hτ0 : Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) = 0
        · rw [hτ0]
          simp
        · have hτpos : 0 < Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) :=
            lt_of_le_of_ne htrans (Ne.symm hτ0)
          have hargpos : 0 < (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) :=
            (smoothTransition_pos_iff _).mp hτpos
          have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
            have hlt : |R₀| < |R₁| := by
              rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
              exact hR
            have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
            nlinarith
          have hnormge : R₀ ^ 2 ≤ morseNorm n y ^ 2 := by
            have hmain : 0 < morseNorm n y ^ 2 - R₀ ^ 2 := by
              simpa using ((lt_div_iff₀ hden).mp hargpos)
            nlinarith
          have hcapUpper : smoothCap ε r δ (‖negPart hk y‖ ^ 2) =
              ‖negPart hk y‖ ^ 2 - 2 * ε := by
            apply smoothCap_upper hδ
            have hle2 : r ^ 2 + 2 * ε + δ ≤ R₀ ^ 2 / 2 := by
              nlinarith only [hbig, hr]
            have hR₀pos : 0 < R₀ ^ 2 := by
              have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
              have hpos2 : 0 < 2 * (r ^ 2 + 2 * ε + δ) := by nlinarith [hr2, hδ, hε]
              exact lt_of_lt_of_le hpos2 hbig
            have hhalf : R₀ ^ 2 / 2 < R₀ ^ 2 := by nlinarith only [hR₀pos]
            have hmain : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
              calc
                r ^ 2 + 2 * ε + δ ≤ R₀ ^ 2 / 2 := hle2
                _ ≤ R₀ ^ 2 := le_of_lt hhalf
                _ ≤ ‖negPart hk y‖ ^ 2 := by
                  have hnormeq : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 := by
                    rw [morseNorm_sq_eq_negPart_add_posPart hk y]
                    rw [hp]
                    simp
                  nlinarith [hnormge, hnormeq]
            exact hmain
          have hG' : morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c) = 0 := by
            rw [morseNormalForm_split hk c y]
            unfold modelAttachedFunction
            rw [hcapUpper]
            ring
          rw [hG']
          simp
      have hmain : 0 ≤ (‖negPart hk y‖ ^ 2 + 2 * ε - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) / 2 := by
        have hle : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ ‖negPart hk y‖ ^ 2 + 2 * ε := by
          simpa [t] using hcap
        nlinarith
      nlinarith [hmain, hG]
    exact lt_of_le_of_ne hge (Ne.symm hden)
  dsimp [modelSublevelCutoffRatio]
  exact div_nonpos_of_nonpos_of_nonneg (le_of_lt hγ) (le_of_lt hpos)

theorem cutoffFunction_deriv_affine {a ε' w η₁ t : ℝ} (hε' : 0 < ε')
    (htε : ε' < t) (ht₁ : t < 1 - η₁) :
    deriv (cutoffFunction a ε' w η₁) t = a := by
  have hloc : cutoffFunction a ε' w η₁ =ᶠ[nhds t] (fun u : ℝ => a * u) := by
    exact Filter.eventually_of_mem
      (Ioo_mem_nhds htε ht₁) (by
    intro u hu
    dsimp [cutoffFunction]
    have hu0 : 0 < u := lt_trans hε' hu.1
    have huε : ε' < u := hu.1
    have hu₁ : u < 1 - η₁ := hu.2
    rw [if_neg (not_le_of_gt hu0)]
    rw [if_neg (not_le_of_gt huε)]
    rw [if_pos (le_of_lt hu₁)])
  have hder : deriv (fun u : ℝ => a * u) t = a := by
    have hd := deriv_const_mul (c := a) (d := fun u : ℝ => u) (x := t)
      (hd := differentiableAt_id)
    rw [hd]
    have hid : deriv (fun u : ℝ => u) t = 1 := by simp
    rw [hid]
    simp
  rw [hloc.deriv_eq]
  exact hder

theorem cutoffFunction_differentiableAt_affine {a ε' w η₁ t : ℝ} (hε' : 0 < ε')
    (htε : ε' < t) (ht₁ : t < 1 - η₁) :
    DifferentiableAt ℝ (cutoffFunction a ε' w η₁) t := by
  have hloc : cutoffFunction a ε' w η₁ =ᶠ[nhds t] (fun u : ℝ => a * u) := by
    exact Filter.eventually_of_mem
      (Ioo_mem_nhds htε ht₁) (by
    intro u hu
    dsimp [cutoffFunction]
    have hu0 : 0 < u := lt_trans hε' hu.1
    have huε : ε' < u := hu.1
    have hu₁ : u < 1 - η₁ := hu.2
    rw [if_neg (not_le_of_gt hu0)]
    rw [if_neg (not_le_of_gt huε)]
    rw [if_pos (le_of_lt hu₁)])
  have hloc' : cutoffFunction a ε' w η₁ =ᶠ[nhds t] (fun x : ℝ => a) * id := by
    filter_upwards [hloc] with u hu
    simpa using hu
  exact ((differentiableAt_const a).mul differentiableAt_id).congr_of_eventuallyEq hloc'

theorem modelSublevelFamilyCutoff_notCritical_of_affine_ratio {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ a ε' w η₁ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : r ^ 2 = 2 * ε)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀ : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (hε' : 0 < ε')
    (ha : 0 ≤ a) (ha1 : a < 1)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (y : MorseModel n)
    (hρ : ε' < modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y)
    (hρ₁ : modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y < 1 - η₁) :
    fderiv ℝ (fun z => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
      (cutoffFunction a ε' w η₁) s z) y ≠ 0 := by
  intro hcrit
  let θ : ℝ → ℝ := cutoffFunction a ε' w η₁
  let ρ : ℝ := modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y
  let wp : MorseModel n := recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  let G : ℝ := morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)
  let τSlope : ℝ := deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
    (R₁ ^ 2 - R₀ ^ 2)
  let q : ℝ := 1 + 2 * G * τSlope
  have hθdiff : DifferentiableAt ℝ θ ρ := by
    dsimp [θ, ρ]
    exact cutoffFunction_differentiableAt_affine hε' hρ hρ₁
  have hθval : θ ρ = a * ρ := by
    dsimp [θ, ρ]
    exact cutoffFunction_eq_affine hε' hρ (le_of_lt hρ₁)
  have hθderiv : deriv θ ρ = a := by
    dsimp [θ, ρ]
    exact cutoffFunction_deriv_affine hε' hρ hρ₁
  have hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
      (morseNormalForm hk c y - c - ε) ≠ 0 := by
    intro h0
    have hρ0 : ρ = 0 := by
      dsimp [ρ, modelSublevelCutoffRatio]
      rw [h0]
      simp
    have hε'ρ : ε' < ρ := hρ
    rw [hρ0] at hε'ρ
    linarith
  have hdpos := fderiv_modelSublevelFamilyCutoff_direction_pos hk c ε r δ R₀ R₁ ε₀ hR hR0
    θ s y hθdiff hden
  have hwp0 : fderiv ℝ (fun z => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ θ s z) y wp = 0 :=
    congrArg (fun L : (MorseModel n →L[ℝ] ℝ) => L wp) hcrit
  rw [hdpos] at hwp0
  have hG : 0 < q := by
    dsimp [q, G, τSlope]
    have hden_pos : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have hlt : |R₀| < |R₁| := by
        rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
        exact hR
      have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
      nlinarith
    have hτSlope_nonneg : 0 ≤ τSlope := by
      dsimp [τSlope]
      exact div_nonneg (smoothTransition_deriv_nonneg _) (le_of_lt hden_pos)
    have hτSlope_le : τSlope ≤ 40 / (R₁ ^ 2 - R₀ ^ 2) := by
      dsimp [τSlope]
      have hd : deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 40 :=
        Real.smoothTransition_deriv_le_forty _
      exact div_le_div_of_nonneg_right hd (le_of_lt hden_pos)
    have hNεA_ge : -(δ / 2) ≤ G := by
      dsimp [G]
      have hcap : ‖negPart hk y‖ ^ 2 - 2 * ε - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
        smoothCap_ge_sub_two_mul_eps (ε := ε) (δ := δ) hδ
      have hmid : morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c) =
          ε + (1 / 2 : ℝ) * (smoothCap ε r δ (‖negPart hk y‖ ^ 2) - ‖negPart hk y‖ ^ 2) := by
        rw [morseNormalForm_split hk c y]
        unfold modelAttachedFunction
        ring
      rw [hmid]
      nlinarith [hcap]
    have hle1 : 2 * (-(δ / 2)) * τSlope ≤ 2 * G * τSlope := by
      have hpr : 0 ≤ 2 * τSlope := by positivity
      have hmul := mul_le_mul_of_nonneg_right hNεA_ge hpr
      nlinarith only [hmul]
    have hle2 : -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 2 * (-(δ / 2)) * τSlope := by
      have hcoef : 2 * (δ / 2) * τSlope ≤ 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by
        have hmain : 2 * (δ / 2) * τSlope ≤ δ * τSlope := by nlinarith only [hδ]
        have hstep : δ * τSlope ≤ 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by
          have hmul := mul_le_mul_of_nonneg_left hτSlope_le (le_of_lt hδ)
          have heq : δ * (40 / (R₁ ^ 2 - R₀ ^ 2)) = 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := by ring
          rw [← heq]
          exact hmul
        nlinarith only [hmain, hstep]
      have hneg : -(40 * δ / (R₁ ^ 2 - R₀ ^ 2)) ≤ -(2 * (δ / 2) * τSlope) := neg_le_neg hcoef
      have hrew : -(2 * (δ / 2) * τSlope) = 2 * (-(δ / 2)) * τSlope := by ring
      rw [hrew] at hneg
      exact hneg
    have hδR' : 40 * δ / (R₁ ^ 2 - R₀ ^ 2) < 1 := (div_lt_one (by positivity)).2 hδR
    have hA_le_B : -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) ≤ 2 * G * τSlope := le_trans hle2 hle1
    have hlb : 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) ≤ 1 + 2 * G * τSlope := by
      have hrew : 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) = 1 + -((40 * δ) / (R₁ ^ 2 - R₀ ^ 2)) := by ring
      rw [hrew]
      exact add_le_add (le_refl 1) hA_le_B
    have hpos1 : 0 < 1 - 40 * δ / (R₁ ^ 2 - R₀ ^ 2) := sub_pos.mpr hδR'
    exact lt_of_lt_of_le hpos1 hlb
  have h1sa : 0 < 1 - s * a := by
    have hsle : s * a ≤ a := by
      simpa [mul_comm] using (mul_le_of_le_one_right ha hs.2)
    nlinarith [ha1, hsle]
  have hpp : ‖posPart hk y‖ ^ 2 = 0 := by
    have hb : (1 - s * θ ρ - s * deriv θ ρ * (1 - ρ)) *
          (1 + 2 * (morseNormalForm hk c y - c + ε - (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) +
        s * (θ ρ - ρ * deriv θ ρ) =
        (1 - s * a) * (1 + 2 * (morseNormalForm hk c y - c + ε -
          (modelAttachedFunction hk c ε r δ y - c)) *
            (deriv Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) /
              (R₁ ^ 2 - R₀ ^ 2))) := by
      rw [hθval, hθderiv]
      ring
    have hmain : ‖posPart hk y‖ ^ 2 * ((1 - s * a) * q) = 0 := by
      simpa [θ, ρ, wp, q, G, τSlope, hb] using hwp0
    have hprod : (1 - s * a) * q ≠ 0 := mul_ne_zero (ne_of_gt h1sa) (ne_of_gt hG)
    exact (mul_eq_zero.mp hmain).resolve_right hprod
  have hp0 : posPart hk y = 0 := by
    have hnon : 0 ≤ ‖posPart hk y‖ := by positivity
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hpp)
  have hρle : modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y ≤ 0 :=
    modelRoundedFunction_ratio_nonpos_of_posPart_eq_zero hk c ε r δ R₀ R₁ ε₀
      hε hδ hδr hr hR hR0 hbig hε₀ hp0 hden
  have hε'ρ : ε' < modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y := hρ
  linarith

theorem modelSublevelFamilyCutoff_notCritical_of_ratio_neg {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ a ε' w η₁ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀ : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (s : ℝ) (y : MorseModel n)
    (hρ : modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y < 0)
    (hy : |modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ (cutoffFunction a ε' w η₁) s y| ≤ 2 * ε₀) :
    fderiv ℝ (fun z => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
      (cutoffFunction a ε' w η₁) s z) y ≠ 0 := by
  have hρcont : ContinuousAt (fun z : MorseModel n =>
      modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z) y := by
    have hγ : ContinuousAt (fun z : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y :=
      (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁).continuous.continuousAt.sub continuousAt_const
    have hβ : ContinuousAt (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y :=
      (contDiff_morseNormalForm hk c).continuous.continuousAt.sub continuousAt_const |>.sub
        continuousAt_const
    have hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
        (morseNormalForm hk c y - c - ε) ≠ 0 := by
      intro h0
      have hz : modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y = 0 := by
        dsimp [modelSublevelCutoffRatio]
        rw [h0]
        simp
      rw [hz] at hρ
      linarith
    have hnum : ContinuousAt (fun z : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ z - c + ε₀) y :=
      hγ.add continuousAt_const
    have hdenf : ContinuousAt (fun z : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ z - c -
          (morseNormalForm hk c z - c - ε)) y :=
      hγ.sub hβ
    exact hnum.div hdenf hden
  have hρneg : ∀ᶠ z in nhds y, modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z < 0 := by
    have hmain := hρcont.eventually_lt (by fun_prop : ContinuousAt (fun _ : MorseModel n => (0 : ℝ)) y) hρ
    simpa using hmain
  have hloc : (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
        (cutoffFunction a ε' w η₁) s z) =ᶠ[nhds y]
      (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ 0 z) := by
    filter_upwards [hρneg] with z hz
    dsimp [modelSublevelFamilyCutoff, modelSublevelFamily]
    have hθ0 : cutoffFunction a ε' w η₁ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z) = 0 :=
      cutoffFunction_nonpos (le_of_lt hz)
    rw [hθ0]
    ring
  have hy0 : |modelSublevelFamily hk c ε r δ R₀ R₁ 0 y| ≤ 2 * ε₀ := by
    have hmain : modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
        (cutoffFunction a ε' w η₁) s y = modelSublevelFamily hk c ε r δ R₀ R₁ 0 y :=
      hloc.self_of_nhds
    rw [← hmain]
    exact hy
  have hne0 := modelSublevelFamily_notCritical_of_strip hk c ε r δ R₀ R₁ ε₀ hε hδ hδr hR hR0
    hbig hδR hε₀ (0 : ℝ) (by norm_num) y hy0
  have hder : fderiv ℝ (fun z => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
      (cutoffFunction a ε' w η₁) s z) y =
      fderiv ℝ (fun z => modelSublevelFamily hk c ε r δ R₀ R₁ 0 z) y :=
    hloc.fderiv_eq
  rw [hder]
  exact hne0

theorem modelSublevelFamilyCutoff_notCritical_of_ratio_top {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ ε₀ a ε' w η₁ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀ : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (hη₁ : 0 < η₁) (hε'1 : ε' < 1)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (y : MorseModel n)
    (hρ : 1 < modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y)
    (hy : |modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀ (cutoffFunction a ε' w η₁) s y| ≤ 2 * ε₀) :
    fderiv ℝ (fun z => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
      (cutoffFunction a ε' w η₁) s z) y ≠ 0 := by
  have hρcont : ContinuousAt (fun z : MorseModel n =>
      modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z) y := by
    have hγ : ContinuousAt (fun z : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ z - c) y :=
      (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁).continuous.continuousAt.sub continuousAt_const
    have hβ : ContinuousAt (fun z : MorseModel n => morseNormalForm hk c z - c - ε) y :=
      (contDiff_morseNormalForm hk c).continuous.continuousAt.sub continuousAt_const |>.sub
        continuousAt_const
    have hden : modelRoundedFunction hk c ε r δ R₀ R₁ y - c -
        (morseNormalForm hk c y - c - ε) ≠ 0 := by
      intro h0
      have hz : modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ y = 0 := by
        dsimp [modelSublevelCutoffRatio]
        rw [h0]
        simp
      have hz' : (1 : ℝ) < 0 := by simpa [hz] using hρ
      linarith
    have hnum : ContinuousAt (fun z : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ z - c + ε₀) y :=
      hγ.add continuousAt_const
    have hdenf : ContinuousAt (fun z : MorseModel n =>
        modelRoundedFunction hk c ε r δ R₀ R₁ z - c -
          (morseNormalForm hk c z - c - ε)) y :=
      hγ.sub hβ
    exact hnum.div hdenf hden
  have hρtop : ∀ᶠ z in nhds y, 1 < modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z := by
    have hmain : ∀ᶠ z in nhds y,
        modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z ∈ Set.Ioi (1 : ℝ) :=
      hρcont.tendsto.eventually (isOpen_Ioi.mem_nhds hρ)
    filter_upwards [hmain] with z hz
    exact hz
  have hloc : (fun z : MorseModel n => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
        (cutoffFunction a ε' w η₁) s z) =ᶠ[nhds y]
      (fun z : MorseModel n => modelSublevelFamily hk c ε r δ R₀ R₁ s z) := by
    filter_upwards [hρtop] with z hz
    dsimp [modelSublevelFamilyCutoff, modelSublevelFamily]
    have hθ1 : cutoffFunction a ε' w η₁ (modelSublevelCutoffRatio hk c ε r δ R₀ R₁ ε₀ z) = 1 :=
      cutoffFunction_eq_one hη₁ hε'1 hz
    rw [hθ1]
    ring
  have hy0 : |modelSublevelFamily hk c ε r δ R₀ R₁ s y| ≤ 2 * ε₀ := by
    have hmain : modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
        (cutoffFunction a ε' w η₁) s y = modelSublevelFamily hk c ε r δ R₀ R₁ s y :=
      hloc.self_of_nhds
    rw [← hmain]
    exact hy
  have hne0 := modelSublevelFamily_notCritical_of_strip hk c ε r δ R₀ R₁ ε₀ hε hδ hδr hR hR0
    hbig hδR hε₀ s hs y hy0
  have hder : fderiv ℝ (fun z => modelSublevelFamilyCutoff hk c ε r δ R₀ R₁ ε₀
      (cutoffFunction a ε' w η₁) s z) y =
      fderiv ℝ (fun z => modelSublevelFamily hk c ε r δ R₀ R₁ s z) y :=
    hloc.fderiv_eq
  rw [hder]
  exact hne0

theorem modelAttachedUnstretch_mem_upper_of_roundedSublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0) {y : MorseModel n}
    (hy : modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) ≤ c + r ^ 2 / 2 := by
  have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
    (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp hy
  exact (modelAttachedStretch_equiv hk c ε r δ hδ hδr hr).2.1 y hyatt

theorem modelAttachedUnstretch_boundary_of_roundedSublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    {y : MorseModel n} (hy : modelRoundedFunction hk c ε r δ R₀ R₁ y = c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) = c + r ^ 2 / 2 := by
  have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
    (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp
      (le_of_eq hy)
  have hA : modelAttachedFunction hk c ε r δ y = c :=
    (modelRoundedFunction_eq_c_iff_attachedFunction_eq hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp hy
  exact modelAttachedFunction_unstretch_boundary hk c ε r δ hδ hδr y hyatt hA

theorem modelAttachedUnstretch_strict_of_roundedSublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    {y : MorseModel n} (hy : modelRoundedFunction hk c ε r δ R₀ R₁ y < c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) < c + r ^ 2 / 2 := by
  have hyatt : y ∈ modelAttachedRegion hk ε r δ :=
    (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp
      (le_of_lt hy)
  have hA : modelAttachedFunction hk c ε r δ y < c :=
    (modelRoundedFunction_lt_c_iff_attachedFunction_lt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp hy
  exact modelAttachedFunction_unstretch_strict hk c ε r δ hδ hδr y hyatt hA

theorem modelLevelDampedUnstretch_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (η ε₀ : ℝ) (hact : ε₀ + δ / 2 < η)
    (hε₀ : 0 < ε₀) {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hg : modelRoundedFunction hk c ε r δ R₀ R₁ y = c) :
    morseNormalForm hk c (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) = c + r ^ 2 / 2 := by
  have hA : modelAttachedFunction hk c ε r δ y = c :=
    (modelRoundedFunction_eq_c_iff_attachedFunction_eq hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp hg
  have hp_eq : ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hsplit : modelAttachedFunction hk c ε r δ y =
        c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
      dsimp [modelAttachedFunction]
    nlinarith [hA, hsplit]
  have hf_ge : c - ε - δ / 2 ≤ morseNormalForm hk c y := by
    have hcap : ‖negPart hk y‖ ^ 2 - 2 * ε - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      smoothCap_ge_sub_two_mul_eps (ε := ε) (δ := δ) hδ
    have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
      morseNormalForm_split hk c y
    rw [hf, hp_eq]
    nlinarith [hcap]
  have hf_gt : c - ε - η + ε₀ < morseNormalForm hk c y := by nlinarith [hf_ge, hact]
  have hEq := modelLevelDampedUnstretch_eq_unstretch hk ε r δ c η ε₀ hε₀ y (le_of_lt hf_gt)
  rw [hEq]
  exact modelAttachedFunction_unstretch_boundary hk c ε r δ hδ hδr y hy hA

theorem modelLevelDampedUnstretch_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (η ε₀ : ℝ)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hg : modelRoundedFunction hk c ε r δ R₀ R₁ y < c) :
    morseNormalForm hk c (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) < c + r ^ 2 / 2 := by
  have hle := modelLevelDampedUnstretch_f_le_unstretch_f hk c ε r δ η ε₀ (le_of_lt hε) hδ hδr y
  have hA : modelAttachedFunction hk c ε r δ y < c :=
    (modelRoundedFunction_lt_c_iff_attachedFunction_lt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig y).mp hg
  have hstrict := modelAttachedFunction_unstretch_strict hk c ε r δ hδ hδr y hy hA
  exact lt_of_le_of_lt hle hstrict

theorem modelAttachedStretch_mem_roundedSublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0) {u : MorseModel n} (hu : morseNormalForm hk c u ≤ c + r ^ 2 / 2) :
    modelRoundedFunction hk c ε r δ R₀ R₁ (modelAttachedStretch hk ε r δ u) ≤ c := by
  have huatt : modelAttachedStretch hk ε r δ u ∈ modelAttachedRegion hk ε r δ :=
    (modelAttachedStretch_equiv hk c ε r δ hδ hδr hr).1 u hu
  exact (modelRoundedFunction_le_c_iff_mem_attachedRegion hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig
    (modelAttachedStretch hk ε r δ u)).mpr huatt

theorem modelAttachedStretch_boundary_of_roundedSublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0) {u : MorseModel n} (hu : morseNormalForm hk c u = c + r ^ 2 / 2) :
    modelRoundedFunction hk c ε r δ R₀ R₁ (modelAttachedStretch hk ε r δ u) = c := by
  have hA : modelAttachedFunction hk c ε r δ (modelAttachedStretch hk ε r δ u) = c :=
    modelAttachedFunction_stretch_boundary hk c ε r δ hδ hδr hr u hu
  exact (modelRoundedFunction_eq_c_iff_attachedFunction_eq hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig
    (modelAttachedStretch hk ε r δ u)).mpr hA

theorem modelAttachedStretch_strict_of_roundedSublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0) {u : MorseModel n} (hu : morseNormalForm hk c u < c + r ^ 2 / 2) :
    modelRoundedFunction hk c ε r δ R₀ R₁ (modelAttachedStretch hk ε r δ u) < c := by
  have hA : modelAttachedFunction hk c ε r δ (modelAttachedStretch hk ε r δ u) < c :=
    modelAttachedFunction_stretch_strict hk c ε r δ hδ hδr hr u hu
  exact (modelRoundedFunction_lt_c_iff_attachedFunction_lt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig
    (modelAttachedStretch hk ε r δ u)).mpr hA

noncomputable def modelAttachedUnstretchTime {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : ℝ :=
  ‖posPart hk y‖ ^ 2 * (1 - (‖negPart hk y‖ ^ 2 + r ^ 2) /
    smoothCap ε r δ (‖negPart hk y‖ ^ 2)) / 2

theorem modelAttachedUnstretch_eq_modelFlow {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    modelAttachedUnstretch hk ε r δ y =
      modelFlow hk (modelAttachedUnstretchTime hk ε r δ y) y := by
  let sc : ℝ := smoothCap ε r δ (‖negPart hk y‖ ^ 2)
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hsc : 0 < sc := by
    dsimp [sc]
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  by_cases hp : ‖posPart hk y‖ = 0
  · have hp0 : posPart hk y = 0 := norm_eq_zero.mp hp
    dsimp [modelAttachedUnstretch, modelFlow, modelAttachedUnstretchTime]
    rw [hp0]
    simp
  · have hpn : ‖posPart hk y‖ ≠ 0 := hp
    have hp2 : ‖posPart hk y‖ ^ 2 ≠ 0 := pow_ne_zero 2 hpn
    apply congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => recombine hk (negPart hk y) v)
    dsimp [modelAttachedUnstretch, modelFlow, modelAttachedUnstretchTime, sc, t]
    have harg : 1 - 2 * (‖posPart hk y‖ ^ 2 * (1 - (t + r ^ 2) / sc) / 2) / ‖posPart hk y‖ ^ 2 =
        (t + r ^ 2) / sc := by
      field_simp [hp2, ne_of_gt hsc]
      ring
    rw [harg]

noncomputable def modelLevelDampedUnstretchTime {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (y : MorseModel n) : ℝ :=
  ‖posPart hk y‖ ^ 2 * (1 - (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
    smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
      Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2) / 2

theorem modelLevelDampedUnstretch_eq_modelFlow {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    modelLevelDampedUnstretch hk ε r δ c η ε₀ y =
      modelFlow hk (modelLevelDampedUnstretchTime hk ε r δ c η ε₀ y) y := by
  let S : ℝ := 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
    smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
      Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)
  by_cases hp : ‖posPart hk y‖ = 0
  · have hp0 : posPart hk y = 0 := norm_eq_zero.mp hp
    dsimp [modelLevelDampedUnstretch, modelFlow, modelLevelDampedUnstretchTime, S]
    rw [hp0]
    simp
  · have hpn : ‖posPart hk y‖ ≠ 0 := hp
    have hp2 : ‖posPart hk y‖ ^ 2 ≠ 0 := pow_ne_zero 2 hpn
    apply congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => recombine hk (negPart hk y) v)
    dsimp [modelLevelDampedUnstretch, modelFlow, modelLevelDampedUnstretchTime, S]
    have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
    have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
      have hle : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2) ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
          rw [max_le_iff]
          constructor <;> nlinarith [sq_nonneg ‖negPart hk y‖]
        exact le_trans (smoothCap_le_max (ε := ε) (r := r) (δ := δ)
          (t := ‖negPart hk y‖ ^ 2) hε hδ0) hmax
      have hr2 : 0 < r ^ 2 := by nlinarith [hδ0, hδr]
      exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (div_nonneg (by nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ), hr2])
          (le_of_lt hsc))).2 (by
        norm_num
        rw [one_le_div hsc]
        nlinarith)
    have hS0 : 0 ≤ S := by
      have hσ0 : 0 ≤ Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) :=
        Real.smoothTransition.nonneg _
      dsimp [S]
      nlinarith
    have harg : 1 - 2 * (‖posPart hk y‖ ^ 2 * (1 - (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2) / 2) /
          ‖posPart hk y‖ ^ 2 =
        (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2 := by
      field_simp [hp2]
      ring
    rw [harg]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg hS0]

theorem modelLevelDampedUnstretchTime_zero_of_deep {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hε₀ : 0 < ε₀) (y : MorseModel n)
    (hy : morseNormalForm hk c y ≤ c - ε - η) :
    modelLevelDampedUnstretchTime hk ε r δ c η ε₀ y = 0 := by
  have hσ : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hε₀)
  dsimp [modelLevelDampedUnstretchTime]
  rw [hσ]
  ring

theorem modelLevelDampedUnstretchTime_eq_unstretchTime {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hε₀ : 0 < ε₀) (y : MorseModel n)
    (hy : c - ε - η + ε₀ ≤ morseNormalForm hk c y) :
    modelLevelDampedUnstretchTime hk ε r δ c η ε₀ y = modelAttachedUnstretchTime hk ε r δ y := by
  have hσ : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [one_le_div hε₀]
    nlinarith
  dsimp [modelLevelDampedUnstretchTime, modelAttachedUnstretchTime]
  rw [hσ]
  have hsqrt : (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 =
      (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
    Real.sq_sqrt (by
      have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ hδr
      have hr2 : 0 < r ^ 2 := by nlinarith [hδ, hδr]
      exact div_nonneg (by positivity) (le_of_lt hsc))
  have hfac : 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) * 1 =
      Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
    ring
  rw [hfac]
  rw [hsqrt]

theorem contDiff_modelLevelDampedUnstretchTime {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hδ : 0 < δ) (hδr : δ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLevelDampedUnstretchTime hk ε r δ c η ε₀) := by
  have hnormPos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin (n - k), (posPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    fun_prop
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) :=
    hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hcap_pos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    intro y
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ hδr
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    hden.div hcap (by intro y; exact ne_of_gt (hcap_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) :=
    harg.sqrt (by
      intro y
      have hr2 : 0 < r ^ 2 := by nlinarith [hδ, hδr]
      exact ne_of_gt (div_pos (by positivity) (hcap_pos y)))
  have hnf : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y) := by
    have hsplit : (fun y : MorseModel n => morseNormalForm hk c y) =
        fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
      funext y
      exact morseNormalForm_split hk c y
    rw [hsplit]
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c)).add
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 / 2 : ℝ))).mul
        (hnormPos.sub hnormNeg))
  have hσarg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (morseNormalForm hk c y - c + ε + η) / ε₀) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => morseNormalForm hk c y - c + ε + η) := by
      have h' : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : MorseModel n => morseNormalForm hk c y - (c - ε - η)) :=
        hnf.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c - ε - η))
      convert h' using 1
      ext y
      ring
    exact hlin.div_const ε₀
  have hσ : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.smoothTransition
        ((morseNormalForm hk c y - c + ε + η) / ε₀)) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hσarg
  have hS : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) := by
    simpa [mul_assoc] using
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).add
        ((hsqrt.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ)))).mul hσ))
  have hSsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2) :=
    hS.pow 2
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
    ‖posPart hk y‖ ^ 2 * (1 - (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2) / 2)
  exact (hnormPos.mul ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).sub hSsq)).div_const 2

theorem modelAttachedUnstretchTime_eq_of_negPart_large {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) {y : MorseModel n} (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelAttachedUnstretchTime hk ε r δ y =
      -‖posPart hk y‖ ^ 2 * (r ^ 2 + 2 * ε) / (2 * (‖negPart hk y‖ ^ 2 - 2 * ε)) := by
  dsimp [modelAttachedUnstretchTime]
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
    smoothCap_upper hδ0 ht
  have hne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by nlinarith [ht, hδ0]
  rw [hsc]
  field_simp [hne]
  ring

theorem modelAttachedUnstretchTime_eq_boundary {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) {y : MorseModel n}
    (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2)
    (hp : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε) :
    modelAttachedUnstretchTime hk ε r δ y = -(r ^ 2 + 2 * ε) / 2 := by
  rw [modelAttachedUnstretchTime_eq_of_negPart_large hk ε r δ hδ0 ht, hp]
  have hpos : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by nlinarith [ht, hδ0]
  field_simp [hpos]

theorem modelAttachedUnstretchTime_neg_of_posPart_ne_zero {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hpos : ‖posPart hk y‖ ≠ 0) (hneg : ‖negPart hk y‖ ≠ 0) :
    modelAttachedUnstretchTime hk ε r δ y < 0 := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  let b : ℝ := ‖posPart hk y‖ ^ 2
  let sc : ℝ := smoothCap ε r δ t
  have htpos : 0 < t := by
    dsimp [t]
    exact sq_pos_of_ne_zero hneg
  have hbpos : 0 < b := by
    dsimp [b]
    exact sq_pos_of_ne_zero hpos
  have hscpos : 0 < sc := by
    dsimp [sc]
    exact smoothCap_pos hδ hδr
  have hβ : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hsc_lt : sc < t + r ^ 2 := by
    dsimp [sc, smoothCap]
    by_cases hβ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) = 1
    · rw [hβ1]
      have hpos : 0 < t - (t - 2 * ε - r ^ 2) := by nlinarith [hδr]
      nlinarith [hpos]
    · have hβlt1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) < 1 :=
        lt_of_le_of_ne hβ.2 hβ1
      have h1 : 0 < t * (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) := by
        exact mul_pos htpos (sub_pos.mpr hβlt1)
      have h2 : 0 ≤ (2 * ε + r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) := by
        exact mul_nonneg (by nlinarith [hδr]) hβ.1
      nlinarith
  have hratio_gt : 1 < (t + r ^ 2) / sc := by
    exact (one_lt_div hscpos).2 hsc_lt
  dsimp [modelAttachedUnstretchTime]
  have hneg : 1 - (t + r ^ 2) / sc < 0 := by linarith
  have hmain : b * (1 - (t + r ^ 2) / sc) < 0 := by
    exact mul_neg_of_pos_of_neg hbpos hneg
  nlinarith

theorem modelAttachedUnstretchTime_abs_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelAttachedRegion hk ε r δ) :
    |modelAttachedUnstretchTime hk ε r δ y| ≤ (2 * ε + r ^ 2 + δ) / 2 := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  let b : ℝ := ‖posPart hk y‖ ^ 2
  let sc : ℝ := smoothCap ε r δ t
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hscpos : 0 < sc := by
    dsimp [sc]
    exact smoothCap_pos hδ hδr
  have hbsc : b ≤ sc := by
    dsimp [b, sc]
    exact hy
  have hβ : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hcap_le : sc ≤ t + r ^ 2 := by
    dsimp [sc, smoothCap]
    have h1 : 0 ≤ t * (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) := by
      exact mul_nonneg ht0 (sub_nonneg.mpr hβ.2)
    have h2 : 0 ≤ (2 * ε + r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) := by
      exact mul_nonneg (by nlinarith [hδr]) hβ.1
    nlinarith
  have hdiff_le : t + r ^ 2 - sc ≤ 2 * ε + r ^ 2 + δ := by
    dsimp [sc, smoothCap]
    by_cases hβ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) = 1
    · rw [hβ1]
      nlinarith [hδr]
    · have hβlt1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) < 1 :=
        lt_of_le_of_ne hβ.2 hβ1
      have harglt : t < r ^ 2 + 2 * ε + δ := by
        by_contra hnot
        have hge : r ^ 2 + 2 * ε + δ ≤ t := le_of_not_gt hnot
        have harg1 : 1 ≤ (t - (r ^ 2 + 2 * ε - δ)) / (2 * δ) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]
          nlinarith
        exact hβ1 (Real.smoothTransition.eq_one_iff_one_le.mpr harg1)
      have hle1 : t - 2 * ε - r ^ 2 ≤ δ := by nlinarith [harglt]
      have hmul : (t - 2 * ε - r ^ 2) * (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) ≤ δ := by
        have hpos : 0 ≤ 1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
          sub_nonneg.mpr hβ.2
        have hmul' : (t - 2 * ε - r ^ 2) * (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) ≤
            δ * (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) := by
          exact mul_le_mul_of_nonneg_right hle1 hpos
        have hle2 : δ * (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) ≤ δ := by
          have hnonneg : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
            Real.smoothTransition.nonneg _
          nlinarith
        exact le_trans hmul' hle2
      nlinarith
  have hmain : b * ((t + r ^ 2) / sc - 1) ≤ 2 * ε + r ^ 2 + δ := by
    have hb : b * ((t + r ^ 2) / sc - 1) ≤ sc * ((t + r ^ 2) / sc - 1) := by
      have hdiff0 : 0 ≤ (t + r ^ 2) / sc - 1 := by
        rw [le_sub_iff_add_le]
        rw [le_div_iff₀ hscpos]
        nlinarith [hcap_le]
      exact mul_le_mul_of_nonneg_right hbsc hdiff0
    have hsc : sc * ((t + r ^ 2) / sc - 1) = t + r ^ 2 - sc := by
      field_simp [ne_of_gt hscpos]
    nlinarith [hb, hsc, hdiff_le]
  dsimp [modelAttachedUnstretchTime]
  have harg : b * (1 - (t + r ^ 2) / sc) / 2 = -(b * ((t + r ^ 2) / sc - 1) / 2) := by ring
  rw [harg]
  rw [abs_neg]
  rw [abs_div]
  have hbabs : |b * ((t + r ^ 2) / sc - 1)| = b * ((t + r ^ 2) / sc - 1) := by
    rw [abs_of_nonneg]
    have hdiff0 : 0 ≤ (t + r ^ 2) / sc - 1 := by
      rw [le_sub_iff_add_le]
      rw [le_div_iff₀ hscpos]
      nlinarith [hcap_le]
    exact mul_nonneg hb0 hdiff0
  rw [hbabs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  nlinarith [hmain]

theorem contDiff_modelAttachedUnstretchTime {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ : 0 < δ) (hδr : δ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedUnstretchTime hk ε r δ) := by
  have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) :=
    contDiff_posPart_normSq hk
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) :=
    contDiff_negPart_normSq hk
  have hsc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hneg
  have hsc0 : ∀ y : MorseModel n, smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≠ 0 := by
    intro y
    exact ne_of_gt (smoothCap_pos (ε := ε) (r := r) (δ := δ)
      (t := ‖negPart hk y‖ ^ 2) hδ hδr)
  have hratio : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
    exact (hneg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))).div hsc hsc0
  have hone : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ)) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ)))
  have hmain : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n =>
        ‖posPart hk y‖ ^ 2 * (1 - (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) / 2) := by
    exact ((hpos.mul (hone.sub hratio)).div
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (2 : ℝ)))
      (fun _ : MorseModel n => (by norm_num : (2 : ℝ) ≠ 0)))
  simpa [modelAttachedUnstretchTime] using hmain

theorem fderiv_morseNormalForm_modelFlowField {n k : ℕ} (hk : k ≤ n) (c : ℝ) {y : MorseModel n}
    (hpos : ‖posPart hk y‖ ≠ 0) :
    fderiv ℝ (morseNormalForm hk c) y (modelFlowField hk y) = -1 := by
  have hdiff : DifferentiableAt ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y := by
    exact (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y := by
    exact (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfderiv : fderiv ℝ (morseNormalForm hk c) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
        fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y) := by
    have hmain : (fun z : MorseModel n =>
        c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) =
        morseNormalForm hk c := by
      funext z
      exact (morseNormalForm_split hk c z).symm
    rw [← hmain]
    rw [fderiv_const_add]
    have hsub : DifferentiableAt ℝ (fun z : MorseModel n =>
        ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y := hdiff.sub hdiffNeg
    have hmul : fderiv ℝ (fun z : MorseModel n =>
        (1 / 2 : ℝ) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) y =
        (1 / 2 : ℝ) • fderiv ℝ (fun z : MorseModel n =>
          ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y :=
      fderiv_const_mul hsub (1 / 2 : ℝ)
    rw [hmul]
    congr 1
    exact fderiv_sub (f := fun z : MorseModel n => ‖posPart hk z‖ ^ 2)
      (g := fun z : MorseModel n => ‖negPart hk z‖ ^ 2)
      (hf := hdiff) (hg := hdiffNeg)
  let w : MorseModel n := modelFlowField hk y
  have hposPart : posPart hk w = -(‖posPart hk y‖ ^ 2)⁻¹ • posPart hk y := by
    simpa [w] using posPart_modelFlowField hk y
  have hnegPart : negPart hk w = 0 := by
    simpa [w] using negPart_modelFlowField hk y
  have hA : fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y w = -2 := by
    rw [fderiv_posPart_normSq hk y w]
    rw [hposPart]
    have hterm : ∀ j : Fin (n - k), (posPart hk y j) *
        (-(‖posPart hk y‖ ^ 2)⁻¹ • posPart hk y) j =
        -(‖posPart hk y‖ ^ 2)⁻¹ * (posPart hk y j) ^ 2 := by
      intro j
      have hsmul : (-(‖posPart hk y‖ ^ 2)⁻¹ • posPart hk y) j =
          -(‖posPart hk y‖ ^ 2)⁻¹ * (posPart hk y j) := by
        rfl
      rw [hsmul]
      ring
    have hsum : ∑ j : Fin (n - k), (posPart hk y j) *
        (-(‖posPart hk y‖ ^ 2)⁻¹ • posPart hk y) j =
        -(‖posPart hk y‖ ^ 2)⁻¹ * ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm j)
    rw [hsum]
    have hsq : ∑ j : Fin (n - k), (posPart hk y j) ^ 2 = ‖posPart hk y‖ ^ 2 := by
      exact (EuclideanSpace.real_norm_sq_eq (posPart hk y)).symm
    rw [hsq]
    have hne : ‖posPart hk y‖ ^ 2 ≠ 0 := pow_ne_zero 2 hpos
    field_simp [hne]
  have hB : fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y w = 0 := by
    rw [fderiv_negPart_normSq hk y w]
    rw [hnegPart]
    simp
  rw [hfderiv]
  change ((1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
    fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y)) w = -1
  rw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.sub_apply, hA, hB]
  rw [smul_eq_mul]
  norm_num

theorem contMDiff_modelAttachedUnstretch_sublevel {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c) :=
      sublevelChartedSpace (m := m) (modelRoundedFunction hk c ε r δ R₀ R₁) c
        (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
        (fun y hy => fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c,
      hcs₁.chartAt y =
        (if h : modelRoundedFunction hk c ε r δ R₀ R₁ y.1 = c then
          sublevelBoundaryChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y h
            (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
            (fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y.1 h)
        else sublevelInteriorChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y
          (lt_of_le_of_ne (show modelRoundedFunction hk c ε r δ R₀ R₁ y.1 ≤ c from y.2) h)
          (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c =>
        (⟨modelAttachedUnstretch hk ε r δ y.1,
          modelAttachedUnstretch_mem_upper_of_roundedSublevel hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig
            hr y.2⟩ :
          SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2))) := by
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (modelAttachedUnstretch hk ε r δ) Set.univ :=
    contDiffOn_univ.mpr (contDiff_modelAttachedUnstretch hk ε r δ hδ hδr hr)
  exact contMDiff_sublevelMap_on (m := m) (modelRoundedFunction hk c ε r δ R₀ R₁)
    (morseNormalForm hk c) c (c + r ^ 2 / 2)
    (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁) (contDiff_morseNormalForm hk c)
    (fun y hy => fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hy)
    (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (modelAttachedUnstretch hk ε r δ) Set.univ isOpen_univ (fun y hy => trivial) hΦ
    (fun y hy => modelAttachedUnstretch_mem_upper_of_roundedSublevel hk c ε r δ R₀ R₁
      hε hδ hδr hR hR0 hbig hr hy)
    (fun y hy => modelAttachedUnstretch_boundary_of_roundedSublevel hk c ε r δ R₀ R₁
      hε hδ hδr hR hR0 hbig hy)
    (fun y hy => modelAttachedUnstretch_strict_of_roundedSublevel hk c ε r δ R₀ R₁
      hε hδ hδr hR hR0 hbig hy)
    (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem contMDiff_modelAttachedStretch_sublevel {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c) :=
      sublevelChartedSpace (m := m) (modelRoundedFunction hk c ε r δ R₀ R₁) c
        (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
        (fun y hy => fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hy))
    (hchart₁ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₁.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c,
      hcs₂.chartAt y =
        (if h : modelRoundedFunction hk c ε r δ R₀ R₁ y.1 = c then
          sublevelBoundaryChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y h
            (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
            (fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y.1 h)
        else sublevelInteriorChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y
          (lt_of_le_of_ne (show modelRoundedFunction hk c ε r δ R₀ R₁ y.1 ≤ c from y.2) h)
          (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun u : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2) =>
        (⟨modelAttachedStretch hk ε r δ u.1,
          modelAttachedStretch_mem_roundedSublevel hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig hr u.2⟩ :
          SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c)) := by
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (modelAttachedStretch hk ε r δ) Set.univ :=
    contDiffOn_univ.mpr (contDiff_modelAttachedStretch hk ε r δ hδ hδr hr)
  exact contMDiff_sublevelMap_on (m := m) (morseNormalForm hk c)
    (modelRoundedFunction hk c ε r δ R₀ R₁) (c + r ^ 2 / 2) c
    (contDiff_morseNormalForm hk c) (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
    (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (fun y hy => fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hy)
    (modelAttachedStretch hk ε r δ) Set.univ isOpen_univ (fun y hy => trivial) hΦ
    (fun u hu => modelAttachedStretch_mem_roundedSublevel hk c ε r δ R₀ R₁
      hε hδ hδr hR hR0 hbig hr hu)
    (fun u hu => modelAttachedStretch_boundary_of_roundedSublevel hk c ε r δ R₀ R₁
      hε hδ hδr hR hR0 hbig hr hu)
    (fun u hu => modelAttachedStretch_strict_of_roundedSublevel hk c ε r δ R₀ R₁
      hε hδ hδr hR hR0 hbig hr hu)
    (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

noncomputable def modelRoundedSublevelDiffeomorphUpper {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c) :=
      sublevelChartedSpace (m := m) (modelRoundedFunction hk c ε r δ R₀ R₁) c
        (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
        (fun y hy => fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c,
      hcs₁.chartAt y =
        (if h : modelRoundedFunction hk c ε r δ R₀ R₁ y.1 = c then
          sublevelBoundaryChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y h
            (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
            (fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y.1 h)
        else sublevelInteriorChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y
          (lt_of_le_of_ne (show modelRoundedFunction hk c ε r δ R₀ R₁ y.1 ≤ c from y.2) h)
          (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c) _ hcs₁
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) _ hcs₂
      (⊤ : ℕ∞) where
  toEquiv :=
    { toFun := fun y => (⟨modelAttachedUnstretch hk ε r δ y.1,
        modelAttachedUnstretch_mem_upper_of_roundedSublevel hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig
          hr y.2⟩ :
          SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2))
      invFun := fun u => (⟨modelAttachedStretch hk ε r δ u.1,
        modelAttachedStretch_mem_roundedSublevel hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig hr u.2⟩ :
          SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c)
      left_inv := by
        intro y
        apply Subtype.ext
        exact modelAttachedStretch_unstretch hk ε r δ hδ hδr hr y.1
      right_inv := by
        intro u
        apply Subtype.ext
        exact modelAttachedUnstretch_stretch hk ε r δ hδ hδr hr u.1 }
  contMDiff_toFun := by
    simpa using (contMDiff_modelAttachedUnstretch_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (R₀ := R₀) (R₁ := R₁) (hε := hε) (hδ := hδ) (hδr := hδr) (hR := hR) (hR0 := hR0)
      (hbig := hbig) (hr := hr) (hcs₁ := hcs₁) (hcs₂ := hcs₂)
      (hchart₁ := hchart₁) (hchart₂ := hchart₂))
  contMDiff_invFun := by
    simpa using (contMDiff_modelAttachedStretch_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (R₀ := R₀) (R₁ := R₁) (hε := hε) (hδ := hδ) (hδr := hδr) (hR := hR) (hR0 := hR0)
      (hbig := hbig) (hr := hr) (hcs₁ := hcs₂) (hcs₂ := hcs₁)
      (hchart₁ := hchart₂) (hchart₂ := hchart₁))

noncomputable def modelRoundedSublevelDiffeomorphModified {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c) :=
      sublevelChartedSpace (m := m) (modelRoundedFunction hk c ε r δ R₀ R₁) c
        (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
        (fun y hy => fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hcs₃ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c,
      hcs₁.chartAt y =
        (if h : modelRoundedFunction hk c ε r δ R₀ R₁ y.1 = c then
          sublevelBoundaryChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y h
            (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)
            (fderiv_modelRoundedFunction_ne_zero hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig y.1 h)
        else sublevelInteriorChart (modelRoundedFunction hk c ε r δ R₀ R₁) c y
          (lt_of_le_of_ne (show modelRoundedFunction hk c ε r δ R₀ R₁ y.1 ≤ c from y.2) h)
          (contDiff_modelRoundedFunction hk c ε r δ R₀ R₁)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₂.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl)
    (hchart₃ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₃.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (modelRoundedFunction hk c ε r δ R₀ R₁) c) _ hcs₁
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) _ hcs₂
      (⊤ : ℕ∞) :=
  (modelRoundedSublevelDiffeomorphUpper hk c ε r δ R₀ R₁ hε hδ hδr hR hR0 hbig hr
    (hcs₁ := hcs₁) (hcs₂ := hcs₃) (hchart₁ := hchart₁) (hchart₂ := hchart₃)).trans
    (modelModifiedSublevelDiffeomorph hk c ε r δ hε hδ hr
      (hcs₁ := hcs₂) (hcs₂ := hcs₃) (hchart₁ := hchart₂) (hchart₂ := hchart₃)).symm

theorem contDiffOn_modelFlowField_of_posPart_ne_zero {n k : ℕ} (hk : k ≤ n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelFlowField hk)
      {y : MorseModel n | posPart hk y ≠ 0} := by
  intro y hy
  have hpos : ‖posPart hk y‖ ≠ 0 := by
    intro hz
    exact hy (norm_eq_zero.mp hz)
  have hsq : ‖posPart hk y‖ ^ 2 ≠ 0 := pow_ne_zero 2 hpos
  have hns : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y := by
    exact (contDiff_posPart_normSq hk).contDiffAt
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel n => (‖posPart hk z‖ ^ 2)⁻¹) y := by
    exact hns.inv (by
      intro hz
      exact hsq (congrArg (fun t : ℝ => t) hz))
  have hsmul : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => -(‖posPart hk z‖ ^ 2)⁻¹ • posPart hk z) y := by
    have hneg : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel n => -(‖posPart hk z‖ ^ 2)⁻¹) y :=
      hinv.neg
    exact hneg.smul (posPartCLM hk).contDiff.contDiffAt
  have hrec : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := recombine_contDiff_generic hk
  have hmain : ContDiffAt ℝ (⊤ : ℕ∞) (modelFlowField hk) y := by
    dsimp [modelFlowField]
    exact (ContDiff.contDiffAt hrec).comp y (by
      have hzero : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel n => (0 : EuclideanSpace ℝ (Fin k))) y :=
        contDiffAt_const
      exact hzero.prodMk hsmul)
  exact hmain.contDiffWithinAt

theorem contMDiffOn_modelFlowField_section {n k : ℕ} (hk : k ≤ n) :
    ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n).tangent (⊤ : ℕ∞)
      (fun y : MorseModel n => (⟨y, modelFlowField hk y⟩ : TangentBundle 𝓘(ℝ, MorseModel n) (MorseModel n)))
      {y : MorseModel n | posPart hk y ≠ 0} := by
  intro y₀ hy₀
  have hsecAt : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n).tangent (⊤ : ℕ∞)
      (fun y : MorseModel n => (⟨y, modelFlowField hk y⟩ : TangentBundle 𝓘(ℝ, MorseModel n) (MorseModel n))) y₀ := by
    rw [Bundle.Trivialization.contMDiffAt_section_iff
      (e := trivializationAt (MorseModel n) (TangentSpace 𝓘(ℝ, MorseModel n)) y₀)
      (by
        rw [TangentBundle.trivializationAt_baseSet]
        exact mem_chart_source (H := MorseModel n) (M := MorseModel n) y₀)]
    have hfib : (fun y : MorseModel n => (trivializationAt (MorseModel n) (TangentSpace 𝓘(ℝ, MorseModel n)) y₀
        (⟨y, modelFlowField hk y⟩ : TangentBundle 𝓘(ℝ, MorseModel n) (MorseModel n))).2) =ᶠ[nhds y₀]
        (fun y : MorseModel n => modelFlowField hk y) := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      simp
    have hwOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (⊤ : ℕ∞)
        (modelFlowField hk) {y : MorseModel n | posPart hk y ≠ 0} := by
      exact contMDiffOn_iff_contDiffOn.mpr (contDiffOn_modelFlowField_of_posPart_ne_zero hk)
    have hwAt : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (⊤ : ℕ∞)
        (modelFlowField hk) y₀ := by
      have hopen : IsOpen {y : MorseModel n | posPart hk y ≠ 0} :=
        isOpen_ne.preimage (continuous_posPart hk)
      exact hwOn.contMDiffAt (hopen.mem_nhds hy₀)
    exact hwAt.congr_of_eventuallyEq hfib
  exact hsecAt.contMDiffWithinAt

end DifferentialGeometry.Topology.Morse.CellAttachment
