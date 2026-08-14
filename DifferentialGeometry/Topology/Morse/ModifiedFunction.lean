import DifferentialGeometry.Topology.Morse.CellAttachment
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace DifferentialGeometry.Topology.Morse.CellAttachment

open Filter Set
open scoped Topology BigOperators ContDiff

noncomputable section

def modMu (ε : ℝ) : ℝ → ℝ := fun t => (3 / 2 * ε) * (1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε)))

def modGamma (δ : ℝ) : ℝ → ℝ := fun s => 1 - Real.smoothTransition ((2 * s - δ) / δ)

def negPartCLM {n k : ℕ} (hk : k ≤ n) : MorseModel n →L[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun := fun y => negPart hk y
  map_add' := by
    intro x y
    ext i
    simp [negPart]
  map_smul' := by
    intro a x
    ext i
    simp [negPart]
  cont := by
    have h : Continuous (fun y : MorseModel n => (fun i : Fin k => y (negIdx hk i))) :=
      continuous_pi (fun i => continuous_apply (negIdx hk i))
    exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)).comp h

def posPartCLM {n k : ℕ} (hk : k ≤ n) : MorseModel n →L[ℝ] EuclideanSpace ℝ (Fin (n - k)) where
  toFun := fun y => posPart hk y
  map_add' := by
    intro x y
    ext i
    simp [posPart]
  map_smul' := by
    intro a x
    ext i
    simp [posPart]
  cont := by
    have h : Continuous (fun y : MorseModel n => (fun i : Fin (n - k) => y (posIdx hk i))) :=
      continuous_pi (fun i => continuous_apply (posIdx hk i))
    exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin (n - k) => ℝ)).comp h

def negBasis {n k : ℕ} (hk : k ≤ n) (i : Fin k) : MorseModel n :=
  fun r => if r = negIdx hk i then (1 : ℝ) else 0

def negUnit {k : ℕ} (i : Fin k) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp (p := 2) (fun j : Fin k => if j = i then (1 : ℝ) else 0)

theorem negPart_negBasis {n k : ℕ} (hk : k ≤ n) (i : Fin k) :
    negPart hk (negBasis hk i) = negUnit i := by
  ext j
  change (if negIdx hk j = negIdx hk i then (1 : ℝ) else 0) =
      (if j = i then (1 : ℝ) else 0)
  by_cases h : i = j
  · have hz : negIdx hk j = negIdx hk i := by rw [h]
    simp [h, hz]
  · have h' : negIdx hk j ≠ negIdx hk i := by
      intro hz
      exact h (Fin.castLE_injective hk hz).symm
    have hc2 : ¬(j = i) := fun hj => h hj.symm
    rw [if_neg h', if_neg hc2]

theorem posPart_negBasis {n k : ℕ} (hk : k ≤ n) (i : Fin k) :
    posPart hk (negBasis hk i) = 0 := by
  ext j
  simp only [negBasis, posPart]
  have h : posIdx hk j ≠ negIdx hk i := by
    intro hz
    have hval : (posIdx hk j).val = (negIdx hk i).val := congrArg Fin.val hz
    dsimp [posIdx, negIdx] at hval
    omega
  rw [if_neg h]
  rfl

def posBasis {n k : ℕ} (hk : k ≤ n) (j : Fin (n - k)) : MorseModel n :=
  fun r => if r = posIdx hk j then (1 : ℝ) else 0

def posUnit {m : ℕ} (j : Fin m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp (p := 2) (fun i : Fin m => if i = j then (1 : ℝ) else 0)

def modifiedNormalForm {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) : ℝ :=
  morseNormalForm hk c y - modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ (‖posPart hk y‖)

theorem negPart_posBasis {n k : ℕ} (hk : k ≤ n) (j : Fin (n - k)) :
    negPart hk (posBasis hk j) = 0 := by
  ext i
  simp only [negPart, posBasis]
  have h : posIdx hk j ≠ negIdx hk i := by
    intro hz
    have hval : (posIdx hk j).val = (negIdx hk i).val := congrArg Fin.val hz
    dsimp [posIdx, negIdx] at hval
    omega
  have h' : ¬(negIdx hk i = posIdx hk j) := by
    intro hz
    exact h hz.symm
  rw [if_neg h']
  rfl

theorem posPart_posBasis {n k : ℕ} (hk : k ≤ n) (j : Fin (n - k)) :
    posPart hk (posBasis hk j) = posUnit j := by
  ext i
  simp only [posPart, posBasis, posUnit]
  by_cases h : i = j
  · have hz : posIdx hk j = posIdx hk i := by rw [h]
    rw [if_pos hz.symm, if_pos h]
  · have h' : posIdx hk j ≠ posIdx hk i := by
      intro hz
      have hval : (posIdx hk j).val = (posIdx hk i).val := congrArg Fin.val hz
      dsimp [posIdx] at hval
      omega
    rw [if_neg h'.symm, if_neg h]

lemma posPart_add_smul_pos {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) (h : ℝ)
    (j : Fin (n - k)) :
    posPart hk (y + h • posBasis hk j) = posPart hk y + h • posUnit j := by
  change posPartCLM hk (y + h • posBasis hk j) =
      posPartCLM hk y + h • posUnit j
  rw [map_add, map_smul]
  have hpos : posPartCLM hk (posBasis hk j) = posUnit j := by
    simpa using (posPart_posBasis hk j)
  rw [hpos]

lemma negPart_add_smul_pos {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) (h : ℝ)
    (j : Fin (n - k)) :
    negPart hk (y + h • posBasis hk j) = negPart hk y := by
  change negPartCLM hk (y + h • posBasis hk j) = negPartCLM hk y
  rw [map_add, map_smul]
  have hneg : negPartCLM hk (posBasis hk j) = 0 := by
    simpa using (negPart_posBasis hk j)
  rw [hneg, smul_zero, add_zero]

theorem modMu_const {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 2 * ε) : modMu ε t = 3 / 2 * ε := by
  dsimp [modMu]
  have h : (t - 2 * ε) / (2 * ε) ≤ 0 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * ε)]
    nlinarith
  rw [Real.smoothTransition.zero_of_nonpos h]
  ring

theorem modMu_zero {ε t : ℝ} (hε : 0 < ε) (ht : 4 * ε ≤ t) : modMu ε t = 0 := by
  dsimp [modMu]
  have h : 1 ≤ (t - 2 * ε) / (2 * ε) := by
    rw [one_le_div (by positivity : 0 < 2 * ε)]
    nlinarith
  rw [Real.smoothTransition.one_of_one_le h]
  ring

theorem modMu_nonneg {ε t : ℝ} (hε : 0 ≤ ε) : 0 ≤ modMu ε t := by
  dsimp [modMu]
  have h1 : 0 ≤ Real.smoothTransition ((t - 2 * ε) / (2 * ε)) := Real.smoothTransition.nonneg _
  have h2 : Real.smoothTransition ((t - 2 * ε) / (2 * ε)) ≤ 1 := Real.smoothTransition.le_one _
  nlinarith

theorem modMu_antitone {ε : ℝ} (hε : 0 ≤ ε) : AntitoneOn (modMu ε) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  dsimp [modMu]
  have hmono : (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) a ≤
      (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) b := by
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε))
  have hmono' : 1 - Real.smoothTransition ((b - 2 * ε) / (2 * ε)) ≤
      1 - Real.smoothTransition ((a - 2 * ε) / (2 * ε)) := by linarith
  exact mul_le_mul_of_nonneg_left hmono' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hε)

theorem modGamma_one {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ δ / 2) : modGamma δ s = 1 := by
  dsimp [modGamma]
  have h : (2 * s - δ) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ]
    nlinarith
  rw [Real.smoothTransition.zero_of_nonpos h]
  norm_num

theorem modGamma_zero {δ s : ℝ} (hδ : 0 < δ) (hs : 3 * δ / 2 ≤ s) : modGamma δ s = 0 := by
  dsimp [modGamma]
  have h : 1 ≤ (2 * s - δ) / δ := by
    rw [one_le_div hδ]
    nlinarith
  rw [Real.smoothTransition.one_of_one_le h]
  norm_num

theorem modGamma_nonneg (δ s : ℝ) : 0 ≤ modGamma δ s := by
  dsimp [modGamma]
  have h1 : 0 ≤ Real.smoothTransition ((2 * s - δ) / δ) := Real.smoothTransition.nonneg _
  have h2 : Real.smoothTransition ((2 * s - δ) / δ) ≤ 1 := Real.smoothTransition.le_one _
  nlinarith

theorem modGamma_le_one (δ s : ℝ) : modGamma δ s ≤ 1 := by
  dsimp [modGamma]
  have h1 : 0 ≤ Real.smoothTransition ((2 * s - δ) / δ) := Real.smoothTransition.nonneg _
  nlinarith

theorem modGamma_antitone {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (modGamma δ) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  dsimp [modGamma]
  have hmono : (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) a ≤
      (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) b := by
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hδ)
  have hmono' : 1 - Real.smoothTransition ((2 * b - δ) / δ) ≤
      1 - Real.smoothTransition ((2 * a - δ) / δ) := by linarith
  exact hmono'

theorem modifiedNormalForm_le_f {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (hε : 0 < ε)
    (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y ≤ morseNormalForm hk c y := by
  dsimp [modifiedNormalForm]
  have h1 : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) :=
    modMu_nonneg (ε := ε) (t := ‖negPart hk y‖ ^ 2) (le_of_lt hε)
  have h2 : 0 ≤ modGamma δ ‖posPart hk y‖ := modGamma_nonneg δ _
  have h3 : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ := mul_nonneg h1 h2
  linarith

theorem modifiedNormalForm_sublevel_upper {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : 9 * δ ^ 2 < 4 * ε) :
    {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c + ε} =
      {y : MorseModel n | morseNormalForm hk c y ≤ c + ε} := by
  ext y
  constructor
  · intro hy
    by_contra hnot
    have hf : c + ε < morseNormalForm hk c y := lt_of_not_ge hnot
    have hcorr0 : modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ = 0 := by
      by_cases hs : 3 * δ / 2 ≤ ‖posPart hk y‖
      · have hγ : modGamma δ ‖posPart hk y‖ = 0 := modGamma_zero hδ hs
        simp [hγ]
      · have hs' : ‖posPart hk y‖ < 3 * δ / 2 := lt_of_not_ge hs
        have hsq : ‖posPart hk y‖ ^ 2 < ε := by
          have hs'' : ‖posPart hk y‖ ^ 2 < (3 * δ / 2) ^ 2 := by
            apply sq_lt_sq.mpr
            rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 3 * δ / 2)]
            exact hs'
          nlinarith [hs'', hδε]
        have hwell : morseNormalForm hk c y < c + ε := by
          have hsplit := morseNormalForm_split hk c y
          rw [hsplit]
          nlinarith [hsq, sq_nonneg ‖negPart hk y‖]
        exact False.elim (not_lt_of_ge hf.le hwell)
    have hg : modifiedNormalForm hk c ε δ y = morseNormalForm hk c y := by
      dsimp [modifiedNormalForm]
      simp [hcorr0]
    exact (not_lt_of_ge hy) (hg ▸ hf)
  · intro hy
    exact le_trans (modifiedNormalForm_le_f hk c ε δ hε y) hy

theorem modifiedNormalForm_cell_mem_lower {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (x : ClosedCell k) :
    modifiedNormalForm hk c ε δ (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤
      c - ε := by
  let y : MorseModel n := cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
  have hpos : posPart hk y = 0 := by
    ext j
    dsimp [y, posPart]
    exact cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) j
  have ht : ‖negPart hk y‖ ^ 2 ≤ 2 * ε := by
    have hle : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε) := by
      have hne : negPart hk y = (Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin k)) := by
        ext i
        dsimp [y, negPart]
        rw [cellMap_negIdx]
      rw [hne]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) x.2
    have hsq' : ‖negPart hk y‖ ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hle)
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)] at hsq'
    exact hsq'
  have hμ : modMu ε (‖negPart hk y‖ ^ 2) = 3 / 2 * ε := modMu_const hε ht
  have hγ : modGamma δ ‖posPart hk y‖ = 1 := by
    have hs : ‖posPart hk y‖ ≤ δ / 2 := by
      rw [hpos]
      simp only [norm_zero]
      exact le_of_lt (half_pos hδ)
    exact modGamma_one hδ hs
  have hf : morseNormalForm hk c y ≤ c := by
    dsimp [y]
    rw [morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))]
    have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
    rw [hsq]
    have hnorm : 0 ≤ ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 := sq_nonneg _
    nlinarith
  dsimp [modifiedNormalForm]
  rw [hμ, hγ]
  nlinarith [hε]

theorem differentiableAt_modMu {ε : ℝ} (x : ℝ) : DifferentiableAt ℝ (modMu ε) x := by
  have hst : DifferentiableAt ℝ Real.smoothTransition ((x - 2 * ε) / (2 * ε)) :=
    by
      have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
        Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
      exact (hc.contDiffAt (x := (x - 2 * ε) / (2 * ε))).differentiableAt (by norm_num)
  have hinner : DifferentiableAt ℝ (fun t : ℝ => (t - 2 * ε) / (2 * ε)) x := by
    fun_prop
  have hcomp : DifferentiableAt ℝ (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) x :=
    DifferentiableAt.comp (x := x) (g := Real.smoothTransition)
      (f := fun t : ℝ => (t - 2 * ε) / (2 * ε)) hst hinner
  have hone : DifferentiableAt ℝ (fun t : ℝ => 1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε))) x :=
    DifferentiableAt.sub (differentiableAt_const (1 : ℝ)) hcomp
  have hres : DifferentiableAt ℝ (fun t : ℝ =>
      (3 / 2 * ε) * (1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε)))) x :=
    hone.const_mul (3 / 2 * ε)
  simpa [modMu] using hres

theorem differentiableAt_modGamma {δ : ℝ} (x : ℝ) : DifferentiableAt ℝ (modGamma δ) x := by
  change DifferentiableAt ℝ (fun s : ℝ => 1 - Real.smoothTransition ((2 * s - δ) / δ)) x
  have hst : DifferentiableAt ℝ Real.smoothTransition ((2 * x - δ) / δ) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
    exact (hc.contDiffAt (x := (2 * x - δ) / δ)).differentiableAt (by norm_num)
  have hinner : DifferentiableAt ℝ (fun s : ℝ => (2 * s - δ) / δ) x := by
    fun_prop
  have hcomp : DifferentiableAt ℝ (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) x :=
    DifferentiableAt.comp (x := x) (g := Real.smoothTransition)
      (f := fun s : ℝ => (2 * s - δ) / δ) hst hinner
  have hc1 : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) x := differentiableAt_const (1 : ℝ)
  exact hc1.sub hcomp

private lemma fderiv_apply_eq_deriv_line {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : MorseModel n → F} {y e : MorseModel n}
    (hgdiff : DifferentiableAt ℝ g y) {D : F}
    (hline : HasDerivAt (fun h : ℝ => g (y + h • e)) D 0) :
    fderiv ℝ g y e = D := by
  have hTdiff : DifferentiableAt ℝ (fun h : ℝ => y + h • e) 0 := by
    fun_prop
  have hcomp := fderiv_comp' (g := g) (f := fun h : ℝ => y + h • e) (x := 0)
    (by simpa using hgdiff) hTdiff
  have hT : fderiv ℝ (fun h : ℝ => y + h • e) 0 = (1 : ℝ →L[ℝ] ℝ).smulRight e := by
    apply ContinuousLinearMap.ext
    intro v
    have hlin : HasFDerivAt (fun h : ℝ => h • e) ((1 : ℝ →L[ℝ] ℝ).smulRight e) 0 := by
      exact (ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight e) (x := 0))
    have hconst : HasFDerivAt (fun h : ℝ => y) (0 : ℝ →L[ℝ] MorseModel n) 0 :=
      hasFDerivAt_const _ _
    have hsum := hlin.add hconst
    have hfd := hsum.fderiv
    have hgoal : fderiv ℝ (fun h : ℝ => y + h • e) 0 = (1 : ℝ →L[ℝ] ℝ).smulRight e := by
      have hfuneq : (fun h : ℝ => y + h • e) = (fun h : ℝ => h • e) + (fun h : ℝ => y) := by
        funext h
        simp only [Pi.add_apply]
        ring_nf
      exact ((congrArg (fun f : ℝ → MorseModel n => fderiv ℝ f 0) hfuneq).trans hfd).trans
        (add_zero _)
    have hh := congrArg (fun L : ℝ →L[ℝ] MorseModel n => L v) hgoal
    simpa using hh
  have hline' : fderiv ℝ (fun h : ℝ => g (y + h • e)) 0 (1 : ℝ) = D := by
    have hf := hline.hasFDerivAt
    have hfd : fderiv ℝ (fun h : ℝ => g (y + h • e)) 0 =
        (ContinuousLinearMap.toSpanSingleton ℝ D : ℝ →L[ℝ] F) := hf.fderiv
    have hh := congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) hfd
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hh
  have hh := congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) hcomp
  have hfuneq2 : (fun y_1 : ℝ => g ((fun h : ℝ => y + h • e) y_1)) =
      (fun h : ℝ => g (y + h • e)) := by
    rfl
  rw [hfuneq2] at hh
  rw [hT] at hh
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul] at hh
  rw [← hline']
  simpa using hh.symm

private lemma hasDerivAt_smul_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (w : F) :
    HasDerivAt (fun h : ℝ => h • w) w 0 := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hL : HasFDerivAt (fun h : ℝ => h • w) ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
    exact ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight w) (x := 0)
  have hEq : ContinuousLinearMap.toSpanSingleton ℝ w = (1 : ℝ →L[ℝ] ℝ).smulRight w := by
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rwa [hEq]

private lemma hasDerivAt_const_add_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (x w : F) :
    HasDerivAt (fun h : ℝ => x + h • w) w 0 := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun h : ℝ => h • w) ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
    exact ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight w) (x := 0)
  have h2 : HasFDerivAt (fun h : ℝ => x) (0 : ℝ →L[ℝ] F) 0 := hasFDerivAt_const x 0
  have h3 := h1.add h2
  have hEq' : ContinuousLinearMap.toSpanSingleton ℝ w = (1 : ℝ →L[ℝ] ℝ).smulRight w := by
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  convert h3 using 1
  · funext h
    simp only [Pi.add_apply]
    rw [add_comm]
  · simp [hEq']

private lemma hasDerivAt_norm_add_smul {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x w : F} (hx : x ≠ 0) :
    HasDerivAt (fun h : ℝ => ‖x + h • w‖) (inner ℝ x w / ‖x‖) 0 := by
  have hsmulw : HasDerivAt (fun h : ℝ => h • w) w 0 := hasDerivAt_smul_const w
  have hlin : HasDerivAt (fun h : ℝ => x + h • w) w 0 := by
    rw [hasDerivAt_iff_hasFDerivAt]
    have h1 : HasFDerivAt (fun h : ℝ => h • w) ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
      exact ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight w) (x := 0)
    have h2 : HasFDerivAt (fun h : ℝ => x) (0 : ℝ →L[ℝ] F) 0 := hasFDerivAt_const x 0
    have h3 := h1.add h2
    have hEq' : ContinuousLinearMap.toSpanSingleton ℝ w = (1 : ℝ →L[ℝ] ℝ).smulRight w := by
      ext
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    convert h3 using 1
    · funext h
      simp only [Pi.add_apply]
      rw [add_comm]
    · simp [hEq']
  have hsq : HasDerivAt (fun h : ℝ => ‖x + h • w‖ ^ 2) (2 * inner ℝ x w) 0 := by
    simpa using (HasDerivAt.norm_sq hlin)
  have hne : ‖x + (0 : ℝ) • w‖ ^ 2 ≠ 0 := by
    simpa only [zero_smul, add_zero] using (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hsqrt := hsq.sqrt hne
  have hfun : (fun h : ℝ => ‖x + h • w‖) = (fun h : ℝ => Real.sqrt (‖x + h • w‖ ^ 2)) := by
    funext h
    rw [Real.sqrt_sq (norm_nonneg _)]
  have hval : (2 * inner ℝ x w) / (2 * ‖x‖) = inner ℝ x w / ‖x‖ := by
    field_simp [norm_pos_iff.mpr hx]
  convert hsqrt using 1
  · simp [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _), hval]

lemma hasDerivAt_modifiedNormalForm_posCoord {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (y : MorseModel n) (j : Fin (n - k)) (hpos : posPart hk y ≠ 0) :
    HasDerivAt (fun h : ℝ => modifiedNormalForm hk c ε δ (y + h • posBasis hk j))
      ((posPart hk y j) * (1 - modMu ε (‖negPart hk y‖ ^ 2) * deriv (modGamma δ) ‖posPart hk y‖ /
        ‖posPart hk y‖)) 0 := by
  let e : MorseModel n := posBasis hk j
  have hu : ∀ h : ℝ, negPart hk (y + h • e) = negPart hk y :=
    fun h => by simpa [e] using (negPart_add_smul_pos hk y h j)
  have hp : ∀ h : ℝ, posPart hk (y + h • e) = posPart hk y + h • posUnit j :=
    fun h => by simpa [e] using (posPart_add_smul_pos hk y h j)
  have hlin : HasDerivAt (fun h : ℝ => posPart hk y + h • posUnit j)
      (posUnit j : EuclideanSpace ℝ (Fin (n - k))) 0 := by
    exact hasDerivAt_const_add_smul (posPart hk y) (posUnit j)
  have hsq : HasDerivAt (fun h : ℝ => ‖posPart hk (y + h • e)‖ ^ 2) (2 * posPart hk y j) 0 := by
    have h' := hlin.norm_sq
    have hfun : (fun h : ℝ => ‖posPart hk (y + h • e)‖ ^ 2) =
        (fun h : ℝ => ‖posPart hk y + h • posUnit j‖ ^ 2) := by
      funext h
      rw [hp h]
    have hval : 2 * inner ℝ (posPart hk y) (posUnit j) = 2 * posPart hk y j := by
      have hin : inner ℝ (posPart hk y) (posUnit j) = posPart hk y j := by
        rw [PiLp.inner_apply]
        rw [Finset.sum_eq_single j]
        · have hfiber : inner ℝ (posPart hk y j) (1 : ℝ) = posPart hk y j := by
            rw [real_inner_eq_re_inner]
            rw [RCLike.inner_apply']
            simp
          simpa [posUnit] using hfiber
        · intro i hi hij
          have hzero : inner ℝ (posPart hk y i) (0 : ℝ) = 0 := by
            rw [real_inner_eq_re_inner, RCLike.inner_apply']
            simp
          simp [hij, posUnit]
        · intro hj
          exact False.elim (hj (Finset.mem_univ j))
      rw [hin]
    rw [hfun]
    simpa [hval] using h'
  have hf : HasDerivAt (fun h : ℝ => morseNormalForm hk c (y + h • e)) (posPart hk y j) 0 := by
    have hsplit : (fun h : ℝ => morseNormalForm hk c (y + h • e)) =
        (fun h : ℝ => c + (1 / 2) * (‖posPart hk (y + h • e)‖ ^ 2 - ‖negPart hk (y + h • e)‖ ^ 2)) := by
      funext h
      rw [morseNormalForm_split hk c (y + h • e)]
    rw [hsplit]
    have hneg' : HasDerivAt (fun h : ℝ => ‖negPart hk (y + h • e)‖ ^ 2) 0 0 := by
      have hfun : (fun h : ℝ => ‖negPart hk (y + h • e)‖ ^ 2) = fun _ : ℝ => ‖negPart hk y‖ ^ 2 := by
        funext h
        rw [hu h]
      rw [hfun]
      exact hasDerivAt_const (c := ‖negPart hk y‖ ^ 2) (x := (0 : ℝ))
    have hsub := hsq.sub hneg'
    have hmul : HasDerivAt (fun h : ℝ => (1 / 2) * (‖posPart hk (y + h • e)‖ ^ 2 - ‖negPart hk (y + h • e)‖ ^ 2))
        ((1 / 2) * (2 * posPart hk y j - 0)) 0 :=
      hsub.const_mul (1 / 2)
    have hconst : HasDerivAt (fun _ : ℝ => c) 0 (0 : ℝ) :=
      hasDerivAt_const (x := (0 : ℝ)) (c := c)
    have hadd := HasDerivAt.add hconst hmul
    have hval : (1 / 2) * (2 * posPart hk y j - 0) = posPart hk y j := by ring
    convert hadd using 1
    · rw [hval]
      simp
  have hga : HasDerivAt (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖)
      (deriv (modGamma δ) ‖posPart hk y‖ * (inner ℝ (posPart hk y) (posUnit j) / ‖posPart hk y‖)) 0 := by
    have hnorm : HasDerivAt (fun h : ℝ => ‖posPart hk y + h • posUnit j‖)
        (inner ℝ (posPart hk y) (posUnit j) / ‖posPart hk y‖) 0 := by
      exact hasDerivAt_norm_add_smul hpos
    have hfun : (fun h : ℝ => ‖posPart hk (y + h • e)‖) =
        (fun h : ℝ => ‖posPart hk y + h • posUnit j‖) := by
      funext h
      rw [hp h]
    have hnorm' : HasDerivAt (fun h : ℝ => ‖posPart hk (y + h • e)‖)
        (inner ℝ (posPart hk y) (posUnit j) / ‖posPart hk y‖) 0 := by
      rw [hfun]
      exact hnorm
    have hg : HasDerivAt (modGamma δ) (deriv (modGamma δ) ‖posPart hk y‖) ‖posPart hk y‖ :=
      (differentiableAt_modGamma (δ := δ) ‖posPart hk y‖).hasDerivAt
    have hg0 : HasDerivAt (modGamma δ) (deriv (modGamma δ) ‖posPart hk y‖)
        (‖posPart hk (y + (0 : ℝ) • e)‖) := by
      simpa using hg
    have hcomp := hg0.comp (x := 0) hnorm'
    have hfuneq : (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖) =
        modGamma δ ∘ (fun h : ℝ => ‖posPart hk (y + h • e)‖) := by
      rfl
    rw [hfuneq]
    exact hcomp
  have hval : inner ℝ (posPart hk y) (posUnit j) = posPart hk y j := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_single j]
    · have hfiber : inner ℝ (posPart hk y j) (1 : ℝ) = posPart hk y j := by
        rw [real_inner_eq_re_inner]
        rw [RCLike.inner_apply']
        simp
      simpa [posUnit] using hfiber
    · intro i hi hij
      have hzero : inner ℝ (posPart hk y i) (0 : ℝ) = 0 := by
        rw [real_inner_eq_re_inner, RCLike.inner_apply']
        simp
      simp [hij, posUnit]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  have hgaval : deriv (modGamma δ) ‖posPart hk y‖ * (posPart hk y j / ‖posPart hk y‖) =
      (posPart hk y j) * (deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖) := by
    ring
  have hga' : HasDerivAt (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖)
      ((posPart hk y j) * (deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖)) 0 := by
    simpa [hval, hgaval] using hga
  have hprod : HasDerivAt (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2) * modGamma δ ‖posPart hk (y + h • e)‖)
      (modMu ε (‖negPart hk y‖ ^ 2) * ((posPart hk y j) * (deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖))) 0 := by
    have hmu0 : HasDerivAt (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2)) 0 0 := by
      have hfun : (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2)) =
          fun _ : ℝ => modMu ε (‖negPart hk y‖ ^ 2) := by
        funext h
        rw [hu h]
      rw [hfun]
      exact hasDerivAt_const (c := modMu ε (‖negPart hk y‖ ^ 2)) (x := (0 : ℝ))
    have hmul := hmu0.mul hga'
    have hval' : 0 * modGamma δ ‖posPart hk y‖ +
        modMu ε (‖negPart hk y‖ ^ 2) * ((posPart hk y j) * (deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖)) =
        modMu ε (‖negPart hk y‖ ^ 2) * ((posPart hk y j) * (deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖)) := by
      ring
    simpa [Pi.mul_apply, hval'] using hmul
  have hsub := hf.sub hprod
  have hval'' : posPart hk y j - modMu ε (‖negPart hk y‖ ^ 2) * (posPart hk y j *
      (deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖)) =
      (posPart hk y j) * (1 - modMu ε (‖negPart hk y‖ ^ 2) * deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖) := by
    ring
  simpa [modifiedNormalForm, hval''] using hsub

lemma negPart_add_smul {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) (h : ℝ)
    (i : Fin k) :
    negPart hk (y + h • negBasis hk i) =
      negPart hk y + h • negUnit i := by
  change negPartCLM hk (y + h • negBasis hk i) =
      negPartCLM hk y + h • negUnit i
  rw [map_add, map_smul]
  have hneg : negPartCLM hk (negBasis hk i) = negUnit i := by
    simpa using (negPart_negBasis hk i)
  rw [hneg]

lemma posPart_add_smul {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) (h : ℝ)
    (i : Fin k) :
    posPart hk (y + h • negBasis hk i) = posPart hk y := by
  ext j
  simp only [posPart, Pi.add_apply, Pi.smul_apply, negBasis]
  have h : posIdx hk j ≠ negIdx hk i := by
    intro hz
    have hval : (posIdx hk j).val = (negIdx hk i).val := congrArg Fin.val hz
    dsimp [posIdx, negIdx] at hval
    omega
  simp [h]

lemma hasDerivAt_modifiedNormalForm_negCoord {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (y : MorseModel n) (i : Fin k) :
    HasDerivAt (fun h : ℝ => modifiedNormalForm hk c ε δ
      (y + h • negBasis hk i))
      (-(negPart hk y i) * (1 + 2 * deriv (modMu ε) (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖)) 0 := by
  let e : MorseModel n := negBasis hk i
  have hu : ∀ h : ℝ, negPart hk (y + h • e) =
      negPart hk y + h • negUnit i :=
    fun h => by simpa [e] using (negPart_add_smul hk y h i)
  have hp : ∀ h : ℝ, posPart hk (y + h • e) = posPart hk y :=
    fun h => by simpa [e] using (posPart_add_smul hk y h i)
  have hlin : HasDerivAt (fun h : ℝ => negPart hk y + h • negUnit i)
      (negUnit i : EuclideanSpace ℝ (Fin k)) 0 := by
    exact hasDerivAt_const_add_smul (negPart hk y) (negUnit i)
  have ht : HasDerivAt (fun h : ℝ => ‖negPart hk (y + h • e)‖ ^ 2) (2 * negPart hk y i) 0 := by
    have h' := hlin.norm_sq
    have hfun : (fun h : ℝ => ‖negPart hk (y + h • e)‖ ^ 2) =
        (fun h : ℝ => ‖negPart hk y + h • negUnit i‖ ^ 2) := by
      funext h
      rw [hu h]
    have hval : 2 * inner ℝ (negPart hk y) (negUnit i) = 2 * negPart hk y i := by
      have hin : inner ℝ (negPart hk y) (negUnit i) = negPart hk y i := by
        rw [PiLp.inner_apply]
        rw [Finset.sum_eq_single i]
        · have hfiber : inner ℝ (negPart hk y i) (1 : ℝ) = negPart hk y i := by
            rw [real_inner_eq_re_inner]
            rw [RCLike.inner_apply']
            simp
          simpa [negUnit, negPart] using hfiber
        · intro j hj hji
          have hzero : inner ℝ (negPart hk y j) (0 : ℝ) = 0 := by
            rw [real_inner_eq_re_inner, RCLike.inner_apply']
            simp
          simpa only [hji, negUnit, negPart] using hzero
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      rw [hin]
    rw [hfun]
    simpa [hval] using h'
  have hf : HasDerivAt (fun h : ℝ => morseNormalForm hk c (y + h • e)) (-(negPart hk y i)) 0 := by
    have hsplit : (fun h : ℝ => morseNormalForm hk c (y + h • e)) =
        (fun h : ℝ => c + (1 / 2) * (‖posPart hk (y + h • e)‖ ^ 2 - ‖negPart hk (y + h • e)‖ ^ 2)) := by
      funext h
      rw [morseNormalForm_split hk c (y + h • e)]
    rw [hsplit]
    have hpos' : HasDerivAt (fun h : ℝ => ‖posPart hk (y + h • e)‖ ^ 2) 0 0 := by
      have hfun : (fun h : ℝ => ‖posPart hk (y + h • e)‖ ^ 2) = fun _ : ℝ => ‖posPart hk y‖ ^ 2 := by
        funext h
        rw [hp h]
      rw [hfun]
      exact hasDerivAt_const (c := ‖posPart hk y‖ ^ 2) (x := (0 : ℝ))
    have hsub := hpos'.sub ht
    have hmul : HasDerivAt (fun h : ℝ => (1 / 2) * (‖posPart hk (y + h • e)‖ ^ 2 - ‖negPart hk (y + h • e)‖ ^ 2))
        ((1 / 2) * (0 - 2 * negPart hk y i)) 0 :=
      hsub.const_mul (1 / 2)
    have hconst : HasDerivAt (fun _ : ℝ => c) 0 (0 : ℝ) :=
      hasDerivAt_const (x := (0 : ℝ)) (c := c)
    have hadd := HasDerivAt.add hconst hmul
    have hval : (1 / 2) * (0 - 2 * negPart hk y i) = -(negPart hk y i) := by ring
    convert hadd using 1
    · rw [hval]
      simp
  have hmu : HasDerivAt (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2))
      (deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i)) 0 := by
    have hcv : HasDerivAt (modMu ε) (deriv (modMu ε) (‖negPart hk y‖ ^ 2)) (‖negPart hk y‖ ^ 2) :=
      (differentiableAt_modMu (ε := ε) (‖negPart hk y‖ ^ 2)).hasDerivAt
    have hcv0 : HasDerivAt (modMu ε) (deriv (modMu ε) (‖negPart hk y‖ ^ 2))
        (‖negPart hk (y + (0 : ℝ) • e)‖ ^ 2) := by
      simpa using hcv
    simpa [Function.comp_def] using (hcv0.comp (x := 0) ht)
  have hga : HasDerivAt (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖) 0 0 := by
    have hfun : (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖) = fun _ : ℝ => modGamma δ ‖posPart hk y‖ := by
      funext h
      rw [hp h]
    rw [hfun]
    exact hasDerivAt_const (c := modGamma δ ‖posPart hk y‖) (x := (0 : ℝ))
  have hprod : HasDerivAt (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2) * modGamma δ ‖posPart hk (y + h • e)‖)
      (deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i) * modGamma δ ‖posPart hk y‖) 0 := by
    have hmul := hmu.mul hga
    have hval : (deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i)) * modGamma δ ‖posPart hk y‖ +
        modMu ε (‖negPart hk y‖ ^ 2) * 0 =
        deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i) * modGamma δ ‖posPart hk y‖ := by
      ring
    simpa [Pi.mul_apply, hval] using hmul
  have hsub := hf.sub hprod
  have hval : -(negPart hk y i) - deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i) *
      modGamma δ ‖posPart hk y‖ =
      -(negPart hk y i) * (1 + 2 * deriv (modMu ε) (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖) := by
    ring
  simpa [modifiedNormalForm, hval] using hsub

theorem modMu_le {ε t : ℝ} (hε : 0 ≤ ε) : modMu ε t ≤ 3 / 2 * ε := by
  dsimp [modMu]
  have h1 : 0 ≤ Real.smoothTransition ((t - 2 * ε) / (2 * ε)) := Real.smoothTransition.nonneg _
  nlinarith

theorem modMu_antitone_global {ε : ℝ} (hε : 0 < ε) : Antitone (modMu ε) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · exact modMu_antitone (le_of_lt hε) ha (le_trans ha hab) hab
  · have hma : modMu ε a = 3 / 2 * ε := modMu_const hε (by nlinarith [ha])
    rw [hma]
    exact modMu_le (le_of_lt hε)

theorem modGamma_antitone_global {δ : ℝ} (hδ : 0 < δ) : Antitone (modGamma δ) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · exact modGamma_antitone (le_of_lt hδ) ha (le_trans ha hab) hab
  · have harg : (2 * a - δ) / δ ≤ 0 := by
      rw [div_le_iff₀ hδ]
      nlinarith [ha, hδ]
    have hga : modGamma δ a = 1 := by
      dsimp [modGamma]
      rw [Real.smoothTransition.zero_of_nonpos harg]
      norm_num
    rw [hga]
    exact modGamma_le_one δ b

theorem deriv_modMu_nonpos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : deriv (modMu ε) t ≤ 0 :=
  (differentiableAt_modMu (ε := ε) t).hasDerivAt.nonpos_of_antitone (modMu_antitone_global hε)

theorem deriv_modGamma_nonpos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : deriv (modGamma δ) s ≤ 0 :=
  (differentiableAt_modGamma (δ := δ) s).hasDerivAt.nonpos_of_antitone (modGamma_antitone_global hδ)

theorem contDiff_modMu {ε : ℝ} : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (modMu ε) := by
  have hst : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  have haff : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t - 2 * ε) / (2 * ε)) := by
    fun_prop
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) :=
    ContDiff.comp hst haff
  have hone : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => 1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε))) :=
    ContDiff.sub (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ))) hcomp
  have hmul : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (3 / 2 * ε) * (1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε)))) := by
    simpa [smul_eq_mul] using (ContDiff.const_smul (3 / 2 * ε) hone)
  simpa [modMu] using hmul

theorem contDiff_modGamma {δ : ℝ} : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (modGamma δ) := by
  have hst : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  have haff : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (2 * s - δ) / δ) := by
    fun_prop
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) :=
    ContDiff.comp hst haff
  have hone : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => 1 - Real.smoothTransition ((2 * s - δ) / δ)) :=
    ContDiff.sub (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ))) hcomp
  simpa [modGamma] using hone

theorem contDiff_morseNormalForm {n k : ℕ} (hk : k ≤ n) (c : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseNormalForm hk c) := by
  have hpos : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) :=
    ContDiff.norm_sq ℝ (ContinuousLinearMap.contDiff (posPartCLM hk))
  have hneg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) :=
    ContDiff.norm_sq ℝ (ContinuousLinearMap.contDiff (negPartCLM hk))
  have hdiff := ContDiff.sub hpos hneg
  have hhalf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel n => (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2)) :=
    ContDiff.mul (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : MorseModel n => (1 / 2 : ℝ))) hdiff
  have hcst : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : MorseModel n => c) := contDiff_const
  have hsum : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2)) :=
    ContDiff.add hcst hhalf
  change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y)
  simpa [morseNormalForm_split] using hsum

theorem contDiff_modGamma_norm {n k : ℕ} (hk : k ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => modGamma δ ‖posPart hk y‖) := by
  let s : Set (MorseModel n) := {y : MorseModel n | ‖posPart hk y‖ < δ / 2}
  let t : Set (MorseModel n) := {y : MorseModel n | ‖posPart hk y‖ > δ / 4}
  have hcontPos : Continuous (fun y : MorseModel n => ‖posPart hk y‖) :=
    continuous_norm.comp (posPartCLM hk).continuous
  have hs : IsOpen s := isOpen_lt hcontPos continuous_const
  have ht : IsOpen t := isOpen_lt continuous_const hcontPos
  have hconstOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel n => modGamma δ ‖posPart hk y‖) s := by
    rintro y hy
    exact (ContDiffAt.contDiffWithinAt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := y)
      (ContDiffAt.congr_of_eventuallyEq
        (contDiffAt_const (x := y) (c := (1 : ℝ)))
        (by
          filter_upwards [hs.mem_nhds hy] with z hz
          exact modGamma_one hδ (le_of_lt hz))))
  have hnormOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖) t :=
    by
      rintro y hy
      exact (ContDiffAt.contDiffWithinAt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := y)
        (ContDiffAt.norm ℝ
          (ContDiff.contDiffAt (ContinuousLinearMap.contDiff (posPartCLM hk)))
          (by
            have hgt : ‖posPart hk y‖ > δ / 4 := hy
            have hpos : 0 < ‖posPart hk y‖ :=
              lt_of_lt_of_le (div_pos hδ (by norm_num)) (le_of_lt hgt)
            exact norm_ne_zero_iff.mp (ne_of_gt hpos))))
  have hgammaOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel n => modGamma δ ‖posPart hk y‖) t := by
    rintro y hy
    exact (ContDiffAt.contDiffWithinAt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := y) (by
      have hposAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => posPart hk z) y :=
        ContDiff.contDiffAt (ContinuousLinearMap.contDiff (posPartCLM hk))
      have hgt : ‖posPart hk y‖ > δ / 4 := hy
      have hpos : 0 < ‖posPart hk y‖ :=
        lt_of_lt_of_le (div_pos hδ (by norm_num)) (le_of_lt hgt)
      have hnormAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => ‖posPart hk z‖) y :=
        ContDiffAt.norm ℝ hposAt (norm_ne_zero_iff.mp (ne_of_gt hpos))
      have hgammaAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (modGamma δ) (‖posPart hk y‖) :=
        ContDiff.contDiffAt (contDiff_modGamma (δ := δ))
      have hcompAt := ContDiffAt.comp y hgammaAt hnormAt
      simpa [Function.comp_def] using hcompAt))
  have hst : s ∪ t = Set.univ := by
    ext y
    constructor
    · intro
      trivial
    · intro
      by_cases hlt : ‖posPart hk y‖ < δ / 2
      · exact Or.inl hlt
      · have hge : δ / 2 ≤ ‖posPart hk y‖ := le_of_not_gt hlt
        have hgt : δ / 4 < ‖posPart hk y‖ := by nlinarith [hδ, hge]
        exact Or.inr hgt
  exact contDiff_of_contDiffOn_union_of_isOpen hconstOn hgammaOn hst hs ht

theorem contDiff_modifiedNormalForm {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (modifiedNormalForm hk c ε δ) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseNormalForm hk c) := contDiff_morseNormalForm hk c
  have hmu : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel n => modMu ε (‖negPart hk y‖ ^ 2)) := by
    have hn : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) :=
      ContDiff.norm_sq ℝ (ContinuousLinearMap.contDiff (negPartCLM hk))
    simpa [Function.comp_def] using (ContDiff.comp (contDiff_modMu (ε := ε)) hn)
  have hgamma : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel n => modGamma δ ‖posPart hk y‖) :=
    contDiff_modGamma_norm hk δ hδ
  simpa [modifiedNormalForm] using (ContDiff.sub h1 (ContDiff.mul hmu hgamma))

theorem modifiedNormalForm_split {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y =
      c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) -
        modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ := by
  dsimp [modifiedNormalForm]
  rw [morseNormalForm_split]

theorem modifiedNormalForm_zero {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    modifiedNormalForm hk c ε δ 0 = c - 3 / 2 * ε := by
  rw [modifiedNormalForm_split]
  have hmu : modMu ε (‖negPart hk (0 : MorseModel n)‖ ^ 2) = 3 / 2 * ε := by
    have hz : negPart hk (0 : MorseModel n) = 0 := by
      ext i
      simp [negPart]
    rw [hz]
    exact modMu_const hε (by simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hε)))
  have hga : modGamma δ ‖posPart hk (0 : MorseModel n)‖ = 1 := by
    have hz : posPart hk (0 : MorseModel n) = 0 := by
      ext j
      simp [posPart]
    rw [hz]
    exact modGamma_one hδ (by simpa using (div_nonneg (le_of_lt hδ) (by norm_num : (0 : ℝ) ≤ 2)))
  have hz : negPart hk (0 : MorseModel n) = 0 := by
    ext i
    simp [negPart]
  have hpz : posPart hk (0 : MorseModel n) = 0 := by
    ext j
    simp [posPart]
  rw [hmu, hga, hz, hpz]
  simp

theorem modifiedNormalForm_recombine_scale_le {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k)))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε) (hδ : 0 < δ) :
    modifiedNormalForm hk c ε δ (recombine hk a (s • b)) ≤
      modifiedNormalForm hk c ε δ (recombine hk a b) := by
  rw [modifiedNormalForm_split, modifiedNormalForm_split]
  have hneg : ‖negPart hk (recombine hk a (s • b))‖ ^ 2 =
      ‖negPart hk (recombine hk a b)‖ ^ 2 := by
    have hnegp : negPart hk (recombine hk a (s • b)) = negPart hk (recombine hk a b) := by
      ext i
      simp [negPart, recombine_negPart]
    rw [hnegp]
  have hpos : ‖posPart hk (recombine hk a (s • b))‖ = s * ‖b‖ := by
    have hval : posPart hk (recombine hk a (s • b)) = s • b := by
      ext j
      simp [posPart, recombine_posPart]
    rw [hval, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hpos1 : ‖posPart hk (recombine hk a b)‖ = ‖b‖ := by
    have hval : posPart hk (recombine hk a b) = b := by
      ext j
      simp [posPart, recombine_posPart]
    rw [hval]
  have hgam : modGamma δ ‖b‖ ≤ modGamma δ (s * ‖b‖) := by
    have hle : s * ‖b‖ ≤ ‖b‖ := by
      nlinarith [mul_le_of_le_one_right (norm_nonneg b) hs1]
    have hleft : s * ‖b‖ ∈ Set.Ici (0 : ℝ) := by
      exact mul_nonneg hs0 (norm_nonneg b)
    have hright : ‖b‖ ∈ Set.Ici (0 : ℝ) := norm_nonneg b
    exact modGamma_antitone (le_of_lt hδ) hleft hright hle
  have hle1 : (s * ‖b‖) ^ 2 ≤ ‖b‖ ^ 2 := by
    have hle : s * ‖b‖ ≤ ‖b‖ := by
      nlinarith [mul_le_of_le_one_right (norm_nonneg b) hs1]
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (mul_nonneg hs0 (norm_nonneg b)), abs_of_nonneg (norm_nonneg b)]
      exact hle)
  have hmu : 0 ≤ modMu ε (‖negPart hk (recombine hk a b)‖ ^ 2) :=
    modMu_nonneg (ε := ε) (t := ‖negPart hk (recombine hk a b)‖ ^ 2) (le_of_lt hε)
  rw [hneg, hpos, hpos1]
  have hmmul : 0 ≤ modMu ε (‖negPart hk (recombine hk a b)‖ ^ 2) *
      (modGamma δ (s * ‖b‖) - modGamma δ ‖b‖) :=
    mul_nonneg hmu (sub_nonneg.mpr hgam)
  nlinarith [hle1, hmmul]

theorem modifiedNormalForm_lt_of_posPart_zero {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n} (hy : posPart hk y = 0) :
    modifiedNormalForm hk c ε δ y < c - ε := by
  rw [modifiedNormalForm_split]
  have hpos : ‖posPart hk y‖ = 0 := by rw [hy]; simp
  by_cases h : 2 * ε < ‖negPart hk y‖ ^ 2
  · have hlt : c - (1 / 2) * ‖negPart hk y‖ ^ 2 < c - ε := by nlinarith
    have hle : c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) -
        modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ ≤
        c - (1 / 2) * ‖negPart hk y‖ ^ 2 := by
      have hmu : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) :=
        modMu_nonneg (ε := ε) (t := ‖negPart hk y‖ ^ 2) (le_of_lt hε)
      have hga : 0 ≤ modGamma δ ‖posPart hk y‖ := modGamma_nonneg δ _
      nlinarith [hpos, mul_nonneg hmu hga]
    exact lt_of_le_of_lt hle hlt
  · have hle2 : ‖negPart hk y‖ ^ 2 ≤ 2 * ε := le_of_not_gt h
    have hmu : modMu ε (‖negPart hk y‖ ^ 2) = 3 / 2 * ε := modMu_const hε hle2
    have hga : modGamma δ ‖posPart hk y‖ = 1 := by
      have hs : ‖posPart hk y‖ ≤ δ / 2 := by
        rw [hpos]
        exact le_of_lt (half_pos hδ)
      exact modGamma_one hδ hs
    rw [hmu, hga, hpos]
    have hnonneg : 0 ≤ ‖negPart hk y‖ ^ 2 := sq_nonneg _
    nlinarith [hnonneg, hε]

theorem modifiedNormalForm_posPart_eq_zero_of_fderiv_eq_zero {n k : ℕ} (hk : k ≤ n)
    (c ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : fderiv ℝ (modifiedNormalForm hk c ε δ) y = 0) :
    posPart hk y = 0 := by
  by_contra hpos
  have hne : ∃ j : Fin (n - k), posPart hk y j ≠ 0 := by
    by_contra h
    apply hpos
    ext j
    by_contra hj
    exact h ⟨j, hj⟩
  rcases hne with ⟨j, hj⟩
  have hd : DifferentiableAt ℝ (modifiedNormalForm hk c ε δ) y :=
    ((contDiff_modifiedNormalForm hk c ε δ hδ).differentiable (by norm_num)).differentiableAt
  have hline := hasDerivAt_modifiedNormalForm_posCoord hk c ε δ y j hpos
  have hfderiv : fderiv ℝ (modifiedNormalForm hk c ε δ) y (posBasis hk j) = 0 := by
    rw [hy]
    rfl
  have hline' : fderiv ℝ (modifiedNormalForm hk c ε δ) y (posBasis hk j) =
      (posPart hk y j) * (1 - modMu ε (‖negPart hk y‖ ^ 2) * deriv (modGamma δ) ‖posPart hk y‖ /
        ‖posPart hk y‖) :=
    fderiv_apply_eq_deriv_line (g := modifiedNormalForm hk c ε δ) (y := y) (e := posBasis hk j)
      hd hline
  have hzero : (posPart hk y j) * (1 - modMu ε (‖negPart hk y‖ ^ 2) *
      deriv (modGamma δ) ‖posPart hk y‖ / ‖posPart hk y‖) = 0 := by
    rw [← hline']
    exact hfderiv
  have hmu : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) :=
    modMu_nonneg (ε := ε) (t := ‖negPart hk y‖ ^ 2) (le_of_lt hε)
  have hdg : deriv (modGamma δ) ‖posPart hk y‖ ≤ 0 := deriv_modGamma_nonpos hδ _
  have hnorm : 0 < ‖posPart hk y‖ := norm_pos_iff.mpr hpos
  have hnonpos : modMu ε (‖negPart hk y‖ ^ 2) * deriv (modGamma δ) ‖posPart hk y‖ /
      ‖posPart hk y‖ ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hmu hdg) (le_of_lt hnorm)
  have hfact : 1 - modMu ε (‖negPart hk y‖ ^ 2) * deriv (modGamma δ) ‖posPart hk y‖ /
      ‖posPart hk y‖ ≠ 0 := by
    nlinarith
  have hcoh : posPart hk y j = 0 := (mul_eq_zero.mp hzero).resolve_right hfact
  exact hj hcoh

theorem modifiedNormalForm_no_critical_point_in_strip {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : modifiedNormalForm hk c ε δ y ∈ Set.Icc (c - ε) (c + ε)) :
    fderiv ℝ (modifiedNormalForm hk c ε δ) y ≠ 0 := by
  intro hcrit
  have hpos := modifiedNormalForm_posPart_eq_zero_of_fderiv_eq_zero hk c ε δ hε hδ hcrit
  have hlt : modifiedNormalForm hk c ε δ y < c - ε :=
    modifiedNormalForm_lt_of_posPart_zero hk c ε δ hε hδ hpos
  exact (not_lt_of_ge hy.1) hlt

def modifiedCollarRetraction {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (y : MorseModel n) : MorseModel n :=
  if morseNormalForm hk c y ≤ c - ε then y
  else if ‖negPart hk y‖ ^ 2 ≤ 2 * ε then spineMap hk y
  else recombine hk (negPart hk y)
    ((Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)) • posPart hk y)

def modifiedCollarHomotopy {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (t : ℝ) (y : MorseModel n) :
    MorseModel n :=
  if morseNormalForm hk c y ≤ c - ε then y
  else if ‖negPart hk y‖ ^ 2 ≤ 2 * ε then
    recombine hk (negPart hk y) ((1 - t) • posPart hk y)
  else recombine hk (negPart hk y)
    ((1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)) • posPart hk y)

theorem modifiedCollarRetraction_mem_lowerCellUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (hε : 0 < ε) (y : MorseModel n) :
    modifiedCollarRetraction hk c ε y ∈ lowerCellUnion hk c ε := by
  by_cases hf : morseNormalForm hk c y ≤ c - ε
  · dsimp [modifiedCollarRetraction]
    rw [if_pos hf]
    exact Or.inl (by simpa [sublevel] using hf)
  · by_cases hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε
    · dsimp [modifiedCollarRetraction]
      rw [if_neg hf, if_pos hb]
      exact Or.inr (spineMap_mem_cell hk ε hε hb)
    · have hP : ‖posPart hk y‖ ^ 2 ≠ 0 := by
        intro hP
        apply hf
        have hN : 2 * ε < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hb
        rw [morseNormalForm_split]
        have hP0 : ‖posPart hk y‖ = 0 := by
          exact sq_eq_zero_iff.mp hP
        nlinarith [sq_nonneg ‖negPart hk y‖, hN]
      have hPpos : 0 < ‖posPart hk y‖ ^ 2 :=
        sq_pos_of_ne_zero ((pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hP)
      have hNge : 0 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
        exact sub_nonneg.mpr (le_of_lt (lt_of_not_ge hb))
      let s : ℝ := Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hsq : s ^ 2 * ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε := by
        dsimp [s]
        rw [Real.sq_sqrt (div_nonneg hNge (le_of_lt hPpos))]
        rw [div_mul_eq_mul_div]
        rw [mul_div_assoc]
        rw [div_self hPpos.ne']
        rw [mul_one]
      have hval : morseNormalForm hk c (recombine hk (negPart hk y) (s • posPart hk y)) = c - ε := by
        rw [morseNormalForm_split]
        have hneg' : negPart hk (recombine hk (negPart hk y) (s • posPart hk y)) = negPart hk y := by
          ext i
          simp [negPart, recombine_negPart]
        have hpos' : posPart hk (recombine hk (negPart hk y) (s • posPart hk y)) = s • posPart hk y := by
          ext j
          simp [posPart, recombine_posPart]
        rw [hneg', hpos']
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        nlinarith [hsq]
      dsimp [modifiedCollarRetraction]
      rw [if_neg hf, if_neg hb]
      exact Or.inl (by simpa [s, sublevel] using (le_of_eq hval))

theorem modifiedCollarHomotopy_mem_sublevel {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {y : MorseModel n}
    (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    modifiedNormalForm hk c ε δ (modifiedCollarHomotopy hk c ε t y) ≤ c - ε := by
  by_cases hf : morseNormalForm hk c y ≤ c - ε
  · simpa [modifiedCollarHomotopy, hf] using hy
  · by_cases hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε
    · have hs0 : 0 ≤ 1 - t := by linarith
      have hs1 : 1 - t ≤ 1 := by linarith
      have hle := modifiedNormalForm_recombine_scale_le hk c ε δ (negPart hk y) (posPart hk y)
        hs0 hs1 hε hδ
      have hy' : modifiedNormalForm hk c ε δ (recombine hk (negPart hk y) (posPart hk y)) ≤ c - ε := by
        simpa [recombine_decompose] using hy
      simpa [modifiedCollarHomotopy, hf, hb] using (le_trans hle hy')
    · have hNPlt : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by
        have hgt : c - ε < morseNormalForm hk c y := lt_of_not_ge hf
        rw [morseNormalForm_split] at hgt
        nlinarith
      have hP : ‖posPart hk y‖ ^ 2 ≠ 0 := by
        intro hP
        apply hf
        have hN : 2 * ε < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hb
        rw [morseNormalForm_split]
        have hP0 : ‖posPart hk y‖ = 0 := sq_eq_zero_iff.mp hP
        nlinarith [sq_nonneg ‖negPart hk y‖, hN]
      have hPpos : 0 < ‖posPart hk y‖ ^ 2 :=
        sq_pos_of_ne_zero ((pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hP)
      have hNge : 0 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
        exact sub_nonneg.mpr (le_of_lt (lt_of_not_ge hb))
      have hratio : (‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2 ≤ 1 := by
        exact le_of_lt ((div_lt_one hPpos).2 hNPlt)
      have hs₀0 : 0 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) :=
        Real.sqrt_nonneg _
      have hs₀1 : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) ≤ 1 := by
        exact Real.sqrt_le_one.mpr hratio
      have hs0 : 0 ≤ 1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) := by
        nlinarith [ht0, hs₀0]
      have hs1 : 1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) ≤ 1 := by
        nlinarith [ht0, hs₀1]
      have hle := modifiedNormalForm_recombine_scale_le hk c ε δ (negPart hk y) (posPart hk y)
        hs0 hs1 hε hδ
      have hy' : modifiedNormalForm hk c ε δ (recombine hk (negPart hk y) (posPart hk y)) ≤ c - ε := by
        simpa [recombine_decompose] using hy
      simpa [modifiedCollarHomotopy, hf, hb] using (le_trans hle hy')

theorem modifiedCollarHomotopy_zero {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (y : MorseModel n) :
    modifiedCollarHomotopy hk c ε 0 y = y := by
  dsimp [modifiedCollarHomotopy]
  by_cases hf : morseNormalForm hk c y ≤ c - ε
  · simp [hf]
  · by_cases hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε
    · simp [hf, hb, recombine_decompose]
    · rw [if_neg hf, if_neg hb]
      have hsc : (1 - 0 + 0 * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)) = 1 := by
        norm_num
      rw [hsc, one_smul]
      exact recombine_decompose hk y

theorem modifiedCollarHomotopy_one {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (y : MorseModel n) :
    modifiedCollarHomotopy hk c ε 1 y = modifiedCollarRetraction hk c ε y := by
  dsimp [modifiedCollarHomotopy, modifiedCollarRetraction]
  by_cases hf : morseNormalForm hk c y ≤ c - ε
  · simp [hf]
  · by_cases hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε
    · simp [hf, hb, spineMap]
    · simp [hf, hb]

theorem modifiedCollarHomotopy_mem_lowerCellUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (hε : 0 < ε) {t : ℝ} {y : MorseModel n} (hy : y ∈ lowerCellUnion hk c ε) :
    modifiedCollarHomotopy hk c ε t y ∈ lowerCellUnion hk c ε := by
  rcases hy with hf | hcell
  · have hy' : morseNormalForm hk c y ≤ c - ε := by simpa [sublevel] using hf
    dsimp [modifiedCollarHomotopy]
    rw [if_pos hy']
    exact Or.inl hf
  · rcases hcell with ⟨x, hx⟩
    have hpos : posPart hk y = 0 := by
      rw [← hx]
      ext j
      simp [posPart, cellMap_posIdx]
    by_cases hfy : morseNormalForm hk c y ≤ c - ε
    · dsimp [modifiedCollarHomotopy]
      rw [if_pos hfy]
      exact Or.inr ⟨x, hx⟩
    · have hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε := by
        rw [← hx]
        have hnp : negPart hk (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) =
            (Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin k)) := by
          ext i
          simp [negPart, cellMap_negIdx]
        rw [hnp]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hxle : ‖(x : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := x.2
        have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := Real.sq_sqrt (by positivity)
        have hsq' : (Real.sqrt (2 * ε) * ‖(x : EuclideanSpace ℝ (Fin k))‖) ^ 2 =
            (Real.sqrt (2 * ε)) ^ 2 * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by ring
        have hxle2 : ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
          have habs : |‖(x : EuclideanSpace ℝ (Fin k))‖| ≤ |(1 : ℝ)| := by
            rw [abs_of_nonneg (norm_nonneg (x : EuclideanSpace ℝ (Fin k))),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
            exact hxle
          simpa using (sq_le_sq.mpr habs)
        have hbnd : (Real.sqrt (2 * ε)) ^ 2 * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
            (Real.sqrt (2 * ε)) ^ 2 := by
          simpa using (mul_le_mul_of_nonneg_left hxle2 (sq_nonneg (Real.sqrt (2 * ε))))
        nlinarith [hsq, hsq', hbnd]
      have hstep : modifiedCollarHomotopy hk c ε t y = y := by
        dsimp [modifiedCollarHomotopy]
        rw [if_neg hfy, if_pos hb]
        rw [hpos, smul_zero]
        rw [← hpos]
        exact recombine_decompose hk y
      rw [hstep]
      exact Or.inr ⟨x, hx⟩

private lemma frontier_eq_of_continuous_le {X : Type} [TopologicalSpace X] (g : X → ℝ)
    (hg : Continuous g) (a : ℝ) {x : X} (hx : x ∈ frontier {x : X | g x ≤ a}) : g x = a := by
  have hyc : x ∈ closure {x : X | g x ≤ a} := frontier_subset_closure hx
  have hle : g x ≤ a := by
    have hclosed : IsClosed {x : X | g x ≤ a} := isClosed_le hg continuous_const
    exact closure_minimal (by intro z hz; exact hz) hclosed hyc
  have hyc2 : x ∈ closure {x : X | a < g x} := by
    have hfront : x ∈ frontier {x : X | a < g x} := by
      rw [show {x : X | a < g x} = ({x : X | g x ≤ a})ᶜ by ext z; simp]
      rwa [frontier_compl]
    exact frontier_subset_closure hfront
  have hge : a ≤ g x := by
    have hclosed : IsClosed {x : X | a ≤ g x} := isClosed_le continuous_const hg
    exact closure_minimal (by intro z hz; exact le_of_lt (by simpa using hz)) hclosed hyc2
  exact le_antisymm hle hge

private lemma morseNormalForm_eq_of_mem_frontier_sublevel {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    {y : MorseModel n} (hy : y ∈ frontier {y : MorseModel n | morseNormalForm hk c y ≤ c - ε}) :
    morseNormalForm hk c y = c - ε :=
  frontier_eq_of_continuous_le (fun y : MorseModel n => morseNormalForm hk c y)
    (contDiff_morseNormalForm hk c).continuous (c - ε) hy

private lemma negPart_sq_eq_of_mem_frontier {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    {y : MorseModel n} (hy : y ∈ frontier {y : MorseModel n | ‖negPart hk y‖ ^ 2 ≤ 2 * ε}) :
    ‖negPart hk y‖ ^ 2 = 2 * ε :=
  frontier_eq_of_continuous_le (fun y : MorseModel n => ‖negPart hk y‖ ^ 2)
    ((contDiff_norm_sq ℝ (n := 0)).continuous.comp (continuous_negPart hk)) (2 * ε) hy

private lemma posPart_eq_zero_of_morseNormalForm_eq {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    {y : MorseModel n} (hf : morseNormalForm hk c y = c - ε)
    (hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε) : posPart hk y = 0 := by
  have hP : ‖posPart hk y‖ ^ 2 = 0 := by
    have hsplit := morseNormalForm_split hk c y
    rw [hf] at hsplit
    nlinarith [hb, sq_nonneg ‖posPart hk y‖]
  have hnorm : ‖posPart hk y‖ = 0 := sq_eq_zero_iff.mp hP
  exact norm_eq_zero.mp hnorm

private lemma recombine_ratio_eq_self_of_morseNormalForm_eq {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    {y : MorseModel n} (hf : morseNormalForm hk c y = c - ε)
    (hb : ¬‖negPart hk y‖ ^ 2 ≤ 2 * ε) :
    recombine hk (negPart hk y)
      ((Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)) • posPart hk y) = y := by
  have hP : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    have hsplit := morseNormalForm_split hk c y
    rw [hf] at hsplit
    nlinarith
  have hN : 2 * ε < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hb
  have hPne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by linarith
  have hs1 : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) = 1 := by
    rw [hP]
    rw [div_self hPne]
    exact Real.sqrt_one
  rw [hs1, one_smul]
  exact recombine_decompose hk y

private lemma recombine_ratio_homotopy_eq_self_of_morseNormalForm_eq {n k : ℕ} (hk : k ≤ n)
    (c ε : ℝ) (t : ℝ) {y : MorseModel n} (hf : morseNormalForm hk c y = c - ε)
    (hb : ¬‖negPart hk y‖ ^ 2 ≤ 2 * ε) :
    recombine hk (negPart hk y)
      ((1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)) • posPart hk y) = y := by
  have hP : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    have hsplit := morseNormalForm_split hk c y
    rw [hf] at hsplit
    nlinarith
  have hN : 2 * ε < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hb
  have hPne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by linarith
  have hs1 : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) = 1 := by
    rw [hP]
    rw [div_self hPne]
    exact Real.sqrt_one
  rw [hs1]
  ring_nf
  rw [one_smul]
  exact recombine_decompose hk y

private lemma norm_ratio_smul_posPart_le {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (y : MorseModel n) :
    ‖Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) • posPart hk y‖ ≤
      Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) := by
  by_cases hN : 2 * ε ≤ ‖negPart hk y‖ ^ 2
  · by_cases hP : ‖posPart hk y‖ = 0
    · have h0 : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) • posPart hk y = 0 := by
        rw [hP]
        simp
      rw [h0]
      simp
    · have hPpos : 0 < ‖posPart hk y‖ :=
        lt_of_le_of_ne (norm_nonneg (posPart hk y)) (Ne.symm hP)
      rw [norm_smul]
      have ha : 0 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) :=
        Real.sqrt_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg ha]
      have hratio : 0 ≤ (‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2 := by
        exact div_nonneg (sub_nonneg.mpr hN) (sq_nonneg _)
      have hsqrt : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) *
          Real.sqrt (‖posPart hk y‖ ^ 2) = Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) := by
        have hm : (‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2 =
            ‖negPart hk y‖ ^ 2 - 2 * ε := by
          rw [div_mul_eq_mul_div]
          rw [mul_div_assoc]
          rw [div_self ((pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr hP)]
          rw [mul_one]
        calc
          Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) *
              Real.sqrt (‖posPart hk y‖ ^ 2)
              = Real.sqrt (((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) *
                  ‖posPart hk y‖ ^ 2) := by
                exact (Real.sqrt_mul hratio (‖posPart hk y‖ ^ 2)).symm
          _ = Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) := by rw [hm]
      have hsq : Real.sqrt (‖posPart hk y‖ ^ 2) = ‖posPart hk y‖ := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      rw [hsq] at hsqrt
      rw [hsqrt]
  · have hsub : ‖negPart hk y‖ ^ 2 - 2 * ε < 0 := sub_neg.mpr (lt_of_not_ge hN)
    have hsqrt2 : Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (le_of_lt hsub)
    rw [hsqrt2]
    have hneg : (‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (le_of_lt hsub) (sq_nonneg _)
    have hsqrt : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hneg
    rw [hsqrt]
    simp

private theorem continuousAt_collarRatio {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (y : MorseModel n) (hP : ‖posPart hk y‖ ≠ 0) :
    ContinuousAt (fun z : MorseModel n =>
      recombine hk (negPart hk z)
        (Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z)) y := by
  have hnum : ContinuousAt (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 - 2 * ε) y :=
    ((contDiff_norm_sq ℝ (n := 0)).continuous.comp (continuous_negPart hk)).continuousAt.sub
      continuousAt_const
  have hden : ContinuousAt (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y :=
    ((contDiff_norm_sq ℝ (n := 0)).continuous.comp (continuous_posPart hk)).continuousAt
  have hdenne : ‖posPart hk y‖ ^ 2 ≠ 0 :=
    (pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr hP
  have hdiv : ContinuousAt (fun z : MorseModel n =>
      (‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) y :=
    hnum.div hden hdenne
  have hsqrt : ContinuousAt (fun z : MorseModel n =>
      Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2)) y :=
    Real.continuous_sqrt.continuousAt.comp hdiv
  have hsmul : ContinuousAt (fun z : MorseModel n =>
      Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z) y := by
    have hpair : ContinuousAt (fun z : MorseModel n =>
        (Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2), posPart hk z)) y :=
      ContinuousAt.prodMk hsqrt (continuous_posPart hk).continuousAt
    exact continuous_smul.continuousAt.comp hpair
  have hpair2 : ContinuousAt (fun z : MorseModel n =>
      (negPart hk z,
        Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z)) y :=
    ContinuousAt.prodMk (continuous_negPart hk).continuousAt hsmul
  exact (continuous_recombine hk).continuousAt.comp hpair2

private theorem continuousOn_collarRatio {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    ContinuousOn (fun y : MorseModel n =>
      recombine hk (negPart hk y)
        (Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) • posPart hk y))
      {y : MorseModel n | 2 * ε ≤ ‖negPart hk y‖ ^ 2 ∧ c - ε ≤ morseNormalForm hk c y} := by
  let S : Set (MorseModel n) := {y : MorseModel n |
    2 * ε ≤ ‖negPart hk y‖ ^ 2 ∧ c - ε ≤ morseNormalForm hk c y}
  let F : MorseModel n → MorseModel n := fun y =>
    recombine hk (negPart hk y)
      (Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) • posPart hk y)
  intro y hy
  by_cases hN : 2 * ε < ‖negPart hk y‖ ^ 2
  · have hP : ‖posPart hk y‖ ≠ 0 := by
      intro hz
      have hf : morseNormalForm hk c y = c - (1 / 2) * ‖negPart hk y‖ ^ 2 := by
        rw [morseNormalForm_split]
        rw [hz]
        norm_num
        ring
      have hle : c - ε ≤ c - (1 / 2) * ‖negPart hk y‖ ^ 2 := by
        simpa [hf] using hy.2
      nlinarith [hN, hle]
    have hF := continuousAt_collarRatio hk ε y hP
    have hUniv : ContinuousWithinAt F Set.univ y := hF.continuousWithinAt
    exact hUniv.mono (s := S) (by intro z hz; trivial)
  · have hN2 : ‖negPart hk y‖ ^ 2 = 2 * ε := le_antisymm (le_of_not_gt hN) hy.1
    have hFy : F y = recombine hk (negPart hk y) 0 := by
      dsimp [F]
      rw [hN2]
      simp
    have hsqrt0 : Tendsto (fun z : MorseModel n => Real.sqrt (‖negPart hk z‖ ^ 2 - 2 * ε))
        (nhdsWithin y S) (nhds 0) := by
      have hcont : ContinuousAt (fun z : MorseModel n => Real.sqrt (‖negPart hk z‖ ^ 2 - 2 * ε)) y := by
        have hnum : ContinuousAt (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 - 2 * ε) y :=
          ((contDiff_norm_sq ℝ (n := 0)).continuous.comp (continuous_negPart hk)).continuousAt.sub
            continuousAt_const
        exact Real.continuous_sqrt.continuousAt.comp hnum
      have hmain : Tendsto (fun z : MorseModel n => Real.sqrt (‖negPart hk z‖ ^ 2 - 2 * ε))
          (nhds y) (nhds 0) := by
        simpa [hN2] using hcont.tendsto
      exact hmain.mono_left nhdsWithin_le_nhds
    have hvsq : Tendsto (fun z : MorseModel n =>
        Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z)
        (nhdsWithin y S) (nhds 0) := by
      have hsqueeze : Tendsto (fun z : MorseModel n =>
          ‖Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z‖)
          (nhdsWithin y S) (nhds 0) := by
        apply squeeze_zero'
        · exact Eventually.of_forall (fun z => norm_nonneg _)
        · exact Eventually.of_forall (fun z => norm_ratio_smul_posPart_le hk ε z)
        · exact hsqrt0
      exact (tendsto_zero_iff_norm_tendsto_zero).2 hsqueeze
    have hpair : Tendsto (fun z : MorseModel n =>
        (negPart hk z,
          Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z))
        (nhdsWithin y S) (nhds (negPart hk y, (0 : EuclideanSpace ℝ (Fin (n - k))))) := by
      have hfst : Tendsto (fun z : MorseModel n => negPart hk z) (nhdsWithin y S)
          (nhds (negPart hk y)) :=
        (continuous_negPart hk).continuousWithinAt.tendsto
      exact hfst.prodMk_nhds hvsq
    have hcomp : Tendsto (fun z : MorseModel n =>
        recombine hk (negPart hk z)
          (Real.sqrt ((‖negPart hk z‖ ^ 2 - 2 * ε) / ‖posPart hk z‖ ^ 2) • posPart hk z))
        (nhdsWithin y S) (nhds (recombine hk (negPart hk y) 0)) :=
      ((continuous_recombine hk).tendsto
        (x := (negPart hk y, (0 : EuclideanSpace ℝ (Fin (n - k)))))).comp hpair
    change Tendsto F (nhdsWithin y S) (nhds (F y))
    rw [hFy]
    exact hcomp

theorem continuousOn_modifiedCollarRetraction_sublevel {n k : ℕ} (hk : k ≤ n)
    (c ε δ : ℝ) :
    ContinuousOn (modifiedCollarRetraction hk c ε)
      {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε} := by
  let L : Set (MorseModel n) := {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}
  let inner : MorseModel n → MorseModel n := fun y =>
    if ‖negPart hk y‖ ^ 2 ≤ 2 * ε then spineMap hk y
    else recombine hk (negPart hk y)
      (Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) • posPart hk y)
  have hinnerOn : ContinuousOn inner (L ∩ closure {y : MorseModel n | ¬(morseNormalForm hk c y ≤ c - ε)}) := by
    have hge : L ∩ closure {y : MorseModel n | ¬(morseNormalForm hk c y ≤ c - ε)} ⊆
        {y : MorseModel n | c - ε ≤ morseNormalForm hk c y} := by
      intro y hy
      have hyc : y ∈ closure {z : MorseModel n | ¬(morseNormalForm hk c z ≤ c - ε)} := hy.2
      have hclosed : IsClosed {z : MorseModel n | c - ε ≤ morseNormalForm hk c z} :=
        isClosed_le continuous_const (contDiff_morseNormalForm hk c).continuous
      exact closure_minimal (by intro z hz; exact le_of_lt (lt_of_not_ge hz)) hclosed hyc
    have hin : ContinuousOn inner {y : MorseModel n | c - ε ≤ morseNormalForm hk c y} := by
      refine ContinuousOn.if ?_ ?_ ?_
      · intro y hy
        have hEq := negPart_sq_eq_of_mem_frontier hk ε hy.2
        have hspine : spineMap hk y = recombine hk (negPart hk y) 0 := rfl
        rw [hspine]
        congr 1
        rw [hEq]
        simp
      · exact (continuous_spineMap hk).continuousOn.mono (by intro y hy; exact hy.1)
      · exact (continuousOn_collarRatio hk c ε).mono (by
          intro y hy
          have hNge : 2 * ε ≤ ‖negPart hk y‖ ^ 2 := by
            have hclosed : IsClosed {z : MorseModel n | 2 * ε ≤ ‖negPart hk z‖ ^ 2} :=
              isClosed_le continuous_const
                ((contDiff_norm_sq ℝ (n := 0)).continuous.comp (continuous_negPart hk))
            exact closure_minimal (by intro z hz; exact le_of_lt (lt_of_not_ge hz)) hclosed hy.2
          exact ⟨hNge, hy.1⟩)
    exact hin.mono hge
  refine ContinuousOn.if ?_ ?_ hinnerOn
  · intro y hy
    have hEq := morseNormalForm_eq_of_mem_frontier_sublevel hk c ε hy.2
    by_cases hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε
    · have hpos := posPart_eq_zero_of_morseNormalForm_eq hk c ε hEq hb
      have hspine : spineMap hk y = y := by
        dsimp [spineMap]
        rw [← hpos]
        exact recombine_decompose hk y
      rw [if_pos hb]
      exact hspine.symm
    · have hr3 := recombine_ratio_eq_self_of_morseNormalForm_eq hk c ε hEq hb
      rw [if_neg hb]
      exact hr3.symm
  · exact continuous_id.continuousOn.mono (by intro y hy; exact hy.1)


private theorem continuousAt_collarRatioHomotopy {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (p : Set.Icc (0 : ℝ) 1 × MorseModel n) (hP : ‖posPart hk p.2‖ ≠ 0) :
    ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      recombine hk (negPart hk q.2)
        ((1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
          ‖posPart hk q.2‖ ^ 2)) • posPart hk q.2)) p := by
  have hnum : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      ‖negPart hk q.2‖ ^ 2 - 2 * ε) p :=
    ((contDiff_norm_sq ℝ (n := 0)).continuous.comp
      ((continuous_negPart hk).comp continuous_snd)).continuousAt.sub continuousAt_const
  have hden : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => ‖posPart hk q.2‖ ^ 2) p :=
    ((contDiff_norm_sq ℝ (n := 0)).continuous.comp
      ((continuous_posPart hk).comp continuous_snd)).continuousAt
  have hdenne : ‖posPart hk p.2‖ ^ 2 ≠ 0 :=
    (pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr hP
  have hdiv : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2) p :=
    hnum.div hden hdenne
  have hsqrt : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2)) p :=
    Real.continuous_sqrt.continuousAt.comp hdiv
  have ht : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => (q.1 : ℝ)) p :=
    (continuous_subtype_val.comp continuous_fst).continuousAt
  have hcoef : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
        ‖posPart hk q.2‖ ^ 2)) p :=
    ((continuousAt_const.sub ht).add (ht.mul hsqrt))
  have hsmul : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
        ‖posPart hk q.2‖ ^ 2)) • posPart hk q.2) p := by
    have hpair : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        (1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
          ‖posPart hk q.2‖ ^ 2), posPart hk q.2)) p :=
      ContinuousAt.prodMk hcoef ((continuous_posPart hk).comp continuous_snd).continuousAt
    exact continuous_smul.continuousAt.comp hpair
  have hpair2 : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (negPart hk q.2,
        (1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
          ‖posPart hk q.2‖ ^ 2)) • posPart hk q.2)) p :=
    ContinuousAt.prodMk ((continuous_negPart hk).comp continuous_snd).continuousAt hsmul
  exact (continuous_recombine hk).continuousAt.comp hpair2

private theorem continuousOn_collarRatioHomotopy {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      recombine hk (negPart hk p.2)
        ((1 - (p.1 : ℝ) + (p.1 : ℝ) * Real.sqrt ((‖negPart hk p.2‖ ^ 2 - 2 * ε) /
          ‖posPart hk p.2‖ ^ 2)) • posPart hk p.2))
      (Set.univ ×ˢ {y : MorseModel n | 2 * ε ≤ ‖negPart hk y‖ ^ 2 ∧ c - ε ≤ morseNormalForm hk c y}) := by
  let S : Set (MorseModel n) := {y : MorseModel n |
    2 * ε ≤ ‖negPart hk y‖ ^ 2 ∧ c - ε ≤ morseNormalForm hk c y}
  let P : Set (Set.Icc (0 : ℝ) 1 × MorseModel n) := Set.univ ×ˢ S
  let F : Set.Icc (0 : ℝ) 1 × MorseModel n → MorseModel n := fun p =>
    recombine hk (negPart hk p.2)
      ((1 - (p.1 : ℝ) + (p.1 : ℝ) * Real.sqrt ((‖negPart hk p.2‖ ^ 2 - 2 * ε) /
        ‖posPart hk p.2‖ ^ 2)) • posPart hk p.2)
  intro p hp
  by_cases hN : 2 * ε < ‖negPart hk p.2‖ ^ 2
  · have hP : ‖posPart hk p.2‖ ≠ 0 := by
      intro hz
      have hf : morseNormalForm hk c p.2 = c - (1 / 2) * ‖negPart hk p.2‖ ^ 2 := by
        rw [morseNormalForm_split]
        rw [hz]
        norm_num
        ring
      have hle : c - ε ≤ c - (1 / 2) * ‖negPart hk p.2‖ ^ 2 := by
        simpa [hf] using hp.2.2
      nlinarith [hN, hle]
    have hF := continuousAt_collarRatioHomotopy hk ε p hP
    have hUniv : ContinuousWithinAt F Set.univ p := hF.continuousWithinAt
    exact hUniv.mono (s := P) (by intro q hq; trivial)
  · have hN2 : ‖negPart hk p.2‖ ^ 2 = 2 * ε := le_antisymm (le_of_not_gt hN) hp.2.1
    have hFy : F p = recombine hk (negPart hk p.2) ((1 - (p.1 : ℝ)) • posPart hk p.2) := by
      dsimp [F]
      rw [hN2]
      simp
    have hsqrt0 : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        Real.sqrt (‖negPart hk q.2‖ ^ 2 - 2 * ε)) (nhdsWithin p P) (nhds 0) := by
      have hcont : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
          Real.sqrt (‖negPart hk q.2‖ ^ 2 - 2 * ε)) p := by
        have hnum : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
            ‖negPart hk q.2‖ ^ 2 - 2 * ε) p :=
          ((contDiff_norm_sq ℝ (n := 0)).continuous.comp
            ((continuous_negPart hk).comp continuous_snd)).continuousAt.sub continuousAt_const
        exact Real.continuous_sqrt.continuousAt.comp hnum
      have hmain : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
          Real.sqrt (‖negPart hk q.2‖ ^ 2 - 2 * ε)) (nhds p) (nhds 0) := by
        simpa [hN2] using hcont.tendsto
      exact hmain.mono_left nhdsWithin_le_nhds
    have hvsq : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2) • posPart hk q.2)
        (nhdsWithin p P) (nhds 0) := by
      have hsqueeze : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
          ‖Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2) • posPart hk q.2‖)
          (nhdsWithin p P) (nhds 0) := by
        apply squeeze_zero'
        · exact Eventually.of_forall (fun q => norm_nonneg _)
        · exact Eventually.of_forall (fun q => norm_ratio_smul_posPart_le hk ε q.2)
        · exact hsqrt0
      exact (tendsto_zero_iff_norm_tendsto_zero).2 hsqueeze
    have hfst : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => negPart hk q.2)
        (nhdsWithin p P) (nhds (negPart hk p.2)) :=
      ((continuous_negPart hk).comp continuous_snd).continuousWithinAt.tendsto
    have ht0c : ContinuousAt (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => (q.1 : ℝ)) p :=
      (continuous_subtype_val.comp continuous_fst).continuousAt
    have hpos : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => posPart hk q.2)
        (nhdsWithin p P) (nhds (posPart hk p.2)) :=
      ((continuous_posPart hk).comp continuous_snd).continuousWithinAt.tendsto
    have hpart1 : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        (1 - (q.1 : ℝ)) • posPart hk q.2)
        (nhdsWithin p P) (nhds ((1 - (p.1 : ℝ)) • posPart hk p.2)) := by
      have hpairo : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
          ((1 - (q.1 : ℝ)), posPart hk q.2))
          (nhdsWithin p P) (nhds ((1 - (p.1 : ℝ)), posPart hk p.2)) :=
        (continuousAt_const.sub ht0c).continuousWithinAt.tendsto.prodMk_nhds hpos
      have hsmulT : Tendsto (fun tw : ℝ × EuclideanSpace ℝ (Fin (n - k)) => tw.1 • tw.2)
          (nhds ((1 - (p.1 : ℝ)), posPart hk p.2))
          (nhds ((1 - (p.1 : ℝ)) • posPart hk p.2)) :=
        continuous_smul.tendsto ((1 - (p.1 : ℝ)), posPart hk p.2)
      exact hsmulT.comp hpairo
    have hpart2 : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        (q.1 : ℝ) • (Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2) •
          posPart hk q.2))
        (nhdsWithin p P) (nhds 0) := by
      have hpairs : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
          ((q.1 : ℝ), Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2) •
            posPart hk q.2))
          (nhdsWithin p P) (nhds ((p.1 : ℝ), (0 : EuclideanSpace ℝ (Fin (n - k))))) :=
        ht0c.continuousWithinAt.tendsto.prodMk_nhds hvsq
      have hsmulT : Tendsto (fun tw : ℝ × EuclideanSpace ℝ (Fin (n - k)) => tw.1 • tw.2)
          (nhds ((p.1 : ℝ), (0 : EuclideanSpace ℝ (Fin (n - k)))))
          (nhds ((p.1 : ℝ) • (0 : EuclideanSpace ℝ (Fin (n - k))))) :=
        continuous_smul.tendsto ((p.1 : ℝ), (0 : EuclideanSpace ℝ (Fin (n - k))))
      simpa using (hsmulT.comp hpairs)
    have hsum : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        (1 - (q.1 : ℝ)) • posPart hk q.2 +
          (q.1 : ℝ) • (Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) / ‖posPart hk q.2‖ ^ 2) •
            posPart hk q.2))
        (nhdsWithin p P) (nhds ((1 - (p.1 : ℝ)) • posPart hk p.2)) := by
      simpa using (hpart1.add hpart2)
    have hpair2 : Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        (negPart hk q.2,
          (1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
            ‖posPart hk q.2‖ ^ 2)) • posPart hk q.2))
        (nhdsWithin p P) (nhds (negPart hk p.2, (1 - (p.1 : ℝ)) • posPart hk p.2)) := by
      have hfuneq : (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
          (negPart hk q.2,
            (1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
              ‖posPart hk q.2‖ ^ 2)) • posPart hk q.2)) =
          (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
            (negPart hk q.2,
              (1 - (q.1 : ℝ)) • posPart hk q.2 +
                (q.1 : ℝ) • (Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
                  ‖posPart hk q.2‖ ^ 2) • posPart hk q.2))) := by
        funext q
        congr 1
        rw [add_smul]
        rw [smul_smul]
      rw [hfuneq]
      exact hfst.prodMk_nhds hsum
    have hcomp2 : Tendsto F (nhdsWithin p P) (nhds (F p)) := by
      change Tendsto (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        recombine hk (negPart hk q.2)
          ((1 - (q.1 : ℝ) + (q.1 : ℝ) * Real.sqrt ((‖negPart hk q.2‖ ^ 2 - 2 * ε) /
            ‖posPart hk q.2‖ ^ 2)) • posPart hk q.2))
        (nhdsWithin p P) (nhds (F p))
      rw [hFy]
      exact ((continuous_recombine hk).tendsto
        (x := (negPart hk p.2, (1 - (p.1 : ℝ)) • posPart hk p.2))).comp hpair2
    exact hcomp2

theorem continuousOn_modifiedCollarHomotopy_sublevel {n k : ℕ} (hk : k ≤ n)
    (c ε δ : ℝ) :
    ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2)
      (Set.univ ×ˢ {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}) := by
  let L : Set (MorseModel n) := {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}
  let P : Set (Set.Icc (0 : ℝ) 1 × MorseModel n) := Set.univ ×ˢ L
  let inner : Set.Icc (0 : ℝ) 1 × MorseModel n → MorseModel n := fun p =>
    if ‖negPart hk p.2‖ ^ 2 ≤ 2 * ε then
      recombine hk (negPart hk p.2) ((1 - (p.1 : ℝ)) • posPart hk p.2)
    else recombine hk (negPart hk p.2)
      ((1 - (p.1 : ℝ) + (p.1 : ℝ) * Real.sqrt ((‖negPart hk p.2‖ ^ 2 - 2 * ε) /
        ‖posPart hk p.2‖ ^ 2)) • posPart hk p.2)
  have hbCont : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      recombine hk (negPart hk p.2) ((1 - (p.1 : ℝ)) • posPart hk p.2)) := by
    have ht : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n => 1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have hsmul : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
        (1 - (p.1 : ℝ)) • posPart hk p.2) :=
      continuous_smul.comp (ht.prodMk ((continuous_posPart hk).comp continuous_snd))
    exact continuous_recombine hk |>.comp
      (((continuous_negPart hk).comp continuous_snd).prodMk hsmul)
  have hinnerOn : ContinuousOn inner (P ∩ closure {p | ¬(morseNormalForm hk c p.2 ≤ c - ε)}) := by
    have hge : P ∩ closure {p | ¬(morseNormalForm hk c p.2 ≤ c - ε)} ⊆
        Set.univ ×ˢ {y : MorseModel n | c - ε ≤ morseNormalForm hk c y} := by
      intro p hp
      have hclosed : IsClosed {q : Set.Icc (0 : ℝ) 1 × MorseModel n |
          c - ε ≤ morseNormalForm hk c q.2} :=
        isClosed_le continuous_const
          ((contDiff_morseNormalForm hk c).continuous.comp continuous_snd)
      exact ⟨trivial, closure_minimal (by intro q hq; exact le_of_lt (lt_of_not_ge hq)) hclosed hp.2⟩
    have hin : ContinuousOn inner (Set.univ ×ˢ {y : MorseModel n | c - ε ≤ morseNormalForm hk c y}) := by
      refine ContinuousOn.if ?_ ?_ ?_
      · intro p hp
        have hEq := frontier_eq_of_continuous_le
          (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => ‖negPart hk q.2‖ ^ 2)
          ((contDiff_norm_sq ℝ (n := 0)).continuous.comp
            ((continuous_negPart hk).comp continuous_snd)) (2 * ε) hp.2
        have hEq' : ‖negPart hk p.2‖ ^ 2 = 2 * ε := by simpa using hEq
        congr 1
        rw [hEq']
        simp
      · exact hbCont.continuousOn.mono (by intro p hp; exact hp.1)
      · exact (continuousOn_collarRatioHomotopy hk c ε).mono (by
          intro q hq
          have hNge : 2 * ε ≤ ‖negPart hk q.2‖ ^ 2 := by
            have hclosed : IsClosed {a : Set.Icc (0 : ℝ) 1 × MorseModel n |
                2 * ε ≤ ‖negPart hk a.2‖ ^ 2} :=
              isClosed_le continuous_const
                ((contDiff_norm_sq ℝ (n := 0)).continuous.comp
                  ((continuous_negPart hk).comp continuous_snd))
            have hsub : {a : Set.Icc (0 : ℝ) 1 × MorseModel n |
                ¬‖negPart hk a.2‖ ^ 2 ≤ 2 * ε} ⊆
                {a : Set.Icc (0 : ℝ) 1 × MorseModel n | 2 * ε ≤ ‖negPart hk a.2‖ ^ 2} := by
              intro a ha
              exact le_of_lt (lt_of_not_ge ha)
            exact closure_minimal hsub hclosed hq.2
          exact ⟨trivial, ⟨hNge, hq.1.2⟩⟩)
    exact hin.mono hge
  refine ContinuousOn.if ?_ ?_ hinnerOn
  · intro p hp
    have hEq := frontier_eq_of_continuous_le
      (fun q : Set.Icc (0 : ℝ) 1 × MorseModel n => morseNormalForm hk c q.2)
      ((contDiff_morseNormalForm hk c).continuous.comp continuous_snd) (c - ε) hp.2
    by_cases hb : ‖negPart hk p.2‖ ^ 2 ≤ 2 * ε
    · have hpos := posPart_eq_zero_of_morseNormalForm_eq hk c ε hEq hb
      have hstep : recombine hk (negPart hk p.2) ((1 - (p.1 : ℝ)) • posPart hk p.2) = p.2 := by
        rw [hpos, smul_zero]
        rw [← hpos]
        exact recombine_decompose hk p.2
      rw [if_pos hb]
      exact hstep.symm
    · have hr3 := recombine_ratio_homotopy_eq_self_of_morseNormalForm_eq hk c ε (p.1 : ℝ) hEq hb
      rw [if_neg hb]
      exact hr3.symm
  · exact (continuous_snd.comp continuous_id).continuousOn.mono (by intro p hp; exact hp.1)

private theorem lowerCellUnion_subset_modifiedSublevel {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n} (hy : y ∈ lowerCellUnion hk c ε) :
    modifiedNormalForm hk c ε δ y ≤ c - ε := by
  rcases hy with hf | hcell
  · have hfy : morseNormalForm hk c y ≤ c - ε := by simpa [sublevel] using hf
    exact le_trans (modifiedNormalForm_le_f hk c ε δ hε y) hfy
  · rcases hcell with ⟨x, hx⟩
    rw [← hx]
    exact modifiedNormalForm_cell_mem_lower hk c ε δ hε hδ x

private noncomputable def modifiedCollarRetractionC {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) :
    C({y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε}, lowerUnion hk c ε) :=
  ⟨fun y => ⟨modifiedCollarRetraction hk c ε y.1,
    modifiedCollarRetraction_mem_lowerCellUnion hk c ε hε y.1⟩, by
    have hcont : Continuous (fun y : {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        modifiedCollarRetraction hk c ε y.1) := by
      change Continuous (({y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}).restrict
        (modifiedCollarRetraction hk c ε))
      exact (continuousOn_iff_continuous_restrict).1 (continuousOn_modifiedCollarRetraction_sublevel hk c ε δ)
    exact (Topology.IsInducing.subtypeVal.continuous_iff).2 hcont⟩

private noncomputable def modifiedCollarInclusionC {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    C(lowerUnion hk c ε, {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε}) :=
  ⟨fun y => ⟨y.1, lowerCellUnion_subset_modifiedSublevel hk c ε δ hε hδ y.2⟩, by
    have hcont : Continuous (fun y : lowerUnion hk c ε => (y.1 : MorseModel n)) :=
      continuous_subtype_val
    exact (Topology.IsInducing.subtypeVal.continuous_iff).2 hcont⟩

noncomputable def modifiedCollarRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    Set.Icc (0 : ℝ) 1 × {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} →
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} :=
  fun p => ⟨modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) p.2.1,
    modifiedCollarHomotopy_mem_sublevel hk c ε δ hε hδ (by linarith [p.1.2.2]) (by linarith [p.1.2.1]) p.2.2⟩

noncomputable def modifiedCollarInclusionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (hε : 0 < ε) :
    Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε → lowerUnion hk c ε :=
  fun p => ⟨modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) p.2.1,
    modifiedCollarHomotopy_mem_lowerCellUnion hk c ε hε p.2.2⟩

theorem continuous_modifiedCollarRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    Continuous (modifiedCollarRetractionHomotopyFun hk c ε δ hε hδ) := by
  let S : Set (Set.Icc (0 : ℝ) 1 × MorseModel n) :=
    Set.univ ×ˢ {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}
  let F : Set.Icc (0 : ℝ) 1 × MorseModel n → MorseModel n := fun p =>
    modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2
  have hmainRestr : Continuous (S.restrict F) :=
    (continuousOn_iff_continuous_restrict).1 (continuousOn_modifiedCollarHomotopy_sublevel hk c ε δ)
  have hembed : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
      (⟨(p.1, (p.2.1 : MorseModel n)), ⟨trivial, p.2.2⟩⟩ : S)) := by
    exact Continuous.subtype_mk
      (f := fun p : Set.Icc (0 : ℝ) 1 ×
        {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        (p.1, (p.2.1 : MorseModel n)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (by intro p; exact ⟨trivial, p.2.2⟩)
  have hstep : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
      modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) := by
    have hc : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
        {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        (S.restrict F) (⟨(p.1, (p.2.1 : MorseModel n)), ⟨trivial, p.2.2⟩⟩ : S)) :=
      hmainRestr.comp hembed
    have hfun : (fun p : Set.Icc (0 : ℝ) 1 ×
        {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        (S.restrict F) (⟨(p.1, (p.2.1 : MorseModel n)), ⟨trivial, p.2.2⟩⟩ : S)) =
        (fun p : Set.Icc (0 : ℝ) 1 ×
        {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) := by
      funext p
      simp [S, F]
    rwa [← hfun]
  let reparam : Set.Icc (0 : ℝ) 1 ×
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} →
      Set.Icc (0 : ℝ) 1 × {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} :=
    fun p => ((⟨1 - (p.1 : ℝ), by linarith [p.1.2.2], by linarith [p.1.2.1]⟩ :
      Set.Icc (0 : ℝ) 1), p.2)
  have hreparam : Continuous reparam := by
    have ht : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
        {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        (⟨1 - (p.1 : ℝ), by linarith [p.1.2.2], by linarith [p.1.2.1]⟩ :
          Set.Icc (0 : ℝ) 1)) := by
      exact Continuous.subtype_mk
        (f := fun p : Set.Icc (0 : ℝ) 1 ×
          {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
          1 - (p.1 : ℝ))
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
        (by intro p; exact ⟨by linarith [p.1.2.2], by linarith [p.1.2.1]⟩)
    simpa [reparam] using (ht.prodMk continuous_snd)
  have hcont : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
      modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) p.2.1) := by
    have hcomp := hstep.comp hreparam
    have hfun : (fun p : Set.Icc (0 : ℝ) 1 ×
        {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
        modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) p.2.1) =
        ((fun p : Set.Icc (0 : ℝ) 1 ×
          {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
          modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) ∘ reparam) := by
      funext p
      simp [reparam]
    change Continuous ((fun p : Set.Icc (0 : ℝ) 1 ×
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε} =>
      modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) ∘ reparam)
    exact hcomp
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 hcont

theorem continuous_modifiedCollarInclusionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    Continuous (modifiedCollarInclusionHomotopyFun hk c ε hε) := by
  let S : Set (Set.Icc (0 : ℝ) 1 × MorseModel n) :=
    Set.univ ×ˢ {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}
  let F : Set.Icc (0 : ℝ) 1 × MorseModel n → MorseModel n := fun p =>
    modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2
  have hmainRestr : Continuous (S.restrict F) :=
    (continuousOn_iff_continuous_restrict).1 (continuousOn_modifiedCollarHomotopy_sublevel hk c ε δ)
  have hembed : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      (⟨(p.1, (p.2.1 : MorseModel n)), ⟨trivial,
        lowerCellUnion_subset_modifiedSublevel hk c ε δ hε hδ p.2.2⟩⟩ : S)) := by
    exact Continuous.subtype_mk
      (f := fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
        (p.1, (p.2.1 : MorseModel n)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (by intro p; exact ⟨trivial, lowerCellUnion_subset_modifiedSublevel hk c ε δ hε hδ p.2.2⟩)
  have hstep : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) := by
    have hc : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
        (S.restrict F) (⟨(p.1, (p.2.1 : MorseModel n)), ⟨trivial,
          lowerCellUnion_subset_modifiedSublevel hk c ε δ hε hδ p.2.2⟩⟩ : S)) :=
      hmainRestr.comp hembed
    have hfun : (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
        (S.restrict F) (⟨(p.1, (p.2.1 : MorseModel n)), ⟨trivial,
          lowerCellUnion_subset_modifiedSublevel hk c ε δ hε hδ p.2.2⟩⟩ : S)) =
        (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
        modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) := by
      funext p
      simp [S, F]
    rwa [← hfun]
  let reparam : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε →
      Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε :=
    fun p => ((⟨1 - (p.1 : ℝ), by linarith [p.1.2.2], by linarith [p.1.2.1]⟩ :
      Set.Icc (0 : ℝ) 1), p.2)
  have hreparam : Continuous reparam := by
    have ht : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
        (⟨1 - (p.1 : ℝ), by linarith [p.1.2.2], by linarith [p.1.2.1]⟩ :
          Set.Icc (0 : ℝ) 1)) := by
      exact Continuous.subtype_mk
        (f := fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε => 1 - (p.1 : ℝ))
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
        (by intro p; exact ⟨by linarith [p.1.2.2], by linarith [p.1.2.1]⟩)
    simpa [reparam] using (ht.prodMk continuous_snd)
  have hcont : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) p.2.1) := by
    have hcomp := hstep.comp hreparam
    have hfun : (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
        modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) p.2.1) =
        ((fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
          modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) ∘ reparam) := by
      funext p
      simp [reparam]
    change Continuous ((fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      modifiedCollarHomotopy hk c ε (p.1 : ℝ) p.2.1) ∘ reparam)
    exact hcomp
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 hcont

theorem modifiedCollarRetractionHomotopyFun_zero {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (y : {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε}) :
    modifiedCollarRetractionHomotopyFun hk c ε δ hε hδ (⟨0, by norm_num⟩, y) =
      (modifiedCollarInclusionC hk c ε δ hε hδ).comp
        (modifiedCollarRetractionC hk c ε δ hε) y := by
  apply Subtype.ext
  dsimp [modifiedCollarRetractionHomotopyFun, modifiedCollarInclusionC, modifiedCollarRetractionC]
  rw [sub_zero]
  exact modifiedCollarHomotopy_one hk c ε y.1

theorem modifiedCollarRetractionHomotopyFun_one {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (y : {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε}) :
    modifiedCollarRetractionHomotopyFun hk c ε δ hε hδ (⟨1, by norm_num⟩, y) = y := by
  apply Subtype.ext
  dsimp [modifiedCollarRetractionHomotopyFun]
  rw [sub_self]
  exact modifiedCollarHomotopy_zero hk c ε y.1

theorem modifiedCollarInclusionHomotopyFun_zero {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (z : lowerUnion hk c ε) :
    modifiedCollarInclusionHomotopyFun hk c ε hε (⟨0, by norm_num⟩, z) =
      (modifiedCollarRetractionC hk c ε δ hε).comp
        (modifiedCollarInclusionC hk c ε δ hε hδ) z := by
  apply Subtype.ext
  dsimp [modifiedCollarInclusionHomotopyFun, modifiedCollarRetractionC, modifiedCollarInclusionC]
  rw [sub_zero]
  exact modifiedCollarHomotopy_one hk c ε z.1

theorem modifiedCollarInclusionHomotopyFun_one {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (hε : 0 < ε) (z : lowerUnion hk c ε) :
    modifiedCollarInclusionHomotopyFun hk c ε hε (⟨1, by norm_num⟩, z) = z := by
  apply Subtype.ext
  dsimp [modifiedCollarInclusionHomotopyFun]
  rw [sub_self]
  exact modifiedCollarHomotopy_zero hk c ε z.1

noncomputable def modifiedCollarRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ContinuousMap.Homotopy
      ((modifiedCollarInclusionC hk c ε δ hε hδ).comp
        (modifiedCollarRetractionC hk c ε δ hε))
      (ContinuousMap.id {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε}) where
  toFun := ContinuousMap.mk (modifiedCollarRetractionHomotopyFun hk c ε δ hε hδ)
    (continuous_modifiedCollarRetractionHomotopyFun hk c ε δ hε hδ)
  map_zero_left := by
    intro y
    exact modifiedCollarRetractionHomotopyFun_zero hk c ε δ hε hδ y
  map_one_left := by
    intro y
    exact modifiedCollarRetractionHomotopyFun_one hk c ε δ hε hδ y

noncomputable def modifiedCollarInclusionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ContinuousMap.Homotopy
      ((modifiedCollarRetractionC hk c ε δ hε).comp
        (modifiedCollarInclusionC hk c ε δ hε hδ))
      (ContinuousMap.id (lowerUnion hk c ε)) where
  toFun := ContinuousMap.mk (modifiedCollarInclusionHomotopyFun hk c ε hε)
    (continuous_modifiedCollarInclusionHomotopyFun hk c ε δ hε hδ)
  map_zero_left := by
    intro z
    exact modifiedCollarInclusionHomotopyFun_zero hk c ε δ hε hδ z
  map_one_left := by
    intro z
    exact modifiedCollarInclusionHomotopyFun_one hk c ε hε z

noncomputable def modifiedSublevelHomotopyEquiv {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ContinuousMap.HomotopyEquiv
      {y : MorseModel n // modifiedNormalForm hk c ε δ y ≤ c - ε}
      (lowerUnion hk c ε) where
  toFun := modifiedCollarRetractionC hk c ε δ hε
  invFun := modifiedCollarInclusionC hk c ε δ hε hδ
  left_inv := ⟨modifiedCollarRetractionHomotopy hk c ε δ hε hδ⟩
  right_inv := ⟨modifiedCollarInclusionHomotopy hk c ε δ hε hδ⟩

theorem modifiedNormalForm_eq_of_modulation_zero {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    {y : MorseModel n} (hy : modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ = 0) :
    modifiedNormalForm hk c ε δ y = morseNormalForm hk c y := by
  dsimp [modifiedNormalForm]
  rw [hy]
  ring

theorem modMu_mul_modGamma_eq_zero_of_norm_gt {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n y ^ 2) :
    modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ = 0 := by
  by_contra h
  have hmu : modMu ε (‖negPart hk y‖ ^ 2) ≠ 0 := by
    intro h0
    exact h (by rw [h0]; simp)
  have hga : modGamma δ ‖posPart hk y‖ ≠ 0 := by
    intro h0
    exact h (by rw [h0]; simp)
  have hN : ‖negPart hk y‖ ^ 2 < 4 * ε := by
    have hst : Real.smoothTransition ((‖negPart hk y‖ ^ 2 - 2 * ε) / (2 * ε)) ≠ 1 := by
      intro hst
      apply hmu
      dsimp [modMu]
      rw [hst]
      ring
    have hlt : (‖negPart hk y‖ ^ 2 - 2 * ε) / (2 * ε) < 1 := by
      by_contra hge
      have h1 : 1 ≤ (‖negPart hk y‖ ^ 2 - 2 * ε) / (2 * ε) := le_of_not_gt hge
      exact hst (Real.smoothTransition.eq_one_iff_one_le.mpr h1)
    rw [div_lt_one (by positivity : 0 < 2 * ε)] at hlt
    linarith
  have hP : ‖posPart hk y‖ < 3 * δ / 2 := by
    have hst : Real.smoothTransition ((2 * ‖posPart hk y‖ - δ) / δ) ≠ 1 := by
      intro hst
      apply hga
      dsimp [modGamma]
      rw [hst]
      norm_num
    have hlt : (2 * ‖posPart hk y‖ - δ) / δ < 1 := by
      by_contra hge
      have h1 : 1 ≤ (2 * ‖posPart hk y‖ - δ) / δ := le_of_not_gt hge
      exact hst (Real.smoothTransition.eq_one_iff_one_le.mpr h1)
    rw [div_lt_one hδ] at hlt
    linarith
  have hnorm : morseNorm n y ^ 2 < 4 * ε + 9 * δ ^ 2 / 4 := by
    have hP2 : ‖posPart hk y‖ ^ 2 < 9 * δ ^ 2 / 4 := by
      have hsq : ‖posPart hk y‖ ^ 2 < (3 * δ / 2) ^ 2 := by
        simpa [pow_two] using (mul_self_lt_mul_self (norm_nonneg (posPart hk y)) hP)
      nlinarith [hsq]
    rw [morseNorm_sq_eq_negPart_add_posPart hk y]
    nlinarith [hN, hP2]
  exact (not_lt_of_ge (le_of_lt hy)) hnorm

private lemma morseNorm_recombine_scale_le {n k : ℕ} (hk : k ≤ n)
    (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k))) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    morseNorm n (recombine hk a (s • b)) ≤ morseNorm n (recombine hk a b) := by
  have h1 : morseNorm n (recombine hk a (s • b)) ^ 2 ≤ morseNorm n (recombine hk a b) ^ 2 := by
    rw [morseNorm_sq_eq_negPart_add_posPart hk (recombine hk a (s • b)),
      morseNorm_sq_eq_negPart_add_posPart hk (recombine hk a b)]
    have hna : negPart hk (recombine hk a (s • b)) = a := by
      ext i
      simp [negPart, recombine_negPart]
    have hpa : posPart hk (recombine hk a (s • b)) = s • b := by
      ext j
      simp [posPart, recombine_posPart]
    have hnb : negPart hk (recombine hk a b) = a := by
      ext i
      simp [negPart, recombine_negPart]
    have hpb : posPart hk (recombine hk a b) = b := by
      ext j
      simp [posPart, recombine_posPart]
    rw [hna, hpa, hnb, hpb]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    have habs : |s| ≤ |(1 : ℝ)| := by
      rw [abs_of_nonneg hs0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      exact hs1
    nlinarith [sq_le_sq.mpr habs, sq_nonneg ‖b‖]
  have hnn : 0 ≤ morseNorm n (recombine hk a (s • b)) := norm_nonneg _
  have hny : 0 ≤ morseNorm n (recombine hk a b) := norm_nonneg _
  have habs := sq_le_sq.mp h1
  rwa [abs_of_nonneg hnn, abs_of_nonneg hny] at habs

theorem morseNorm_modifiedCollarHomotopy_le {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : MorseModel n) :
    morseNorm n (modifiedCollarHomotopy hk c ε t y) ≤ morseNorm n y := by
  by_cases hf : morseNormalForm hk c y ≤ c - ε
  · dsimp [modifiedCollarHomotopy]
    rw [if_pos hf]
  · by_cases hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε
    · have hcoef0 : 0 ≤ 1 - t := by linarith
      have hcoef1 : 1 - t ≤ 1 := by linarith
      dsimp [modifiedCollarHomotopy]
      rw [if_neg hf, if_pos hb]
      calc
        morseNorm n (recombine hk (negPart hk y) ((1 - t) • posPart hk y))
            ≤ morseNorm n (recombine hk (negPart hk y) (posPart hk y)) :=
          morseNorm_recombine_scale_le hk (negPart hk y) (posPart hk y) hcoef0 hcoef1
        _ = morseNorm n y := by rw [recombine_decompose]
    · have hNPlt : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by
        have hgt : c - ε < morseNormalForm hk c y := lt_of_not_ge hf
        rw [morseNormalForm_split] at hgt
        nlinarith
      have hP : ‖posPart hk y‖ ^ 2 ≠ 0 := by
        intro hP
        apply hf
        have hN : 2 * ε < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hb
        rw [morseNormalForm_split]
        have hP0 : ‖posPart hk y‖ = 0 := by exact sq_eq_zero_iff.mp hP
        nlinarith [sq_nonneg ‖negPart hk y‖, hN]
      have hPpos : 0 < ‖posPart hk y‖ ^ 2 :=
        sq_pos_of_ne_zero ((pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hP)
      have hNge : 0 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
        exact sub_nonneg.mpr (le_of_lt (lt_of_not_ge hb))
      have hratio : (‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2 ≤ 1 := by
        exact le_of_lt ((div_lt_one hPpos).2 hNPlt)
      have hs0 : 0 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) :=
        Real.sqrt_nonneg _
      have hs1 : Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) ≤ 1 := by
        exact Real.sqrt_le_one.mpr hratio
      have hcoef0 : 0 ≤ 1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) := by
        nlinarith [ht0, hs0]
      have hcoef1 : 1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2) ≤ 1 := by
        nlinarith [ht0, hs1]
      dsimp [modifiedCollarHomotopy]
      rw [if_neg hf, if_neg hb]
      calc
        morseNorm n (recombine hk (negPart hk y)
            ((1 - t + t * Real.sqrt ((‖negPart hk y‖ ^ 2 - 2 * ε) / ‖posPart hk y‖ ^ 2)) •
              posPart hk y))
            ≤ morseNorm n (recombine hk (negPart hk y) (posPart hk y)) :=
          morseNorm_recombine_scale_le hk (negPart hk y) (posPart hk y) hcoef0 hcoef1
        _ = morseNorm n y := by rw [recombine_decompose]

theorem modifiedCollarHomotopy_fix_cell {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (hε : 0 < ε) {t : ℝ} {y : MorseModel n}
    (hy : y ∈ Set.range (fun x : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))) :
    modifiedCollarHomotopy hk c ε t y = y := by
  rcases hy with ⟨x, hx⟩
  have hpos : posPart hk y = 0 := by
    rw [← hx]
    ext j
    simp [posPart, cellMap_posIdx]
  by_cases hfy : morseNormalForm hk c y ≤ c - ε
  · dsimp [modifiedCollarHomotopy]
    rw [if_pos hfy]
  · have hb : ‖negPart hk y‖ ^ 2 ≤ 2 * ε := by
      rw [← hx]
      have hnp : negPart hk (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) =
          (Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin k)) := by
        ext i
        simp [negPart, cellMap_negIdx]
      rw [hnp]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hxle : ‖(x : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := x.2
      have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := Real.sq_sqrt (by positivity)
      have hsq' : (Real.sqrt (2 * ε) * ‖(x : EuclideanSpace ℝ (Fin k))‖) ^ 2 =
          (Real.sqrt (2 * ε)) ^ 2 * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by ring
      have hxle2 : ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
        have habs : |‖(x : EuclideanSpace ℝ (Fin k))‖| ≤ |(1 : ℝ)| := by
          rw [abs_of_nonneg (norm_nonneg (x : EuclideanSpace ℝ (Fin k))),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
          exact hxle
        simpa using (sq_le_sq.mpr habs)
      have hbnd : (Real.sqrt (2 * ε)) ^ 2 * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
          (Real.sqrt (2 * ε)) ^ 2 := by
        simpa using (mul_le_mul_of_nonneg_left hxle2 (sq_nonneg (Real.sqrt (2 * ε))))
      nlinarith [hsq, hsq', hbnd]
    dsimp [modifiedCollarHomotopy]
    rw [if_neg hfy, if_pos hb]
    rw [hpos, smul_zero]
    rw [← hpos]
    exact recombine_decompose hk y

theorem modifiedCollarHomotopy_eq_self_of_lower {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) {t : ℝ}
    {y : MorseModel n} (hy : morseNormalForm hk c y ≤ c - ε) :
    modifiedCollarHomotopy hk c ε t y = y := by
  dsimp [modifiedCollarHomotopy]
  rw [if_pos hy]

end

end DifferentialGeometry.Topology.Morse.CellAttachment
