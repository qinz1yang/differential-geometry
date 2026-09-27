/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SmoothNormalForm
import DifferentialGeometry.Topology.Morse.ConnectingOrbit

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Morse

noncomputable def saddleLevelPoint (ε : ℝ) (side : Bool) (t : ℝ) : MorseModel 2 :=
  ![if side then Real.sqrt (2 * ε + t ^ 2) else -Real.sqrt (2 * ε + t ^ 2), t]

theorem contDiff_saddleLevelPoint {ε : ℝ} (hε : 0 < ε) (side : Bool) :
    ContDiff ℝ ∞ (saddleLevelPoint ε side) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (2 * ε + t ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun t => by positivity)
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t : ℝ => if side then _ else _)
    cases side
    · exact hs.neg
    · exact hs
  · change ContDiff ℝ ∞ (fun t : ℝ => t)
    exact contDiff_id

theorem saddleLevelPoint_injective {ε : ℝ} (hε : 0 < ε) :
    Injective (fun p : Bool × ℝ => saddleLevelPoint ε p.1 p.2) := by
  rintro ⟨b, s⟩ ⟨d, t⟩ heq
  have ht : s = t := congrArg (fun z : MorseModel 2 => z 1) heq
  subst t
  have hx := congrArg (fun z : MorseModel 2 => z 0) heq
  have hpos : 0 < Real.sqrt (2 * ε + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  cases b <;> cases d
  · rfl
  · change -Real.sqrt (2 * ε + s ^ 2) = Real.sqrt (2 * ε + s ^ 2) at hx
    linarith
  · change Real.sqrt (2 * ε + s ^ 2) = -Real.sqrt (2 * ε + s ^ 2) at hx
    linarith
  · rfl

theorem norm_saddleLevelPoint_le {ε R t : ℝ} (hR : 0 ≤ R)
    (hεR : 2 * ε ≤ R ^ 2) (ht : |t| ≤ R) (side : Bool) :
    ‖saddleLevelPoint ε side t‖ ≤ 2 * R := by
  have hs : Real.sqrt (2 * ε + t ^ 2) ≤ 2 * R := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have ht2 : t ^ 2 ≤ R ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) hR).2 ht
    nlinarith [sq_nonneg R]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * R)).mpr
  intro i
  fin_cases i
  · cases side
    · change ‖-Real.sqrt (2 * ε + t ^ 2)‖ ≤ 2 * R
      simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hs
    · change ‖Real.sqrt (2 * ε + t ^ 2)‖ ≤ 2 * R
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hs
  · change ‖t‖ ≤ 2 * R
    simpa only [Real.norm_eq_abs] using ht.trans (by linarith : R ≤ 2 * R)

theorem saddleLevelPoint_height {ε : ℝ} (hε : 0 ≤ ε) (side : Bool) (t c : ℝ) :
    c + ((saddleLevelPoint ε side t 1) ^ 2 - (saddleLevelPoint ε side t 0) ^ 2) / 2 =
      c - ε := by
  have hs : (Real.sqrt (2 * ε + t ^ 2)) ^ 2 = 2 * ε + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  cases side
  · change c + (t ^ 2 - (-Real.sqrt (2 * ε + t ^ 2)) ^ 2) / 2 = c - ε
    rw [neg_sq, hs]
    ring
  · change c + (t ^ 2 - (Real.sqrt (2 * ε + t ^ 2)) ^ 2) / 2 = c - ε
    rw [hs]
    ring

theorem exists_saddleLevelPoint_of_sq_eq {ε : ℝ} {z : MorseModel 2}
    (hz : z 0 ^ 2 = 2 * ε + z 1 ^ 2) : ∃ side : Bool, saddleLevelPoint ε side (z 1) = z := by
  have hs : (Real.sqrt (2 * ε + z 1 ^ 2)) ^ 2 = 2 * ε + z 1 ^ 2 :=
    Real.sq_sqrt (hz ▸ sq_nonneg (z 0))
  have he : z 0 = Real.sqrt (2 * ε + z 1 ^ 2) ∨
      z 0 = -Real.sqrt (2 * ε + z 1 ^ 2) := sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans hs.symm)
  rcases he with he | he
  · refine ⟨true, ?_⟩
    ext i
    fin_cases i
    · exact he.symm
    · rfl
  · refine ⟨false, ?_⟩
    ext i
    fin_cases i
    · exact he.symm
    · rfl

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_section_of_unique_descendingConnection {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    {p q : M} (hp : I.IsInteriorPoint p) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1) {γ : ℝ → M}
    (hγ : IsDescendingConnection I f v p q γ)
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    {O : Set M} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, MorseModel 2) I (MorseModel 2) M ∞,
      0 ∈ χ.source ∧ χ 0 = p ∧
      (∀ z ∈ χ.source, f (χ z) = f p + (z 1 ^ 2 - z 0 ^ 2) / 2) ∧
      ∃ R ε T : ℝ, ∃ side : Bool,
        0 < R ∧ 0 < ε ∧ 2 * ε ≤ R ^ 2 ∧ f p - ε ∈ Ioo (f q) (f p) ∧
        (∀ z, ‖z‖ ≤ 2 * R → z ∈ χ.source ∧ χ z ∈ O) ∧
        let A : Bool → ℝ → M := fun b t => χ (saddleLevelPoint ε b t)
        (∀ b, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (A b) (Icc (-R) R)) ∧
        (∀ b, Topology.IsClosedEmbedding (fun t : Icc (-R) R => A b t)) ∧
        (∀ b, A b '' Icc (-R) R ⊆ O ∩ f ⁻¹' {f p - ε}) ∧
        Disjoint (A false '' Icc (-R) R) (A true '' Icc (-R) R) ∧
        (⋃ b, A b '' Icc (-R) R) =
          {x | x ∈ χ.target ∧ |χ.symm x 1| ≤ R ∧ f x = f p - ε} ∧
        (∃ t ∈ Ioo (-R) R, A side t = γ T) ∧
        connectingLocus I f v p q ∩ A side '' Icc (-R) R = {γ T} ∧
        connectingLocus I f v p q ∩ A (!side) '' Icc (-R) R = ∅ := by
  obtain ⟨χ, hχ0, hχp, hn, _⟩ := exists_interior_morse_normal_form I f hf p
    hp 1 (by decide) hnd hindex
  have hnormal (z : MorseModel 2) (hz : z ∈ χ.source) :
      f (χ z) = f p + (z 1 ^ 2 - z 0 ^ 2) / 2 := by
    rw [hn z hz]
    simp only [morseNormalForm, Nat.reduceSub, Fin.sum_univ_one]
    change f p + 1 / 2 * (-z 0 ^ 2 + z 1 ^ 2) = _
    ring
  have hnhds : χ.source ∩ χ ⁻¹' O ∈ 𝓝 (0 : MorseModel 2) :=
    inter_mem (χ.open_source.mem_nhds hχ0)
      ((χ.contMDiffOn.continuousOn.continuousAt (χ.open_source.mem_nhds hχ0)).preimage_mem_nhds
        (hO.mem_nhds (hχp.symm ▸ hpO)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let R := r / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall (z : MorseModel 2) (hz : ‖z‖ ≤ 2 * R) : z ∈ χ.source ∧ χ z ∈ O := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [R] at hz
    linarith
  have hballR : Metric.ball (0 : MorseModel 2) R ⊆ χ.source := by
    intro z hz
    have hzr : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact (hsmall z (hzr.le.trans (by linarith))).1
  have hopen := χ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hballR
  have hpimage : p ∈ χ '' Metric.ball (0 : MorseModel 2) R :=
    ⟨0, by simpa only [Metric.mem_ball, dist_self] using hR, hχp⟩
  obtain ⟨T, z, hz, hzT⟩ := (hγ.2.1.eventually (hopen.mem_nhds hpimage)).exists
  change χ z = γ T at hzT
  have hzR : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzs : z ∈ χ.source := hballR hz
  let ε := f p - f (γ T)
  have hε : 0 < ε := sub_pos.mpr (hγ.value_mem_Ioo hf T).2
  have he : f (γ T) = f p - ε := by dsimp [ε]; ring
  have hsq : z 0 ^ 2 = 2 * ε + z 1 ^ 2 := by
    have hnz := hnormal z hzs
    rw [hzT, he] at hnz
    linarith
  have hcoord (i : Fin 2) : |z i| < R := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm z i).trans_lt hzR
  have hεR : 2 * ε ≤ R ^ 2 := by
    have hz02 : z 0 ^ 2 ≤ R ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z 0)) hR.le).2 (hcoord 0).le
    nlinarith [sq_nonneg (z 1)]
  have hc : f p - ε ∈ Ioo (f q) (f p) := he ▸ hγ.value_mem_Ioo hf T
  obtain ⟨side, hside⟩ := exists_saddleLevelPoint_of_sq_eq hsq
  let A : Bool → ℝ → M := fun b t => χ (saddleLevelPoint ε b t)
  have hpoints (b : Bool) (t : ℝ) (ht : t ∈ Icc (-R) R) :
      saddleLevelPoint ε b t ∈ χ.source ∧ A b t ∈ O :=
    hsmall _ (norm_saddleLevelPoint_le hR.le hεR (abs_le.mpr ht) b)
  have hheight (b : Bool) (t : ℝ) (ht : t ∈ Icc (-R) R) : f (A b t) = f p - ε := by
    exact (hnormal _ (hpoints b t ht).1).trans (saddleLevelPoint_height hε.le b t (f p))
  have hsm (b : Bool) : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (A b) (Icc (-R) R) :=
    χ.contMDiffOn.comp (contDiff_saddleLevelPoint hε b).contMDiff.contMDiffOn
      (fun t ht => (hpoints b t ht).1)
  have hjoint {b d : Bool} {s t : ℝ} (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R)
      (hh : A b s = A d t) : (b, s) = (d, t) :=
    saddleLevelPoint_injective hε (χ.injOn (hpoints b s hs).1 (hpoints d t ht).1 hh)
  have hclosed (b : Bool) : Topology.IsClosedEmbedding (fun t : Icc (-R) R => A b t) := by
    apply (hsm b).continuousOn.domRestrict.isClosedEmbedding
    intro s t heq
    apply Subtype.ext
    exact congrArg Prod.snd (hjoint s.2 t.2 heq)
  have hdis (b : Bool) : Disjoint (A b '' Icc (-R) R) (A (!b) '' Icc (-R) R) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    have heqb : b = !b := congrArg Prod.fst (hjoint hs ht heq.symm)
    cases b <;> cases heqb
  have hunion : (⋃ b, A b '' Icc (-R) R) =
      {x | x ∈ χ.target ∧ |χ.symm x 1| ≤ R ∧ f x = f p - ε} := by
    ext x
    constructor
    · intro hmem
      rcases mem_iUnion.mp hmem with ⟨b, t, ht, rfl⟩
      have hi : χ.symm (χ (saddleLevelPoint ε b t)) = saddleLevelPoint ε b t :=
        χ.left_inv (hpoints b t ht).1
      refine ⟨χ.map_source (hpoints b t ht).1, ?_, hheight b t ht⟩
      change |χ.symm (χ (saddleLevelPoint ε b t)) 1| ≤ R
      rw [hi]
      exact abs_le.mpr ht
    · rintro ⟨hxt, ht, hfval⟩
      have hnz := hnormal (χ.symm x) (χ.map_target hxt)
      have hinv : χ (χ.symm x) = x := χ.right_inv hxt
      rw [hinv, hfval] at hnz
      have hsquare : χ.symm x 0 ^ 2 = 2 * ε + χ.symm x 1 ^ 2 := by linarith
      obtain ⟨b, hb⟩ := exists_saddleLevelPoint_of_sq_eq hsquare
      apply mem_iUnion.mpr
      refine ⟨b, χ.symm x 1, abs_le.mp ht, ?_⟩
      change χ (saddleLevelPoint ε b (χ.symm x 1)) = x
      rw [hb]
      exact hinv
  have hhit : A side (z 1) = γ T := by
    change χ (saddleLevelPoint ε side (z 1)) = γ T
    rw [hside, hzT]
  have hzI : z 1 ∈ Ioo (-R) R := abs_lt.mp (hcoord 1)
  have hx : connectingLocus I f v p q ∩ f ⁻¹' {f p - ε} = {γ T} := by
    simpa only [he] using hγ.connectingLocus_inter_level hf hunique T
  have hsubset (b : Bool) : A b '' Icc (-R) R ⊆ O ∩ f ⁻¹' {f p - ε} := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨(hpoints b t ht).2, hheight b t ht⟩
  have hin : γ T ∈ A side '' Icc (-R) R := ⟨z 1, Ioo_subset_Icc_self hzI, hhit⟩
  have hselect : connectingLocus I f v p q ∩ A side '' Icc (-R) R = {γ T} := by
    apply Subset.antisymm
    · intro y hy
      rw [← hx]
      exact ⟨hy.1, (hsubset side hy.2).2⟩
    · rintro y rfl
      exact ⟨⟨γ, hγ, T, rfl⟩, hin⟩
  refine ⟨χ, hχ0, hχp, hnormal, R, ε, T, side, hR, hε, hεR, hc, hsmall,
    hsm, hclosed, hsubset, hdis false, hunion, ⟨z 1, hzI, hhit⟩, hselect, ?_⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hym : y ∈ ({γ T} : Set M) := by
    rw [← hx]
    exact ⟨hy.1, (hsubset (!side) hy.2).2⟩
  have hyT : y = γ T := hym
  subst y
  exact Set.disjoint_left.mp (hdis side) hin hy.2

end DifferentialGeometry.Morse
