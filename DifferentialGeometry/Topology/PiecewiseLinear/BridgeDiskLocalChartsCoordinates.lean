/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskLocalChartsComparison
import DifferentialGeometry.Topology.PiecewiseLinear.StandardBoxBridge

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local notation "Q" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "C₀" => (J ×ˢ J) ×ˢ I
local notation "A₀" => ({((0 : ℝ), (0 : ℝ))} ×ˢ I)
local notation "B₀" => (I ×ˢ {(0 : ℝ)}) ×ˢ I
local notation "O₀" => (Set.prod (Set.prod (Ioo (-1 / 4 : ℝ) (1 / 4)) (Ioo (-1 / 4 : ℝ) (1 / 4)))
  (Ioo (-1 / 4 : ℝ) (1 / 4)))

theorem IsPLHomeomorphOn.exists_open_chart_of_model
    {ι : Type*} {U : Set E} {V : Set Q} {f : E → Q} {x : E}
    (hf : IsPLHomeomorphOn f U V) (hU : IsOpen U) (hV : IsOpen V) (hx : x ∈ U)
    (e : Q ≃ᵃ[ℝ] Q) {O : Set Q} (hO : IsOpen O) (h0 : (0 : Q) ∈ O)
    (hfx : f x = e 0) {S : ι → Set E} {T Z : ι → Set Q}
    (hmap : ∀ i, f '' (U ∩ S i) = V ∩ T i)
    (hmodel : ∀ p ∈ O, ∀ i, e p ∈ T i ↔ p ∈ Z i) :
    ∃ (U' : Set E) (V' : Set Q) (g : E → Q), IsOpen U' ∧ IsOpen V' ∧ x ∈ U' ∧
      (0 : Q) ∈ V' ∧ IsPLHomeomorphOn g U' V' ∧ g x = 0 ∧
      ∀ z ∈ U', ∀ i, z ∈ S i ↔ g z ∈ Z i := by
  have he := isPLHomeomorphOn_univ_of_affineEquiv e
  have hei := isPLHomeomorphOn_univ_of_affineEquiv e.symm
  have heO : IsOpen (e '' O) := he.isOpen_image_of_isOpen isOpen_univ hO (subset_univ _)
  let U' := U ∩ f ⁻¹' (e '' O)
  have hU' : IsOpen U' := hf.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU heO
  have hx' : x ∈ U' := ⟨hx, ⟨0, h0, hfx.symm⟩⟩
  have himage : IsOpen (f '' U') := hf.isOpen_image_of_isOpen hV hU' inter_subset_left
  have hV' : IsOpen (e.symm '' (f '' U')) :=
    hei.isOpen_image_of_isOpen isOpen_univ himage (subset_univ _)
  have hg := (hf.restrict_isOpen hU' inter_subset_left himage).trans
    (hei.restrict_isOpen himage (subset_univ _) hV')
  have hgx : (e.symm ∘ f) x = 0 := by simp only [Function.comp_apply, hfx, e.symm_apply_apply]
  refine ⟨U', e.symm '' (f '' U'), e.symm ∘ f, hU', hV', hx',
    hgx ▸ hg.bijOn.mapsTo hx', hg, hgx, ?_⟩
  intro z hz i
  have hzO : e.symm (f z) ∈ O := by
    obtain ⟨p, hp, heq⟩ := hz.2
    rw [← heq, e.symm_apply_apply]
    exact hp
  have hmem : z ∈ S i ↔ f z ∈ T i := by
    constructor
    · intro hzS
      exact ((hmap i).subset ⟨z, ⟨hz.1, hzS⟩, rfl⟩).2
    · intro hzT
      obtain ⟨w, hw, heq⟩ := (hmap i).symm.subset ⟨hf.bijOn.mapsTo hz.1, hzT⟩
      exact hf.bijOn.injOn hw.1 hz.1 heq ▸ hw.2
  exact hmem.trans (by
    simpa only [e.apply_symm_apply, Function.comp_apply] using hmodel (e.symm (f z)) hzO i)

theorem IsBridgeDisk.exists_left_endpoint_chart
    {C A B : Set E} {a b : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C) :
    ∃ (U : Set E) (V : Set Q) (f : E → Q), IsOpen U ∧ IsOpen V ∧ a ∈ U ∧
      (0 : Q) ∈ V ∧ IsPLHomeomorphOn f U V ∧ f a = 0 ∧
      ∀ z ∈ U,
        (z ∈ C ↔ 0 ≤ (f z).1.2) ∧ (z ∈ frontier C ↔ (f z).1.2 = 0) ∧
        (z ∈ B ↔ (f z).1.1 = 0 ∧ 0 ≤ (f z).1.2 ∧ 0 ≤ (f z).2) ∧
        (z ∈ B ∩ frontier C ↔ (f z).1.1 = 0 ∧ (f z).1.2 = 0 ∧ 0 ≤ (f z).2) ∧
        (z ∈ A ↔ (f z).1.1 = 0 ∧ 0 ≤ (f z).1.2 ∧ (f z).2 = 0) := by
  obtain ⟨U, V, f, hU, hV, haU, h0V, hf, hfa, hfC, hfF, hfB, hfβ, hfA⟩ :=
    h.exists_local_equivalence_at_endpoints isBridgeDisk_standardBox_axis hdim
      (by simp [Module.finrank_prod]) hC isPLBall_standardBox (Or.inl rfl) (Or.inl rfl)
  obtain ⟨hO, h0O, _, _, he0, hemodel⟩ := standardBoxBridgeLeftChart_on_openBox
  let S : Fin 5 → Set E := ![C, frontier C, B, B ∩ frontier C, A]
  let T : Fin 5 → Set Q := ![C₀, frontier C₀, B₀, B₀ ∩ frontier C₀, A₀]
  let Z : Fin 5 → Set Q := ![{p | 0 ≤ p.1.2}, {p | p.1.2 = 0},
    {p | p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2}, {p | p.1.1 = 0 ∧ p.1.2 = 0 ∧ 0 ≤ p.2},
    {p | p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 = 0}]
  have hmap : ∀ i, f '' (U ∩ S i) = V ∩ T i := by
    intro i
    fin_cases i
    · exact hfC
    · exact hfF
    · exact hfB
    · exact hfβ
    · exact hfA
  have hmodel : ∀ p ∈ O₀, ∀ i, standardBoxBridgeLeftChart p ∈ T i ↔ p ∈ Z i := by
    intro p hp i
    obtain ⟨h1, h2, h3, h4, h5⟩ := hemodel p hp
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  obtain ⟨U', V', g, hU', hV', haU', h0V', hg, hga, hflags⟩ :=
    hf.exists_open_chart_of_model hU hV haU standardBoxBridgeLeftChart hO h0O
      (hfa.trans he0.symm) hmap hmodel
  exact ⟨U', V', g, hU', hV', haU', h0V', hg, hga, fun z hz =>
    ⟨hflags z hz 0, hflags z hz 1, hflags z hz 2, hflags z hz 3, hflags z hz 4⟩⟩

theorem IsBridgeDisk.exists_right_endpoint_chart
    {C A B : Set E} {a b : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C) :
    ∃ (U : Set E) (V : Set Q) (f : E → Q), IsOpen U ∧ IsOpen V ∧ b ∈ U ∧
      (0 : Q) ∈ V ∧ IsPLHomeomorphOn f U V ∧ f b = 0 ∧
      ∀ z ∈ U,
        (z ∈ C ↔ 0 ≤ (f z).1.2) ∧ (z ∈ frontier C ↔ (f z).1.2 = 0) ∧
        (z ∈ B ↔ (f z).1.1 = 0 ∧ 0 ≤ (f z).1.2 ∧ (f z).2 ≤ 0) ∧
        (z ∈ B ∩ frontier C ↔ (f z).1.1 = 0 ∧ (f z).1.2 = 0 ∧ (f z).2 ≤ 0) ∧
        (z ∈ A ↔ (f z).1.1 = 0 ∧ 0 ≤ (f z).1.2 ∧ (f z).2 = 0) := by
  obtain ⟨U, V, f, hU, hV, hbU, h1V, hf, hfb, hfC, hfF, hfB, hfβ, hfA⟩ :=
    h.exists_local_equivalence_at_endpoints isBridgeDisk_standardBox_axis hdim
      (by simp [Module.finrank_prod]) hC isPLBall_standardBox (Or.inr rfl) (Or.inr rfl)
  obtain ⟨hO, h0O, _, _, he0, hemodel⟩ := standardBoxBridgeRightChart_on_openBox
  let S : Fin 5 → Set E := ![C, frontier C, B, B ∩ frontier C, A]
  let T : Fin 5 → Set Q := ![C₀, frontier C₀, B₀, B₀ ∩ frontier C₀, A₀]
  let Z : Fin 5 → Set Q := ![{p | 0 ≤ p.1.2}, {p | p.1.2 = 0},
    {p | p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 ≤ 0}, {p | p.1.1 = 0 ∧ p.1.2 = 0 ∧ p.2 ≤ 0},
    {p | p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 = 0}]
  have hmap : ∀ i, f '' (U ∩ S i) = V ∩ T i := by
    intro i
    fin_cases i
    · exact hfC
    · exact hfF
    · exact hfB
    · exact hfβ
    · exact hfA
  have hmodel : ∀ p ∈ O₀, ∀ i, standardBoxBridgeRightChart p ∈ T i ↔ p ∈ Z i := by
    intro p hp i
    obtain ⟨h1, h2, h3, h4, h5⟩ := hemodel p hp
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  obtain ⟨U', V', g, hU', hV', hbU', h0V', hg, hgb, hflags⟩ :=
    hf.exists_open_chart_of_model hU hV hbU standardBoxBridgeRightChart hO h0O
      (hfb.trans he0.symm) hmap hmodel
  exact ⟨U', V', g, hU', hV', hbU', h0V', hg, hgb, fun z hz =>
    ⟨hflags z hz 0, hflags z hz 1, hflags z hz 2, hflags z hz 3, hflags z hz 4⟩⟩

theorem IsBridgeDisk.exists_frontier_chart
    {C A B : Set E} {a b x : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C)
    (hxβ : x ∈ B ∩ frontier C) (hxends : x ∉ ({a, b} : Set E)) :
    ∃ (U : Set E) (V : Set Q) (f : E → Q), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧
      (0 : Q) ∈ V ∧ IsPLHomeomorphOn f U V ∧ f x = 0 ∧
      ∀ z ∈ U,
        (z ∈ C ↔ 0 ≤ (f z).1.2) ∧ (z ∈ frontier C ↔ (f z).1.2 = 0) ∧
        (z ∈ B ↔ (f z).1.1 = 0 ∧ 0 ≤ (f z).1.2) ∧
        (z ∈ B ∩ frontier C ↔ (f z).1.1 = 0 ∧ (f z).1.2 = 0) ∧ z ∉ A := by
  have hmβ : (((1 / 2 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈ B₀ ∩ frontier C₀ := by
    have hm := standardBoxBridgeMiddleChart_on_openBox
    have hz := (hm.2.2.2.2.2 0 hm.2.1).2.2.2.1.mpr (by simp)
    simpa only [hm.2.2.2.2.1] using hz
  have hmends : (((1 / 2 : ℝ), (0 : ℝ)), (0 : ℝ)) ∉
      ({(((0 : ℝ), (0 : ℝ)), (0 : ℝ)), (((0 : ℝ), (0 : ℝ)), (1 : ℝ))} : Set Q) := by
    norm_num
  obtain ⟨U, V, f, hU, hV, hxU, hmV, hf, hfx, hfC, hfF, hfB, hfβ, hfA⟩ :=
    h.exists_local_equivalence_at_frontier isBridgeDisk_standardBox_axis hdim
      (by simp [Module.finrank_prod]) hC isPLBall_standardBox hxβ hmβ hxends hmends
  obtain ⟨hO, h0O, _, _, he0, hemodel⟩ := standardBoxBridgeMiddleChart_on_openBox
  let S : Fin 5 → Set E := ![C, frontier C, B, B ∩ frontier C, A]
  let T : Fin 5 → Set Q := ![C₀, frontier C₀, B₀, B₀ ∩ frontier C₀, A₀]
  let Z : Fin 5 → Set Q := ![{p | 0 ≤ p.1.2}, {p | p.1.2 = 0},
    {p | p.1.1 = 0 ∧ 0 ≤ p.1.2}, {p | p.1.1 = 0 ∧ p.1.2 = 0}, ∅]
  have hmap : ∀ i, f '' (U ∩ S i) = V ∩ T i := by
    intro i
    fin_cases i
    · exact hfC
    · exact hfF
    · exact hfB
    · exact hfβ
    · exact hfA
  have hmodel : ∀ p ∈ O₀, ∀ i, standardBoxBridgeMiddleChart p ∈ T i ↔ p ∈ Z i := by
    intro p hp i
    obtain ⟨h1, h2, h3, h4, h5⟩ := hemodel p hp
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact iff_false_intro h5
  obtain ⟨U', V', g, hU', hV', hxU', h0V', hg, hgx, hflags⟩ :=
    hf.exists_open_chart_of_model hU hV hxU standardBoxBridgeMiddleChart hO h0O
      (hfx.trans he0.symm) hmap hmodel
  refine ⟨U', V', g, hU', hV', hxU', h0V', hg, hgx, fun z hz =>
    ⟨hflags z hz 0, hflags z hz 1, hflags z hz 2, hflags z hz 3, ?_⟩⟩
  exact fun hA => (hflags z hz 4).mp hA

end DifferentialGeometry.Topology.PiecewiseLinear
