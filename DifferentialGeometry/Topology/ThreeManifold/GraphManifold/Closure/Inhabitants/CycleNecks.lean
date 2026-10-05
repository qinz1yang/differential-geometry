import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NeckBox
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleBalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleRim
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

/-!
Four actual stereographic necks separate the two polar caps and the inner and outer radial bands.
Their explicit rational outer radius preserves the native antipodal radius-four normalization.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold GC.Endpoint
open scoped ContDiff Manifold Topology InnerProductSpace

namespace GC.GraphManifold.Assembly

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

local instance cycleNecksDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private def cycleOuterRadius : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := 4 / (1 + t)
  invFun r := 4 / r - 1
  source := Ioi (-1)
  target := Ioi 0
  map_source' t ht := by
    change -1 < t at ht
    change 0 < 4 / (1 + t)
    exact div_pos (by norm_num) (by linarith)
  map_target' r hr := by
    change 0 < r at hr
    change -1 < 4 / r - 1
    have h : 0 < (4 : ℝ) / r := div_pos (by norm_num) hr
    linarith
  left_inv' t ht := by
    change -1 < t at ht
    have hn : 1 + t ≠ 0 := by linarith [ht]
    change 4 / (4 / (1 + t)) - 1 = t
    field_simp [hn]
    ring
  right_inv' r hr := by
    change 0 < r at hr
    have hn : r ≠ 0 := ne_of_gt hr
    change 4 / (1 + (4 / r - 1)) = r
    field_simp [hn]
    ring
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  contMDiffOn_toFun := ((contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
    (by intro t ht; change -1 < t at ht; change 1 + t ≠ 0; linarith)) :
      ContDiffOn ℝ ∞ (fun t : ℝ => 4 / (1 + t)) (Ioi (-1))).contMDiffOn
  contMDiffOn_invFun := ((contDiffOn_const.div contDiffOn_id
    (by intro r hr; exact ne_of_gt (show 0 < r from hr))).sub contDiffOn_const :
      ContDiffOn ℝ ∞ (fun r : ℝ => 4 / r - 1) (Ioi 0)).contMDiffOn

private def cycleInnerRadius : ℝ ≃ₘ[ℝ] ℝ where
  toFun t := 1 + t
  invFun r := r - 1
  left_inv t := by dsimp; ring
  right_inv r := by dsimp; ring
  contMDiff_toFun := contMDiff_const.add contMDiff_id
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

private def cycleNeckRadiusPD (b e : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
  if Bool.xor b e then cycleOuterRadius else cycleInnerRadius.toPartialDiffeomorph

private def cycleNeckDirection (b : Bool) : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
  (Handle.stereoChart northPole).symm.trans
    (if b then sphereAntipodalDiffeomorph.toPartialDiffeomorph else
      (Diffeomorph.refl (𝓡 2) S2 ∞).toPartialDiffeomorph)

private def cycleNeckFull (b e : Bool) : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    (E2 × ℝ) (NoCuts.carrier standardThreeSphereLift.{0}).Carrier ∞ :=
  ((DifferentialGeometry.Topology.PartialDiffeomorph.prod (cycleNeckDirection b)
    (cycleNeckRadiusPD b e)).trans (spherePolarChart (n := 2) southPole)).trans
      (cycleBallAmbient false)

private theorem cycleNeckFull_mem (b e : Bool) {p : E2 × ℝ}
    (hp : p ∈ neckDomain (1 / 16)) : p ∈ (cycleNeckFull b e).source := by
  have ht : -1 < p.2 := by have h := (abs_lt.mp hp.2).1; linarith
  have ha : p.1 ∈ (cycleNeckDirection b).source := by
    have h : p.1 ∈ (Handle.stereoChart northPole).target := by
      rw [Handle.stereoChart_target]
      exact mem_univ _
    cases b <;> exact ⟨h, trivial⟩
  have hr : p.2 ∈ (cycleNeckRadiusPD b e).source ∧ 0 < cycleNeckRadiusPD b e p.2 := by
    cases b <;> cases e
    · change True ∧ 0 < 1 + p.2
      exact ⟨trivial, by linarith⟩
    · change -1 < p.2 ∧ 0 < 4 / (1 + p.2)
      exact ⟨ht, div_pos (by norm_num) (by linarith)⟩
    · change -1 < p.2 ∧ 0 < 4 / (1 + p.2)
      exact ⟨ht, div_pos (by norm_num) (by linarith)⟩
    · change True ∧ 0 < 1 + p.2
      exact ⟨trivial, by linarith⟩
  change ((p.1 ∈ (cycleNeckDirection b).source ∧
    p.2 ∈ (cycleNeckRadiusPD b e).source) ∧ 0 < cycleNeckRadiusPD b e p.2) ∧ _
  refine ⟨⟨⟨ha, hr.1⟩, hr.2⟩, ?_⟩
  change spherePolarChart (n := 2) southPole
    (cycleNeckDirection b p.1, cycleNeckRadiusPD b e p.2) ∈ (cycleBallAmbient false).source
  rw [cycleBallAmbient_source]
  exact mem_univ _

def cycleNeck (b e : Bool) : PartialDiffeomorph 𝓘(ℝ, E2 × ℝ) (𝓡 3)
    (E2 × ℝ) (NoCuts.carrier standardThreeSphereLift.{0}).Carrier ∞ := by
  have D := restrictNeck (cycleNeckFull b e) (neckDomain (1 / 16)) (isOpen_neckDomain _)
  exact
    { toPartialEquiv := D.toPartialEquiv
      open_source := D.open_source
      open_target := D.open_target
      contMDiffOn_toFun := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact D.contMDiffOn_toFun
      contMDiffOn_invFun := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact D.contMDiffOn_invFun }

theorem cycleNeck_source (b e : Bool) : (cycleNeck b e).source = neckDomain (1 / 16) := by
  exact restrictNeck_source_of_subset (cycleNeckFull b e) (isOpen_neckDomain (1 / 16))
    (fun p hp => cycleNeckFull_mem b e hp)

private theorem cycleNeck_apply (b e : Bool) (p : E2 × ℝ) :
    cycleNeck b e p = cycleBallAmbient false
      (cycleNeckRadiusPD b e p.2 • (cycleNeckDirection b p.1 : E3)) := rfl

private theorem cycleNeckDirection_apply (b : Bool) (x : E2) :
    cycleNeckDirection b x = if b then -(Handle.stereoChart northPole).symm x else
      (Handle.stereoChart northPole).symm x := by
  cases b <;> rfl

private theorem cycleNeckDirection_negative {x : E2} (hx : ‖x‖ < 9 / 8) :
    ⟪((Handle.stereoChart northPole).symm x : E3), (northPole : E3)⟫_ℝ < 0 := by
  rw [Handle.inner_stereoChart_symm]
  apply div_neg_of_neg_of_pos
  · nlinarith [norm_nonneg x]
  · positivity

private theorem cycleNeckRadius_positive (b e : Bool) {p : E2 × ℝ}
    (hp : p ∈ neckDomain (1 / 16)) : 0 < cycleNeckRadiusPD b e p.2 := by
  have hl := (abs_lt.mp hp.2).1
  cases b <;> cases e
  · change 0 < 1 + p.2
    linarith
  · change 0 < 4 / (1 + p.2)
    exact div_pos (by norm_num) (by linarith)
  · change 0 < 4 / (1 + p.2)
    exact div_pos (by norm_num) (by linarith)
  · change 0 < 1 + p.2
    linarith

private theorem cycleNeckRadius_band (b e : Bool) {p : E2 × ℝ}
    (hp : p ∈ neckDomain (1 / 16)) :
    if Bool.xor b e then 3 < cycleNeckRadiusPD b e p.2 else
      cycleNeckRadiusPD b e p.2 < 2 := by
  have hl := (abs_lt.mp hp.2).1
  have hu := (abs_lt.mp hp.2).2
  cases b <;> cases e
  · change 1 + p.2 < 2
    linarith
  · change 3 < 4 / (1 + p.2)
    rw [lt_div_iff₀ (by linarith : 0 < 1 + p.2)]
    linarith
  · change 3 < 4 / (1 + p.2)
    rw [lt_div_iff₀ (by linarith : 0 < 1 + p.2)]
    linarith
  · change 1 + p.2 < 2
    linarith

theorem cycleNeck_disjoint {b e b' e' : Bool} (h : (b, e) ≠ (b', e')) :
    Disjoint (cycleNeck b e).target (cycleNeck b' e').target := by
  rw [Set.disjoint_left]
  intro z hz hz'
  let p := (cycleNeck b e).symm z
  let q := (cycleNeck b' e').symm z
  have hp : p ∈ neckDomain (1 / 16) := by
    rw [← cycleNeck_source b e]
    exact (cycleNeck b e).map_target hz
  have hq : q ∈ neckDomain (1 / 16) := by
    rw [← cycleNeck_source b' e']
    exact (cycleNeck b' e').map_target hz'
  have hm : cycleNeck b e p = cycleNeck b' e' q :=
    ((cycleNeck b e).right_inv hz).trans ((cycleNeck b' e').right_inv hz').symm
  rw [cycleNeck_apply, cycleNeck_apply] at hm
  have hc := (cycleBallAmbient false).injOn
    (by rw [cycleBallAmbient_source]; exact mem_univ _)
    (by rw [cycleBallAmbient_source]; exact mem_univ _) hm
  have hrp := cycleNeckRadius_positive b e hp
  have hrq := cycleNeckRadius_positive b' e' hq
  by_cases hbb : b = b'
  · subst b'
    have hn := congrArg norm hc
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrp,
      norm_eq_of_mem_sphere, mul_one, norm_smul, Real.norm_eq_abs, abs_of_pos hrq,
      norm_eq_of_mem_sphere, mul_one] at hn
    have hb := cycleNeckRadius_band b e hp
    have hb' := cycleNeckRadius_band b e' hq
    cases b <;> cases e <;> cases e'
    all_goals first
      | exact (h rfl).elim
      | simp [Bool.xor] at hb hb'; linarith
  · have hd := congrArg (sphereDirection southPole) hc
    rw [sphereDirection_pos_smul southPole (cycleNeckDirection b p.1) hrp,
      sphereDirection_pos_smul southPole (cycleNeckDirection b' q.1) hrq] at hd
    rw [cycleNeckDirection_apply, cycleNeckDirection_apply] at hd
    have hi := congrArg (fun θ : S2 => ⟪(θ : E3), (northPole : E3)⟫_ℝ) hd
    have hp' := cycleNeckDirection_negative (show ‖p.1‖ < 9 / 8 by linarith [hp.1])
    have hq' := cycleNeckDirection_negative (show ‖q.1‖ < 9 / 8 by linarith [hq.1])
    cases b <;> cases b'
    · exact (hbb rfl).elim
    · change ⟪((Handle.stereoChart northPole).symm p.1 : E3), (northPole : E3)⟫_ℝ =
        ⟪-((Handle.stereoChart northPole).symm q.1 : E3), (northPole : E3)⟫_ℝ at hi
      rw [inner_neg_left] at hi
      linarith
    · change ⟪-((Handle.stereoChart northPole).symm p.1 : E3), (northPole : E3)⟫_ℝ =
        ⟪((Handle.stereoChart northPole).symm q.1 : E3), (northPole : E3)⟫_ℝ at hi
      rw [inner_neg_left] at hi
      linarith
    · exact (hbb rfl).elim

end GC.GraphManifold.Assembly
