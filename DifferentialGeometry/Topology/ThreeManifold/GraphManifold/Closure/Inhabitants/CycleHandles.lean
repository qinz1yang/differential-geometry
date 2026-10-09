import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleBalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleProfile
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
Two opposite polar disk handles in the genuine stereographic shell use the strictly increasing
radius interpolation. Their local coordinates extend across every corner of the compact source.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold GC.Endpoint
open scoped ContDiff Manifold Topology InnerProductSpace

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

local instance cycleHandlesDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private def cycleHandleInterval : Set ℝ := Ioo (-1 / 2) (3 / 2)

private theorem cycleHandleRadius_strict : StrictMonoOn cycleHandleRadius cycleHandleInterval := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-1 / 2) (3 / 2))
  · exact cycleHandleRadius_smooth.continuousOn.mono (by
      intro t ht
      change t < 2
      linarith [ht.2])
  · intro t ht
    have ht' := interior_subset ht
    exact cycleHandleRadius_deriv_pos (by linarith [ht'.2])

private theorem cycleHandleRadius_positive {t : ℝ} (ht : t ∈ cycleHandleInterval) :
    0 < cycleHandleRadius t := by
  by_cases hsmall : t ≤ 1 / 4
  · rw [cycleHandleRadius_inner hsmall]
    linarith [ht.1]
  · have hquarter : (1 / 4 : ℝ) ∈ cycleHandleInterval := by constructor <;> norm_num
    have h := cycleHandleRadius_strict hquarter ht (not_le.mp hsmall)
    rw [cycleHandleRadius_inner le_rfl] at h
    linarith

private theorem cycleHandleRadius_local :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ cycleHandleRadius cycleHandleInterval := by
  have hs : ContDiffOn ℝ ∞ cycleHandleRadius cycleHandleInterval :=
    cycleHandleRadius_smooth.mono (by intro t ht; change t < 2; linarith [ht.2])
  apply hs.contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv isOpen_Ioo (by simp)
  intro t ht
  rw [mfderiv_eq_fderiv]
  have hi : Injective (fderiv ℝ cycleHandleRadius t) := by
    intro x y hxy
    simp only [fderiv_eq_deriv_mul] at hxy
    exact mul_left_cancel₀ (cycleHandleRadius_deriv_pos (by linarith [ht.2])).ne' hxy
  have hb : Bijective (fderiv ℝ cycleHandleRadius t) :=
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ cycleHandleRadius t)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2), rfl⟩

private theorem cycleHandleRadius_pd_exists :
    ∃ D : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D.source = cycleHandleInterval ∧ D.target = cycleHandleRadius '' cycleHandleInterval ∧
        (D : ℝ → ℝ) = cycleHandleRadius :=
  DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    cycleHandleRadius_local isOpen_Ioo ⟨0, by constructor <;> norm_num⟩
      cycleHandleRadius_strict.injOn

private def cycleHandleRadiusPD := Classical.choose cycleHandleRadius_pd_exists

private theorem cycleHandleRadiusPD_source :
    cycleHandleRadiusPD.source = cycleHandleInterval :=
  (Classical.choose_spec cycleHandleRadius_pd_exists).1

private theorem cycleHandleRadiusPD_apply (t : ℝ) :
    cycleHandleRadiusPD t = cycleHandleRadius t :=
  congrFun (Classical.choose_spec cycleHandleRadius_pd_exists).2.2 t

private def cycleHandleReverse : ℝ ≃ₘ[ℝ] ℝ where
  toFun t := 1 - t
  invFun t := 1 - t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  contMDiff_toFun := contMDiff_const.sub contMDiff_id
  contMDiff_invFun := contMDiff_const.sub contMDiff_id

private def cycleHandleTime (b : Bool) : ℝ ≃ₘ[ℝ] ℝ :=
  if b then cycleHandleReverse else Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞

private def cycleHandleAngle (b : Bool) : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
  (Handle.stereoChart northPole).symm.trans
    (if b then sphereAntipodalDiffeomorph.toPartialDiffeomorph else
      (Diffeomorph.refl (𝓡 2) S2 ∞).toPartialDiffeomorph)

def cycleHandleChart (b : Bool) : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    (E2 × ℝ) (NoCuts.carrier standardThreeSphereLift.{0}).Carrier ∞ :=
  (((DifferentialGeometry.Topology.PartialDiffeomorph.prod (cycleHandleAngle b)
    ((cycleHandleTime b).toPartialDiffeomorph.trans cycleHandleRadiusPD)).trans
      (spherePolarChart (n := 2) southPole)).trans (cycleBallAmbient false))

theorem cycleHandleChart_source (b : Bool) :
    (cycleHandleChart b).source = univ ×ˢ Ioo (-1 / 2) (3 / 2) := by
  ext p
  change (((p.1 ∈ (cycleHandleAngle b).source ∧
    p.2 ∈ ((cycleHandleTime b).toPartialDiffeomorph.trans cycleHandleRadiusPD).source) ∧
    0 < cycleHandleRadiusPD (cycleHandleTime b p.2)) ∧
    (spherePolarChart (n := 2) southPole (cycleHandleAngle b p.1,
      cycleHandleRadiusPD (cycleHandleTime b p.2))) ∈ (cycleBallAmbient false).source) ↔
        (True ∧ p.2 ∈ Ioo (-1 / 2) (3 / 2))
  rw [cycleBallAmbient_source, cycleHandleRadiusPD_apply]
  have ha : p.1 ∈ (cycleHandleAngle b).source := by
    have hs : p.1 ∈ (Handle.stereoChart northPole).target := by
      rw [Handle.stereoChart_target]
      exact mem_univ _
    cases b <;> exact ⟨hs, trivial⟩
  have ht : p.2 ∈ ((cycleHandleTime b).toPartialDiffeomorph.trans cycleHandleRadiusPD).source ↔
      p.2 ∈ cycleHandleInterval := by
    change (True ∧ cycleHandleTime b p.2 ∈ cycleHandleRadiusPD.source) ↔ _
    rw [cycleHandleRadiusPD_source]
    cases b
    · change (True ∧ p.2 ∈ cycleHandleInterval) ↔ p.2 ∈ cycleHandleInterval
      simp only [true_and]
    · change (True ∧ (-1 / 2 < 1 - p.2 ∧ 1 - p.2 < 3 / 2)) ↔
        (-1 / 2 < p.2 ∧ p.2 < 3 / 2)
      constructor
      · intro h
        constructor <;> linarith [h.2.1, h.2.2]
      · intro h
        exact ⟨trivial, by constructor <;> linarith [h.1, h.2]⟩
  constructor
  · intro h
    exact ⟨trivial, ht.mp h.1.1.2⟩
  · intro h
    have hmem := ht.mpr h.2
    have ht' : cycleHandleTime b p.2 ∈ cycleHandleInterval := by
      have hh := hmem.2
      change cycleHandleTime b p.2 ∈ cycleHandleRadiusPD.source at hh
      rwa [cycleHandleRadiusPD_source] at hh
    exact ⟨⟨⟨ha, hmem⟩, cycleHandleRadius_positive ht'⟩, mem_univ _⟩

private def cycleHandleInclusion : ClosedCell 2 × Icc (0 : ℝ) 1 → E2 × ℝ :=
  Prod.map Subtype.val Subtype.val

private theorem cycleHandleInclusion_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      cycleHandleInclusion :=
  (isSmoothEmbedding_closedCell_inclusion 1).contMDiff.prodMap
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))

private theorem cycleHandleInclusion_bijective (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      cycleHandleInclusion p) := by
  have hi := (isSmoothEmbedding_closedCell_inclusion 1).prodMap
    (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  exact bijective_mfderiv_of_isImmersionAt ((𝓡∂ 2).prod (𝓡∂ 1))
    ((𝓡 2).prod 𝓘(ℝ, ℝ)) cycleHandleInclusion p
    (hi.isImmersion.isImmersionAt p) (by simp)

private theorem cycleHandleInclusion_mem (b : Bool) (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    cycleHandleInclusion p ∈ (cycleHandleChart b).source := by
  rw [cycleHandleChart_source]
  exact ⟨trivial, by
    dsimp [cycleHandleInclusion]
    constructor <;> linarith [p.2.property.1, p.2.property.2]⟩

def cycleS3Handle (b : Bool) : EdgeHandle (NoCuts.carrier standardThreeSphereLift.{0}) where
  map := cycleHandleChart b ∘ cycleHandleInclusion
  smooth := by
    intro p
    exact ((cycleHandleChart b).contMDiffOn_toFun.contMDiffAt
      ((cycleHandleChart b).open_source.mem_nhds (cycleHandleInclusion_mem b p))).comp p
        (cycleHandleInclusion_smooth p)
  mfderiv_bijective p := by
    have hd : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (cycleHandleChart b) (cycleHandleInclusion p) :=
      ((cycleHandleChart b).contMDiffOn_toFun.contMDiffAt
        ((cycleHandleChart b).open_source.mem_nhds (cycleHandleInclusion_mem b p)))
          |>.mdifferentiableAt (by simp)
    rw [mfderiv_comp p hd (cycleHandleInclusion_smooth.mdifferentiableAt (by simp))]
    exact (((cycleHandleChart b).isLocalDiffeomorphAt _ _ ∞
      (cycleHandleInclusion_mem b p)).mfderivToContinuousLinearEquiv (by simp)).bijective.comp
        (cycleHandleInclusion_bijective p)
  injective := by
    intro p q hpq
    have h := (cycleHandleChart b).injOn (cycleHandleInclusion_mem b p)
      (cycleHandleInclusion_mem b q) hpq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  interior := by intro x hx; exact BoundarylessManifold.isInteriorPoint


private theorem cycleHandleAngle_apply (b : Bool) (x : E2) :
    cycleHandleAngle b x =
      if b then -(Handle.stereoChart northPole).symm x else
        (Handle.stereoChart northPole).symm x := by
  cases b <;> rfl

theorem cycleHandleChart_apply (b : Bool) (p : E2 × ℝ) :
    cycleHandleChart b p = cycleBallAmbient false
      (cycleHandleRadius (if b then 1 - p.2 else p.2) •
        ((cycleHandleAngle b p.1 : S2) : E3)) := by
  change cycleBallAmbient false
    (cycleHandleRadiusPD (cycleHandleTime b p.2) • (cycleHandleAngle b p.1 : E3)) = _
  rw [cycleHandleRadiusPD_apply]
  cases b <;> rfl

private theorem cycleHandleAngle_negative (x : ClosedCell 2) :
    ⟪((Handle.stereoChart northPole).symm x.val : E3), (northPole : E3)⟫_ℝ < 0 := by
  rw [Handle.inner_stereoChart_symm]
  apply div_neg_of_neg_of_pos
  · have hn := x.property
    have hn0 := norm_nonneg x.val
    nlinarith
  · positivity

theorem cycleS3Handle_disjoint : Disjoint (range (cycleS3Handle false).map)
    (range (cycleS3Handle true).map) := by
  rw [Set.disjoint_left]
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  change cycleHandleChart true (cycleHandleInclusion q) =
    cycleHandleChart false (cycleHandleInclusion p) at hq
  rw [cycleHandleChart_apply, cycleHandleChart_apply] at hq
  have he := (cycleBallAmbient false).injOn
    (by rw [cycleBallAmbient_source]; exact mem_univ _)
    (by rw [cycleBallAmbient_source]; exact mem_univ _) hq
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  have hp0 : 0 < cycleHandleRadius p.2.val :=
    cycleHandleRadius_positive (by constructor <;> linarith [p.2.property.1, p.2.property.2])
  have hq0 : 0 < cycleHandleRadius (1 - q.2.val) :=
    cycleHandleRadius_positive (by constructor <;> linarith [q.2.property.1, q.2.property.2])
  have hdir := congrArg (sphereDirection southPole) he
  change sphereDirection southPole
    (cycleHandleRadius (1 - q.2.val) • (cycleHandleAngle true q.1.val : E3)) =
      sphereDirection southPole
        (cycleHandleRadius p.2.val • (cycleHandleAngle false p.1.val : E3)) at hdir
  rw [sphereDirection_pos_smul southPole (cycleHandleAngle true q.1.val) hq0,
    sphereDirection_pos_smul southPole (cycleHandleAngle false p.1.val) hp0] at hdir
  rw [cycleHandleAngle_apply, cycleHandleAngle_apply] at hdir
  simp only [Bool.false_eq_true, ↓reduceIte] at hdir
  have hinner := congrArg (fun θ : S2 => ⟪(θ : E3), (northPole : E3)⟫_ℝ) hdir
  change ⟪-((Handle.stereoChart northPole).symm q.1.val : E3), (northPole : E3)⟫_ℝ =
    ⟪((Handle.stereoChart northPole).symm p.1.val : E3), (northPole : E3)⟫_ℝ at hinner
  rw [inner_neg_left] at hinner
  linarith [cycleHandleAngle_negative p.1, cycleHandleAngle_negative q.1]


end GC.GraphManifold.Assembly
