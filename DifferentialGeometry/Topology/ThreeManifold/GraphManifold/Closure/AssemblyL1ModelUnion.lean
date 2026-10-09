import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelCycleSets
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1GluingSmooth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere

/-!
# Chapter-14 assembly, item L1, group G3a: the union of the model cycle is the solid torus

The balls, handles and rounded necks of the model cycle lie in the solid torus, and their union
`modelUnion` is closed (balls, handles and the compact fillets) and relatively open in the solid
torus: near a neck point the union is the solid torus by the rounded union of the neck; near a
remaining ball point the ball is the solid torus (its radius is the radius off the cap regions);
near a remaining handle point the handle is the solid torus (its radius is the radius off the end
strips). The solid torus is connected, so the union is the solid torus
(`solidTorusSet_eq_modelUnion`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsU_ASML1d : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance diskChartsU_ASML1d : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {len : ℕ} {ε : ℝ}

/-- The union of the model cycle. -/
def modelUnion (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) : Set SphereCarrier.{u} :=
  ((⋃ k, range (modelBall.{u} len ε k)) ∪ ⋃ k, range (modelHandle.{u} len ε k)) ∪
    ⋃ k, ⋃ b, modelNeck.{u} hlen hε hε' k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0}

/-! ## The pieces lie in the solid torus -/

theorem modelBall_mem_solidTorusSet (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (x : ClosedCell 3) : modelBall.{u} len ε k x ∈ solidTorusSet.{u} := by
  have hB := ballMap_range hε hε' (modelBase k) x
  have h0 := norm_nonneg (ballMap ε (modelBase k) (x : EuclideanSpace ℝ (Fin 3))).1
  have h2 : ‖(ballMap ε (modelBase k) (x : EuclideanSpace ℝ (Fin 3))).1‖ ^ 2 ≤ 2 := by
    nlinarith [hB.1]
  unfold modelBall ballSphere
  rw [modelSphere_mem_solidTorusSet_iff len h2]
  exact hB.1

theorem norm_zoneChartMap_middle (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {y : ModelSpace}
    (hy : ‖y.1‖ ≤ 1 + ε / 2) (ht : ε ≤ y.2) (ht' : y.2 ≤ 1 - ε) :
    ‖(zoneChartMap ε c y).1‖ = ‖y.1‖ := by
  have hz : y ∈ zoneDomain := ⟨by linarith, by linarith, by linarith⟩
  rw [norm_zoneChartMap_fst hε hε' c hz]
  set s := ‖y.1‖
  have hs0 : 0 ≤ s := norm_nonneg _
  have hU := zoneHeight_mem hs0 hz.1 hz.2.1 hz.2.2
  have hq := capCos_gt_of_lt hs0 hz.1
  have hq1 := capCos_le_one s
  have hb0 := Real.smoothTransition.nonneg (3 * y.2 - 1)
  have hb1 := Real.smoothTransition.le_one (3 * y.2 - 1)
  have hUdef : zoneHeight s y.2 = (1 + y.2) * capCos s + zoneBlend y.2 * (4 - 3 * capCos s) := rfl
  have hblend : zoneBlend y.2 = Real.smoothTransition (3 * y.2 - 1) := rfl
  rcases le_total (zoneHeight s y.2) 2 with h2 | h2
  · rw [zoneRadius_eq_lower hε hε' hs0 (by linarith) h2 (by linarith [hU.1])]
    apply neckRadius_eq_left hε
    have : (1 + y.2) * capCos s ≤ zoneHeight s y.2 := by nlinarith
    have : 1 + y.2 ≤ zoneHeight s y.2 / capCos s := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith
  · rw [zoneRadius_eq_upper hε hε' hs0 (by linarith) h2 (by linarith [hU.2])]
    apply neckRadius_eq_left hε
    have : (2 - y.2) * capCos s ≤ 4 - zoneHeight s y.2 := by nlinarith
    have : 2 - y.2 ≤ (4 - zoneHeight s y.2) / capCos s := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith

theorem modelHandle_mem_solidTorusSet (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (q : ClosedCell 2 × Icc (0 : ℝ) 1) : modelHandle.{u} len ε k q ∈ solidTorusSet.{u} := by
  obtain ⟨hz, -, hU⟩ := modelHandle_height hε hε' k q
  have hz' := handleInclusion_mem_zoneDomain q
  have h0 := norm_nonneg (zoneChartMap ε (modelBase k) (handleInclusion q)).1
  have h2 : ‖(zoneChartMap ε (modelBase k) (handleInclusion q)).1‖ ^ 2 ≤ 2 := by nlinarith [hz]
  change modelSphere.{u} len (zoneChartMap ε (modelBase k) (handleInclusion q)) ∈ solidTorusSet.{u}
  rw [modelSphere_mem_solidTorusSet_iff len h2]
  rw [norm_zoneChartMap_fst hε hε' _ hz']
  have hs1 : ‖(q.1 : ModelPlane)‖ ≤ 1 := q.1.2
  change zoneRadius ε ‖(q.1 : ModelPlane)‖ (zoneHeight ‖(q.1 : ModelPlane)‖ (q.2 : ℝ)) ≤ 1
  exact (zoneRadius_le hε hε' (norm_nonneg _) (by linarith) (by linarith [hU.1])
    (by linarith [hU.2])).trans hs1

theorem modelUnion_subset (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    modelUnion.{u} hlen hε hε' ⊆ solidTorusSet.{u} := by
  rintro p ((hp | hp) | hp)
  · obtain ⟨k, x, rfl⟩ := Set.mem_iUnion.mp hp
    exact modelBall_mem_solidTorusSet hε hε' k x
  · obtain ⟨k, q, rfl⟩ := Set.mem_iUnion.mp hp
    exact modelHandle_mem_solidTorusSet hε hε' k q
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    obtain ⟨b, q, ⟨hq, hψ⟩, rfl⟩ := Set.mem_iUnion.mp hk
    exact (modelNeck_mem_solidTorusSet_iff hlen hε hε' k b hq).mpr hψ

/-! ## The union is closed -/

theorem modelUnion_eq_fillets (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    modelUnion.{u} hlen hε hε' =
      ((⋃ k, range (modelBall.{u} len ε k)) ∪ ⋃ k, range (modelHandle.{u} len ε k)) ∪
        ⋃ k, ⋃ b, modelNeck.{u} hlen hε hε' k b '' (filletBox ε ∩ {q | neckRounding ε q ≤ 0}) := by
  apply Subset.antisymm
  · rintro p (hp | hp)
    · exact Or.inl hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
      obtain ⟨b, q, ⟨hq, hψ⟩, rfl⟩ := Set.mem_iUnion.mp hk
      by_cases h2 : q.2 ≤ 0
      · obtain ⟨x, hx⟩ := (modelNeck_mem_range_ball_iff hlen hε hε' k b hq).mpr h2
        exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨_, x, hx⟩))
      · by_cases h1 : ‖q.1‖ ≤ 1
        · obtain ⟨q', hq'⟩ := (modelNeck_mem_range_handle_iff hlen hε hε' k b hq).mpr
            ⟨(not_le.mp h2).le, h1⟩
          exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨_, q', hq'⟩))
        · exact Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨b, q,
            ⟨mem_filletBox_of_neckRounding_nonpos hε (not_le.mp h1) (not_le.mp h2) hψ, hψ⟩, rfl⟩⟩)
  · rintro p (hp | hp)
    · exact Or.inl hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
      obtain ⟨b, q, ⟨hq, hψ⟩, rfl⟩ := Set.mem_iUnion.mp hk
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨b, q,
        ⟨filletBox_subset_neckDomain hε hq, hψ⟩, rfl⟩⟩)

theorem isClosed_modelUnion (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    IsClosed (modelUnion.{u} hlen hε hε') := by
  rw [modelUnion_eq_fillets]
  refine ((isClosed_iUnion_of_finite fun k =>
    (isCompact_range (modelBall_smooth hlen hε hε' k).continuous).isClosed).union
    (isClosed_iUnion_of_finite fun k =>
      (isCompact_range (modelHandle_smooth hlen hε hε' k).continuous).isClosed)).union ?_
  refine isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun b => ?_
  have hK : IsCompact (filletBox ε ∩ {q | neckRounding ε q ≤ 0}) := by
    apply (isCompact_filletBox ε).inter_right
    have hc : Continuous fun q : ModelSpace => neckRounding ε q := by
      have : (fun q : ModelSpace => neckRounding ε q) = fun q =>
          standardRimRounding ((‖q.1‖ - 1) / ε, q.2 / ε) := rfl
      rw [this]
      exact contDiff_standardRimRounding.continuous.comp
        ((((continuous_norm.comp continuous_fst).sub continuous_const).div_const ε).prodMk
          (continuous_snd.div_const ε))
    exact isClosed_le hc continuous_const
  apply IsCompact.isClosed
  apply hK.image_of_continuousOn
  apply (modelNeck.{u} hlen hε hε' k b).contMDiffOn.continuousOn.mono
  rw [modelNeck_source]
  exact fun q hq => filletBox_subset_neckDomain hε hq.1

/-! ## The union is relatively open in the solid torus -/

theorem ballHeightAbs_le {h : ℝ} (hh : |h| ≤ 1 / 4) : ballHeightAbs h ≤ 1 / 4 := by
  have hmono := (Real.smoothAbs.strictMonoOn_Ici (show (0 : ℝ) < 1 / 4 by norm_num)).monotoneOn
    (abs_nonneg h) (show (0 : ℝ) ≤ 1 / 4 by norm_num) hh
  rw [Real.smoothAbs.abs (by norm_num), Real.smoothAbs.eq_self_of_le (by norm_num) le_rfl] at hmono
  exact hmono

/-- At a sphere point outside the two cap regions the stereographic margin is large. -/
theorem ballMargin_of_not_cap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (x : ClosedCell 3)
    (hx1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1) (hS : x ∉ neckCapRegion ε false)
    (hN : x ∉ neckCapRegion ε true) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖ + ε / 4 <
      2 * ‖(ballCoord (x : EuclideanSpace ℝ (Fin 3))).1‖ /
        ballDen (‖(ballCoord (x : EuclideanSpace ℝ (Fin 3))).1‖ ^ 2)
          (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 := by
  set ξ := (ballCoord (x : EuclideanSpace ℝ (Fin 3))).1
  set h := (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 with hh
  have hR2 : ‖ξ‖ ^ 2 + h ^ 2 = 1 := by
    rw [norm_sq_ballCoord, hx1]
    norm_num
  have hcut : ballCutSq (‖ξ‖ ^ 2 + h ^ 2) = 1 := by
    rw [hR2, ballCutSq, Real.sqrt_one, ballCut_eq_self (by norm_num [ballCutCentre, ballCutWidth])]
  have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx1
    exact zero_ne_one hx1
  rw [ballDen, hcut, hx1]
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
  rcases le_or_gt (1 / 4) |h| with hh4 | hh4
  · rw [ballHeightAbs_eq hh4]
    rcases lt_or_gt_of_ne (show h ≠ 0 by intro h0; rw [h0, abs_zero] at hh4; norm_num at hh4)
      with hneg | hpos
    · -- south side
      have hRh : 0 < 1 - h := by linarith
      have hcap := capMap_false_eq hx0 (by rw [hx1, ← ballCoord_snd]; exact hRh.ne')
      have hnot : ¬ (1 - 2 * ε < ‖(x : EuclideanSpace ℝ (Fin 3))‖ ∧
          0 < inner ℝ (x : EuclideanSpace ℝ (Fin 3))
            ((capPole false : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)) ∧
          ‖(capMap false (x : EuclideanSpace ℝ (Fin 3))).1‖ < 1 + 2 * ε) := hS
      rw [inner_capPole_false, hcap, hx1, norm_smul, Real.norm_of_nonneg (by positivity)] at hnot
      have hge : 1 + 2 * ε ≤ 2 / (1 - h) * ‖ξ‖ := by
        by_contra hlt
        exact hnot ⟨by linarith, by linarith, not_le.mp hlt⟩
      rw [abs_of_neg hneg]
      have : 2 * ‖ξ‖ / (1 + -h) = 2 / (1 - h) * ‖ξ‖ := by rw [← sub_eq_add_neg]; ring
      rw [this]
      linarith
    · -- north side
      have hRh : 0 < 1 + h := by linarith
      have hcap := capMap_true_eq hx0 (by rw [hx1, ← ballCoord_snd]; exact hRh.ne')
      have hnot : ¬ (1 - 2 * ε < ‖(x : EuclideanSpace ℝ (Fin 3))‖ ∧
          0 < inner ℝ (x : EuclideanSpace ℝ (Fin 3))
            ((capPole true : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)) ∧
          ‖(capMap true (x : EuclideanSpace ℝ (Fin 3))).1‖ < 1 + 2 * ε) := hN
      rw [inner_capPole_true, hcap, hx1, norm_smul, Real.norm_of_nonneg (by positivity)] at hnot
      have hge : 1 + 2 * ε ≤ 2 / (1 + h) * ‖ξ‖ := by
        by_contra hlt
        exact hnot ⟨by linarith, by linarith, not_le.mp hlt⟩
      rw [abs_of_pos hpos]
      have : 2 * ‖ξ‖ / (1 + h) = 2 / (1 + h) * ‖ξ‖ := by ring
      rw [this]
      linarith
  · have hη := ballHeightAbs_le hh4.le
    have hηpos := ballHeightAbs_pos h
    have hh2 : h ^ 2 < 1 / 16 := by
      have := abs_lt.mp hh4
      nlinarith
    have hξ2 : 15 / 16 < ‖ξ‖ ^ 2 := by linarith
    have hξ : 31 / 33 < ‖ξ‖ := by nlinarith
    rw [lt_div_iff₀ (by linarith)]
    nlinarith

theorem continuous_ballMargin :
    Continuous fun y : EuclideanSpace ℝ (Fin 3) =>
      2 * ‖(ballCoord y).1‖ / ballDen (‖(ballCoord y).1‖ ^ 2) (ballCoord y).2 := by
  have hρ : Continuous fun y : EuclideanSpace ℝ (Fin 3) => ‖(ballCoord y).1‖ :=
    continuous_norm.comp (continuous_fst.comp ballCoord.continuous)
  have hh : Continuous fun y : EuclideanSpace ℝ (Fin 3) => (ballCoord y).2 :=
    continuous_snd.comp ballCoord.continuous
  have hD : Continuous fun y : EuclideanSpace ℝ (Fin 3) =>
      ballDen (‖(ballCoord y).1‖ ^ 2) (ballCoord y).2 := by
    have : (fun y : EuclideanSpace ℝ (Fin 3) => ballDen (‖(ballCoord y).1‖ ^ 2) (ballCoord y).2) =
        fun y => ballCutSq (‖(ballCoord y).1‖ ^ 2 + (ballCoord y).2 ^ 2) +
          Real.smoothAbs (1 / 4) (ballCoord y).2 := rfl
    rw [this]
    exact (contDiff_ballCutSq.continuous.comp ((hρ.pow 2).add (hh.pow 2))).add
      ((Real.smoothAbs.contDiff (1 / 4)).continuous.comp hh)
  exact (continuous_const.mul hρ).div hD fun y => (ballDen_pos _ _).ne'

/-- **Relative openness of the union.** -/
theorem exists_open_subset_modelUnion (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    {p : SphereCarrier.{u}} (hp : p ∈ modelUnion.{u} hlen hε hε') :
    ∃ O : Set SphereCarrier.{u}, IsOpen O ∧ p ∈ O ∧
      O ∩ solidTorusSet.{u} ⊆ modelUnion.{u} hlen hε hε' := by
  by_cases hT : ∃ k b, p ∈ (modelNeck.{u} hlen hε hε' k b).target
  · obtain ⟨k, b, hk⟩ := hT
    refine ⟨_, (modelNeck.{u} hlen hε hε' k b).open_target, hk, ?_⟩
    rintro p' ⟨hp'T, hp'S⟩
    rw [modelNeck_target] at hp'T
    obtain ⟨q, hq, rfl⟩ := hp'T
    refine Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨b, q, ⟨hq, ?_⟩, ?_⟩⟩)
    · exact (modelNeck_mem_solidTorusSet_iff hlen hε hε' k b hq).mp
        (by rw [modelNeck_apply]; exact hp'S)
    · exact modelNeck_apply hlen hε hε' k b q
  push Not at hT
  have hneck : ∀ k b {q}, q ∈ neckDomain ε → modelNeck.{u} hlen hε hε' k b q ≠ p := by
    intro k b q hq h
    apply hT k b
    rw [← h]
    exact (modelNeck.{u} hlen hε hε' k b).map_source (by rw [modelNeck_source]; exact hq)
  rcases hp with (hp | hp) | hp
  · obtain ⟨j, x, rfl⟩ := Set.mem_iUnion.mp hp
    have hCs := modelBallChart_source.{u} hlen hε hε' j
    have hx1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
    rcases lt_or_eq_of_le hx1 with hlt | heq
    · refine ⟨(modelBallChart.{u} hlen hε hε' j).toOpenPartialHomeomorph '' ball 0 1,
        (modelBallChart.{u} hlen hε hε' j).toOpenPartialHomeomorph.isOpen_image_of_subset_source
          isOpen_ball (by
            change ball 0 1 ⊆ (modelBallChart.{u} hlen hε hε' j).source
            rw [hCs]
            exact ball_subset_ball (by norm_num)), ?_, ?_⟩
      · refine ⟨(x : EuclideanSpace ℝ (Fin 3)), mem_ball_zero_iff.mpr hlt, ?_⟩
        rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, modelBallChart_apply]
        rfl
      · rintro p' ⟨⟨y, hy, rfl⟩, -⟩
        rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
        refine Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨j, ⟨y, (mem_ball_zero_iff.mp hy).le⟩, ?_⟩))
        rw [modelBallChart_apply]
        rfl
    · -- a sphere point outside the cap regions
      have hS : x ∉ neckCapRegion ε false := by
        intro hc
        apply hneck j false (capMap_mem_neckDomain hc).1
        rw [← modelBall_cap hlen hε hε' j false x hc, rimBall_false]
      have hN : x ∉ neckCapRegion ε true := by
        intro hc
        apply hneck ((finRotate len).symm j) true (capMap_mem_neckDomain hc).1
        rw [← modelBall_cap hlen hε hε' _ true x hc, rimBall_true, Equiv.apply_symm_apply]
      have hmargin := ballMargin_of_not_cap hε hε' x heq hS hN
      set O' : Set (EuclideanSpace ℝ (Fin 3)) := {y | y ∈ ball 0 (6 / 5) ∧ 3 / 4 < ‖y‖ ∧
        ‖y‖ + ε / 4 < 2 * ‖(ballCoord y).1‖ / ballDen (‖(ballCoord y).1‖ ^ 2) (ballCoord y).2}
      have hO' : IsOpen O' :=
        isOpen_ball.inter ((isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt (continuous_norm.add continuous_const) continuous_ballMargin))
      have hxO' : (x : EuclideanSpace ℝ (Fin 3)) ∈ O' :=
        ⟨closedCell_mem_ball x, by rw [heq]; norm_num, hmargin⟩
      refine ⟨(modelBallChart.{u} hlen hε hε' j).toOpenPartialHomeomorph '' O',
        (modelBallChart.{u} hlen hε hε' j).toOpenPartialHomeomorph.isOpen_image_of_subset_source hO'
          (by
            change O' ⊆ (modelBallChart.{u} hlen hε hε' j).source
            rw [hCs]
            exact fun y hy => hy.1),
        ⟨(x : EuclideanSpace ℝ (Fin 3)), hxO', ?_⟩, ?_⟩
      · rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, modelBallChart_apply]
        rfl
      · rintro p' ⟨⟨y, ⟨hyb, hy34, hym⟩, rfl⟩, hp'S⟩
        rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, modelBallChart_apply] at hp'S ⊢
        have hR : Real.sqrt (‖(ballCoord y).1‖ ^ 2 + (ballCoord y).2 ^ 2) = ‖y‖ := sqrt_ballCoord y
        have hrad : ‖(ballMap ε (modelBase j) y).1‖ = ‖y‖ := by
          rw [norm_ballMap_fst hε hε', ballRadius_eq_radius hε hε' (norm_nonneg _)
            (by rw [hR]; norm_num [ballCutCentre, ballCutWidth]; linarith) (by rw [hR]; exact hym.le),
            hR]
        have hy2 : ‖(ballMap ε (modelBase j) y).1‖ ^ 2 ≤ 2 := by
          rw [hrad]
          have : ‖y‖ < 6 / 5 := mem_ball_zero_iff.mp hyb
          nlinarith [norm_nonneg y]
        unfold ballSphere at hp'S
        rw [modelSphere_mem_solidTorusSet_iff len hy2, hrad] at hp'S
        exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨j, ⟨y, hp'S⟩, rfl⟩))
  · obtain ⟨j, q, rfl⟩ := Set.mem_iUnion.mp hp
    have hCs := modelHandleChart_source.{u} hlen hε hε' j
    have hq1 : ‖(q.1 : ModelPlane)‖ ≤ 1 := q.1.2
    have ht := q.2.2
    have ht0 : 2 * ε ≤ (q.2 : ℝ) := by
      by_contra hlt
      push Not at hlt
      apply hneck j false (q := handleEnd false q)
        ⟨by change ‖(q.1 : ModelPlane)‖ < 1 + 2 * ε; linarith,
          by change |(q.2 : ℝ)| < 2 * ε; rw [abs_of_nonneg ht.1]; exact hlt⟩
      exact (modelHandle_end hlen hε hε' j false q).symm
    have ht1 : (q.2 : ℝ) ≤ 1 - 2 * ε := by
      by_contra hlt
      push Not at hlt
      apply hneck j true (q := handleEnd true q)
        ⟨by change ‖(q.1 : ModelPlane)‖ < 1 + 2 * ε; linarith,
          by change |1 - (q.2 : ℝ)| < 2 * ε; rw [abs_of_nonneg (by linarith [ht.2])]; linarith⟩
      exact (modelHandle_end hlen hε hε' j true q).symm
    set O' : Set ModelSpace := {y | ‖y.1‖ < 1 + ε / 2 ∧ ε < y.2 ∧ y.2 < 1 - ε}
    have hO' : IsOpen O' :=
      (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
    have hO'z : O' ⊆ zoneDomain := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2.1],
      by linarith [hy.2.2]⟩
    refine ⟨(modelHandleChart.{u} hlen hε hε' j).toOpenPartialHomeomorph '' O',
      (modelHandleChart.{u} hlen hε hε' j).toOpenPartialHomeomorph.isOpen_image_of_subset_source hO'
        (by
          change O' ⊆ (modelHandleChart.{u} hlen hε hε' j).source
          rw [hCs]
          exact hO'z),
      ⟨handleInclusion q, ⟨by change ‖(q.1 : ModelPlane)‖ < 1 + ε / 2; linarith,
        by change ε < (q.2 : ℝ); linarith, by change (q.2 : ℝ) < 1 - ε; linarith⟩, ?_⟩, ?_⟩
    · rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, modelHandleChart_apply]
      rfl
    · rintro p' ⟨⟨y, hy, rfl⟩, hp'S⟩
      rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, modelHandleChart_apply] at hp'S ⊢
      have hrad := norm_zoneChartMap_middle hε hε' (modelBase j) hy.1.le hy.2.1.le hy.2.2.le
      have hy2 : ‖(zoneChartMap ε (modelBase j) y).1‖ ^ 2 ≤ 2 := by
        rw [hrad]
        have := hy.1
        nlinarith [norm_nonneg y.1]
      unfold zoneSphere at hp'S
      rw [modelSphere_mem_solidTorusSet_iff len hy2, hrad] at hp'S
      refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, (⟨y.1, by simpa using hp'S⟩,
        ⟨y.2, by linarith [hy.2.1], by linarith [hy.2.2]⟩), ?_⟩))
      rfl
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    obtain ⟨b, q, ⟨hq, -⟩, rfl⟩ := Set.mem_iUnion.mp hk
    exact absurd rfl (hneck k b hq)

/-- **The union of the model cycle is the solid torus.** -/
theorem solidTorusSet_eq_modelUnion (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    solidTorusSet.{u} = modelUnion.{u} hlen hε hε' := by
  apply Subset.antisymm _ (modelUnion_subset hlen hε hε')
  set W : Set solidTorusSet.{u} := {p | (p : SphereCarrier.{u}) ∈ modelUnion.{u} hlen hε hε'}
  have hWc : IsClosed W := (isClosed_modelUnion hlen hε hε').preimage continuous_subtype_val
  have hWo : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨O, hO, hpO, hOU⟩ := exists_open_subset_modelUnion hlen hε hε' hp
    exact ⟨Subtype.val ⁻¹' O, fun p' hp' => hOU ⟨hp', p'.2⟩, hO.preimage continuous_subtype_val,
      hpO⟩
  have hne : W.Nonempty := by
    let k : Fin len := ⟨0, hlen⟩
    let x0 : ClosedCell 3 := ⟨0, by simp⟩
    exact ⟨⟨modelBall.{u} len ε k x0, modelBall_mem_solidTorusSet hε hε' k x0⟩,
      Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨k, x0, rfl⟩))⟩
  have hWu := IsClopen.eq_univ ⟨hWc, hWo⟩ hne
  intro p hp
  have : (⟨p, hp⟩ : solidTorusSet.{u}) ∈ W := by rw [hWu]; trivial
  exact this

end GC.GraphManifold.Assembly
