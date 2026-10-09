import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersJunction

/-!
# FC39 producer, packet P0 (gate 1): the WIDE S³ labelled corner tubes

Part C of the circle kind of the S³ inhabitant. The labelled corner tubes `sphereLabelledTubes J`
have base EXACTLY the corner chart target of `sphereCircleRegion` (slacks `|16 · slack| < 2`), so
their tubes equal the rim targets; `AdaptedEdgeRimData.rim_closure_in_safe` asks for the CLOSURE of
the rim targets inside a safe tube inside the raw tube, which is impossible for an open proper
subset of the connected `S³`. The raw tubes must be strictly wider than the final corners.

This module gives the WIDE tubes (same slack-pair chart, same descended function):

* the one-variable bounds for `|s| < 5/2` (`…W`), the wide plane target `circPlaneTargetW`
  (`|16 · slack| < 5/2`), the wide plane and corner charts `circPlaneChartW`, `circCornerChartW`;
* the corner-tube geometry on the wide targets (`circHandleS_memW`, `sphereCircleChart_eq_handleW`,
  `circTube_mem_edgeSourceW`, `circTube_heightW`, `circTube_projEW`); `5/2 < 16 · 72/445` keeps the
  handle parameter in the inner / outer zones of `cycleHandleRadius`;
* **`sphereLabelledTubesW J : LabelledCornerTubes J`** with base the wide target (every `J`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## One-variable bounds for `|s| < 5/2` -/

theorem one_add_pos_of_absW {s : ℝ} (hs : |s| < 5 / 2) : 0 < 1 + 1 / 16 * s := by
  have := (abs_lt.1 hs).1
  linarith

theorem circCornerInv_posW (a σ : Bool) {s : ℝ} (hs : |s| < 5 / 2) : 0 < circCornerInv a σ s := by
  have hu := one_add_pos_of_absW hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  have hsq := Real.sqrt_pos.2 hu
  cases a <;> cases σ <;> simp only [circCornerInv]
  · exact hsq
  · positivity
  · exact circQ_pos ⟨by linarith, by linarith⟩
  · exact circQ_pos ⟨by linarith, by linarith⟩

theorem circSlack_circCornerInvW (a σ : Bool) {s : ℝ} (hs : |s| < 5 / 2) :
    circSlack a σ (circCornerInv a σ s) = 1 / 16 * s := by
  have hu := one_add_pos_of_absW hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  cases a <;> cases σ <;> simp only [circSlack, circCornerInv]
  · rw [Real.sq_sqrt hu.le]
    ring
  · have hsq := Real.sqrt_pos.2 hu
    rw [div_pow, Real.sq_sqrt hu.le]
    field_simp
    ring
  · rw [circHeight_circQ ⟨by linarith, by linarith⟩]
    ring
  · rw [circHeight_circQ ⟨by linarith, by linarith⟩]
    ring

theorem circCornerInv_mem_wideW (a σ : Bool) {s : ℝ} (hs : |s| < 5 / 2) :
    circCornerInv a σ s ∈ Ioo (1 / 2 : ℝ) 8 := by
  have hu := one_add_pos_of_absW hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  have hs1 : 1 / 2 < √(1 + 1 / 16 * s) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hs2 : √(1 + 1 / 16 * s) < 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have hsq := Real.sqrt_pos.2 hu
  cases a <;> cases σ <;> simp only [circCornerInv]
  · exact ⟨hs1, hs2⟩
  · constructor
    · rw [lt_div_iff₀ hsq]
      linarith
    · rw [div_lt_iff₀ hsq]
      linarith
  · exact circQ_mem_wide (by linarith) (by linarith)
  · exact circQ_mem_wide (by linarith) (by linarith)

theorem contDiffAt_circCornerInvW (a σ : Bool) {s : ℝ} (hs : |s| < 5 / 2) :
    ContDiffAt ℝ ∞ (circCornerInv a σ) s := by
  have hu := one_add_pos_of_absW hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  have hlin : ContDiffAt ℝ ∞ (fun s : ℝ => 1 + 1 / 16 * s) s :=
    contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)
  have hsq : ContDiffAt ℝ ∞ (fun s : ℝ => √(1 + 1 / 16 * s)) s := hlin.sqrt hu.ne'
  cases a <;> cases σ
  · exact hsq
  · exact contDiffAt_const.div hsq (Real.sqrt_pos.2 hu).ne'
  · exact (contDiffAt_circQ ⟨by linarith, by linarith⟩).comp s
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)
  · exact (contDiffAt_circQ ⟨by linarith, by linarith⟩).comp s
      (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id))

/-- The two slacks of one axis cannot both be `< 5/32` (wide version of `circSlack_other_gt`). -/
theorem circSlack_other_gtW (a σ : Bool) {t : ℝ} (ht : 0 < t) (h : |circSlack a σ t| < 5 / 32) :
    1 < circSlack a (!σ) t := by
  have hl := (abs_lt.1 h).1
  have hu := (abs_lt.1 h).2
  have ht2 : 0 < t ^ 2 := by positivity
  cases a <;> cases σ <;> simp only [circSlack, Bool.not_false, Bool.not_true] at hl hu ⊢
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ ht2]
    nlinarith
  · have h16 : 16 / t ^ 2 < 37 / 32 := by linarith
    rw [div_lt_iff₀ ht2] at h16
    nlinarith
  · linarith
  · linarith

theorem abs_sixteen_mul_ltW {s : ℝ} (h : |16 * s| < 5 / 2) : -(5 / 32) < s ∧ s < 5 / 32 := by
  rw [abs_lt] at h
  constructor <;> linarith [h.1, h.2]

/-! ## The wide plane and corner charts -/

/-- The wide target: positive coordinates with slacks in `(−5/32, 5/32)`. -/
def circPlaneTargetW (σ σ' : Bool) : Set (ℝ × ℝ) :=
  {u | 0 < u.1 ∧ 0 < u.2 ∧ |16 * circSlack false σ u.1| < 5 / 2 ∧
    |16 * circSlack true σ' u.2| < 5 / 2}

theorem isOpen_circPlaneTargetW (σ σ' : Bool) : IsOpen (circPlaneTargetW σ σ') := by
  have hQ : IsOpen {u : ℝ × ℝ | 0 < u.1 ∧ 0 < u.2} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
  have h := (contDiffOn_circPlaneInv σ σ').continuousOn.isOpen_inter_preimage hQ
    ((isOpen_Ioo (a := (-5 / 2 : ℝ)) (b := 5 / 2)).prod
      (isOpen_Ioo (a := (-5 / 2 : ℝ)) (b := 5 / 2)))
  convert h using 1
  ext u
  simp only [circPlaneTargetW, circPlaneInv, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod,
    mem_Ioo, abs_lt]
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, h5, h6⟩
    exact ⟨⟨h1, h2⟩, ⟨by linarith, h4⟩, ⟨by linarith, h6⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨h1, h2, ⟨by linarith, h4⟩, ⟨by linarith, h6⟩⟩

theorem contDiffOn_circPlaneMapW (σ σ' : Bool) :
    ContDiffOn ℝ ∞ (circPlaneMap σ σ') (rimBox (5 / 2)) :=
  fun v hv => (((contDiffAt_circCornerInvW false σ hv.1).comp v contDiffAt_fst).prodMk
    ((contDiffAt_circCornerInvW true σ' hv.2).comp v contDiffAt_snd)).contDiffWithinAt

/-- **The wide plane corner chart** `(x, y) ↦ (ψ, r)` with slacks `(x / 16, y / 16)`,
`|x|, |y| < 5/2`. -/
def circPlaneChartW (σ σ' : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun := circPlaneMap σ σ'
  invFun := circPlaneInv σ σ'
  source := rimBox (5 / 2)
  target := circPlaneTargetW σ σ'
  map_source' v hv := by
    refine ⟨circCornerInv_posW false σ hv.1, circCornerInv_posW true σ' hv.2, ?_, ?_⟩
    · change |16 * circSlack false σ (circCornerInv false σ v.1)| < 5 / 2
      rw [circSlack_circCornerInvW false σ hv.1, sixteen_mul_one_div]
      exact hv.1
    · change |16 * circSlack true σ' (circCornerInv true σ' v.2)| < 5 / 2
      rw [circSlack_circCornerInvW true σ' hv.2, sixteen_mul_one_div]
      exact hv.2
  map_target' u hu := ⟨hu.2.2.1, hu.2.2.2⟩
  left_inv' v hv := by
    change (16 * circSlack false σ (circCornerInv false σ v.1),
      16 * circSlack true σ' (circCornerInv true σ' v.2)) = v
    rw [circSlack_circCornerInvW false σ hv.1, circSlack_circCornerInvW true σ' hv.2,
      sixteen_mul_one_div, sixteen_mul_one_div]
  right_inv' u hu := by
    change (circCornerInv false σ (16 * circSlack false σ u.1),
      circCornerInv true σ' (16 * circSlack true σ' u.2)) = u
    rw [circCornerInv_circSlack false σ hu.1, circCornerInv_circSlack true σ' hu.2.1]
  open_source := isOpen_rimBox_CIRCB (5 / 2)
  open_target := isOpen_circPlaneTargetW σ σ'
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 (contDiffOn_circPlaneMapW σ σ')
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2
    ((contDiffOn_circPlaneInv σ σ').mono fun _ hu => ⟨hu.1, hu.2.1⟩)

/-- **The wide corner chart** of the corner `(b, e)`. -/
def circCornerChartW (b e : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) sphereCircleBaseOpens ∞ :=
  (circPlaneChartW b (b ^^ e)).trans circToBase

theorem circPlaneMap_mem_baseW {σ σ' : Bool} {v : ℝ × ℝ} (hv : v ∈ rimBox (5 / 2)) :
    sphereCircleEquiv.symm (circPlaneMap σ σ' v) ∈ sphereCircleBaseSet :=
  sphereCircleEquiv_symm_mem (circCornerInv_mem_wideW false σ hv.1)
    (circCornerInv_mem_wideW true σ' hv.2)

theorem circCornerChartW_source (b e : Bool) : (circCornerChartW b e).source = rimBox (5 / 2) := by
  ext v
  change v ∈ rimBox (5 / 2) ∩ circPlaneMap b (b ^^ e) ⁻¹' circToBase.source ↔ _
  rw [circToBase_source]
  exact ⟨fun h => h.1, fun h => ⟨h, circPlaneMap_mem_baseW h⟩⟩

theorem circCornerChartW_val (b e : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox (5 / 2)) :
    (circCornerChartW b e v).val = sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) v) :=
  circToBase_val (circPlaneMap_mem_baseW hv)

theorem mem_circCornerChartW_target {b e : Bool} {c : sphereCircleBaseOpens} :
    c ∈ (circCornerChartW b e).target ↔ sphereCircleEquiv c.val ∈ circPlaneTargetW b (b ^^ e) := by
  change c ∈ circToBase.target ∩ circToBase.symm ⁻¹' circPlaneTargetW b (b ^^ e) ↔ _
  rw [mem_inter_iff, mem_preimage, circToBase_symm]
  exact ⟨fun h => h.2, fun h => ⟨mem_circToBase_target c, h⟩⟩

theorem circCornerChartW_eq (b e : Bool) (v : ℝ × ℝ) : circCornerChartW b e v = circCornerChart b e v :=
  rfl

theorem circPlaneTarget_subset_W (σ σ' : Bool) : circPlaneTarget σ σ' ⊆ circPlaneTargetW σ σ' :=
  fun _ hu => ⟨hu.1, hu.2.1, by linarith [hu.2.2.1], by linarith [hu.2.2.2]⟩

/-! ## The handle coordinates of a wide corner tube point -/

theorem circHandleS_memW (σ' : Bool) {r : ℝ} (hr : 0 < r) (h : |16 * circSlack true σ' r| < 5 / 2) :
    circHandleS σ' r ∈ Ioo (-1 / 2 : ℝ) (3 / 2) ∧ cycleHandleRadius (circHandleS σ' r) = r ∧
      (σ' = false → circHandleS σ' r ≤ 1 / 4) ∧ (σ' = true → 3 / 4 ≤ circHandleS σ' r) := by
  have hb := abs_sixteen_mul_ltW h
  have hD : 0 < 5 * (r ^ 2 + 4) := by positivity
  cases σ'
  · simp only [circSlack] at hb
    rw [circHeight_add] at hb
    have h1 := hb.1
    have h2 := hb.2
    rw [lt_div_iff₀ hD] at h1
    rw [div_lt_iff₀ hD] at h2
    have hr1 : r < 5 / 4 := by nlinarith
    have hr2 : 1 / 2 < r := by nlinarith
    simp only [circHandleS]
    refine ⟨⟨by linarith, by linarith⟩, ?_, fun _ => by linarith, fun h => absurd h (by decide)⟩
    rw [cycleHandleRadius_inner (by linarith)]
    ring
  · simp only [circSlack] at hb
    rw [circHeight_sub] at hb
    have h1 := hb.1
    have h2 := hb.2
    rw [lt_div_iff₀ hD] at h1
    rw [div_lt_iff₀ hD] at h2
    have hr1 : 16 / 5 < r := by nlinarith
    have hr2 : r < 6 := by nlinarith
    have hq1 : 4 / r < 5 / 4 := by rw [div_lt_iff₀ hr]; linarith
    have hq2 : 2 / 3 < 4 / r := by rw [lt_div_iff₀ hr]; linarith
    simp only [circHandleS]
    refine ⟨⟨by linarith, by linarith⟩, ?_, fun h => absurd h (by decide), fun _ => by linarith⟩
    rw [cycleHandleRadius_outer (by linarith)]
    field_simp
    ring

theorem circHandleW_mem_ballW (b : Bool) {ψ : ℝ} (hψ : 0 < ψ) (θ : Circle)
    (h : |16 * circSlack false b ψ| < 5 / 2) : circHandleW b ψ θ ∈ Metric.ball (0 : E2) 2 := by
  have hb := abs_sixteen_mul_ltW h
  rw [Metric.mem_ball, dist_zero_right]
  have hsq := circHandleW_norm_sq b hψ θ
  have hn := norm_nonneg (circHandleW b ψ θ)
  nlinarith

theorem circTube_mem_edgeBoxW {b σ' : Bool} {u : ℝ × ℝ} (hu : u ∈ circPlaneTargetW b σ')
    (θ : Circle) :
    (circHandleW b u.1 θ, handleRadiusParam b (circHandleS σ' u.2)) ∈ edgeBox :=
  ⟨circHandleW_mem_ballW b hu.1 θ hu.2.2.1,
    handleRadiusParam_mem_Ioo b (circHandleS_memW σ' hu.2.1 hu.2.2.2).1⟩

/-- **A wide corner tube point is a handle chart point.** -/
theorem sphereCircleChart_eq_handleW {b σ' : Bool} {u : ℝ × ℝ} (hu : u ∈ circPlaneTargetW b σ')
    (θ : Circle) :
    sphereCircleChart (sphereCircleEquiv.symm u, θ) =
      cycleHandleChart b (circHandleW b u.1 θ, handleRadiusParam b (circHandleS σ' u.2)) := by
  have hr := (circHandleS_memW σ' hu.2.1 hu.2.2.2).2.1
  have hψ : 0 < u.1 := hu.1
  rw [show u = (u.1, u.2) from rfl, sphereCircleChart_equiv_symm, cycleHandleChart_eq_FC39P0]
  dsimp only
  cases b
  · simp only [handleRadiusParam, Bool.cond_false, Bool.false_eq_true, ↓reduceIte, hr]
    rfl
  · simp only [handleRadiusParam, Bool.cond_true, ↓reduceIte, sub_sub_cancel, hr]
    have hs := sphereCircleChart_neg (div_pos (by norm_num : (0 : ℝ) < 4) hψ) u.2
      (circleAntipode_CIRCA θ)
    rw [circleAntipode_antipode_CIRCA] at hs
    rw [show 4 / (4 / u.1) = u.1 by field_simp] at hs
    rw [show circHandleW true u.1 θ = (4 / u.1) • planeOfCircle (circleAntipode_CIRCA θ) from rfl,
      hs, sphereCircleChart_equiv_symm]

section TubeW

variable {b σ' : Bool} {x : sphereCircleDomain}

theorem circTube_eq_handleW
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTargetW b σ') :
    x.val = cycleHandleChart b
      (circHandleW b (circCoordL false (sphereCircleProj x).val) (sphereCircleChart.symm x.val).2,
        handleRadiusParam b (circHandleS σ' (circCoordL true (sphereCircleProj x).val))) :=
  (circDomain_eq_chart x).trans (sphereCircleChart_eq_handleW hx _)

theorem circTube_mem_boxW
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTargetW b σ') :
    (circHandleW b (circCoordL false (sphereCircleProj x).val) (sphereCircleChart.symm x.val).2,
        handleRadiusParam b (circHandleS σ' (circCoordL true (sphereCircleProj x).val))) ∈
      edgeBox :=
  circTube_mem_edgeBoxW hx _

theorem circTube_mem_edgeSourceW
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTargetW b σ') :
    x.val ∈ edgeSource := by
  rw [circTube_eq_handleW hx]
  exact chart_mem_edgeSource (circTube_mem_boxW hx)

theorem circTube_heightW
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTargetW b σ') :
    edgeHeightR x.val = circSlack false b (circCoordL false (sphereCircleProj x).val) + 1 := by
  rw [circTube_eq_handleW hx, edgeHeightR_chart (circTube_mem_boxW hx)]
  exact circHandleW_norm_sq b (circCoordL_pos false _) _

theorem circTube_projEW
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTargetW b σ') :
    edgeProjE x.val = edgeLineEquiv
      (handleRadiusParam b (circHandleS σ' (circCoordL true (sphereCircleProj x).val)) +
        edgeShift b) := by
  rw [circTube_eq_handleW hx, edgeProjE_chart (circTube_mem_boxW hx)]

end TubeW

/-! ## The wide tube chart -/

/-- The wide base neighbourhood of an endpoint: the target of its wide corner chart. -/
def circTubeBaseW (e : sphereEdgeBundle.EdgeEnd) : TopologicalSpace.Opens sphereCircleBaseOpens :=
  ⟨(circCornerChartW (circEndSide e) (circEndEnd e)).target,
    (circCornerChartW (circEndSide e) (circEndEnd e)).open_target⟩

theorem mem_circTubeBaseW {e : sphereEdgeBundle.EdgeEnd} {c : sphereCircleBaseOpens} :
    c ∈ circTubeBaseW e ↔
      sphereCircleEquiv c.val ∈ circPlaneTargetW (circEndSide e) (circEndLabel e) :=
  mem_circCornerChartW_target

theorem circTubeBase_subset_W (e : sphereEdgeBundle.EdgeEnd) :
    (circTubeBase e : Set sphereCircleBaseOpens) ⊆ circTubeBaseW e := fun _ hc =>
  mem_circTubeBaseW.2 (circPlaneTarget_subset_W _ _ (mem_circTubeBase.1 hc))

/-- **The wide labelled corner chart of an endpoint**: `c ↦ (ψ-slack, r-slack)`. -/
def circTubeChartW (e : sphereEdgeBundle.EdgeEnd) :
    PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) sphereCircleBaseOpens (ℝ × ℝ) ∞ :=
  (circCornerChartW (circEndSide e) (circEndEnd e)).symm.trans circTubeScale

/-- The wide chart is the same slack pair. -/
theorem circTubeChartW_eq (e : sphereEdgeBundle.EdgeEnd) (c : sphereCircleBaseOpens) :
    circTubeChartW e c = circTubeChart e c :=
  rfl

theorem circTubeChartW_center (e : sphereEdgeBundle.EdgeEnd) :
    circTubeChartW e (circCornerChart (circEndSide e) (circEndEnd e) (0, 0)) = (0, 0) := by
  rw [circTubeChartW_eq]
  exact circTubeChart_center e

theorem circTubeChartW_source (e : sphereEdgeBundle.EdgeEnd) :
    (circTubeChartW e).source = (circCornerChartW (circEndSide e) (circEndEnd e)).target := by
  change (circCornerChartW (circEndSide e) (circEndEnd e)).target ∩
    (circCornerChartW (circEndSide e) (circEndEnd e)).symm ⁻¹' univ = _
  rw [preimage_univ, inter_univ]

section TubePointW

variable {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}

theorem circTube_targetW (hx : sphereCircleProj x ∈ circTubeBaseW e) :
    sphereCircleEquiv (sphereCircleProj x).val ∈
      circPlaneTargetW (circEndSide e) (circEndLabel e) :=
  mem_circTubeBaseW.1 hx

theorem circHandleS_mem_Icc_iffW {σ' : Bool} {r : ℝ} (hr : 0 < r)
    (h : |16 * circSlack true σ' r| < 5 / 2) :
    circHandleS σ' r ∈ Icc (0 : ℝ) 1 ↔ 0 ≤ circSlack true σ' r := by
  obtain ⟨-, -, h1, h2⟩ := circHandleS_memW σ' hr h
  cases σ'
  · rw [circSlack_false_nonneg_iff true hr]
    have h1' := h1 rfl
    simp only [circHandleS, mem_Icc] at h1' ⊢
    constructor
    · intro h
      linarith [h.1]
    · intro h
      exact ⟨by linarith, by linarith⟩
  · rw [circSlack_true_nonneg_iff true hr]
    have h2' := h2 rfl
    simp only [circHandleS, mem_Icc] at h2' ⊢
    have key : 1 ≤ 4 / r ↔ r ≤ 4 := by
      rw [le_div_iff₀ hr, one_mul]
    constructor
    · intro h
      exact key.1 (by linarith [h.2])
    · intro h
      exact ⟨by linarith, by linarith [key.2 h]⟩

theorem circSlack_mem_Icc_iffW (a σ : Bool) {t : ℝ} (ht : 0 < t)
    (h : |16 * circSlack a σ t| < 5 / 2) :
    t ∈ Icc (1 : ℝ) 4 ↔ 0 ≤ circSlack a σ t := by
  have h' : |circSlack a σ t| < 5 / 32 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
    linarith
  have hother := circSlack_other_gtW a σ ht h'
  rw [mem_Icc]
  cases σ
  · rw [circSlack_false_nonneg_iff a ht]
    have h4 := (circSlack_true_nonneg_iff a ht).1
      (by simp only [Bool.not_false] at hother; linarith)
    exact ⟨fun h => h.1, fun h => ⟨h, h4⟩⟩
  · rw [circSlack_true_nonneg_iff a ht]
    have h1 := (circSlack_false_nonneg_iff a ht).1
      (by simp only [Bool.not_true] at hother; linarith)
    exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩

theorem circTube_descendedW (hx : sphereCircleProj x ∈ circTubeBaseW e) :
    circSlack true (circEndLabel e) (circCoordL true (sphereCircleProj x).val) =
      circDescended e (edgeProj ⟨x.val, circTube_mem_edgeSourceW (circTube_targetW hx)⟩) := by
  have hx' := circTube_targetW hx
  have hr := (circHandleS_memW (r := circCoordL true (sphereCircleProj x).val) (circEndLabel e)
    (circCoordL_pos true _) hx'.2.2.2).2.1
  change _ = circDescendedReal e (edgeLineEquiv.symm (edgeProjE x.val))
  rw [circTube_projEW hx', ContinuousLinearEquiv.symm_apply_apply, circDescendedReal,
    add_sub_cancel_right, handleRadiusParam_involutive_CIRCC, hr]

theorem circTube_edge_sideW (hx : sphereCircleProj x ∈ circTubeBaseW e) :
    x.val ∈ sphereEdgeBundle.wholeComponent e.component ↔
      0 ≤ (circTubeChartW e (sphereCircleProj x)).2 ∧
        (circTubeChartW e (sphereCircleProj x)).1 ≤ 0 := by
  have hx' := circTube_targetW hx
  have hcomp : e.component.1 = range (edgeInterval (circEndSide e)) :=
    connectedComponentIn_edgeCbase ⟨iccEnd (circEndEnd e), (circEnd_val e).symm⟩
  rw [EdgeBundle.mem_wholeComponent_iff_CIRCC (circTube_mem_edgeSourceW hx'), hcomp,
    circTubeChartW_eq, circTubeChart_apply]
  apply and_congr
  · change edgeProj ⟨x.val, circTube_mem_edgeSourceW hx'⟩ ∈ range (edgeInterval (circEndSide e)) ↔ _
    rw [range_edgeInterval, mem_preimage]
    change edgeLineEquiv.symm (edgeProjE x.val) ∈ _ ↔ _
    rw [circTube_projEW hx', ContinuousLinearEquiv.symm_apply_apply,
      ← circHandleS_mem_Icc_iffW (r := circCoordL true (sphereCircleProj x).val)
        (circCoordL_pos true _) hx'.2.2.2,
      ← handleRadiusParam_mem_Icc_iff_CIRCC (circEndSide e)]
    simp only [mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · change edgeHeightR x.val ≤ 1 ↔ _
    rw [circTube_heightW hx']
    constructor <;> intro h <;> linarith

theorem circTube_region_sideW (hx : sphereCircleProj x ∈ circTubeBaseW e) :
    x.val ∈ sphereCircleBundle.region ↔
      0 ≤ (circTubeChartW e (sphereCircleProj x)).1 ∧
        0 ≤ (circTubeChartW e (sphereCircleProj x)).2 := by
  have hx' := circTube_targetW hx
  have hmem : x.val ∈ sphereCircleBundle.region ↔ sphereCircleProj x ∈ sphereCircleCbase :=
    Subtype.val_injective.mem_set_image
  rw [hmem, circTubeChartW_eq, circTubeChart_apply]
  change (sphereCircleEquiv (sphereCircleProj x).val).1 ∈ Icc (1 : ℝ) 4 ∧
    (sphereCircleEquiv (sphereCircleProj x).val).2 ∈ Icc (1 : ℝ) 4 ↔ _
  exact and_congr
    (circSlack_mem_Icc_iffW false _ (circCoordL_pos false (sphereCircleProj x)) hx'.2.2.1)
    (circSlack_mem_Icc_iffW true _ (circCoordL_pos true (sphereCircleProj x)) hx'.2.2.2)

end TubePointW

/-! ## The wide labelled corner tubes -/

variable (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
  sphereSlimPieces sphereEdgeBundle sphereCircleBundle)

theorem circTube_residual_descendedW {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}
    (hx : sphereCircleProj x ∈ circTubeBaseW e) :
    sphereSlimPieces.residualFn (J.horizontal e) x.val =
      circDescended e (edgeProj ⟨x.val, circTube_mem_edgeSourceW (circTube_targetW hx)⟩) := by
  rw [horizontal_eq_circEndLabel J e, residualFn_circDomain]
  exact circTube_descendedW hx

/-- **The wide S³ labelled corner tubes** for every joint junction structure `J`: base = the wide
target `|16 · slack| < 5/2`, chart = the slack pair. -/
def sphereLabelledTubesW : LabelledCornerTubes J where
  base := circTubeBaseW
  rimBase_mem e := circTubeBase_subset_W e ((sphereLabelledTubes J).rimBase_mem e)
  chart := circTubeChartW
  chart_source := circTubeChartW_source
  chart_center e := by
    rw [rimBase_eq_circCorner J e]
    exact circTubeChartW_center e
  tube_source e := by
    rintro _ ⟨x, hx, rfl⟩
    exact circTube_mem_edgeSourceW (circTube_targetW (x := x) hx)
  tube_near e := by
    rintro _ ⟨x, -, rfl⟩
    rw [horizontal_eq_circEndLabel J e]
    exact circDomain_mem_residualNear _ x
  height_eq e x hx := by
    refine ⟨circTube_mem_edgeSourceW (circTube_targetW (x := x) hx), ?_⟩
    change (circTubeChartW e (sphereCircleProj x)).1 = edgeHeightR x.val - 1
    rw [circTubeChartW_eq, circTubeChart_apply, circTube_heightW (circTube_targetW (x := x) hx)]
    ring
  face_eq e x _ := by
    change (circTubeChartW e (sphereCircleProj x)).2 = _
    rw [circTubeChartW_eq]
    exact circTube_face J x
  descended := circDescended
  descended_smooth e := ⟨circDescendedBase e, mem_circDescendedBase e, circDescended_smooth e⟩
  descended_regular := circDescended_regular
  descended_eq e x hx := ⟨_, circTube_residual_descendedW J (x := x) hx⟩
  vertex_side {e} {x} _ := by
    change _ ↔ (circTubeChartW e (sphereCircleProj x)).2 ≤ 0
    rw [circTubeChartW_eq]
    exact circTube_vertex_side J (x := x)
  edge_side {_} {_} hx := circTube_edge_sideW hx
  region_side {_} {_} hx := circTube_region_sideW hx

theorem sphereLabelledTubesW_base (e : sphereEdgeBundle.EdgeEnd) :
    (sphereLabelledTubesW J).base e = circTubeBaseW e :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
