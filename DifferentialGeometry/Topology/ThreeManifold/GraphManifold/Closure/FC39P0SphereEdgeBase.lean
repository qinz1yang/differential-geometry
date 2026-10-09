import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereZero
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleHandles
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding

/-!
# FC39 producer, packet P0 (gate 1), §7.3: the S³ edge kind, the edge bundle

Task-47 draft §7.3 / §7.9 rows "edge manifold / source / proj / height", "edge rank / proper /
full disks", for the S³ inhabitant (disposition D10), in the stereographic convention of
`FC39P0SphereZero.lean` (deviation B.13 of the gate-1 report). The two polar disk handles of the
cycle inhabitant, `cycleS3Handle false` (south cap) and `cycleS3Handle true` (north cap), are the
handles; their charts `χ_b = cycleHandleChart b` (polar cap stereographic disk × the strictly
increasing radius `1 → 4`, reversed for `b = true`) are extended to the open boxes
`B(0, 2) × (−1/2, 3/2)`, whose images `A_b` are open and disjoint (`edgeSide_disjoint`: the cap
direction stays in one open hemisphere for `‖w‖ < 2`). In these coordinates `(w, t)`:

* `source = A_false ∪ A_true`;
* `Base` = the open subset `(−1/2, 3/2) ∪ (5/2, 9/2)` of `ℝ¹` (two open intervals), `proj = t`
  on `A_false` and `t + 3` on `A_true`;
* `height = ‖w‖²`, `level = 1` (the draft's `4 + a − |u|`, `4`, replaced by the disk coordinate:
  every disk fibre is the image of the whole closed unit disk, every rim of the unit circle);
* `cbase = [0, 1] ∪ [3, 4]`, with the four endpoints and the affine boundary functions.

Result: `sphereEdgeBundle : EdgeBundle sphereW`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance diskChartsEdgeBase_FC39P0b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## The radius profile and the handle charts -/

theorem cycleHandleRadius_strictMonoOn_FC39P0 :
    StrictMonoOn cycleHandleRadius (Ioo (-1 / 2 : ℝ) (3 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-1 / 2) (3 / 2))
  · exact cycleHandleRadius_smooth.continuousOn.mono (by
      intro t ht
      change t < 2
      linarith [ht.2])
  · intro t ht
    have ht' := interior_subset ht
    exact cycleHandleRadius_deriv_pos (by linarith [ht'.2])

theorem cycleHandleRadius_pos_FC39P0 {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    0 < cycleHandleRadius t := by
  by_cases hsmall : t ≤ 1 / 4
  · rw [cycleHandleRadius_inner hsmall]
    linarith [ht.1]
  · have hquarter : (1 / 4 : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := by constructor <;> norm_num
    have h := cycleHandleRadius_strictMonoOn_FC39P0 hquarter ht (not_le.mp hsmall)
    rw [cycleHandleRadius_inner le_rfl] at h
    linarith

/-- The handle chart in closed form (the cap direction made explicit). -/
theorem cycleHandleChart_eq_FC39P0 (b : Bool) (p : E2 × ℝ) :
    cycleHandleChart b p = cycleBallAmbient false
      (cycleHandleRadius (if b then 1 - p.2 else p.2) •
        (if b then -((Handle.stereoChart northPole).symm p.1 : E3) else
          ((Handle.stereoChart northPole).symm p.1 : E3))) := by
  rw [cycleHandleChart_apply]
  cases b <;> rfl

/-! ## The open chart box and the two open sides -/

/-- The open chart box `B(0, 2) × (−1/2, 3/2)`. -/
def edgeBox : Set (E2 × ℝ) :=
  ball (0 : E2) 2 ×ˢ Ioo (-1 / 2 : ℝ) (3 / 2)

theorem isOpen_edgeBox : IsOpen edgeBox :=
  isOpen_ball.prod isOpen_Ioo

theorem edgeBox_subset_source (b : Bool) : edgeBox ⊆ (cycleHandleChart b).source := by
  rw [cycleHandleChart_source]
  exact prod_mono (subset_univ _) Subset.rfl

/-- The open side `A_b = χ_b(B(0, 2) × (−1/2, 3/2))`. -/
def edgeSide (b : Bool) : Set sphereW.Carrier :=
  cycleHandleChart b '' edgeBox

theorem isOpen_edgeSide (b : Bool) : IsOpen (edgeSide b) :=
  (cycleHandleChart b).toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_edgeBox
    (edgeBox_subset_source b)

/-- The vertical component `⟪χ_b(w, t), N⟫` in the stereographic chart has the sign of `b`. -/
theorem inner_stereoChart_symm_neg_FC39P0 {w : E2} (hw : w ∈ ball (0 : E2) 2) :
    ⟪((Handle.stereoChart northPole).symm w : E3), (northPole : E3)⟫_ℝ < 0 := by
  rw [Handle.inner_stereoChart_symm]
  apply div_neg_of_neg_of_pos
  · have h := mem_ball_zero_iff.1 hw
    have h0 := norm_nonneg w
    nlinarith
  · positivity

/-- **The two sides are disjoint** (south cap directions against north cap directions). -/
theorem edgeSide_disjoint : Disjoint (edgeSide false) (edgeSide true) := by
  rw [Set.disjoint_left]
  rintro z ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
  rw [cycleHandleChart_eq_FC39P0, cycleHandleChart_eq_FC39P0] at hpq
  have he := (cycleBallAmbient false).injOn
    (by rw [cycleBallAmbient_source]; exact mem_univ _)
    (by rw [cycleBallAmbient_source]; exact mem_univ _) hpq
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  have hq0 : 0 < cycleHandleRadius (1 - q.2) :=
    cycleHandleRadius_pos_FC39P0 (by constructor <;> linarith [hq.2.1, hq.2.2])
  have hp0 : 0 < cycleHandleRadius p.2 := cycleHandleRadius_pos_FC39P0 hp.2
  have hinner := congrArg (fun v : E3 => ⟪v, (northPole : E3)⟫_ℝ) he
  simp only [inner_smul_left, inner_neg_left, RCLike.conj_to_real] at hinner
  have h1 := inner_stereoChart_symm_neg_FC39P0 hq.1
  have h2 := inner_stereoChart_symm_neg_FC39P0 hp.1
  nlinarith [mul_pos hq0 (neg_pos.2 h1), mul_pos hp0 (neg_pos.2 h2)]

/-! ## Chart coordinates on the two sides -/

/-- The shift of the base coordinate on the side `b` (`0` south, `3` north). -/
def edgeShift (b : Bool) : ℝ :=
  if b then 3 else 0

open scoped Classical in
/-- The chart coordinates `(w, t)` of a point (read in `χ_true` on `A_true`, else in `χ_false`). -/
def edgeCoord (x : sphereW.Carrier) : E2 × ℝ :=
  if x ∈ edgeSide true then (cycleHandleChart true).symm x else (cycleHandleChart false).symm x

open scoped Classical in
/-- The base shift of a point (`3` on `A_true`, else `0`). -/
def edgeOffset (x : sphereW.Carrier) : ℝ :=
  if x ∈ edgeSide true then 3 else 0

theorem chart_mem_edgeSide {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    cycleHandleChart b p ∈ edgeSide b :=
  mem_image_of_mem _ hp

theorem not_mem_edgeSide_true {x : sphereW.Carrier} (hx : x ∈ edgeSide false) :
    x ∉ edgeSide true :=
  Set.disjoint_left.1 edgeSide_disjoint hx

theorem edgeCoord_eq_of_mem {b : Bool} {x : sphereW.Carrier} (hx : x ∈ edgeSide b) :
    edgeCoord x = (cycleHandleChart b).symm x := by
  cases b
  · exact ite_eq_right (not_mem_edgeSide_true hx)
  · exact ite_eq_left hx

theorem edgeOffset_eq_of_mem {b : Bool} {x : sphereW.Carrier} (hx : x ∈ edgeSide b) :
    edgeOffset x = edgeShift b := by
  cases b
  · exact ite_eq_right (not_mem_edgeSide_true hx)
  · exact ite_eq_left hx

theorem edgeCoord_chart {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    edgeCoord (cycleHandleChart b p) = p := by
  rw [edgeCoord_eq_of_mem (chart_mem_edgeSide hp)]
  exact (cycleHandleChart b).left_inv (edgeBox_subset_source b hp)

theorem edgeOffset_chart {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    edgeOffset (cycleHandleChart b p) = edgeShift b :=
  edgeOffset_eq_of_mem (chart_mem_edgeSide hp)

theorem edgeCoord_eventuallyEq {b : Bool} {x : sphereW.Carrier} (hx : x ∈ edgeSide b) :
    edgeCoord =ᶠ[𝓝 x] (cycleHandleChart b).symm := by
  filter_upwards [(isOpen_edgeSide b).mem_nhds hx] with y hy
  exact edgeCoord_eq_of_mem hy

theorem edgeOffset_eventuallyEq {b : Bool} {x : sphereW.Carrier} (hx : x ∈ edgeSide b) :
    edgeOffset =ᶠ[𝓝 x] fun _ => edgeShift b := by
  filter_upwards [(isOpen_edgeSide b).mem_nhds hx] with y hy
  exact edgeOffset_eq_of_mem hy

theorem edgeSide_subset_target (b : Bool) : edgeSide b ⊆ (cycleHandleChart b).target := by
  rintro _ ⟨p, hp, rfl⟩
  exact (cycleHandleChart b).map_source (edgeBox_subset_source b hp)

theorem contMDiffAt_chart_symm {b : Bool} {x : sphereW.Carrier} (hx : x ∈ edgeSide b) :
    ContMDiffAt sphereW.model ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (cycleHandleChart b).symm x :=
  ((cycleHandleChart b).symm.contMDiffOn x (edgeSide_subset_target b hx)).contMDiffAt
    ((cycleHandleChart b).open_target.mem_nhds (edgeSide_subset_target b hx))

/-! ## The base: two open intervals of `ℝ¹` -/

/-- The linear identification `ℝ ≃ ℝ¹`. -/
def edgeLineEquiv : ℝ ≃L[ℝ] E1 :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- The base intervals `(−1/2, 3/2) ∪ (5/2, 9/2)`. -/
def edgeBaseReal : Set ℝ :=
  Ioo (-1 / 2) (3 / 2) ∪ Ioo (5 / 2) (9 / 2)

/-- The edge base: the open subset `(−1/2, 3/2) ∪ (5/2, 9/2)` of `ℝ¹`. -/
def edgeBaseOpens : TopologicalSpace.Opens E1 :=
  ⟨edgeLineEquiv.symm ⁻¹' edgeBaseReal,
    (isOpen_Ioo.union isOpen_Ioo).preimage edgeLineEquiv.symm.continuous⟩

/-- The real coordinate of a base point. -/
def edgeBaseCoord (c : edgeBaseOpens) : ℝ :=
  edgeLineEquiv.symm c.val

theorem edgeBaseCoord_mem (c : edgeBaseOpens) : edgeBaseCoord c ∈ edgeBaseReal :=
  c.2

theorem shift_mem_edgeBaseReal (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    t + edgeShift b ∈ edgeBaseReal := by
  cases b
  · left
    simpa [edgeShift] using ht
  · right
    simp only [edgeShift, ite_true]
    constructor <;> linarith [ht.1, ht.2]

/-- The base point with coordinate `t + shift b`. -/
def edgeBasePoint (b : Bool) (t : ℝ) (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) : edgeBaseOpens :=
  ⟨edgeLineEquiv (t + edgeShift b), by
    change edgeLineEquiv.symm (edgeLineEquiv (t + edgeShift b)) ∈ edgeBaseReal
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact shift_mem_edgeBaseReal b ht⟩

theorem edgeBaseCoord_basePoint (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    edgeBaseCoord (edgeBasePoint b t ht) = t + edgeShift b :=
  edgeLineEquiv.symm_apply_apply _

theorem edgeShift_eq_iff {b b' : Bool} {t t' : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2))
    (ht' : t' ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    t + edgeShift b = t' + edgeShift b' ↔ b = b' ∧ t = t' := by
  constructor
  · intro h
    cases b <;> cases b' <;>
      simp only [edgeShift, Bool.false_eq_true, ite_false, ite_true, add_zero] at h
    · exact ⟨rfl, h⟩
    · exfalso
      linarith [ht.2, ht'.1]
    · exfalso
      linarith [ht.1, ht'.2]
    · exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every base point is `edgeBasePoint b t` for one side `b` and one `t ∈ (−1/2, 3/2)`. -/
theorem edgeBase_cases (c : edgeBaseOpens) :
    ∃ b t, ∃ ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2), c = edgeBasePoint b t ht := by
  have hc := edgeBaseCoord_mem c
  have key : ∀ (b : Bool) (t : ℝ) (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)),
      edgeBaseCoord c = t + edgeShift b → c = edgeBasePoint b t ht := by
    intro b t ht h
    apply Subtype.ext
    change c.val = edgeLineEquiv (t + edgeShift b)
    rw [← h, edgeBaseCoord, ContinuousLinearEquiv.apply_symm_apply]
  rcases hc with hc | hc
  · exact ⟨false, _, hc, key false _ hc (by simp [edgeShift])⟩
  · have ht : edgeBaseCoord c - 3 ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := by
      constructor <;> linarith [hc.1, hc.2]
    exact ⟨true, _, ht, key true _ ht (by simp [edgeShift])⟩

/-! ## The source, the projection and the height -/

/-- The source `A_false ∪ A_true`. -/
def edgeSource : TopologicalSpace.Opens sphereW.Carrier :=
  ⟨edgeSide false ∪ edgeSide true, (isOpen_edgeSide false).union (isOpen_edgeSide true)⟩

theorem mem_edgeSource_iff {x : sphereW.Carrier} : x ∈ edgeSource ↔ ∃ b, x ∈ edgeSide b := by
  constructor
  · rintro (h | h)
    exacts [⟨false, h⟩, ⟨true, h⟩]
  · rintro ⟨b, h⟩
    cases b
    exacts [Or.inl h, Or.inr h]

theorem chart_mem_edgeSource {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    cycleHandleChart b p ∈ edgeSource :=
  mem_edgeSource_iff.2 ⟨b, chart_mem_edgeSide hp⟩

/-- The projection to `ℝ¹` (`t` on `A_false`, `t + 3` on `A_true`). -/
def edgeProjE (x : sphereW.Carrier) : E1 :=
  edgeLineEquiv ((edgeCoord x).2 + edgeOffset x)

/-- The height `‖w‖²`. -/
def edgeHeightR (x : sphereW.Carrier) : ℝ :=
  ‖(edgeCoord x).1‖ ^ 2

theorem edgeProjE_chart {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    edgeProjE (cycleHandleChart b p) = edgeLineEquiv (p.2 + edgeShift b) := by
  rw [edgeProjE, edgeCoord_chart hp, edgeOffset_chart hp]

theorem edgeHeightR_chart {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    edgeHeightR (cycleHandleChart b p) = ‖p.1‖ ^ 2 := by
  rw [edgeHeightR, edgeCoord_chart hp]

theorem edgeProjE_mem (x : edgeSource) : edgeProjE x.val ∈ edgeBaseOpens := by
  obtain ⟨b, p, hp, hx⟩ := mem_edgeSource_iff.1 x.2
  rw [← hx, edgeProjE_chart hp]
  change edgeLineEquiv.symm (edgeLineEquiv _) ∈ edgeBaseReal
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact shift_mem_edgeBaseReal b hp.2

/-- The bundle projection `source → Base`. -/
def edgeProj (x : edgeSource) : edgeBaseOpens :=
  ⟨edgeProjE x.val, edgeProjE_mem x⟩

/-- The bundle height `source → ℝ`. -/
def edgeHeight (x : edgeSource) : ℝ :=
  edgeHeightR x.val

theorem contMDiffAt_edgeProjE {x : sphereW.Carrier} (hx : x ∈ edgeSource) :
    ContMDiffAt sphereW.model (𝓡 1) ∞ edgeProjE x := by
  obtain ⟨b, hb⟩ := mem_edgeSource_iff.1 hx
  have h : ContMDiffAt sphereW.model (𝓡 1) ∞
      (fun y => edgeLineEquiv (((cycleHandleChart b).symm y).2 + edgeShift b)) x :=
    edgeLineEquiv.contDiff.contMDiff.contMDiffAt.comp x
      ((contMDiffAt_snd.comp x (contMDiffAt_chart_symm hb)).add contMDiffAt_const)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [edgeCoord_eventuallyEq hb, edgeOffset_eventuallyEq hb] with y h1 h2
  simp only [edgeProjE, h1, h2]

theorem contMDiffAt_edgeHeightR {x : sphereW.Carrier} (hx : x ∈ edgeSource) :
    ContMDiffAt sphereW.model 𝓘(ℝ, ℝ) ∞ edgeHeightR x := by
  obtain ⟨b, hb⟩ := mem_edgeSource_iff.1 hx
  have h : ContMDiffAt sphereW.model 𝓘(ℝ, ℝ) ∞
      (fun y => ‖((cycleHandleChart b).symm y).1‖ ^ 2) x :=
    (contDiff_norm_sq ℝ).contMDiff.contMDiffAt.comp x
      (contMDiffAt_fst.comp x (contMDiffAt_chart_symm hb))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [edgeCoord_eventuallyEq hb] with y h1
  simp only [edgeHeightR, h1]

theorem contMDiff_edgeProj : ContMDiff sphereW.model (𝓡 1) ∞ edgeProj := by
  rw [← DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff edgeBaseOpens edgeProj]
  intro x
  exact contMDiffAt_subtype_iff.2 (contMDiffAt_edgeProjE x.2)

theorem contMDiff_edgeHeight : ContMDiff sphereW.model 𝓘(ℝ, ℝ) ∞ edgeHeight := fun x =>
  contMDiffAt_subtype_iff.2 (contMDiffAt_edgeHeightR x.2)

/-! ## Derivatives in the chart coordinates -/

theorem mdifferentiableAt_chart (b : Bool) {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereW.model (cycleHandleChart b) p :=
  (cycleHandleChart b).mdifferentiableAt (by simp) (edgeBox_subset_source b hp)

/-- `d proj (dχ u) = u_t`. -/
theorem mfderiv_edgeProjE_chart {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) (u : E2 × ℝ) :
    mfderiv sphereW.model (𝓡 1) edgeProjE (cycleHandleChart b p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereW.model (cycleHandleChart b) p u) =
      edgeLineEquiv u.2 := by
  have hf : MDifferentiableAt sphereW.model (𝓡 1) edgeProjE (cycleHandleChart b p) :=
    (contMDiffAt_edgeProjE (chart_mem_edgeSource hp)).mdifferentiableAt (by simp)
  have heq : edgeProjE ∘ cycleHandleChart b =ᶠ[𝓝 p]
      fun q : E2 × ℝ => edgeLineEquiv (q.2 + edgeShift b) := by
    filter_upwards [isOpen_edgeBox.mem_nhds hp] with q hq
    exact edgeProjE_chart hq
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (fun s : ℝ => edgeLineEquiv (s + edgeShift b)) p.2
      (edgeLineEquiv : ℝ →L[ℝ] E1) := by
    have h := (edgeLineEquiv.hasFDerivAt (x := p.2 + edgeShift b)).comp p.2
      ((hasFDerivAt_id p.2).add_const (edgeShift b))
    rw [ContinuousLinearMap.comp_id] at h
    exact h.hasMFDerivAt
  have hd := h1.comp p (hasMFDerivAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) p)
  have hc := mfderiv_comp p hf (mdifferentiableAt_chart b hp)
  rw [(hd.congr_of_eventuallyEq_abuse heq).mfderiv] at hc
  have := congrArg (fun L => L u) hc
  exact this.symm

/-- `d height (dχ u) = 2 ⟪w, u_w⟫`. -/
theorem mfderiv_edgeHeightR_chart {b : Bool} {p : E2 × ℝ} (hp : p ∈ edgeBox) (u : E2 × ℝ) :
    mfderiv sphereW.model 𝓘(ℝ, ℝ) edgeHeightR (cycleHandleChart b p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereW.model (cycleHandleChart b) p u) =
      2 * ⟪p.1, u.1⟫_ℝ := by
  have hf : MDifferentiableAt sphereW.model 𝓘(ℝ, ℝ) edgeHeightR (cycleHandleChart b p) :=
    (contMDiffAt_edgeHeightR (chart_mem_edgeSource hp)).mdifferentiableAt (by simp)
  have heq : edgeHeightR ∘ cycleHandleChart b =ᶠ[𝓝 p] fun q : E2 × ℝ => ‖q.1‖ ^ 2 := by
    filter_upwards [isOpen_edgeBox.mem_nhds hp] with q hq
    exact edgeHeightR_chart hq
  have h1 : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun w : E2 => ‖w‖ ^ 2) p.1
      (2 • innerSL ℝ p.1) :=
    (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.hasMFDerivAt
  have hd := h1.comp p (hasMFDerivAt_fst (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) p)
  have hc := mfderiv_comp p hf (mdifferentiableAt_chart b hp)
  rw [(hd.congr_of_eventuallyEq_abuse heq).mfderiv] at hc
  have := congrArg (fun L => L u) hc
  have h2 : ((2 • innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ E2 ℝ)) u = 2 * ⟪p.1, u.1⟫_ℝ := by
    rw [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply, two_nsmul, two_mul]
    rfl
  exact this.symm.trans h2

theorem mfderiv_edgeProj (x : edgeSource) :
    mfderiv sphereW.model (𝓡 1) edgeProj x = mfderiv sphereW.model (𝓡 1) edgeProjE x.val := by
  rw [← mfderiv_subtypeVal_comp edgeBaseOpens edgeProj x]
  exact DifferentialGeometry.mfderiv_restrict_open edgeProjE edgeSource x

theorem mfderiv_edgeHeight (x : edgeSource) :
    mfderiv sphereW.model 𝓘(ℝ, ℝ) edgeHeight x =
      mfderiv sphereW.model 𝓘(ℝ, ℝ) edgeHeightR x.val :=
  DifferentialGeometry.mfderiv_restrict_open edgeHeightR edgeSource x

/-- **The projection is a submersion.** -/
theorem edgeProj_submersion (x : edgeSource) :
    Surjective (mfderiv sphereW.model (𝓡 1) edgeProj x) := by
  rw [mfderiv_edgeProj]
  obtain ⟨x, hxs⟩ := x
  obtain ⟨b, p, hp, rfl⟩ := mem_edgeSource_iff.1 hxs
  intro v
  refine ⟨mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereW.model (cycleHandleChart b) p
    (0, edgeLineEquiv.symm v), ?_⟩
  change mfderiv sphereW.model (𝓡 1) edgeProjE (cycleHandleChart b p) _ = v
  rw [mfderiv_edgeProjE_chart hp]
  exact edgeLineEquiv.apply_symm_apply v

/-- **Joint rank two on the level `height = 1`.** -/
theorem edge_rank_two (x : edgeSource) (hx : edgeHeight x = 1) :
    Surjective fun v : TangentSpace sphereW.model (x : sphereW.Carrier) =>
      (mfderiv sphereW.model (𝓡 1) edgeProj x v, mfderiv sphereW.model 𝓘(ℝ, ℝ) edgeHeight x v) := by
  rw [mfderiv_edgeProj, mfderiv_edgeHeight]
  obtain ⟨x, hxs⟩ := x
  obtain ⟨b, p, hp, rfl⟩ := mem_edgeSource_iff.1 hxs
  change edgeHeightR (cycleHandleChart b p) = 1 at hx
  rw [edgeHeightR_chart hp] at hx
  rintro ⟨a, c⟩
  refine ⟨mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereW.model (cycleHandleChart b) p
    (((id c : ℝ) / 2) • p.1, edgeLineEquiv.symm (id a : E1)), ?_⟩
  change (mfderiv sphereW.model (𝓡 1) edgeProjE (cycleHandleChart b p) _,
    mfderiv sphereW.model 𝓘(ℝ, ℝ) edgeHeightR (cycleHandleChart b p) _) = (a, c)
  rw [mfderiv_edgeProjE_chart hp, mfderiv_edgeHeightR_chart hp]
  refine Prod.ext (edgeLineEquiv.apply_symm_apply a) ?_
  change 2 * ⟪p.1, ((id c : ℝ) / 2) • p.1⟫_ℝ = (id c : ℝ)
  rw [inner_smul_right, real_inner_self_eq_norm_sq, hx]
  ring


/-! ## Whole inverse images in the chart coordinates -/

/-- **Inverse images in chart coordinates**: the part of the source cut out by a condition on the
projection and a condition on the height is the union over the two sides of the chart images of
the corresponding box points. -/
theorem image_val_edgeSource (Q : E1 → Prop) (R : ℝ → Prop) :
    Subtype.val '' {x : edgeSource | Q (edgeProjE x.val) ∧ R (edgeHeightR x.val)} =
      ⋃ b, cycleHandleChart b ''
        {p | p ∈ edgeBox ∧ Q (edgeLineEquiv (p.2 + edgeShift b)) ∧ R (‖p.1‖ ^ 2)} := by
  ext y
  simp only [mem_image, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hQ, hR⟩, rfl⟩
    obtain ⟨b, p, hp, hx⟩ := mem_edgeSource_iff.1 x.2
    rw [← hx, edgeProjE_chart hp] at hQ
    rw [← hx, edgeHeightR_chart hp] at hR
    exact ⟨b, p, ⟨hp, hQ, hR⟩, hx⟩
  · rintro ⟨b, p, ⟨hp, hQ, hR⟩, rfl⟩
    refine ⟨⟨_, chart_mem_edgeSource hp⟩, ⟨?_, ?_⟩, rfl⟩
    · change Q (edgeProjE (cycleHandleChart b p))
      rw [edgeProjE_chart hp]
      exact hQ
    · change R (edgeHeightR (cycleHandleChart b p))
      rw [edgeHeightR_chart hp]
      exact hR

/-- The projection condition `proj = (b, t)` selects exactly the side `b` and the slice `t`. -/
theorem iUnion_chart_fibre (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2))
    (R : ℝ → Prop) :
    (⋃ b', cycleHandleChart b' ''
        {p | p ∈ edgeBox ∧ edgeLineEquiv (p.2 + edgeShift b') = edgeLineEquiv (t + edgeShift b) ∧
          R (‖p.1‖ ^ 2)}) =
      (fun w => cycleHandleChart b (w, t)) '' {w : E2 | ‖w‖ < 2 ∧ R (‖w‖ ^ 2)} := by
  ext y
  simp only [mem_image, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨b', p, ⟨hp, he, hR⟩, rfl⟩
    obtain ⟨rfl, h2⟩ := (edgeShift_eq_iff hp.2 ht).1 (edgeLineEquiv.injective he)
    refine ⟨p.1, ⟨mem_ball_zero_iff.1 hp.1, hR⟩, ?_⟩
    rw [← h2]
  · rintro ⟨w, ⟨hw, hR⟩, rfl⟩
    exact ⟨b, (w, t), ⟨⟨mem_ball_zero_iff.2 hw, ht⟩, rfl, hR⟩, rfl⟩

/-- The set `{proj = (b, t)} ∩ R(height)` in the source. -/
theorem image_val_edgeSource_fibre (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2))
    (R : ℝ → Prop) :
    Subtype.val '' {x : edgeSource | edgeProj x = edgeBasePoint b t ht ∧ R (edgeHeight x)} =
      (fun w => cycleHandleChart b (w, t)) '' {w : E2 | ‖w‖ < 2 ∧ R (‖w‖ ^ 2)} := by
  rw [← iUnion_chart_fibre b ht R]
  have h := image_val_edgeSource (fun s => s = edgeLineEquiv (t + edgeShift b)) R
  beta_reduce at h
  rw [← h]
  congr 1
  ext x
  exact and_congr_left' Subtype.ext_iff

/-- **The whole disk over a base point** is the chart image of the closed unit disk. -/
theorem edge_disk_eq (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    Subtype.val '' {x : edgeSource | edgeProj x = edgeBasePoint b t ht ∧ edgeHeight x ≤ 1} =
      range fun w : ClosedCell 2 => cycleHandleChart b (w.val, t) := by
  rw [image_val_edgeSource_fibre b ht (· ≤ 1)]
  ext y
  constructor
  · rintro ⟨w, ⟨-, hw⟩, rfl⟩
    exact ⟨⟨w, by nlinarith [norm_nonneg w]⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.val, ⟨by linarith [w.2], by nlinarith [w.2, norm_nonneg w.val]⟩, rfl⟩

/-- A slice of the extended handle chart is a smooth embedding of the closed disk. -/
theorem isSmoothEmbedding_chart_slice (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞
      fun w : ClosedCell 2 => cycleHandleChart b (w.val, t) := by
  have hf : IsSmoothEmbedding (𝓡∂ 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      ((fun v : E2 => (v, t)) ∘ (Subtype.val : ClosedCell 2 → E2)) :=
    IsSmoothEmbedding.comp_of_boundarylessManifold_middle (isSmoothEmbedding_prodMk_const t)
      (isSmoothEmbedding_closedCell_inclusion 1) (by simp)
  have hmem : ∀ w : ClosedCell 2, ((w.val, t) : E2 × ℝ) ∈ (cycleHandleChart b).source := by
    intro w
    rw [cycleHandleChart_source]
    exact ⟨mem_univ _, ht⟩
  have himm : IsImmersion (𝓡∂ 2) (𝓡 3) ∞
      (cycleHandleChart b ∘ ((fun v : E2 => (v, t)) ∘ (Subtype.val : ClosedCell 2 → E2))) := by
    refine hf.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero (fun y => ?_) (by simp)
    obtain ⟨_, w, rfl⟩ := y
    exact (cycleHandleChart b).isLocalDiffeomorphAt _ _ ∞ (hmem w)
  refine ⟨himm, (Continuous.isClosedEmbedding himm.contMDiff.continuous ?_).isEmbedding⟩
  intro w w' h
  have := (cycleHandleChart b).injOn (hmem w) (hmem w') h
  exact Subtype.ext (congrArg Prod.fst this)

/-- **Every fibre is a whole smooth disk.** -/
theorem edge_fibre_disk (c : edgeBaseOpens) :
    ∃ φ : ClosedCell 2 → sphereW.Carrier, IsSmoothEmbedding (𝓡∂ 2) sphereW.model ∞ φ ∧
      range φ = Subtype.val '' {x : edgeSource | edgeProj x = c ∧ edgeHeight x ≤ 1} := by
  obtain ⟨b, t, ht, rfl⟩ := edgeBase_cases c
  exact ⟨_, isSmoothEmbedding_chart_slice b ht, (edge_disk_eq b ht).symm⟩

/-- **Properness**: the whole sublevel inverse image of a compact base set is compact (a finite
union of chart images of `closed disk × compact interval`). -/
theorem edge_proper (K : Set edgeBaseOpens) (hK : IsCompact K) :
    IsCompact (Subtype.val '' {x : edgeSource | edgeProj x ∈ K ∧ edgeHeight x ≤ 1}) := by
  set K' : Set E1 := Subtype.val '' K with hK'def
  have hK' : IsCompact K' := hK.image continuous_subtype_val
  have hset : {x : edgeSource | edgeProj x ∈ K ∧ edgeHeight x ≤ 1} =
      {x : edgeSource | edgeProjE x.val ∈ K' ∧ edgeHeightR x.val ≤ 1} := by
    ext x
    refine and_congr_left' ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨k, hk, hkx⟩
    have hk' : k = edgeProj x := Subtype.ext hkx
    rwa [← hk']
  have h := image_val_edgeSource (· ∈ K') (· ≤ 1)
  beta_reduce at h
  rw [hset, h]
  refine isCompact_iUnion fun b => ?_
  set T : Set ℝ := Icc (-1 / 2) (3 / 2) ∩ (fun s => edgeLineEquiv (s + edgeShift b)) ⁻¹' K'
  have hT : IsCompact T := isCompact_Icc.inter_right
    (hK'.isClosed.preimage (edgeLineEquiv.continuous.comp (continuous_id.add continuous_const)))
  have hTsub : T ⊆ Ioo (-1 / 2) (3 / 2) := by
    rintro t ⟨ht, k, -, hkt⟩
    have hk2 : edgeLineEquiv.symm k.val ∈ edgeBaseReal := k.2
    rw [hkt, ContinuousLinearEquiv.symm_apply_apply] at hk2
    cases b <;> simp only [edgeShift, Bool.false_eq_true, ite_false, ite_true, add_zero] at hk2 <;>
      rcases hk2 with h | h <;> constructor <;> linarith [h.1, h.2, ht.1, ht.2]
  have heq : {p : E2 × ℝ | p ∈ edgeBox ∧ edgeLineEquiv (p.2 + edgeShift b) ∈ K' ∧
      ‖p.1‖ ^ 2 ≤ 1} = closedBall (0 : E2) 1 ×ˢ T := by
    ext p
    constructor
    · rintro ⟨hp, hk, hh⟩
      exact ⟨mem_closedBall_zero_iff.2 (by nlinarith [norm_nonneg p.1]),
        Ioo_subset_Icc_self hp.2, hk⟩
    · rintro ⟨hw, ht, hk⟩
      have hw' := mem_closedBall_zero_iff.1 hw
      refine ⟨⟨mem_ball_zero_iff.2 (by linarith), hTsub ⟨ht, hk⟩⟩, hk, ?_⟩
      nlinarith [norm_nonneg p.1]
  rw [heq]
  refine ((isCompact_closedBall 0 1).prod hT).image_of_continuousOn
    ((cycleHandleChart b).contMDiffOn.continuousOn.mono ?_)
  intro p hp
  rw [cycleHandleChart_source]
  exact ⟨mem_univ _, hTsub hp.2⟩

/-! ## The closed base `C₂ = [0, 1] ∪ [3, 4]` -/

/-- The real closed base `[0, 1] ∪ [3, 4]`. -/
def edgeCbaseReal : Set ℝ :=
  Icc 0 1 ∪ Icc 3 4

/-- The closed edge base `C₂`. -/
def edgeCbase : Set edgeBaseOpens :=
  edgeBaseCoord ⁻¹' edgeCbaseReal

theorem continuous_edgeBaseCoord : Continuous edgeBaseCoord :=
  edgeLineEquiv.symm.continuous.comp continuous_subtype_val

theorem isOpenMap_edgeBaseCoord : IsOpenMap edgeBaseCoord :=
  edgeLineEquiv.symm.toHomeomorph.isOpenMap.comp edgeBaseOpens.isOpen.isOpenMap_subtype_val

theorem isCompact_edgeCbase : IsCompact edgeCbase := by
  rw [Subtype.isCompact_iff]
  have hval : Subtype.val '' edgeCbase = edgeLineEquiv '' edgeCbaseReal := by
    ext s
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨edgeBaseCoord c, hc, edgeLineEquiv.apply_symm_apply _⟩
    · rintro ⟨r, hr, rfl⟩
      have hm : edgeLineEquiv r ∈ edgeBaseOpens := by
        change edgeLineEquiv.symm (edgeLineEquiv r) ∈ edgeBaseReal
        rw [ContinuousLinearEquiv.symm_apply_apply]
        rcases hr with h | h
        · left
          constructor <;> linarith [h.1, h.2]
        · right
          constructor <;> linarith [h.1, h.2]
      refine ⟨⟨_, hm⟩, ?_, rfl⟩
      change edgeLineEquiv.symm (edgeLineEquiv r) ∈ edgeCbaseReal
      rwa [ContinuousLinearEquiv.symm_apply_apply]
  rw [hval]
  exact (isCompact_Icc.union isCompact_Icc).image edgeLineEquiv.continuous

theorem frontier_edgeCbaseReal : frontier edgeCbaseReal = {0, 1, 3, 4} := by
  have hcl : closure edgeCbaseReal = edgeCbaseReal := (isClosed_Icc.union isClosed_Icc).closure_eq
  have hint : interior edgeCbaseReal = Ioo 0 1 ∪ Ioo 3 4 := by
    rw [edgeCbaseReal, interior_union_of_disjoint_closure, interior_Icc, interior_Icc]
    rw [closure_Icc, closure_Icc]
    exact Set.disjoint_left.2 fun x h1 h2 => by linarith [h1.2, h2.1]
  rw [frontier, hcl, hint]
  ext s
  simp only [edgeCbaseReal, Set.mem_sdiff, mem_union, mem_Icc, mem_Ioo, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · rcases h1.1.eq_or_lt with h | h
      · exact Or.inl h.symm
      · rcases h1.2.eq_or_lt with h' | h'
        · exact Or.inr (Or.inl h')
        · exact absurd (Or.inl ⟨h, h'⟩) h2
    · rcases h1.1.eq_or_lt with h | h
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · rcases h1.2.eq_or_lt with h' | h'
        · exact Or.inr (Or.inr (Or.inr h'))
        · exact absurd (Or.inr ⟨h, h'⟩) h2
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

/-- The frontier of `C₂` in the base: the four endpoints `0, 1, 3, 4`. -/
theorem mem_frontier_edgeCbase {c : edgeBaseOpens} :
    c ∈ frontier edgeCbase ↔ edgeBaseCoord c ∈ ({0, 1, 3, 4} : Set ℝ) := by
  rw [edgeCbase, ← isOpenMap_edgeBaseCoord.preimage_frontier_eq_frontier_preimage
    continuous_edgeBaseCoord, frontier_edgeCbaseReal]
  rfl

/-- The boundary function of `C₂` at an endpoint `j` with inward sign `σ`. -/
theorem edgeCbase_domain_at (j σ : ℝ) (hσ : σ ≠ 0)
    (hloc : ∀ s ∈ Ioo (j - 1 / 2) (j + 1 / 2), s ∈ edgeCbaseReal ↔ 0 ≤ σ * (s - j))
    (c : edgeBaseOpens) (hc : edgeBaseCoord c = j) :
    ∃ U : TopologicalSpace.Opens edgeBaseOpens, c ∈ U ∧
      ∃ φ : edgeBaseOpens → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧ edgeCbase ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  let g : E1 → ℝ := fun s => σ * (edgeLineEquiv.symm s - j)
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul (edgeLineEquiv.symm.contDiff.sub contDiff_const)
  refine ⟨⟨edgeBaseCoord ⁻¹' Ioo (j - 1 / 2) (j + 1 / 2),
    isOpen_Ioo.preimage continuous_edgeBaseCoord⟩, ?_, fun c' => g c'.val, ?_, ?_, ?_, ?_⟩
  · change edgeBaseCoord c ∈ Ioo _ _
    rw [hc]
    constructor <;> linarith
  · exact (hg.contMDiff.comp contMDiff_subtype_val).contMDiffOn
  · change σ * (edgeBaseCoord c - j) = 0
    rw [hc, sub_self, mul_zero]
  · rw [DifferentialGeometry.mfderiv_restrict_open g edgeBaseOpens c]
    have hd : HasFDerivAt g (σ • (edgeLineEquiv.symm : E1 →L[ℝ] ℝ)) c.val := by
      have h := ((edgeLineEquiv.symm.hasFDerivAt (x := c.val)).sub_const j).const_mul σ
      simpa using h
    rw [hd.hasMFDerivAt.mfderiv]
    intro h
    apply hσ
    have h1 := congrArg (fun L : E1 →L[ℝ] ℝ => L (edgeLineEquiv 1)) h
    have h2 : (σ • (edgeLineEquiv.symm : E1 →L[ℝ] ℝ)) (edgeLineEquiv 1) = σ := by simp
    exact h2.symm.trans h1
  · ext c'
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (hloc _ h2).1 h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(hloc _ h2).2 h1, h2⟩

/-- **The boundary functions of `C₂`** at its four endpoints (`t ≥ 0` at `0, 3`, `1 − t ≥ 0`
at `1, 4`). -/
theorem edgeCbase_domain (c : edgeBaseOpens) (hc : c ∈ frontier edgeCbase) :
    ∃ U : TopologicalSpace.Opens edgeBaseOpens, c ∈ U ∧
      ∃ φ : edgeBaseOpens → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧ edgeCbase ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  rcases mem_frontier_edgeCbase.1 hc with h | h | h | h
  · refine edgeCbase_domain_at 0 1 one_ne_zero (fun s hs => ?_) c h
    simp only [edgeCbaseReal, mem_union, mem_Icc]
    constructor
    · rintro (h' | h') <;> linarith [hs.1, hs.2, h'.1, h'.2]
    · intro h'
      exact Or.inl ⟨by linarith, by linarith [hs.2]⟩
  · refine edgeCbase_domain_at 1 (-1) (by norm_num) (fun s hs => ?_) c h
    simp only [edgeCbaseReal, mem_union, mem_Icc]
    constructor
    · rintro (h' | h') <;> linarith [hs.1, hs.2, h'.1, h'.2]
    · intro h'
      exact Or.inl ⟨by linarith [hs.1], by linarith⟩
  · refine edgeCbase_domain_at 3 1 one_ne_zero (fun s hs => ?_) c h
    simp only [edgeCbaseReal, mem_union, mem_Icc]
    constructor
    · rintro (h' | h') <;> linarith [hs.1, hs.2, h'.1, h'.2]
    · intro h'
      exact Or.inr ⟨by linarith, by linarith [hs.2]⟩
  · refine edgeCbase_domain_at 4 (-1) (by norm_num) (fun s hs => ?_) c h
    simp only [edgeCbaseReal, mem_union, mem_Icc]
    constructor
    · rintro (h' | h') <;> linarith [hs.1, hs.2, h'.1, h'.2]
    · intro h'
      exact Or.inr ⟨by linarith [hs.1], by linarith⟩

/-! ## The edge bundle of the S³ inhabitant -/

/-- **The S³ edge bundle** (§5.4, draft §7.3 in the stereographic convention): source
`A_false ∪ A_true`, base `(−1/2, 3/2) ∪ (5/2, 9/2) ⊆ ℝ¹`, projection `t` / `t + 3`, height `‖w‖²`,
level `1`, closed base `[0, 1] ∪ [3, 4]`. -/
def sphereEdgeBundle : EdgeBundle sphereW where
  Base := edgeBaseOpens
  source := edgeSource
  source_interior _ _ := BoundarylessManifold.isInteriorPoint
  proj := ⟨edgeProj, contMDiff_edgeProj.continuous⟩
  proj_smooth := contMDiff_edgeProj
  proj_submersion := edgeProj_submersion
  height := edgeHeight
  height_smooth := contMDiff_edgeHeight
  level := 1
  rank_two := edge_rank_two
  proper := edge_proper
  fibre_disk := edge_fibre_disk
  cbase := edgeCbase
  cbase_compact := isCompact_edgeCbase
  cbase_domain := edgeCbase_domain

theorem sphereEdgeBundle_proj (x : edgeSource) : sphereEdgeBundle.proj x = edgeProj x :=
  rfl

theorem sphereEdgeBundle_height (x : edgeSource) : sphereEdgeBundle.height x = edgeHeight x :=
  rfl

theorem sphereEdgeBundle_level : sphereEdgeBundle.level = 1 :=
  rfl

theorem sphereEdgeBundle_cbase : sphereEdgeBundle.cbase = edgeCbase :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
