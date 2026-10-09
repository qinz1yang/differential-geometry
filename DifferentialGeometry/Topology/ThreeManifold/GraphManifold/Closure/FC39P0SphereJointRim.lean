import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointShell
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersRim

/-!
# FC39 producer, packet P0 (gate 1): the joint S³ configuration, the rim base map

The labelled smooth rim base of `JunctionsV2` (§5.6, `rimBase`, `rimBase_smooth`, `rim_fibre`)
for the S³ data: the edge base point with real coordinate `τ` (`[0, 1]` the south handle, `[3, 4]`
the north handle, `sphereEdgeBundle`) goes to the circle base point
`(ψ, r) = (1, ρ(τ))` for `τ < 2` and `(4, ρ(4 − τ))` for `τ > 2` (`ρ = cycleHandleRadius`), the
base point of the rim circle of the handle at that parameter (`sphereRim_fibre`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local instance diskChartsRim_JOINT : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## The radius profile on the wide interval -/

theorem cycleHandleRadius_mem_wide_JOINT {s : ℝ} (hs : s ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    cycleHandleRadius s ∈ sphereCircleWide := by
  have hmono := cycleHandleRadius_strictMonoOn_FC39P0
  have hq : (1 / 4 : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := by constructor <;> norm_num
  have h3q : (3 / 4 : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := by constructor <;> norm_num
  have e1 : cycleHandleRadius (1 / 4) = 5 / 4 := by
    rw [cycleHandleRadius_inner le_rfl]
    norm_num
  have e3 : cycleHandleRadius (3 / 4) = 16 / 5 := by
    rw [cycleHandleRadius_outer le_rfl]
    norm_num
  by_cases h1 : s ≤ 1 / 4
  · rw [cycleHandleRadius_inner h1]
    constructor <;> linarith [hs.1]
  by_cases h3 : 3 / 4 ≤ s
  · rw [cycleHandleRadius_outer h3]
    have hd : 0 < 2 - s := by linarith [hs.2]
    constructor
    · rw [lt_div_iff₀ hd]
      linarith [hs.2]
    · rw [div_lt_iff₀ hd]
      linarith [hs.2]
  push Not at h1 h3
  have a := hmono hq hs h1
  have b := hmono hs h3q h3
  rw [e1] at a
  rw [e3] at b
  constructor <;> linarith

/-! ## The rim base map -/

/-- The `ψ` coordinate of the rim over the edge coordinate `τ` (`1` south, `4` north). -/
def sphereRimPsi (τ : ℝ) : ℝ :=
  if τ < 2 then 1 else 4

/-- The radius of the rim over the edge coordinate `τ` (`ρ(τ)` south, `ρ(4 − τ)` north). -/
def sphereRimRadius (τ : ℝ) : ℝ :=
  if τ < 2 then cycleHandleRadius τ else cycleHandleRadius (4 - τ)

/-- The rim base point in `ℝ²`. -/
def sphereRimBaseE (τ : ℝ) : E2 :=
  sphereCircleEquiv.symm (sphereRimPsi τ, sphereRimRadius τ)

theorem sphereRimBaseE_mem (c : edgeBaseOpens) :
    sphereRimBaseE (edgeBaseCoord c) ∈ sphereCircleBaseSet := by
  have hc := edgeBaseCoord_mem c
  unfold sphereRimBaseE sphereRimPsi sphereRimRadius
  rcases hc with hc | hc
  · have h2 : edgeBaseCoord c < 2 := by linarith [hc.2]
    simp only [h2, ite_true]
    exact sphereCircleEquiv_symm_mem ⟨by norm_num, by norm_num⟩
      (cycleHandleRadius_mem_wide_JOINT hc)
  · have h2 : ¬ edgeBaseCoord c < 2 := by linarith [hc.1]
    simp only [h2, ite_false]
    exact sphereCircleEquiv_symm_mem ⟨by norm_num, by norm_num⟩
      (cycleHandleRadius_mem_wide_JOINT ⟨by linarith [hc.2], by linarith [hc.1]⟩)

/-- **The rim base map** `rimBase : C₂-base → C₁-base` of the S³ data. -/
def sphereRimBase (c : edgeBaseOpens) : sphereCircleBaseOpens :=
  ⟨sphereRimBaseE (edgeBaseCoord c), sphereRimBaseE_mem c⟩

theorem sphereRimBase_val (c : edgeBaseOpens) :
    ((sphereRimBase c : sphereCircleBaseOpens) : E2) = sphereRimBaseE (edgeBaseCoord c) :=
  rfl

theorem contDiffAt_sphereRimBaseE {τ : ℝ} (hτ : τ ∈ edgeBaseReal) :
    ContDiffAt ℝ ∞ sphereRimBaseE τ := by
  rcases hτ with hτ | hτ
  · have h2 : τ < 2 := by linarith [hτ.2]
    have hρ : ContDiffAt ℝ ∞ cycleHandleRadius τ :=
      cycleHandleRadius_smooth.contDiffAt (Iio_mem_nhds h2)
    have hg : ContDiffAt ℝ ∞ (fun s : ℝ => sphereCircleEquiv.symm ((1 : ℝ), cycleHandleRadius s))
        τ :=
      sphereCircleEquiv.symm.contDiff.contDiffAt.comp τ (contDiffAt_const.prodMk hρ)
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h2] with s (hs : s < 2)
    simp only [sphereRimBaseE, sphereRimPsi, sphereRimRadius, hs, ite_true]
  · have h2 : 2 < τ := by linarith [hτ.1]
    have h4 : 4 - τ < 2 := by linarith
    have hρ : ContDiffAt ℝ ∞ (fun s : ℝ => cycleHandleRadius (4 - s)) τ :=
      (cycleHandleRadius_smooth.contDiffAt (Iio_mem_nhds h4)).comp τ
        (contDiffAt_const.sub contDiffAt_id)
    have hg : ContDiffAt ℝ ∞
        (fun s : ℝ => sphereCircleEquiv.symm ((4 : ℝ), cycleHandleRadius (4 - s))) τ :=
      sphereCircleEquiv.symm.contDiff.contDiffAt.comp τ (contDiffAt_const.prodMk hρ)
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h2] with s (hs : 2 < s)
    have hs' : ¬ s < 2 := by linarith
    simp only [sphereRimBaseE, sphereRimPsi, sphereRimRadius, hs', ite_false]

theorem contMDiff_edgeBaseCoord_JOINT : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ edgeBaseCoord :=
  edgeLineEquiv.symm.contDiff.contMDiff.comp contMDiff_subtype_val

/-- **`rimBase_smooth`** (in fact smooth on the whole edge base). -/
theorem contMDiff_sphereRimBase : ContMDiff (𝓡 1) (𝓡 2) ∞ sphereRimBase := by
  rw [← DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff sphereCircleBaseOpens
    sphereRimBase]
  intro c
  exact (contDiffAt_sphereRimBaseE (edgeBaseCoord_mem c)).contMDiffAt.comp c
    (contMDiff_edgeBaseCoord_JOINT c)

/-! ## The rims are the circle fibres -/

theorem sphereRimBase_interval (b : Bool) (t : Icc (0 : ℝ) 1) :
    ((sphereRimBase (edgeInterval b t) : sphereCircleBaseOpens) : E2) =
      sphereCircleEquiv.symm (bif b then 4 else 1,
        cycleHandleRadius (handleRadiusParam b t.val)) := by
  rw [sphereRimBase_val, edgeBaseCoord_interval]
  unfold sphereRimBaseE sphereRimPsi sphereRimRadius
  cases b
  · have h2 : t.val + edgeShift false < 2 := by
      simp only [edgeShift, Bool.false_eq_true, ite_false]
      linarith [t.2.2]
    simp only [h2, ↓reduceIte]
    simp only [edgeShift, Bool.false_eq_true, ite_false, add_zero, Bool.cond_false,
      handleRadiusParam]
  · have h2 : ¬ t.val + edgeShift true < 2 := by
      simp only [edgeShift, ite_true]
      linarith [t.2.1]
    simp only [h2, ↓reduceIte]
    simp only [edgeShift, ite_true, Bool.cond_true, handleRadiusParam]
    rw [show (4 : ℝ) - (t.val + 3) = 1 - t.val by ring]

/-- The rim of the handle `b` at the parameter `t` is the circle fibre over its rim base point. -/
theorem sphereHandle_rim_eq_fibre (b : Bool) (t : Icc (0 : ℝ) 1) :
    (fun w => (cycleS3Handle b).map (w, t)) '' diskRim =
      sphereCircleBundle.fibre (sphereRimBase (edgeInterval b t)) := by
  rw [sphereCircleBundle_fibre, sphereRimBase_interval]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : ‖w.val‖ = 1 := diskRim_iff_FC39P0b.1 hw
    have hw0 : w.val ≠ 0 := norm_ne_zero_iff.1 (by rw [h1]; norm_num)
    cases b
    · refine ⟨unitOf (Complex.orthonormalBasisOneI.repr.symm w.val), ?_⟩
      change _ = cycleHandleChart false (w.val, t.val)
      rw [cycleHandleChart_false_eq_circle, h1]
      rfl
    · refine ⟨circleAntipode_CIRCA (unitOf (Complex.orthonormalBasisOneI.repr.symm w.val)), ?_⟩
      change _ = cycleHandleChart true (w.val, t.val)
      rw [cycleHandleChart_true_eq_circle hw0, h1, div_one]
      rfl
  · rintro ⟨s, rfl⟩
    cases b
    · refine ⟨⟨planeOfCircle s, (planeOfCircle_norm_CIRCA s).le⟩,
        diskRim_iff_FC39P0b.2 (planeOfCircle_norm_CIRCA s), ?_⟩
      change cycleHandleChart false (planeOfCircle s, t.val) = _
      rw [cycleHandleChart_false_eq_circle, planeOfCircle_norm_CIRCA, unitOf_planeOfCircle_CIRCB]
      rfl
    · refine ⟨⟨planeOfCircle (circleAntipode_CIRCA s),
        (planeOfCircle_norm_CIRCA _).le⟩, diskRim_iff_FC39P0b.2 (planeOfCircle_norm_CIRCA _), ?_⟩
      have hw0 : planeOfCircle (circleAntipode_CIRCA s) ≠ 0 :=
        norm_ne_zero_iff.1 (by rw [planeOfCircle_norm_CIRCA]; norm_num)
      change cycleHandleChart true (planeOfCircle (circleAntipode_CIRCA s), t.val) = _
      rw [cycleHandleChart_true_eq_circle hw0, planeOfCircle_norm_CIRCA,
        unitOf_planeOfCircle_CIRCB, circleAntipode_antipode_CIRCA, div_one]
      rfl

/-- **`rim_fibre` for the S³ data**: over `C₂` the rim circle is the whole circle fibre over the rim
base point. -/
theorem sphereRim_fibre (c : edgeBaseOpens) (hc : c ∈ sphereEdgeBundle.cbase) :
    sphereEdgeBundle.rim c = sphereCircleBundle.fibre (sphereRimBase c) := by
  have hc' : c ∈ edgeCbase := hc
  rw [edgeCbase_eq] at hc'
  have key : ∀ (b : Bool) (t : Icc (0 : ℝ) 1),
      sphereEdgeBundle.rim (edgeInterval b t) =
        sphereCircleBundle.fibre (sphereRimBase (edgeInterval b t)) := by
    intro b t
    rw [← sphereHandle_rim_eq_fibre, cycleS3Handle_rim]
    rfl
  rcases hc' with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact key false t
  · exact key true t

end GC.GraphManifold.Assembly.FC39P0
