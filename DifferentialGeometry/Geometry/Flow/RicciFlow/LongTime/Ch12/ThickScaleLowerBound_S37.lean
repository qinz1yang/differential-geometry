import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickScaleHI_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.AllBranchesAssembly_CX9
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false

/-!
# CH12-S37 / G1: Q1-scale, a lower bound for the curvature radius of thick points

`thick_scale_lower_bound_S37`: from the zero-order part of W1 and the Hamilton–Ivey pinching, a
point of a late regular slice whose normalised ball of radius equal to its curvature radius `ρ`
has volume `≥ w ρ³` satisfies `ρ ≥ a_w` (`a_w` independent of the slice, the point and the time).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

section Geometry

variable (Q : OrientedThreeStage.{u}) (ĝ : Q.Metric)

/-- The closed ball is in the closure of the open ball (compact slice, minimising geodesics). -/
theorem closedBall_subset_closure_ball_S37 (p : Q.Carrier) {r : ℝ} (hr : 0 < r) :
    riemannianClosedBallOf ĝ p r ⊆ closure (riemannianBallOf ĝ p r) := by
  intro x hx
  by_cases hxr : x ∈ riemannianBallOf ĝ p r
  · exact subset_closure hxr
  have he : riemannianEDistOf ĝ p x = ENNReal.ofReal r := le_antisymm hx (le_of_not_gt hxr)
  have hR : riemannianEDistOf ĝ p x < ENNReal.ofReal (r + 1) := by
    rw [he]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
  obtain ⟨γ, hzero, hend, hγ, hd⟩ :=
    Geometry.Riemannian.exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall
      ĝ p x hR (Geometry.Metric.isClosed_riemannianClosedBallOf ĝ p (r + 1)).isCompact
  have hdist : (riemannianEDistOf ĝ p x).toReal = r := by rw [he, ENNReal.toReal_ofReal hr.le]
  rw [hdist] at hend hγ hd
  have hc : ContinuousWithinAt γ (Ico 0 r) r :=
    (hγ.continuousOn r ⟨hr.le, le_rfl⟩).mono Ico_subset_Icc_self
  rw [← hend]
  apply hc.mem_closure (by rw [closure_Ico hr.ne]; exact ⟨hr.le, le_rfl⟩)
  intro s hs
  change riemannianEDistOf ĝ p (γ s) < ENNReal.ofReal r
  rw [← hzero, hd 0 ⟨le_rfl, hr.le⟩ s ⟨hs.1, hs.2.le⟩]
  simpa only [zero_sub, abs_neg, abs_of_nonneg hs.1] using
    (ENNReal.ofReal_lt_ofReal_iff hr).mpr hs.2

/-- Tube lemma: an open set containing the closed `ρ`-ball contains a larger open ball. -/
theorem exists_gt_ball_subset_of_closedBall_subset_S37 (p : Q.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set Q.Carrier} (hU : IsOpen U) (hsub : riemannianClosedBallOf ĝ p ρ ⊆ U) :
    ∃ r' : ℝ, ρ < r' ∧ riemannianBallOf ĝ p r' ⊆ U := by
  have hcont : Continuous (fun y => riemannianEDistOf ĝ p y) := continuous_riemannianEDist ĝ p
  by_cases hne : (Uᶜ).Nonempty
  · obtain ⟨x, hxC, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hne hcont.continuousOn
    have hx : ENNReal.ofReal ρ < riemannianEDistOf ĝ p x := by
      by_contra hle
      exact hxC (hsub (not_lt.mp hle))
    obtain ⟨r', hr'0, hr'1, hr'2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
    refine ⟨r', (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ.le).mp hr'1, ?_⟩
    intro y hy
    by_contra hyU
    have := hmin hyU
    change riemannianEDistOf ĝ p x ≤ riemannianEDistOf ĝ p y at this
    exact absurd (this.trans_lt hy) (not_lt.mpr hr'2.le)
  · refine ⟨ρ + 1, by linarith, ?_⟩
    intro y _
    by_contra hyU
    exact hne ⟨y, hyU⟩

/-- A finite curvature radius `ρ` gives the sectional bound `-ρ⁻²` on the open `ρ`-ball. -/
theorem sec_lower_on_ball_of_curvatureRadius_S37 (p : Q.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (hcr : curvatureRadius ĝ p = ENNReal.ofReal ρ) :
    ∀ q ∈ riemannianBallOf ĝ p ρ, SectionalBoundedBelowAt ĝ q (-(ρ ^ 2)⁻¹) := by
  intro q hq v w
  by_contra hlt
  rw [not_le] at hlt
  set a := ĝ.inner q v v * ĝ.inner q w w - ĝ.inner q v w ^ 2 with ha
  set Rm := metricRm04StandardAt ĝ q v w w v with hRm
  have hdfin : riemannianEDistOf ĝ p q ≠ ⊤ := ne_top_of_lt hq
  set d := (riemannianEDistOf ĝ p q).toReal with hd
  have hdρ : d < ρ := by
    have := (ENNReal.toReal_lt_toReal hdfin ENNReal.ofReal_ne_top).mpr hq
    rwa [ENNReal.toReal_ofReal hρ.le] at this
  have hcontf : ContinuousAt (fun r : ℝ => -(r ^ 2)⁻¹ * a) ρ := by
    have : ContinuousAt (fun r : ℝ => (r ^ 2)⁻¹) ρ :=
      ((continuousAt_id.pow 2).inv₀ (pow_pos hρ 2).ne')
    exact this.neg.mul continuousAt_const
  have hev : ∀ᶠ r in 𝓝 ρ, Rm < -(r ^ 2)⁻¹ * a := continuousAt_const.eventually_lt hcontf hlt
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp hev
  set r0 := max (ρ - ε / 2) d with hr0
  have hr0ρ : r0 < ρ := max_lt (by linarith) hdρ
  have hlt0 : ENNReal.ofReal r0 < curvatureRadius ĝ p := by
    rw [hcr]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mpr hr0ρ
  unfold curvatureRadius at hlt0
  obtain ⟨r', h1⟩ := lt_iSup_iff.mp hlt0
  obtain ⟨hr'pos, h2⟩ := lt_iSup_iff.mp h1
  obtain ⟨hP, h3⟩ := lt_iSup_iff.mp h2
  have hr0r' : r0 < r' := (ENNReal.ofReal_lt_ofReal_iff hr'pos).mp h3
  have hr'ρ : r' ≤ ρ := by
    have hle : ENNReal.ofReal r' ≤ curvatureRadius ĝ p := by
      unfold curvatureRadius
      exact le_iSup_of_le r' (le_iSup_of_le hr'pos (le_iSup_of_le hP le_rfl))
    rw [hcr] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hρ.le).mp hle
  have hqr' : q ∈ riemannianBallOf ĝ p r' := by
    change riemannianEDistOf ĝ p q < ENNReal.ofReal r'
    rw [← ENNReal.ofReal_toReal hdfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hr'pos).mpr
      (lt_of_le_of_lt (le_max_right _ _) hr0r')
  have hdist : dist r' ρ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_left (ρ - ε / 2) d]
  have := hεball hdist
  have hsec := hP q hqr' v w
  linarith

/-- If the curvature radius of `p` is finite, the component of `p` has a negative plane. -/
theorem exists_negative_plane_of_curvatureRadius_S37 (p : Q.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (hcr : curvatureRadius ĝ p = ENNReal.ofReal ρ) :
    ∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt ĝ z 0 := by
  by_contra hno
  push Not at hno
  have hr1 : 0 < ρ + 1 := by linarith
  have hP : ∀ q ∈ riemannianBallOf ĝ p (ρ + 1),
      SectionalBoundedBelowAt ĝ q (-((ρ + 1) ^ 2)⁻¹) := by
    intro q hq
    have hmem : q ∈ connectedComponent p :=
      (isPathConnected_riemannianBallOf ĝ p hr1).isConnected.isPreconnected.subset_connectedComponent
        (by
          change riemannianEDistOf ĝ p p < ENNReal.ofReal _
          rw [riemannianEDistOf_self]
          exact ENNReal.ofReal_pos.mpr hr1) hq
    exact (hno q hmem).mono (by
      have : 0 ≤ ((ρ + 1) ^ 2)⁻¹ := by positivity
      linarith)
  have hle : ENNReal.ofReal (ρ + 1) ≤ curvatureRadius ĝ p := by
    unfold curvatureRadius
    exact le_iSup_of_le _ (le_iSup_of_le hr1 (le_iSup_of_le hP le_rfl))
  rw [hcr] at hle
  have := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp hle
  linarith

end Geometry

end GC.LongTime.Ch12
