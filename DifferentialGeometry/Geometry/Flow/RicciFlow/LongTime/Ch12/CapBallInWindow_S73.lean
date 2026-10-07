import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapScalarJet0_S64
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapBallNorm_S64
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Completeness

/-!
# CH12-S73, group 1: K-cap ball-in-window sub-lemma (`[FROZEN] CH12-S64`, `ball_subset_image_window_S73`)

For an injective local diffeomorphism `φ : standardCapWindow D → N` with `std ≤ 4 · φ^* h` on
`{‖w‖ < D}`, the `h`-ball of radius `a` about `φ z0` lies in the image of `{‖w‖ < ‖z0‖ + 2a}`
(sharp: the factor `2 = √4` is the only loss; no `Λ (L+1)` slack).  The universe gap (window in `Type`,
`N : Type u`) is handled by working with the `PartialDiffeomorph` of `image_riemannianBallOf_localPullMetric`
and `PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower`, both universe polymorphic.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Window version of the sharp radial placement (`norm_le_add_of_quad_edist_S64`): `std ≤ 4 g` on an open
window `W ⊆ ℝ³` and `d_g(z,y) ≤ a` give `‖y‖ ≤ ‖z‖ + 2a`. -/
theorem norm_le_add_of_quad_edist_window_S73 (W : TopologicalSpace.Opens ThreeSpace)
    (g : SmoothRiemannianMetric ThreeModel W)
    (hu : ∀ (x : W) (v : TangentSpace ThreeModel x),
      StandardCap.metric.inner x.val v v ≤ 4 * g.inner x v v)
    {z y : W} {a : ℝ} (ha : 0 ≤ a)
    (hzy : riemannianEDistOf (I := ThreeModel) g z y ≤ ENNReal.ofReal a) :
    ‖y.val‖ ≤ ‖z.val‖ + 2 * a := by
  have hrestr := edistOf_le_of_quad (I := ThreeModel) g
    (StandardCap.metric.restrictOpen (I := ThreeModel) W) (c := 4) (by norm_num) hu z y
  have hamb := riemannianEDistOf_le_restrictOpen (I := ThreeModel) StandardCap.metric W z y
  have hrad := StandardCap.radial_difference_le_edist z.val y.val
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hmul : riemannianEDistOf (I := ThreeModel) StandardCap.metric z.val y.val ≤
      ENNReal.ofReal (2 * a) := by
    refine hamb.trans (hrestr.trans ?_)
    rw [hs4, ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul' le_rfl hzy
  have h := hrad.trans hmul
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have := (le_abs_self (‖y.val‖ - ‖z.val‖)).trans h
  linarith only [this]

theorem ball_subset_image_window_S73 {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] (h : SmoothRiemannianMetric ThreeModel N) {D : ℝ}
    (φ : standardCapWindow D → N) (hφ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ φ)
    (hinj : Function.Injective φ)
    (hcmp : ∀ w : standardCapWindow D, ‖w.val‖ < D → ∀ v : TangentSpace ThreeModel w,
      StandardCap.metric.inner w.val v v ≤
        4 * h.inner (φ w) (mfderiv ThreeModel ThreeModel φ w v) (mfderiv ThreeModel ThreeModel φ w v))
    (z0 : standardCapWindow D) {a : ℝ} (ha : 0 < a) (hroom : ‖z0.val‖ + 2 * a < D) :
    riemannianBallOf h (φ z0) a ⊆ φ '' {w | ‖w.val‖ < ‖z0.val‖ + 2 * a} := by
  intro y hy
  -- the sub-window `W = {‖x‖ < D}`
  let W : TopologicalSpace.Opens ThreeSpace := standardCapWindow (D - 1)
  have hWD : W ≤ standardCapWindow D := by
    intro x hx
    change ‖x‖ < D + 1
    change ‖x‖ < D - 1 + 1 at hx
    linarith only [hx]
  have hz0D : ‖z0.val‖ < D := by linarith only [hroom, ha, norm_nonneg z0.val]
  let inc : W → standardCapWindow D := TopologicalSpace.Opens.inclusion hWD
  have hinc_c : ContMDiff ThreeModel ThreeModel ∞ inc := contMDiff_inclusion _
  have hinc_loc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc :=
    isLocalDiffeomorph_of_injective_mfderiv inc hinc_c
      (fun x => by rw [mfderiv_opens_incl]; exact fun v w h => h) rfl
  let φ' : W → N := φ ∘ inc
  have hφ' : IsLocalDiffeomorph ThreeModel ThreeModel ∞ φ' := isLocalDiffeomorph_comp hφ hinc_loc
  have hinj' : Function.Injective φ' := by
    intro x x' hxx
    have := hinj hxx
    exact Subtype.ext (congrArg (fun z : standardCapWindow D => z.val) this)
  have hmf : ∀ (x : W) (v : TangentSpace ThreeModel x),
      mfderiv ThreeModel ThreeModel φ' x v = mfderiv ThreeModel ThreeModel φ (inc x) v := by
    intro x v
    have h1 : MDifferentiableAt ThreeModel ThreeModel φ (inc x) :=
      hφ.mdifferentiable (by decide) (inc x)
    have h2 : MDifferentiableAt ThreeModel ThreeModel inc x :=
      hinc_c.contMDiffAt.mdifferentiableAt (by decide)
    change mfderiv ThreeModel ThreeModel (φ ∘ inc) x v = _
    rw [mfderiv_comp x h1 h2, ContinuousLinearMap.comp_apply, mfderiv_opens_incl]
    rfl
  let g' : SmoothRiemannianMetric ThreeModel W := localPullMetric h φ' hφ'
  have hcmp' : ∀ (x : W) (v : TangentSpace ThreeModel x),
      StandardCap.metric.inner x.val v v ≤ 4 * g'.inner x v v := by
    intro x v
    have hxD : ‖(inc x).val‖ < D := by
      have hx := x.2
      change ‖x.val‖ < D - 1 + 1 at hx
      change ‖x.val‖ < D
      linarith only [hx]
    rw [localPullMetric_inner, hmf]
    exact hcmp (inc x) hxD v
  let z0' : W := ⟨z0.val, by
    change ‖z0.val‖ < D - 1 + 1
    linarith only [hz0D]⟩
  have hinc_z0 : inc z0' = z0 := Subtype.ext rfl
  -- compactness of the closed `g'`-ball of radius `a` about `z0'`
  have hplace : ∀ x ∈ riemannianClosedBallOf (I := ThreeModel) g' z0' a,
      x ∈ {x : W | ‖x.val‖ ≤ ‖z0.val‖ + 2 * a} := by
    intro x hx
    have hx' : riemannianEDistOf (I := ThreeModel) g' z0' x ≤ ENNReal.ofReal a := hx
    have := norm_le_add_of_quad_edist_window_S73 W g' hcmp' (z := z0') (y := x) (a := a) ha.le hx'
    exact this
  have hKc : IsCompact {x : W | ‖x.val‖ ≤ ‖z0.val‖ + 2 * a} := by
    rw [Subtype.isCompact_iff]
    have himg : ((↑) : W → ThreeSpace) '' {x : W | ‖x.val‖ ≤ ‖z0.val‖ + 2 * a} =
        Metric.closedBall 0 (‖z0.val‖ + 2 * a) := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx
      · intro hw
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        have hmem : w ∈ W := by
          change ‖w‖ < D - 1 + 1
          linarith only [hw, hroom]
        exact ⟨⟨w, hmem⟩, hw, rfl⟩
    rw [himg]
    exact isCompact_closedBall _ _
  have hcpt : IsCompact (riemannianClosedBallOf (I := ThreeModel) g' z0' a) :=
    hKc.of_isClosed_subset (isClosed_riemannianClosedBallOf _ _ _) hplace
  -- the partial diffeomorphism `Φ : W → N` with `⇑Φ = φ'`
  let V := hφ'.image
  let e : W ≃ₘ⟮ThreeModel, ThreeModel⟯ V := diffeomorphOntoImage φ' hφ' hinj'
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V ⟨e z0'⟩
  let Φ : PartialDiffeomorph ThreeModel ThreeModel W N ∞ := e.toPartialDiffeomorph.trans iV
  have hsource : Φ.source = univ := by
    ext x
    change (x ∈ (univ : Set W) ∧ e x ∈ (univ : Set V)) ↔ x ∈ (univ : Set W)
    simp only [mem_univ, and_self]
  -- the distance `d` from `φ z0` to `y`
  have hfin : riemannianEDistOf h (φ z0) y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy.le
  have hd : 0 ≤ (riemannianEDistOf h (φ z0) y).toReal := ENNReal.toReal_nonneg
  have hda : (riemannianEDistOf h (φ z0) y).toReal < a := ENNReal.toReal_lt_of_lt_ofReal hy
  have hmem : y ∈ riemannianClosedBallOf (I := ThreeModel) h (Φ z0')
      (riemannianEDistOf h (φ z0) y).toReal := by
    change riemannianEDistOf h (φ z0) y ≤ ENNReal.ofReal (riemannianEDistOf h (φ z0) y).toReal
    rw [ENNReal.ofReal_toReal hfin]
  obtain ⟨hyt, hxb⟩ := DifferentialGeometry.PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
    g' h Φ z0' (R := a) (L := 1) (r := (riemannianEDistOf h (φ z0) y).toReal) hd one_pos
    (by rw [one_mul]; exact hda) hcpt (by rw [hsource]; exact subset_univ _)
    (fun x _ v => by
      rw [one_pow, one_mul]
      exact (localPullMetric_inner h φ' hφ' x v v).le) y hmem
  have hnorm := norm_le_add_of_quad_edist_window_S73 W g' hcmp' (by rw [one_mul]; exact hd) hxb
  refine ⟨inc (Φ.symm y), ?_, ?_⟩
  · change ‖(Φ.symm y).val‖ < ‖z0.val‖ + 2 * a
    linarith only [hnorm, hda]
  · exact Φ.right_inv' hyt

end GC.LongTime.Ch12
