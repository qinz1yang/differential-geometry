import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickScaleLowerBound_S37

set_option autoImplicit false

/-!
# CH12-S37 / G1: Q1-scale (main theorem)
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

/-- **Q1-scale.**  For every `w > 0` there is `a_w > 0` and a time `T` such that on every regular
slice after `T`, a point whose curvature radius `ρ` (for the normalised metric) is finite and
whose `ρ`-ball has volume `≥ w ρ³` has `ρ ≥ a_w`.  Inputs: the zero-order part of W1 (inline
hypothesis) and the Hamilton–Ivey pinching of the profile. -/
theorem thick_scale_lower_bound_S37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (K : ℕ)
    (hW1 : ∃ (b T C : ℝ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧ (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹) :
    ∀ w : ℝ, 0 < w → ∃ a : ℝ, 0 < a ∧ ∃ T : ℝ,
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → a ≤ ρ := by
  obtain ⟨b, T0, C, hb, hC, hmain⟩ := hW1
  intro w hw
  -- the threshold `L` and the scale `a`
  set L : ℝ := 3 + 9 * (C w + 1) with hL
  have hCw := hC w
  have hL3 : 3 ≤ L := by rw [hL]; nlinarith
  have hexpL : 0 < Real.exp (-L) := Real.exp_pos _
  refine ⟨min (b w) (Real.exp (-L)), lt_min (hb w hw) hexpL, T0 w, ?_⟩
  intro s hs p ρ hρ hcr hvol
  by_contra hlt
  rw [not_le] at hlt
  have hρb : ρ ≤ b w := (hlt.trans_le (min_le_left _ _)).le
  have hρe : ρ < Real.exp (-L) := hlt.trans_le (min_le_right _ _)
  have hρ1 : ρ < 1 := by
    refine hρe.trans_le ?_
    rw [Real.exp_le_one_iff]; linarith
  -- zero-order curvature bound on the open ball
  have hnorm := hmain w hw s hs p ρ hρ hρb
    (exists_negative_plane_of_curvatureRadius_S37 s.stage s.normalizedMetric p hρ hcr)
    (sec_lower_on_ball_of_curvatureRadius_S37 s.stage s.normalizedMetric p hρ hcr) hvol 0
    (Nat.zero_le K)
  set M0 : ℝ := C w * (ρ ^ (0 + 2))⁻¹ with hM0
  have hcont := continuous_curvatureDerivativeNorm s.normalizedMetric 0
  -- the closed ball lies in the open set `{|Rm| < M0 + 1}`
  have hUopen : IsOpen {y | curvatureDerivativeNorm s.normalizedMetric 0 y < M0 + 1} :=
    isOpen_lt hcont continuous_const
  have hclosed : closure (riemannianBallOf s.normalizedMetric p ρ) ⊆
      {y | curvatureDerivativeNorm s.normalizedMetric 0 y ≤ M0} :=
    closure_minimal (fun q hq => hnorm q hq) (isClosed_le hcont continuous_const)
  have hsubU : riemannianClosedBallOf s.normalizedMetric p ρ ⊆
      {y | curvatureDerivativeNorm s.normalizedMetric 0 y < M0 + 1} := fun y hy => by
    have h : curvatureDerivativeNorm s.normalizedMetric 0 y ≤ M0 :=
      hclosed (closedBall_subset_closure_ball_S37 s.stage s.normalizedMetric p hρ hy)
    change curvatureDerivativeNorm s.normalizedMetric 0 y < M0 + 1
    linarith
  obtain ⟨r', hρr', hr'sub⟩ := exists_gt_ball_subset_of_closedBall_subset_S37 s.stage
    s.normalizedMetric p hρ hUopen hsubU
  -- Hamilton–Ivey: sec ≥ -ρ⁻²/2 on the larger ball
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have hρinv : 0 < (ρ ^ 2)⁻¹ := inv_pos.mpr hρ2
  have hρinv1 : 1 ≤ (ρ ^ 2)⁻¹ := by
    rw [one_le_inv₀ hρ2]; nlinarith
  have hexpgap : Real.exp L < (ρ ^ 2)⁻¹ := by
    have h1 : ρ ^ 2 < Real.exp (-L) := by nlinarith [hρ1, hρe]
    rw [Real.exp_neg] at h1
    exact (lt_inv_comm₀ (Real.exp_pos L) hρ2).mpr h1
  have hΛ3 : Real.exp 3 ≤ 2 * ((ρ ^ 2)⁻¹ / 2) := by
    have : Real.exp 3 ≤ Real.exp L := Real.exp_le_exp.mpr hL3
    linarith
  have hlogL : L < Real.log (2 * ((ρ ^ 2)⁻¹ / 2)) := by
    have : 2 * ((ρ ^ 2)⁻¹ / 2) = (ρ ^ 2)⁻¹ := by ring
    rw [this, Real.lt_log_iff_exp_lt hρinv]
    exact hexpgap
  have hsecΛ : ∀ y ∈ riemannianBallOf s.normalizedMetric p r',
      SectionalBoundedBelowAt s.normalizedMetric y (-((ρ ^ 2)⁻¹ / 2)) := by
    intro y hy
    by_contra hnot
    have hRge := scalar_ge_of_not_sectionalBoundedBelow_S37 Hp s y hΛ3 hnot
    have hcdn : curvatureDerivativeNorm s.normalizedMetric 0 y < M0 + 1 := hr'sub hy
    have hcdn_eq : curvatureDerivativeNorm s.normalizedMetric 0 y =
        Real.sqrt (normSq0S s.normalizedMetric y 4 (metricRm04At s.normalizedMetric y)) := rfl
    have hdim : Module.finrank ℝ (TangentSpace ThreeModel y) = 3 := by
      change Module.finrank ℝ ThreeSpace = 3
      simp [ThreeSpace]
    have hRle : metricScalarAt s.normalizedMetric y ≤
        9 * curvatureDerivativeNorm s.normalizedMetric 0 y := by
      have h := scalar_abs_le_rm s.normalizedMetric y
      rw [hdim, ← hcdn_eq] at h
      norm_num at h
      linarith [le_abs_self (metricScalarAt s.normalizedMetric y)]
    have hM0' : M0 = C w * (ρ ^ 2)⁻¹ := by rw [hM0]
    have hupper : metricScalarAt s.normalizedMetric y < 9 * (C w + 1) * (ρ ^ 2)⁻¹ := by
      have : 9 * curvatureDerivativeNorm s.normalizedMetric 0 y < 9 * (M0 + 1) := by linarith
      rw [hM0'] at this
      nlinarith
    have hlower : 9 * (C w + 1) * (ρ ^ 2)⁻¹ <
        2 * ((ρ ^ 2)⁻¹ / 2) * (Real.log (2 * ((ρ ^ 2)⁻¹ / 2)) - 3) := by
      have : 2 * ((ρ ^ 2)⁻¹ / 2) = (ρ ^ 2)⁻¹ := by ring
      rw [this] at hlogL ⊢
      have hgap : 9 * (C w + 1) < Real.log (ρ ^ 2)⁻¹ - 3 := by rw [hL] at hlogL; linarith
      nlinarith [mul_lt_mul_of_pos_left hgap hρinv]
    linarith
  -- the curvature radius is then larger than `ρ`
  set r'' : ℝ := min r' (7 / 5 * ρ) with hr''
  have hr''pos : 0 < r'' := lt_min (hρ.trans hρr') (by linarith)
  have hr''ρ : ρ < r'' := lt_min hρr' (by linarith)
  have hPr'' : ∀ q ∈ riemannianBallOf s.normalizedMetric p r'',
      SectionalBoundedBelowAt s.normalizedMetric q (-(r'' ^ 2)⁻¹) := by
    intro q hq
    have hq' : q ∈ riemannianBallOf s.normalizedMetric p r' :=
      riemannianBallOf_mono s.normalizedMetric p (min_le_left _ _) hq
    refine (hsecΛ q hq').mono ?_
    have hr2 : r'' ^ 2 ≤ 2 * ρ ^ 2 := by
      have : r'' ≤ 7 / 5 * ρ := min_le_right _ _
      nlinarith [hr''pos]
    have : (ρ ^ 2)⁻¹ / 2 ≤ (r'' ^ 2)⁻¹ := by
      have hr2pos : 0 < r'' ^ 2 := pow_pos hr''pos 2
      have e : (ρ ^ 2)⁻¹ / 2 = (2 * ρ ^ 2)⁻¹ := by field_simp
      rw [e]
      exact inv_anti₀ hr2pos hr2
    linarith
  have hle : ENNReal.ofReal r'' ≤ curvatureRadius s.normalizedMetric p := by
    unfold curvatureRadius
    exact le_iSup_of_le r'' (le_iSup_of_le hr''pos (le_iSup_of_le hPr'' le_rfl))
  rw [hcr] at hle
  have := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp hle
  linarith

end GC.LongTime.Ch12
