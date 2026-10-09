import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PersistGeom_S50
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false

/-!
# CH12-S50 / P4 support: curvature radius vs. the sectional-bound property, ball measure, curvature bound
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem riemannianBallOf_mono_S50 (g : SmoothRiemannianMetric I M) (p : M) {r r' : ℝ} (h : r ≤ r') :
    riemannianBallOf (I := I) g p r ⊆ riemannianBallOf (I := I) g p r' :=
  fun _ hy => lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal h)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem sb_mono_S50 (g : SmoothRiemannianMetric I M) (x : M) {K1 K2 : ℝ} (h : K1 ≤ K2)
    (hs : SectionalBoundedBelowAt g x K2) : SectionalBoundedBelowAt g x K1 := by
  intro v w
  have hg : 0 ≤ g.inner x v v * g.inner x w w - g.inner x v w ^ 2 := by
    by_cases hlin : LinearIndependent ℝ ![v, w]
    · exact (gram_determinant_pos g x v w hlin).le
    · exact (gram_eq_zero_of_not_li_S50 g x v w hlin).ge
  nlinarith [hs v w, mul_le_mul_of_nonneg_right h hg]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem cr_lower_S50 (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R)
    (h : ∀ q ∈ riemannianBallOf (I := I) g p R, SectionalBoundedBelowAt g q (-(R ^ 2)⁻¹)) :
    ENNReal.ofReal R ≤ curvatureRadius g p :=
  le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le h le_rfl))

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem cr_upper_S50 (g : SmoothRiemannianMetric I M) (p : M) {B : ℝ}
    (h : ∀ R : ℝ, 0 < R → (∀ q ∈ riemannianBallOf (I := I) g p R,
      SectionalBoundedBelowAt g q (-(R ^ 2)⁻¹)) → R ≤ B) :
    curvatureRadius g p ≤ ENNReal.ofReal B :=
  iSup_le fun R => iSup_le fun hR => iSup_le fun hp => ENNReal.ofReal_le_ofReal (h R hR hp)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem cr_prop_of_lt_S50 (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hcr : curvatureRadius g p = ENNReal.ofReal r) {r1 : ℝ} (hr1 : 0 < r1) (h : r1 < r) :
    ∀ q ∈ riemannianBallOf (I := I) g p r1, SectionalBoundedBelowAt g q (-(r1 ^ 2)⁻¹) := by
  have hlt : ENNReal.ofReal r1 < curvatureRadius g p :=
    hcr ▸ (ENNReal.ofReal_lt_ofReal_iff (hr1.trans h)).2 h
  unfold curvatureRadius at hlt
  obtain ⟨R', hlt⟩ := lt_iSup_iff.mp hlt
  obtain ⟨hR', hlt⟩ := lt_iSup_iff.mp hlt
  obtain ⟨hprop, hlt⟩ := lt_iSup_iff.mp hlt
  have h1 : r1 < R' := (ENNReal.ofReal_lt_ofReal_iff hR').1 hlt
  intro q hq
  refine sb_mono_S50 g q ?_ (hprop q (riemannianBallOf_mono_S50 g p h1.le hq))
  exact neg_le_neg (inv_anti₀ (pow_pos hr1 2) (pow_le_pow_left₀ hr1.le h1.le 2))

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem cr_not_prop_S50 (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r)
    (hcr : curvatureRadius g p = ENNReal.ofReal r) {r2 : ℝ} (h : r < r2) :
    ∃ q ∈ riemannianBallOf (I := I) g p r2, ¬ SectionalBoundedBelowAt g q (-(r2 ^ 2)⁻¹) := by
  by_contra hne
  push Not at hne
  have := cr_lower_S50 g p (hr.trans h) hne
  rw [hcr, ENNReal.ofReal_le_ofReal_iff hr.le] at this
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem exists_ball_measure_S50 [MeasurableSpace M] (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r)
    (μ : Measure M) {m : ℝ≥0∞} (hm : m < μ (riemannianBallOf (I := I) g p r)) :
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ m < μ (riemannianBallOf (I := I) g p (l * r)) := by
  let s : ℕ → Set M := fun n => riemannianBallOf (I := I) g p ((1 - 1 / ((n : ℝ) + 2)) * r)
  have hmono : Monotone s := fun n n' hnn' => by
    refine riemannianBallOf_mono_S50 g p ?_
    have : (1 : ℝ) / ((n' : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by simpa using hnn')
    nlinarith
  have hU : ⋃ n, s n = riemannianBallOf (I := I) g p r := by
    apply Subset.antisymm
    · refine iUnion_subset fun n => riemannianBallOf_mono_S50 g p ?_
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
    · intro y hy
      change riemannianEDistOf (I := I) g p y < ENNReal.ofReal r at hy
      have hne : riemannianEDistOf (I := I) g p y ≠ ⊤ := hy.ne_top
      have hd : (riemannianEDistOf (I := I) g p y).toReal < r :=
        (ENNReal.toReal_lt_of_lt_ofReal hy)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (r - (riemannianEDistOf (I := I) g p y).toReal) / r
        from div_pos (by linarith) hr)
      refine mem_iUnion.mpr ⟨n, ?_⟩
      change riemannianEDistOf (I := I) g p y < ENNReal.ofReal ((1 - 1 / ((n : ℝ) + 2)) * r)
      rw [← ENNReal.ofReal_toReal hne]
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
      have h2 : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      rw [lt_div_iff₀ hr] at hn
      nlinarith
  rw [← hU, hmono.measure_iUnion] at hm
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hm
  refine ⟨1 - 1 / ((n : ℝ) + 2), ?_, ?_, hn⟩
  · have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith

omit [SigmaCompactSpace M] in
theorem exists_riemann_bound_S50 [CompactSpace M] (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : M) (u v w : TangentSpace I x),
      Real.sqrt (g.inner x (riemannOp (LeviCivita g) x u v w) (riemannOp (LeviCivita g) x u v w)) ≤
        K * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  have hcont : Continuous (fun y : M =>
      normSq0S (I := I) g y 4 (metricRm04 (I := I) (M := M) g y)) :=
    Tensor0SBundle.normSq0S_cont (I := I) g (metricRm04 (I := I) (M := M) g)
  obtain ⟨x1, -, hx1⟩ := isCompact_univ.exists_isMaxOn ⟨x₀, mem_univ _⟩ hcont.continuousOn
  refine ⟨Real.sqrt (normSq0S (I := I) g x1 4 (metricRm04 (I := I) (M := M) g x1)),
    Real.sqrt_nonneg _, fun x u v w => ?_⟩
  refine (sqrt_inner_riemannOp_le g x u v w).trans ?_
  have hle : Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At g x)) ≤
      Real.sqrt (normSq0S (I := I) g x1 4 (metricRm04 (I := I) (M := M) g x1)) :=
    Real.sqrt_le_sqrt (hx1 (mem_univ x))
  gcongr

end GC.LongTime.Ch12
