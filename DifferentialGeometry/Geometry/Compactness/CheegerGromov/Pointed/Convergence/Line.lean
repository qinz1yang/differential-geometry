import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistance
import DifferentialGeometry.Geometry.Comparison.Splitting.MetricApproximateLineLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCovering.Ordered

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance pointedOppositeLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedOppositeLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedOppositeLimitSmooth : IsManifold I ∞ L.M := L.smooth

local instance pointedOppositeTermTopology (k : ℕ) :
    TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
local instance pointedOppositeTermCharted (k : ℕ) :
    ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
local instance pointedOppositeTermSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
private theorem eventually_approximate_ray_mem_ball
    (alpha : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    (hcenter : ∀ k, alpha k 0 = (X.obj (subseq k)).basepoint)
    {t rho : ℝ} (ht : 0 ≤ t) (htrho : t < rho)
    (hcenterDist : Tendsto (fun k => riemannianEDistOf (I := I)
      (X.obj (subseq k)).metric (alpha k 0) (alpha k t))
      atTop (𝓝 (ENNReal.ofReal |0 - t|))) :
    ∀ᶠ k in atTop, alpha k t ∈ riemannianClosedBallOf (I := I)
      (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint rho := by
  have hconv : Tendsto (fun k => riemannianEDistOf (I := I)
      (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint (alpha k t))
      atTop (𝓝 (ENNReal.ofReal t)) := by
    simpa only [hcenter, zero_sub, abs_neg, abs_of_nonneg ht] using hcenterDist
  have hrho : 0 < rho := lt_of_le_of_lt ht htrho
  have hlt : ENNReal.ofReal t < ENNReal.ofReal rho :=
    (ENNReal.ofReal_lt_ofReal_iff hrho).2 htrho
  exact (hconv.eventually (gt_mem_nhds hlt)).mono fun _ hk => hk.le

theorem exists_pointed_line_of_approximate_opposite_rays
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M)
    (alpha beta : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    (halphaCenter : ∀ k, alpha k 0 = (X.obj (subseq k)).basepoint)
    (hbetaCenter : ∀ k, beta k 0 = (X.obj (subseq k)).basepoint)
    (halpha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun k => riemannianEDistOf (I := I) (X.obj (subseq k)).metric
        (alpha k s) (alpha k t)) atTop (𝓝 (ENNReal.ofReal |s - t|)))
    (hbeta : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun k => riemannianEDistOf (I := I) (X.obj (subseq k)).metric
        (beta k s) (beta k t)) atTop (𝓝 (ENNReal.ofReal |s - t|)))
    (hopposite : ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun k => riemannianEDistOf (I := I) (X.obj (subseq k)).metric
        (alpha k r) (beta k r)) atTop (𝓝 (ENNReal.ofReal (2 * r)))) :
    let P := properMetricOn (I := I) L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  let P := properMetricOn (I := I) L hcomplete hconnected
  let m : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
  let _ : MetricSpace L.M := m
  have hm : m = P.ms := MetricSpace.replaceTopology_eq _ _
  have hproper : @ProperSpace L.M m.toPseudoMetricSpace := by
    rw [hm]
    exact P.proper
  let _ : ProperSpace L.M := hproper
  have hrealizes (x y : L.M) : riemannianEDistOf (I := I) L.metric x y =
      ENNReal.ofReal (dist x y) := by
    have h := P.realizes x y
    change riemannianEDistOf (I := I) L.metric x y = ENNReal.ofReal (dist x y) at h
    exact h
  have hdistReal (x y : L.M) :
      dist x y = (riemannianEDistOf (I := I) L.metric x y).toReal := by
    rw [hrealizes, ENNReal.toReal_ofReal dist_nonneg]
  let a : ℕ → ℝ → L.M := fun k t => (Φ.partialDiffeomorph k).symm (alpha k t)
  let b : ℕ → ℝ → L.M := fun k t => (Φ.partialDiffeomorph k).symm (beta k t)
  have haCenter (k : ℕ) : a k 0 = L.basepoint := by
    change (Φ.partialDiffeomorph k).symm (alpha k 0) = L.basepoint
    rw [halphaCenter k, ← Φ.basepoint_map k]
    exact (Φ.partialDiffeomorph k).left_inv' (Φ.base_mem k)
  have hbCenter (k : ℕ) : b k 0 = L.basepoint := by
    change (Φ.partialDiffeomorph k).symm (beta k 0) = L.basepoint
    rw [hbetaCenter k, ← Φ.basepoint_map k]
    exact (Φ.partialDiffeomorph k).left_inv' (Φ.base_mem k)
  have htransport (rho : ℝ) (hrho : 0 ≤ rho)
      (y z : ∀ k : ℕ, (X.obj (subseq k)).M)
      (hball : ∀ᶠ k in atTop,
        y k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
          (X.obj (subseq k)).basepoint rho ∧
        z k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
          (X.obj (subseq k)).basepoint rho)
      (d : ℝ) (hd : 0 ≤ d)
      (hdist : Tendsto (fun k => riemannianEDistOf (I := I)
        (X.obj (subseq k)).metric (y k) (z k)) atTop (𝓝 (ENNReal.ofReal d))) :
      Tendsto (fun k => dist ((Φ.partialDiffeomorph k).symm (y k))
        ((Φ.partialDiffeomorph k).symm (z k))) atTop (𝓝 d) := by
    have hreal : Tendsto (fun k => (riemannianEDistOf (I := I)
        (X.obj (subseq k)).metric (y k) (z k)).toReal) atTop (𝓝 d) := by
      simpa only [Function.comp_def, ENNReal.toReal_ofReal hd] using
        (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hdist
    have h := (tendsto_pointed_inverse_distance
      C hreference hcomplete rho hrho y z hball d hreal).1
    simpa only [← hdistReal] using h
  have halphaBall (t rho : ℝ) (ht : 0 ≤ t) (htrho : t < rho) :
      ∀ᶠ k in atTop, alpha k t ∈ riemannianClosedBallOf (I := I)
        (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint rho :=
    eventually_approximate_ray_mem_ball alpha halphaCenter ht htrho
      (halpha 0 t le_rfl ht)
  have hbetaBall (t rho : ℝ) (ht : 0 ≤ t) (htrho : t < rho) :
      ∀ᶠ k in atTop, beta k t ∈ riemannianClosedBallOf (I := I)
        (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint rho :=
    eventually_approximate_ray_mem_ball beta hbetaCenter ht htrho
      (hbeta 0 t le_rfl ht)
  have ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun k => dist (a k s) (a k t)) atTop (𝓝 |s - t|) := by
    intro s t hs ht
    apply htransport (s + t + 1) (by linarith)
      (fun k => alpha k s) (fun k => alpha k t) _ |s - t| (abs_nonneg _) (halpha s t hs ht)
    exact (halphaBall s (s + t + 1) hs (by linarith)).and
      (halphaBall t (s + t + 1) ht (by linarith))
  have hb : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun k => dist (b k s) (b k t)) atTop (𝓝 |s - t|) := by
    intro s t hs ht
    apply htransport (s + t + 1) (by linarith)
      (fun k => beta k s) (fun k => beta k t) _ |s - t| (abs_nonneg _) (hbeta s t hs ht)
    exact (hbetaBall s (s + t + 1) hs (by linarith)).and
      (hbetaBall t (s + t + 1) ht (by linarith))
  have hab : ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun k => dist (a k r) (b k r)) atTop (𝓝 (2 * r)) := by
    intro r hr
    apply htransport (2 * r + 1) (by linarith)
      (fun k => alpha k r) (fun k => beta k r) _ (2 * r) (by positivity) (hopposite r hr)
    exact (halphaBall r (2 * r + 1) hr (by linarith)).and
      (hbetaBall r (2 * r + 1) hr (by linarith))
  obtain ⟨gamma, hgamma, hzero⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_isometry_of_approximate_opposite_rays
      a b (K := {L.basepoint}) (isCompact_singleton)
      (fun k => (haCenter k).trans (hbCenter k).symm)
      (fun k => by simpa only [Set.mem_singleton_iff] using haCenter k) ha hb hab
  refine ⟨gamma, hgamma, Set.mem_singleton_iff.mp hzero, ?_⟩
  intro s t
  rw [hrealizes, hgamma.dist_eq, Real.dist_eq]

theorem exists_pointed_line_of_asymptotically_isometric_curves
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (γ : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    (hcenter : ∀ k, γ k 0 = (X.obj (subseq k)).basepoint)
    (hdist : ∀ s t : ℝ, Tendsto (fun k =>
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t))
      atTop (𝓝 (ENNReal.ofReal |s - t|))) :
    let P := properMetricOn L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  apply exists_pointed_line_of_approximate_opposite_rays C hreference hcomplete hconnected
    γ (fun k t => γ k (-t)) hcenter (fun k => by simpa using hcenter k)
  · intro s t _ _
    exact hdist s t
  · intro s t _ _
    have heq : -s - -t = -(s - t) := by ring
    simpa only [heq, abs_neg] using hdist (-s) (-t)
  · intro t ht
    simpa only [sub_neg_eq_add, ← two_mul,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht)] using hdist t (-t)

theorem exists_pointed_line_of_asymptotically_isometric_curves_with_bounded_centers
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (γ : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    {B : ℝ} (hB : 0 ≤ B)
    (hcenter : ∀ k, riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (γ k 0) ≤ ENNReal.ofReal B)
    (hdist : ∀ s t : ℝ, Tendsto (fun k =>
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t))
      atTop (𝓝 (ENNReal.ofReal |s - t|))) :
    let P := properMetricOn L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧
      ∀ s t : ℝ, riemannianEDistOf L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  classical
  let P := properMetricOn L hcomplete hconnected
  let m : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
  let _ : MetricSpace L.M := m
  have hm : m = P.ms := MetricSpace.replaceTopology_eq _ _
  have hproper : @ProperSpace L.M m.toPseudoMetricSpace := by
    rw [hm]
    exact P.proper
  let _ : ProperSpace L.M := hproper
  have hrealizes (x y : L.M) : riemannianEDistOf L.metric x y =
      ENNReal.ofReal (dist x y) := by
    have h := P.realizes x y
    change riemannianEDistOf L.metric x y = ENNReal.ofReal (dist x y) at h
    exact h
  have hdistReal (x y : L.M) :
      dist x y = (riemannianEDistOf L.metric x y).toReal := by
    rw [hrealizes, ENNReal.toReal_ofReal dist_nonneg]
  obtain ⟨hcompact, N, hN⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete B hB 1 zero_lt_one
  let a : ℕ → ℝ → L.M := fun k t =>
    if N ≤ k then (Φ.partialDiffeomorph k).symm (γ k t) else L.basepoint
  have haCenter (k : ℕ) : a k 0 ∈ riemannianClosedBallOf L.metric L.basepoint (2 * B) := by
    dsimp only [a]
    split_ifs with hk
    · simpa only [one_add_one_eq_two] using ((hN k hk).1 (γ k 0) (hcenter k)).2
    · change riemannianEDistOf L.metric _ _ ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le
  have hball (t rho : ℝ) (hrho : B + |t| < rho) :
      ∀ᶠ k in atTop, γ k t ∈ riemannianClosedBallOf
        (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint rho := by
    have hgap : 0 < rho - B := by linarith [abs_nonneg t]
    have hlim : Tendsto (fun k => riemannianEDistOf
        (X.obj (subseq k)).metric (γ k 0) (γ k t))
        atTop (𝓝 (ENNReal.ofReal |t|)) := by
      simpa only [zero_sub, abs_neg] using hdist 0 t
    have hsmall := hlim.eventually (gt_mem_nhds
      ((ENNReal.ofReal_lt_ofReal_iff hgap).mpr (by linarith : |t| < rho - B)))
    filter_upwards [hsmall] with k hk
    change riemannianEDistOf (X.obj (subseq k)).metric _ _ ≤ ENNReal.ofReal rho
    calc
      _ ≤ riemannianEDistOf (X.obj (subseq k)).metric
          (X.obj (subseq k)).basepoint (γ k 0) +
          riemannianEDistOf (X.obj (subseq k)).metric (γ k 0) (γ k t) :=
        riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal (rho - B) := add_le_add (hcenter k) hk.le
      _ = ENNReal.ofReal rho := by rw [← ENNReal.ofReal_add hB hgap.le]; congr 1; ring
  have ha (s t : ℝ) : Tendsto (fun k => dist (a k s) (a k t))
      atTop (𝓝 |s - t|) := by
    let rho := B + |s| + |t| + 1
    have hrho : 0 ≤ rho := by dsimp only [rho]; positivity
    have hballs := (hball s rho (by dsimp only [rho]; linarith [abs_nonneg t])).and
      (hball t rho (by dsimp only [rho]; linarith [abs_nonneg s]))
    have hreal : Tendsto (fun k => (riemannianEDistOf
        (X.obj (subseq k)).metric (γ k s) (γ k t)).toReal) atTop (𝓝 |s - t|) := by
      simpa only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using
        (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp (hdist s t)
    have hinv := (tendsto_pointed_inverse_distance C hreference hcomplete rho hrho
      (fun k => γ k s) (fun k => γ k t) hballs |s - t| hreal).1
    have hinvReal : Tendsto (fun k => dist ((Φ.partialDiffeomorph k).symm (γ k s))
        ((Φ.partialDiffeomorph k).symm (γ k t))) atTop (𝓝 |s - t|) := by
      simpa only [← hdistReal] using hinv
    apply hinvReal.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    simp only [a, ite_eq_left hk]
  obtain ⟨gamma, hgamma, _⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_isometry_of_approximate_distance_limits
      a (by simpa only [one_add_one_eq_two] using hcompact) haCenter ha
  refine ⟨gamma, hgamma, ?_⟩
  intro s t
  rw [hrealizes, hgamma.dist_eq, Real.dist_eq]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
private theorem tendsto_distance_of_growing_almost_isometric_segments
    (γ : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hsegment : ∀ k, ∀ s ∈ Set.Icc (-r k) (r k), ∀ t ∈ Set.Icc (-r k) (r k),
      ENNReal.ofReal ((1 - η k) * |s - t|) ≤
        riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ∧
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ≤
        ENNReal.ofReal ((1 + η k) * |s - t|)) :
    ∀ s t : ℝ, Tendsto (fun k =>
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t))
      atTop (𝓝 (ENNReal.ofReal |s - t|)) := by
  intro s t
  have hbounds : ∀ᶠ k in atTop,
      ENNReal.ofReal ((1 - η k) * |s - t|) ≤
        riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ∧
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ≤
        ENNReal.ofReal ((1 + η k) * |s - t|) := by
    filter_upwards [hr.eventually (eventually_ge_atTop (max |s| |t|))] with k hk
    exact hsegment k s (abs_le.mp ((le_max_left _ _).trans hk))
      t (abs_le.mp ((le_max_right _ _).trans hk))
  have hlow : Tendsto (fun k => ENNReal.ofReal ((1 - η k) * |s - t|))
      atTop (𝓝 (ENNReal.ofReal |s - t|)) := by
    simpa only [sub_zero, one_mul] using
      ENNReal.tendsto_ofReal (((tendsto_const_nhds (x := (1 : ℝ))).sub hη).mul_const |s - t|)
  have hupp : Tendsto (fun k => ENNReal.ofReal ((1 + η k) * |s - t|))
      atTop (𝓝 (ENNReal.ofReal |s - t|)) := by
    simpa only [add_zero, one_mul] using
      ENNReal.tendsto_ofReal (((tendsto_const_nhds (x := (1 : ℝ))).add hη).mul_const |s - t|)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem exists_pointed_line_of_growing_almost_isometric_segments_with_bounded_centers
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (γ : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    {B : ℝ} (hB : 0 ≤ B)
    (hcenter : ∀ k, riemannianEDistOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (γ k 0) ≤ ENNReal.ofReal B)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hsegment : ∀ k, ∀ s ∈ Set.Icc (-r k) (r k), ∀ t ∈ Set.Icc (-r k) (r k),
      ENNReal.ofReal ((1 - η k) * |s - t|) ≤
        riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ∧
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ≤
        ENNReal.ofReal ((1 + η k) * |s - t|)) :
    let P := properMetricOn L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧
      ∀ s t : ℝ, riemannianEDistOf L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  exact exists_pointed_line_of_asymptotically_isometric_curves_with_bounded_centers
    C hreference hcomplete hconnected γ hB hcenter
    (tendsto_distance_of_growing_almost_isometric_segments γ r hr η hη hsegment)

theorem exists_pointed_line_of_growing_almost_isometric_segments
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (γ : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    (hcenter : ∀ k, γ k 0 = (X.obj (subseq k)).basepoint)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hsegment : ∀ k, ∀ s ∈ Set.Icc (-r k) (r k), ∀ t ∈ Set.Icc (-r k) (r k),
      ENNReal.ofReal ((1 - η k) * |s - t|) ≤
        riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ∧
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) ≤
        ENNReal.ofReal ((1 + η k) * |s - t|)) :
    let P := properMetricOn L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  exact exists_pointed_line_of_asymptotically_isometric_curves C hreference hcomplete
    hconnected γ hcenter
    (tendsto_distance_of_growing_almost_isometric_segments γ r hr η hη hsegment)

theorem exists_pointed_line_of_growing_minimizing_segments
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) (hconnected : ConnectedSpace L.M)
    (γ : ∀ k : ℕ, ℝ → (X.obj (subseq k)).M)
    (hcenter : ∀ k, γ k 0 = (X.obj (subseq k)).basepoint)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hsegment : ∀ k, ∀ s ∈ Set.Icc (-r k) (r k), ∀ t ∈ Set.Icc (-r k) (r k),
      riemannianEDistOf (X.obj (subseq k)).metric (γ k s) (γ k t) = ENNReal.ofReal |s - t|) :
    let P := properMetricOn L hcomplete hconnected
    let _ : MetricSpace L.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
    ∃ gamma : ℝ → L.M, Isometry gamma ∧ gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  apply exists_pointed_line_of_growing_almost_isometric_segments C hreference hcomplete
    hconnected γ hcenter r hr (fun _ => 0) tendsto_const_nhds
  intro k s hs t ht
  simp only [sub_zero, add_zero, one_mul, hsegment k s hs t ht, le_refl, and_self]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
