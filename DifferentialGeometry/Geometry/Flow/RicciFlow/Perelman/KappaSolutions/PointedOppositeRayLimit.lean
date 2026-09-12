import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedDistanceLimit
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

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
