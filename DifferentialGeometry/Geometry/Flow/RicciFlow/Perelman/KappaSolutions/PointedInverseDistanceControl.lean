import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAmbientMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricInverse

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem quadratic_comparison_of_relative_error
    {a b epsilon : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 < epsilon)
    (herror : |b - a| ≤ epsilon / (1 + epsilon) * a) :
    b ≤ (1 + epsilon) ^ 2 * a ∧ a ≤ (1 + epsilon) ^ 2 * b := by
  have hL : 0 < 1 + epsilon := by linarith
  have hcoef : epsilon / (1 + epsilon) ≤ epsilon :=
    div_le_self hepsilon.le (by linarith)
  have hsq : 1 + epsilon ≤ (1 + epsilon) ^ 2 := by nlinarith
  have hupper : b ≤ (1 + epsilon) * a := by
    have hmul := mul_le_mul_of_nonneg_right hcoef ha
    have habs := (abs_le.mp herror).2
    nlinarith
  have hdivision : a / (1 + epsilon) = a - epsilon / (1 + epsilon) * a := by
    field_simp [ne_of_gt hL]
    ring
  have hlower : a ≤ (1 + epsilon) * b := by
    have hdiv : a / (1 + epsilon) ≤ b := by
      rw [hdivision]
      have habs := (abs_le.mp herror).1
      linarith
    simpa only [mul_comm] using (div_le_iff₀ hL).1 hdiv
  exact ⟨hupper.trans (mul_le_mul_of_nonneg_right hsq ha),
    hlower.trans (mul_le_mul_of_nonneg_right hsq hb)⟩

section BufferedComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem inverse_distance_control_on_buffered_metric_ball
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p : N)
    {L rho : ℝ} (hL : 1 ≤ L) (hrho : 0 ≤ rho)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p (L * (3 * rho + 2))))
    (hsource : riemannianClosedBallOf (I := I) h p (L * (3 * rho + 2)) ⊆ F.source)
    (hupper : ∀ x ∈ riemannianClosedBallOf (I := I) h p (L * (3 * rho + 2)),
      ∀ v : TangentSpace I x,
        g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v) ≤ L ^ 2 * h.inner x v v)
    (hlower : ∀ x ∈ riemannianClosedBallOf (I := I) h p (L * (3 * rho + 2)),
      ∀ v : TangentSpace I x, h.inner x v v ≤
        L ^ 2 * g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v)) :
    (∀ y ∈ riemannianClosedBallOf (I := I) g (F p) rho,
      y ∈ F.target ∧ F.symm y ∈ riemannianClosedBallOf (I := I) h p (L * rho)) ∧
    (∀ y ∈ riemannianClosedBallOf (I := I) g (F p) rho,
      ∀ z ∈ riemannianClosedBallOf (I := I) g (F p) rho,
        riemannianEDistOf (I := I) h (F.symm y) (F.symm z) ≤
          ENNReal.ofReal L * riemannianEDistOf (I := I) g y z ∧
        riemannianEDistOf (I := I) g y z ≤
          ENNReal.ofReal L * riemannianEDistOf (I := I) h (F.symm y) (F.symm z)) := by
  have hLpos : 0 < L := by linarith
  have hR : 0 < L * (3 * rho + 2) := mul_pos hLpos (by linarith)
  have hbpos : 0 < 3 * rho + 1 := by linarith
  have hbuffer : 3 * rho < 3 * rho + 1 := by linarith
  have hcapture : 3 * rho + 1 < L * (3 * rho + 2) / L := by
    apply (lt_div_iff₀ hLpos).2
    nlinarith
  have hrCapture : rho < L * (3 * rho + 2) / L :=
    lt_trans (by linarith) hcapture
  have hconfined : ∀ y ∈ riemannianClosedBallOf (I := I) g (F p) rho,
      y ∈ F.target ∧ F.symm y ∈ riemannianClosedBallOf (I := I) h p (L * rho) := by
    intro y hy
    have htarget := (inverse_mem_closedBall_of_metric_lower
      h g F p hR hLpos hrCapture hcpt hsource hlower y hy).1
    have hyshort : riemannianEDistOf (I := I) g (F p) y <
        ENNReal.ofReal (3 * rho + 1) := by
      exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hbpos).2 (by linarith))
    have hcenter := edistOf_symm_le_of_metric_lower_on_compact_ball
      h g F p hR hLpos hbpos hcapture hcpt hsource hlower y hyshort
    refine ⟨htarget, ?_⟩
    calc
      riemannianEDistOf (I := I) h p (F.symm y) ≤
          ENNReal.ofReal L * riemannianEDistOf (I := I) g (F p) y := hcenter
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal rho := mul_le_mul_right hy _
      _ = ENNReal.ofReal (L * rho) := (ENNReal.ofReal_mul hLpos.le).symm
  refine ⟨hconfined, ?_⟩
  intro y hy z hz
  refine ⟨edistOf_symm_pair_le_of_metric_lower_on_compact_ball
    h g F p hR hLpos hrho hbuffer hcapture hcpt hsource hlower y z hy hz, ?_⟩
  have hforward := edistOf_map_le_of_metric_upper_on_buffered_ball
    h g F p (F.symm y) (F.symm z) (mul_nonneg hLpos.le hrho)
    (by nlinarith : 3 * (L * rho) < L * (3 * rho + 2)) hLpos hsource hupper
    (hconfined y hy).2 (hconfined z hz).2
  have hrightY : F (F.symm y) = y := F.right_inv' (hconfined y hy).1
  have hrightZ : F (F.symm z) = z := F.right_inv' (hconfined z hz).1
  simpa only [hrightY, hrightZ] using hforward

end BufferedComparison

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance pointedInverseDistanceTopology : TopologicalSpace L.M := L.topology
local instance pointedInverseDistanceCharted : ChartedSpace H L.M := L.charted
local instance pointedInverseDistanceSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedInverseDistanceT2 : T2Space L.M := L.t2
local instance pointedInverseDistanceSigmaCompact : SigmaCompactSpace L.M := L.sigmaCompact
local instance pointedInverseDistanceTangentT2 : T2Space (TangentBundle I L.M) :=
  L.t2TangentBundle

theorem exists_pointed_inverse_distance_control
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L)
    (rho : ℝ) (hrho : 0 ≤ rho) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    IsCompact (riemannianClosedBallOf (I := I) L.metric L.basepoint
      ((1 + epsilon) * rho)) ∧
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      (let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
       let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
       (∀ y ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
           (X.obj (subseq k)).basepoint rho,
         y ∈ (Φ.partialDiffeomorph k).target ∧
           (Φ.partialDiffeomorph k).symm y ∈
             riemannianClosedBallOf (I := I) L.metric L.basepoint ((1 + epsilon) * rho)) ∧
       (∀ y ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
           (X.obj (subseq k)).basepoint rho,
         ∀ z ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
           (X.obj (subseq k)).basepoint rho,
           riemannianEDistOf (I := I) L.metric
               ((Φ.partialDiffeomorph k).symm y) ((Φ.partialDiffeomorph k).symm z) ≤
             ENNReal.ofReal (1 + epsilon) *
               riemannianEDistOf (I := I) (X.obj (subseq k)).metric y z ∧
           riemannianEDistOf (I := I) (X.obj (subseq k)).metric y z ≤
             ENNReal.ofReal (1 + epsilon) * riemannianEDistOf (I := I) L.metric
               ((Φ.partialDiffeomorph k).symm y) ((Φ.partialDiffeomorph k).symm z))) := by
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := by
    refine ⟨?_⟩
    exact MetricComplete.complete (I := I) L hcomplete
  have hcompact (r : ℝ) :
      IsCompact (riemannianClosedBallOf (I := I) L.metric L.basepoint r) :=
    RiemannianMetricComplete.closedEBall_isCompact hmetricComplete L.basepoint r
  refine ⟨hcompact ((1 + epsilon) * rho), ?_⟩
  let K := riemannianClosedBallOf (I := I) L.metric L.basepoint
    ((1 + epsilon) * (3 * rho + 2))
  have hdelta : 0 < epsilon / (1 + epsilon) := div_pos hepsilon (by linarith)
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C hreference K (hcompact _) (epsilon / (1 + epsilon)) hdelta
  refine ⟨k0, ?_⟩
  intro k hk
  let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let _ : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let F := Φ.partialDiffeomorph k
  have hquadratic : ∀ x ∈ K, ∀ v : TangentSpace I x,
      (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) ≤
        (1 + epsilon) ^ 2 * L.metric.inner x v v ∧
      L.metric.inner x v v ≤ (1 + epsilon) ^ 2 *
        (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) := by
    intro x hx v
    have ha : 0 ≤ L.metric.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (L.metric.pos x v hv).le
    have hb : 0 ≤ (X.obj (subseq k)).metric.inner (F x)
        (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
        (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) := by
      by_cases hv : mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v = 0
      · simp [hv]
      · exact ((X.obj (subseq k)).metric.pos (F x) _ hv).le
    exact quadratic_comparison_of_relative_error ha hb hepsilon ((hk0 k hk).2 x hx v)
  have hcomparison := inverse_distance_control_on_buffered_metric_ball
    L.metric (X.obj (subseq k)).metric F L.basepoint
    (by linarith : 1 ≤ 1 + epsilon) hrho (hcompact _) (hk0 k hk).1
    (fun x hx v => (hquadratic x hx v).1)
    (fun x hx v => (hquadratic x hx v).2)
  have hbase : F L.basepoint = (X.obj (subseq k)).basepoint := Φ.basepoint_map k
  simpa only [hbase] using hcomparison

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
