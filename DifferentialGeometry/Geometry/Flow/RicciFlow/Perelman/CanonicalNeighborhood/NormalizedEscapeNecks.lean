import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedEscapeLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedSegmentNecks
set_option autoImplicit false
noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_terminal_pointed_limit_with_missing_endpoint_and_necks
    {kappa : ℝ} (hkappa : 0 < kappa) {A : ℝ} (hA : 0 ≤ A)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
              ∃ F : FiniteControlledRadius (X.reindex f hf), ∃ r : ℕ → ℝ,
                (∀ k, 0 < r k ∧ r k < F.radius) ∧ Tendsto r atTop (nhds F.radius) ∧
                ∃ L : PointedRiemannianManifold.{u, 0, 0} (I := I3),
                ∃ hL : PathConnectedSpace L.M,
                let _ : PathConnectedSpace L.M := hL
                ∃ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
                  ∃ C : PointedRiemannianConverges (X.toFlowSequence.atTime 0) L f maps,
                  (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
                  (∀ k, maps.target k = riemannianBallOf ((X.term (f k)).S.base.metric 0)
                    (X.term (f k)).basepoint (r k)) ∧
                  (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
                    ∀ x ∈ maps.source k, ∀ v : TangentSpace I3 x,
                      (1 - eta) * L.metric.inner x v v ≤
                        ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ∧
                      ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ≤
                        (1 + eta) * L.metric.inner x v v) ∧
                  (∀ R : ℝ, 0 ≤ R → R < F.radius →
                    IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
                  metricScalarAt L.metric L.basepoint = 1 ∧
                  (∀ (x : L.M) (v w : TangentSpace I3 x),
                    0 ≤ metricRm04StandardAt L.metric x v w w v) ∧
                    let _ : EMetricSpace L.M := L.emetricSpace
                    let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
                      (fun x y => riemannianEDistOf_ne_top L.metric x y)
                    ∃ phi : ℕ → ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (phi n))).M)
                      (s : ℕ → ℝ) (g : C(Ico 0 F.radius, L.M)),
                      StrictMono phi ∧ Isometry g ∧ g ⟨0, le_rfl, F.radius_pos⟩ = L.basepoint ∧
                      (∀ n,
                        let ell := metricDistance ((X.term (f (phi n))).S.base.metric 0)
                          (X.term (f (phi n))).basepoint (F.points (phi n))
                        s n ∈ Ico 0 ell ∧ γ n 0 = (X.term (f (phi n))).basepoint ∧
                          γ n ell = F.points (phi n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
                          (∀ t, IsGeodesicAt ((X.term (f (phi n))).S.base.metric 0) (γ n) t) ∧
                          (∀ t, ((X.term (f (phi n))).S.base.metric 0).inner (γ n t)
                            (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1)
                            (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1) ∧
                          (∀ t ∈ Icc 0 ell, ∀ v ∈ Icc 0 ell,
                            metricDistance ((X.term (f (phi n))).S.base.metric 0)
                              (γ n t) (γ n v) = |t - v|) ∧
                          (X.term (f (phi n))).S.scalar 0 (γ n (s n)) = 2 ∧
                          (∀ t ∈ Ioc (s n) ell, 2 < (X.term (f (phi n))).S.scalar 0 (γ n t)) ∧
                          c < ell - s n) ∧
                      (∀ A : Set (Ico 0 F.radius), IsCompact A → TendstoUniformlyOn
                        (fun n (t : Ico 0 F.radius) => (maps.partialDiffeomorph (phi n)).symm (γ n t))
                        g atTop A) ∧
                      (∀ x : L.M, ¬ Tendsto g
                        (comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius)) (𝓝 x)) ∧
                      Tendsto (fun t => metricScalarAt L.metric (g t))
                        (comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius)) atTop ∧
                      ∃ q : UniformSpace.Completion L.M,
                        Tendsto (fun t => (g t : UniformSpace.Completion L.M))
                          (comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius)) (𝓝 q) ∧
                        (∀ t : Ico 0 F.radius, dist q (g t : UniformSpace.Completion L.M) =
                          F.radius - t) ∧
                        (q ∉ range (fun x : L.M => (x : UniformSpace.Completion L.M))) ∧
                        (∀ t : Ico 0 F.radius, 2 < metricScalarAt L.metric (g t) →
                          A ^ 2 ≤ metricScalarAt L.metric (g t) *
                            dist q (g t : UniformSpace.Completion L.M) ^ 2) ∧
                        ∀ᶠ (tau : Ico 0 F.radius) in
                          comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius),
                          ∀ᶠ n in atTop,
                            Nonempty (StrongNeck (X.term (f (phi n))).S
                              (2 * alpha) (γ n tau) 0) := by
  obtain ⟨B, epsNeck, hB, hepsNeck, hneck⟩ :=
    exists_eventually_strongNeck_near_scalar_blowup_endpoint.{u} kappa ha hsmall
  obtain ⟨epsEscape, c, hepsEscape, hc, hescape⟩ :=
    exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance.{u}
      hkappa (A := max A B) (hA.trans (le_max_left _ _))
  refine ⟨min epsEscape epsNeck, c, lt_min hepsEscape hepsNeck, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, hquant⟩ := hescape eps heps (hle.trans (min_le_left _ _))
      sigma hsigma Phi hPhi X hnot
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  let ell : ℕ → ℝ := fun n => metricDistance ((X.term (f (phi n))).S.base.metric 0)
    (X.term (f (phi n))).basepoint (F.points (phi n))
  have hell : Tendsto ell atTop (𝓝 F.radius) := F.distance_limit.comp hphi.tendsto_atTop
  let Θ := maps.compSubseq phi hphi
  have hcanonical' (n : ℕ) : (C.metrics.compSubseq phi hphi).domain n =
      CanonicalMetricCompactness.canonicalSourceData Θ n := by
    change (C.metrics.domain (phi n)).compSubseq phi hphi n = _
    rw [hcanonical (phi n)]
    rfl
  have hstay (tau : Ico 0 F.radius) : ∀ᶠ n in atTop, γ n tau ∈ Θ.target n := by
    filter_upwards [hphi.tendsto_atTop (hrT.eventually (eventually_gt_nhds tau.property.2)),
      hell.eventually (eventually_gt_nhds tau.property.2)] with n hn hn'
    change γ n tau ∈ maps.target (phi n)
    rw [htargets]
    change riemannianEDistOf ((X.term (f (phi n))).S.base.metric 0)
      (X.term (f (phi n))).basepoint (γ n tau) < ENNReal.ofReal (r (phi n))
    let _ : ConnectedSpace (X.term (f (phi n))).M := X.connected (f (phi n))
    have hdist' := (hγ n).2.2.2.2.2.2.1 0
      ⟨le_rfl, tau.property.1.trans hn'.le⟩ tau ⟨tau.property.1, hn'.le⟩
    rw [(hγ n).2.1] at hdist'
    simp only [zero_sub, abs_neg, abs_of_nonneg tau.property.1] at hdist'
    have heq := (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top
      ((X.term (f (phi n))).S.base.metric 0) (X.term (f (phi n))).basepoint (γ n tau))).symm
    change _ = ENNReal.ofReal (metricDistance _ _ _) at heq
    rw [hdist'] at heq
    rw [heq]
    exact ENNReal.ofReal_lt_ofReal_iff (hr (phi n)).1 |>.mpr hn
  have hscalar (tau : Ico 0 F.radius) :
      Tendsto (fun n => (X.term (f (phi n))).S.scalar 0 (γ n tau)) atTop
        (𝓝 (metricScalarAt L.metric (g tau))) :=
    pointedScalar_tendsto_of_inverse_tendsto (C.metrics.compSubseq phi hphi) hcanonical'
      (fun n => γ n tau) (hstay tau)
      ((hconv {tau} isCompact_singleton).tendsto_at (mem_singleton tau))
  have hBquant (tau : Ico 0 F.radius) (hR : 2 < metricScalarAt L.metric (g tau)) :
      B ^ 2 ≤ metricScalarAt L.metric (g tau) * (F.radius - tau) ^ 2 := by
    have hh := (pow_le_pow_left₀ hB.le (le_max_right A B) 2).trans (hquant tau hR)
    simpa only [hdist tau] using hh
  have hnecks := hneck eps sigma Phi X (hle.trans (min_le_right _ _))
    (f ∘ phi) γ ell F.radius F.radius_pos hell (fun tau => metricScalarAt L.metric (g tau))
    (fun n => (hγ n).2.2.2.2.2.2.1) hscalar hblow hBquant
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, ?_, hnecks⟩
  intro tau hR
  exact (pow_le_pow_left₀ hA (le_max_left A B) 2).trans (hquant tau hR)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
