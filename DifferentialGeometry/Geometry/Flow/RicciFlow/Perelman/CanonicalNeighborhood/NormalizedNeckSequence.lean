import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLimitNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckSequence
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

theorem exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence
    {kappa : ℝ} (hkappa : 0 < kappa) {A : ℝ} (hA : 0 ≤ A)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000) :
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
                        (∀ᶠ (tau : Ico 0 F.radius) in
                          comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius),
                          Nonempty (SpatialNeck L.metric (2 * alpha) (g tau))) ∧
                        ∃ t : ℕ → Ico 0 F.radius,
                          ∃ nk : ∀ n, SpatialNeck L.metric (2 * alpha) (g (t n)),
                            StrictMono (fun n => (t n : ℝ)) ∧
                            Tendsto (fun n => (t n : ℝ)) atTop (𝓝 F.radius) ∧
                            (∀ n, (t (n + 1) : ℝ) - t n =
                              ((2 * alpha)⁻¹ / 40) /
                                Real.sqrt (metricScalarAt L.metric (g (t n)))) ∧
                            (∀ n, ∃ (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
                              (height : Sphere 2 → ℝ), ContMDiff I2 𝓘(ℝ, ℝ) ∞ height ∧
                              (∀ p, height p ∈ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ∧
                              ∀ p, (nk n).map (p, height p) = (nk (n + 1)).map (eta p, 0)) ∧
                            Pairwise (fun i j =>
                              Disjoint ((nk i).map '' (univ ×ˢ ({0} : Set ℝ)))
                                ((nk j).map '' (univ ×ˢ ({0} : Set ℝ)))) ∧
                            (∀ n, ∃ eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                              ∃ Ψ : PartialDiffeomorph IC I3 Cylinder L.M ∞,
                                (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
                                (∀ p, Ψ (p, 0) = (nk n).map (p, 0)) ∧
                                (∀ p, Ψ (p, 1) = (nk (n + 1)).map (eta p, 0)) ∧
                                IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                (frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                                  (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) ∪
                                    (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                                Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                                  (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) := by
  obtain ⟨epsStar, c, hepsStar, hc, hproduce⟩ :=
    exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks.{u}
      hkappa (A := max A (2 * alpha)⁻¹) (hA.trans (le_max_left _ _)) ha (by linarith)
  refine ⟨epsStar, c, hepsStar, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, hquant, hnecks⟩ :=
      hproduce eps heps hle sigma hsigma Phi hPhi X hnot
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  have htail := (hblow.eventually (eventually_gt_atTop 2)).and hnecks
  obtain ⟨delta, hdelta, hprop⟩ := Metric.eventually_nhds_iff.mp
    (Filter.eventually_comap.mp htail)
  let a := max 0 (F.radius - delta / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have har : a < F.radius := max_lt F.radius_pos (by linarith)
  have hgood (tau : Ico 0 F.radius) (htau : a ≤ (tau : ℝ)) :
      2 < metricScalarAt L.metric (g tau) ∧
        Nonempty (SpatialNeck L.metric (2 * alpha) (g tau)) := by
    have hd : dist (tau : ℝ) F.radius < delta := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr tau.property.2), neg_sub]
      have hh : F.radius - delta / 2 ≤ (tau : ℝ) := (le_max_right _ _).trans htau
      linarith
    exact hprop hd tau rfl
  let incl : C(Ico a F.radius, Ico 0 F.radius) :=
    ⟨fun tau => ⟨tau, ha0.trans tau.property.1, tau.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let curve := g.comp incl
  have hcurve (v w : Ico a F.radius) :
      riemannianEDistOf L.metric (curve v) (curve w) = edist v w := by
    change edist (g (incl v)) (g (incl w)) = edist v w
    rw [hg.edist_eq]
    rfl
  have hquant' (tau : Ico a F.radius) :
      ((2 * alpha)⁻¹) ^ 2 ≤ metricScalarAt L.metric (curve tau) * (F.radius - tau) ^ 2 := by
    have hp : 0 ≤ (2 * alpha)⁻¹ := (inv_pos.mpr (by positivity)).le
    have hh := (pow_le_pow_left₀ hp (le_max_right A (2 * alpha)⁻¹) 2).trans
      (hquant (incl tau) (hgood (incl tau) tau.property.1).1)
    rw [hdist] at hh
    exact hh
  obtain ⟨t, nk, _ht0, hmono, hlim, hstep, _hcover, hgraph, hdisjoint, hannuli⟩ :=
    exists_spatialNeck_sequence_along_isometric_curve L.metric har (by linarith) curve hcurve
      (fun tau => (hgood (incl tau) tau.property.1).2) hquant'
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, ?_, hnecks, incl ∘ t, nk, hmono, hlim, hstep, hgraph, hdisjoint, hannuli⟩
  intro tau hR
  exact (pow_le_pow_left₀ hA (le_max_left A (2 * alpha)⁻¹) 2).trans (hquant tau hR)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
