import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarNonnegativeOfRicciNonnegative
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedReindexing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedEscapeGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLocalCompactness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Curves
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Connected
import DifferentialGeometry.Geometry.Metric.Segment
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

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

private theorem abs_scalar_tendsto_atTop_of_escaping_curves {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ f : ℕ → ℕ, StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
              Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) atTop atTop →
              ∀ (rho : ℝ) (ell : ℕ → ℝ), Tendsto ell atTop (𝓝 rho) →
                ∀ (γ : ∀ n, Ico 0 rho → (X.term (f n)).M),
                  (∀ t : Ico 0 rho, ∀ᶠ n in atTop,
                    riemannianEDistOf ((X.term (f n)).S.base.metric 0) (γ n t) (p n) ≤
                      ENNReal.ofReal (ell n - t)) →
                ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
                  (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                  (C : MetricConvergenceData maps),
                  (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
                  ∀ g : Ico 0 rho → L.M,
                    (∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ n t ∈ maps.target n) →
                    (∀ t : Ico 0 rho, Tendsto
                      (fun n => (maps.partialDiffeomorph n).symm (γ n t)) atTop (𝓝 (g t))) →
                    Tendsto (fun t => |metricScalarAt L.metric (g t)|)
                      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  obtain ⟨epsStar, c, hepsStar, hc, hsep⟩ := eventually_edist_gt_of_scalar_tendsto_atTop hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf p hp rho ell hell γ hdist L maps C hcanonical
    g hstay hconv
  apply tendsto_atTop.mpr
  intro B
  by_cases hB : B ≤ 0
  · exact Eventually.of_forall fun t => hB.trans (abs_nonneg _)
  have hBpos : 0 < B := lt_of_not_ge hB
  let d : ℝ := c / Real.sqrt (2 + B)
  have hd : 0 < d := div_pos hc (Real.sqrt_pos.mpr (by linarith))
  have hgap : Tendsto (fun t : Ico 0 rho => rho - (t : ℝ))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 0) := by
    simpa only [sub_self] using ((tendsto_const_nhds (x := rho)).sub
      (tendsto_comap : Tendsto (Subtype.val : Ico 0 rho → ℝ) _ (𝓝 rho)))
  filter_upwards [hgap.eventually (eventually_lt_nhds hd)] with t ht
  by_contra hR
  have hRlt : |metricScalarAt L.metric (g t)| < B := lt_of_not_ge hR
  have hscalar := pointedScalar_tendsto_of_inverse_tendsto C hcanonical
    (fun n => γ n t) (hstay t) (hconv t)
  have hA : ∀ᶠ n in atTop, |(X.term (f n)).S.scalar 0 (γ n t)| ≤ B + 1 := by
    have hh := hscalar.abs.eventually (eventually_lt_nhds (hRlt.trans (lt_add_one B)))
    exact hh.mono fun _ h => h.le
  have hs : ∀ᶠ n in atTop, (0 : ℝ) ∈ Icc (-((X.reindex f hf).depth n / 2)) 0 :=
    Eventually.of_forall fun n => ⟨by
      change -(X.depth (f n) / 2) ≤ 0
      linarith [X.depth_pos (f n)], le_rfl⟩
  have hseparation := hsep eps heps hle sigma hsigma Phi hPhi (X.reindex f hf)
    (fun _ => 0) (fun n => γ n t) p (B + 1) hs hA hp
  have hbound : ∀ᶠ n in atTop, ENNReal.ofReal d ≤ ENNReal.ofReal (ell n - t) := by
    filter_upwards [hseparation, hdist t] with n hn hn'
    have heq : 1 + (B + 1) = 2 + B := by ring
    rw [heq] at hn
    exact hn.le.trans hn'
  have hlimit : Tendsto (fun n => ENNReal.ofReal (ell n - t)) atTop
      (𝓝 (ENNReal.ofReal (rho - t))) := (ENNReal.continuous_ofReal.tendsto (rho - t)).comp (hell.sub_const (t : ℝ))
  have hle' := ge_of_tendsto hlimit hbound
  have hreal : d ≤ rho - t := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr t.property.2.le)).mp hle'
  exact (not_le.mpr ht) hreal

theorem not_tendsto_edist_zero_of_scalar_tendsto_atTop {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ f : ℕ → ℕ, StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
              Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) atTop atTop →
              ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
                (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                (C : MetricConvergenceData maps),
                (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
                ∀ x : L.M, ¬ Tendsto (fun n => riemannianEDistOf
                  ((X.term (f n)).S.base.metric 0) (p n) (maps.partialDiffeomorph n x))
                    atTop (𝓝 0) := by
  obtain ⟨epsStar, hepsStar, hbound⟩ := eventually_scalar_le_of_edist_tendsto_zero hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf p hp L maps C hcanonical x hd
  have hc := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  let A : ℝ := |metricScalarAt L.metric x| + 1
  have hA : ∀ᶠ n in atTop, |(X.term (f n)).S.scalar 0 (maps.partialDiffeomorph n x)| ≤ A := by
    have hh := hc.abs.eventually (eventually_lt_nhds (lt_add_one |metricScalarAt L.metric x|))
    filter_upwards [hh] with n hn
    exact hn.le
  have hd' : Tendsto (fun n => riemannianEDistOf ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n x) (p n)) atTop (𝓝 0) := by
    exact hd.congr' (Eventually.of_forall fun n => riemannianEDistOf_comm _ _ _)
  have hb := hbound eps heps hle sigma hsigma Phi hPhi (X.reindex f hf)
    (fun _ => 0) (fun n => maps.partialDiffeomorph n x) p A
    (Eventually.of_forall fun n => ⟨by
      change -(X.depth (f n) / 2) ≤ 0
      linarith [X.depth_pos (f n)], le_rfl⟩) hA hd'
  obtain ⟨n, hn, hn'⟩ := (hb.and (hp.eventually (eventually_gt_atTop (4 * (1 + A))))).exists
  exact (not_le.mpr hn') hn

private theorem exists_geodesic_tail_curves
    {eps kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (hf : StrictMono f) (p : ∀ n, (X.term (f n)).M)
    (hp : Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) atTop atTop)
    (hcurves : ∀ᶠ i in atTop, ∀ y : (X.term i).M, 12 < (X.term i).S.scalar 0 y →
      let L := metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
      ∃ (γ : ℝ → (X.term i).M) (s : ℝ), s ∈ Ico 0 L ∧
        γ 0 = (X.term i).basepoint ∧ γ L = y ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ γ ∧
        (∀ t, IsGeodesicAt ((X.term i).S.base.metric 0) γ t) ∧
        (∀ t, ((X.term i).S.base.metric 0).inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I3 γ t 1) (mfderiv 𝓘(ℝ, ℝ) I3 γ t 1) = 1) ∧
        (∀ t ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
          metricDistance ((X.term i).S.base.metric 0) (γ t) (γ v) = |t - v|) ∧
        (X.term i).S.scalar 0 (γ s) = 2 ∧
        (∀ t ∈ Ioc s L, 2 < (X.term i).S.scalar 0 (γ t)) ∧ c < L - s) :
    ∃ N : ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (N + n))).M) (s : ℕ → ℝ), ∀ n,
      let L := metricDistance ((X.term (f (N + n))).S.base.metric 0)
        (X.term (f (N + n))).basepoint (p (N + n))
      s n ∈ Ico 0 L ∧ γ n 0 = (X.term (f (N + n))).basepoint ∧
        γ n L = p (N + n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
        (∀ t, IsGeodesicAt ((X.term (f (N + n))).S.base.metric 0) (γ n) t) ∧
        (∀ t, ((X.term (f (N + n))).S.base.metric 0).inner (γ n t)
          (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1) ∧
        (∀ t ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
          metricDistance ((X.term (f (N + n))).S.base.metric 0) (γ n t) (γ n v) = |t - v|) ∧
        (X.term (f (N + n))).S.scalar 0 (γ n (s n)) = 2 ∧
        (∀ t ∈ Ioc (s n) L, 2 < (X.term (f (N + n))).S.scalar 0 (γ n t)) ∧
        c < L - s n := by
  have hevent := (hp.eventually (eventually_gt_atTop 12)).and (hf.tendsto_atTop hcurves)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hchoice (n : ℕ) := (hN (N + n) (Nat.le_add_right N n)).2 (p (N + n))
    (hN (N + n) (Nat.le_add_right N n)).1
  choose γ s hs using hchoice
  exact ⟨N, γ, s, hs⟩

private theorem scalar_remaining_length_lower_bound_of_escaping_curves {r : ℝ} (hr : 0 ≤ r) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, eps ≤ epsStar →
      ∀ (kappa sigma : ℝ) (Phi : ℝ → ℝ) (X : NormalizedSequence.{u} eps kappa sigma Phi)
        (f : ℕ → ℕ), StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
        Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) atTop atTop →
        ∀ (rho : ℝ) (ell : ℕ → ℝ), Tendsto ell atTop (𝓝 rho) →
          ∀ (γ : ∀ n, Ico 0 rho → (X.term (f n)).M),
            (∀ t : Ico 0 rho, ∀ᶠ n in atTop,
              riemannianEDistOf ((X.term (f n)).S.base.metric 0) (γ n t) (p n) ≤
                ENNReal.ofReal (ell n - t)) →
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
            (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
            (C : MetricConvergenceData maps),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
            ∀ g : Ico 0 rho → L.M,
              (∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ n t ∈ maps.target n) →
              (∀ t : Ico 0 rho, Tendsto
                (fun n => (maps.partialDiffeomorph n).symm (γ n t)) atTop (𝓝 (g t))) →
              ∀ t : Ico 0 rho, 2 < metricScalarAt L.metric (g t) →
                r ^ 2 ≤ metricScalarAt L.metric (g t) * (rho - t) ^ 2 := by
  obtain ⟨epsStar, hepsStar, hsep⟩ := exists_curvature_radius_lower_bound_of_scalar_tendsto_atTop.{u} hr
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps kappa sigma Phi X f hf p hp rho ell hell γ hdist L maps C hcanonical
    g hstay hconv t hR
  have hscalar := pointedScalar_tendsto_of_inverse_tendsto C hcanonical
    (fun n => γ n t) (hstay t) (hconv t)
  have hbound := hsep eps heps kappa sigma Phi (X.reindex f hf) (fun _ => 0)
    (fun n => γ n t) p (metricScalarAt L.metric (g t)) (rho - t) (fun n => ell n - t)
    (Eventually.of_forall fun n => ⟨by
      change -(X.depth (f n)) ≤ 0
      linarith [X.depth_pos (f n)], le_rfl⟩)
    hR hscalar hp (hell.sub_const (t : ℝ)) (hdist t)
  have hRpos : 0 < metricScalarAt L.metric (g t) := by linarith
  have hroot : 0 < Real.sqrt (metricScalarAt L.metric (g t)) := Real.sqrt_pos.mpr hRpos
  have hmul := (div_le_iff₀ hroot).mp hbound
  have hsq := pow_le_pow_left₀ hr hmul 2
  rw [mul_pow, Real.sq_sqrt hRpos.le] at hsq
  simpa only [mul_comm] using hsq


theorem exists_isometric_curve_with_missing_endpoint {kappa : ℝ} (hkappa : 0 < kappa)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ f : ℕ → ℕ, StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
              Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) atTop atTop →
              ∀ (rho : ℝ) (hrho : 0 < rho),
                Tendsto (fun n => metricDistance ((X.term (f n)).S.base.metric 0)
                  (X.term (f n)).basepoint (p n)) atTop (𝓝 rho) →
                ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
                  (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                  (C : MetricConvergenceData maps),
                  (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
                  ∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop (𝓝 rho) →
                    (∀ n, riemannianBallOf ((X.term (f n)).S.base.metric 0)
                      (X.term (f n)).basepoint (r n) ⊆ maps.target n) →
                    (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
                      ∀ x ∈ maps.source n, ∀ v : TangentSpace I3 x,
                        (1 - eta) * L.metric.inner x v v ≤
                          ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
                            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
                            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)) →
                    (∀ R : ℝ, 0 ≤ R → R < rho →
                      IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) →
                    let _ : EMetricSpace L.M := L.emetricSpace
                    ∃ phi : ℕ → ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (phi n))).M)
                      (s : ℕ → ℝ) (g : C(Ico 0 rho, L.M)),
                      StrictMono phi ∧ Isometry g ∧ g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
                      (∀ n,
                        let ell := metricDistance ((X.term (f (phi n))).S.base.metric 0)
                          (X.term (f (phi n))).basepoint (p (phi n))
                        s n ∈ Ico 0 ell ∧ γ n 0 = (X.term (f (phi n))).basepoint ∧
                          γ n ell = p (phi n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
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
                      (∀ A : Set (Ico 0 rho), IsCompact A → TendstoUniformlyOn
                        (fun n (t : Ico 0 rho) => (maps.partialDiffeomorph (phi n)).symm (γ n t))
                        g atTop A) ∧
                      (∀ x : L.M, ¬ Tendsto g
                        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
                      Tendsto (fun t => |metricScalarAt L.metric (g t)|)
                        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop ∧
                      ∀ t : Ico 0 rho, 2 < metricScalarAt L.metric (g t) →
                        A ^ 2 ≤ metricScalarAt L.metric (g t) * (rho - t) ^ 2 := by
  obtain ⟨epsGeo, c, hepsGeo, hc, hgeo⟩ := exists_high_curvature_geodesic_tail hkappa
  obtain ⟨epsScalar, hepsScalar, hescape⟩ := abs_scalar_tendsto_atTop_of_escaping_curves hkappa
  obtain ⟨epsDistance, hepsDistance, hlength⟩ :=
    scalar_remaining_length_lower_bound_of_escaping_curves hA
  refine ⟨min epsGeo (min epsScalar epsDistance), c,
    lt_min hepsGeo (lt_min hepsScalar hepsDistance), hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf p hp rho hrho hdist L maps C hcanonical
    r hr hrconv htarget hlower hcompact
  obtain ⟨hleGeo, hleRest⟩ := le_min_iff.mp hle
  obtain ⟨hleScalar, hleDistance⟩ := le_min_iff.mp hleRest
  let : EMetricSpace L.M := L.emetricSpace
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I3 x,
        ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) x v) ≤ D ^ 2 * L.metric.inner x v v := by
    intro K hK D hD
    obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control C
      (fun n => by rw [hcanonical n]; rfl) K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx v
    have hh := (abs_le.mp ((hN n hn).2 x hx v)).2
    change ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) x v) - L.metric.inner x v v ≤
        (D ^ 2 - 1) * L.metric.inner x v v at hh
    nlinarith
  obtain ⟨N, γ, s, hγdata⟩ := exists_geodesic_tail_curves X f hf p hp
    (hgeo eps heps hleGeo sigma hsigma Phi hPhi X)
  let shift : ℕ → ℕ := fun n => N + n
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_left h N
  let ell : ℕ → ℝ := fun n => metricDistance ((X.term (f (shift n))).S.base.metric 0)
    (X.term (f (shift n))).basepoint (p (shift n))
  let Ψ := maps.compSubseq shift hshift
  have hstart (n : ℕ) : γ n 0 = (X.term (f (shift n))).basepoint := (hγdata n).2.1
  have hsmooth (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 (γ n) (Icc 0 (ell n)) :=
    ((hγdata n).2.2.2.1.of_le (by simp)).contMDiffOn
  have hspeed (n : ℕ) (t : ℝ) : ((X.term (f (shift n))).S.base.metric 0).inner (γ n t)
      (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1 :=
    (hγdata n).2.2.2.2.2.1 t
  have hmin (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (ell n))
      (v : ℝ) (hv : v ∈ Icc 0 (ell n)) :
      edist t v ≤ riemannianEDistOf ((X.term (f (shift n))).S.base.metric 0) (γ n t) (γ n v) := by
    let : ConnectedSpace (X.term (f (shift n))).M := X.connected (f (shift n))
    rw [edist_dist, Real.dist_eq, ← (hγdata n).2.2.2.2.2.2.1 t ht v hv]
    exact (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)).le
  obtain ⟨eta, g, heta, hg, hbase, hconv⟩ := Ψ.exists_isometric_curve_subseq_limit hrho
    (r ∘ shift) ell (fun n => hr (shift n)) (fun _ => ENNReal.toReal_nonneg)
    (hrconv.comp hshift.tendsto_atTop) (hdist.comp hshift.tendsto_atTop)
    (fun n => htarget (shift n))
    (fun e he => hshift.tendsto_atTop (hlower e he))
    (fun K hK D hD => hshift.tendsto_atTop (hupper K hK D hD)) hcompact
    γ hsmooth hstart (fun n t _ => (hspeed n t).le) hmin
  let phi := shift ∘ eta
  have hphi : StrictMono phi := hshift.comp heta
  let Θ := maps.compSubseq phi hphi
  have hstay (t : ℝ) (ht : t ∈ Ico 0 rho) : ∀ᶠ n in atTop,
      γ (eta n) t ∈ (Θ.partialDiffeomorph n).target := by
    filter_upwards [hphi.tendsto_atTop (hrconv.eventually (eventually_gt_nhds ht.2)),
      heta.tendsto_atTop ((hdist.comp hshift.tendsto_atTop).eventually
        (eventually_gt_nhds ht.2))] with n hn hn'
    apply htarget (phi n)
    have hh := Geometry.riemannianEDistOf_le_of_curve_speed_bound
      ((X.term (f (shift (eta n)))).S.base.metric 0) (C := 1) ht.1
      ((hsmooth (eta n)).mono (Icc_subset_Icc le_rfl hn'.le)) (by
        intro v hv
        rw [hspeed, Real.sqrt_one])
    simp only [hstart, sub_zero, ENNReal.ofReal_one, one_mul] at hh
    exact hh.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr (phi n))).mpr hn)
  have hcanonical' (n : ℕ) : (C.compSubseq phi hphi).domain n =
      CanonicalMetricCompactness.canonicalSourceData Θ n := by
    change (C.domain (phi n)).compSubseq phi hphi n = _
    rw [hcanonical (phi n)]
    rfl
  have hdistEnd (t : Ico 0 rho) : ∀ᶠ n in atTop,
      riemannianEDistOf ((X.term ((f ∘ phi) n)).S.base.metric 0)
        (γ (eta n) t) (p (phi n)) ≤ ENNReal.ofReal ((ell ∘ eta) n - t) := by
    filter_upwards [((hdist.comp hshift.tendsto_atTop).comp heta.tendsto_atTop).eventually
      (eventually_gt_nhds t.property.2)] with n hn
    have hb := Geometry.riemannianEDistOf_le_of_curve_speed_bound
      ((X.term (f (shift (eta n)))).S.base.metric 0) (C := 1) hn.le
      ((hsmooth (eta n)).mono (Icc_subset_Icc t.property.1 le_rfl)) (by
        intro v hv
        rw [hspeed, Real.sqrt_one])
    simp only [ENNReal.ofReal_one, one_mul] at hb
    have hend : γ (eta n) (ell (eta n)) = p (phi n) := (hγdata (eta n)).2.2.1
    change riemannianEDistOf ((X.term (f (phi n))).S.base.metric 0)
      (γ (eta n) t) (γ (eta n) (ell (eta n))) ≤ ENNReal.ofReal (ell (eta n) - t) at hb
    rw [hend] at hb
    exact hb
  have hblow := hescape eps heps hleScalar sigma hsigma Phi hPhi X (f ∘ phi)
    (hf.comp hphi) (fun n => p (phi n)) (hp.comp hphi.tendsto_atTop) rho (ell ∘ eta)
    ((hdist.comp hshift.tendsto_atTop).comp heta.tendsto_atTop)
    (fun n t => γ (eta n) t) hdistEnd L Θ (C.compSubseq phi hphi) hcanonical' g
    (fun t => hstay t t.property) (fun t =>
      (hconv {t} isCompact_singleton).tendsto_at (mem_singleton t))
  have hquant := hlength eps hleDistance kappa sigma Phi X (f ∘ phi)
    (hf.comp hphi) (fun n => p (phi n)) (hp.comp hphi.tendsto_atTop) rho (ell ∘ eta)
    ((hdist.comp hshift.tendsto_atTop).comp heta.tendsto_atTop)
    (fun n t => γ (eta n) t) hdistEnd L Θ (C.compSubseq phi hphi) hcanonical' g
    (fun t => hstay t t.property) (fun t =>
      (hconv {t} isCompact_singleton).tendsto_at (mem_singleton t))
  refine ⟨phi, (fun n => γ (eta n)), (fun n => s (eta n)), g, hphi, hg, hbase,
    (fun n => hγdata (eta n)), hconv, ?_, hblow, hquant⟩
  intro x hx
  have hmap : NeBot (map (Subtype.val : Ico 0 rho → ℝ)
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho))) := by
    rw [map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot hrho
  let _ := hmap.of_map
  have hscalar : Tendsto (fun t => |metricScalarAt L.metric (g t)|)
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 |metricScalarAt L.metric x|) :=
    ((metricScalar_smooth L.metric).continuous.abs.tendsto x).comp hx
  exact not_tendsto_nhds_of_tendsto_atTop hblow _ hscalar

theorem exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) {A : ℝ} (hA : 0 ≤ A) :
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
                        ∀ t : Ico 0 F.radius, 2 < metricScalarAt L.metric (g t) →
                          A ^ 2 ≤ metricScalarAt L.metric (g t) *
                            dist q (g t : UniformSpace.Completion L.M) ^ 2 := by
  obtain ⟨epsLocal, hepsLocal, hlocal⟩ :=
    exists_terminal_pointed_convergence_of_not_boundedAtDistance hkappa
  obtain ⟨epsCurve, c, hepsCurve, hc, hcurve⟩ := exists_isometric_curve_with_missing_endpoint hkappa hA
  refine ⟨min epsLocal epsCurve, c, lt_min hepsLocal hepsCurve, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec⟩ := hlocal eps heps (hle.trans (min_le_left _ _))
      sigma hsigma Phi hPhi X hnot
  have hL : PathConnectedSpace L.M :=
    maps.path_connected_space_of_frequently_path_connected_targets
      (Eventually.frequently (Eventually.of_forall fun n => by
        rw [htargets n]
        exact isPathConnected_riemannianBallOf ((X.term (f n)).S.base.metric 0)
          (X.term (f n)).basepoint (hr n).1))
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  have hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace I3 x,
        (1 - eta) * L.metric.inner x v v ≤
          ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v) := by
    intro eta heta
    obtain ⟨N, hN⟩ := hmetrics eta heta
    filter_upwards [eventually_ge_atTop N] with n hn
    exact fun x hx v => (hN n hn x hx v).1
  obtain ⟨phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow, hquant⟩ :=
    hcurve eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X f hf
      F.points F.curvature_limit F.radius F.radius_pos F.distance_limit L maps C.metrics hcanonical
      r (fun n => (hr n).1) hrT (fun n => by rw [htargets n]) hlower hcompact
  have hRnonneg (x : L.M) : 0 ≤ metricScalarAt L.metric x := by
    apply metricScalarAt_nonnegative_of_ricci_nonnegative L.metric x (by simp [ThreeSpace])
    intro v
    rw [metricRicciAt_apply_eq_ricciTensor]
    exact Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec L.metric x
      ((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff L.metric x).mpr (hsec x)) v
  have hblowScalar := hblow.congr' (Eventually.of_forall fun t => abs_of_nonneg (hRnonneg (g t)))
  obtain ⟨q, hq, hdist⟩ := Geometry.exists_completion_endpoint_of_isometry F.radius_pos hg
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblowScalar,
    q, hq, hdist, ?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact hno x ((UniformSpace.Completion.isUniformInducing_coe L.M).isInducing.tendsto_nhds_iff.mpr hq)
  · intro t ht
    rw [hdist t]
    exact hquant t ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
