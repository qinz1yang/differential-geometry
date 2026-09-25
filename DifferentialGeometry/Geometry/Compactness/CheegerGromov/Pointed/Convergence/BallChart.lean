import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {F H' M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem pointedMaps_eventually_fixedDomain_metric_bound
    (Phi : PointedRiemannianConvergenceMaps X L subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (e : M ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens M)
    (B : Set M) (hB : IsCompact B) (hUB : (U : Set M) ⊆ B)
    (p : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ i in atTop, ∃ f : C(U, (X.obj (subseq i)).M),
      ∃ hf : IsSmoothEmbedding J I ∞ f,
        (∀ x : U, f x = Phi.map i (e x.val)) ∧
        ∀ x : U, ∀ a : ℕ, a ≤ p →
          metricDerivNorm a (immersionInducedMetric (X.obj (subseq i)).metric hf.isImmersion)
            ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen U)
            ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen U) x < eta := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨i0, hi0⟩ := C.converges (e '' B) (hB.image e.continuous) p eta heta
  filter_upwards [eventually_ge_atTop i0] with i hi
  obtain ⟨hsource, hsup⟩ := hi0 i hi
  rw [hcanonical i] at hsup
  have hU : e '' (U : Set M) ⊆ Phi.source i := (image_mono hUB).trans hsource
  let f := pointedDomainEmbedding Phi e U i hU
  have hf : IsSmoothEmbedding J I ∞ f := pointedMaps_restrict_isSmoothEmbedding Phi e U i hU
  refine ⟨f,hf,fun _ => rfl,?_⟩
  let D := CanonicalMetricCompactness.canonicalSourceData Phi i
  let _ : TopologicalSpace (MetricSourceDomain Phi i) := D.topology
  let _ : ChartedSpace H (MetricSourceDomain Phi i) := D.charted
  let _ : IsManifold I ∞ (MetricSourceDomain Phi i) := D.smooth
  let _ : T2Space (MetricSourceDomain Phi i) := D.t2
  let _ : SigmaCompactSpace (MetricSourceDomain Phi i) := D.sigmaCompact
  have hcompact : IsCompact (metricSourceCompactSet Phi i (e '' B)) :=
    D.compact_preimage (e '' B) (hB.image e.continuous) hsource
  intro x a ha
  have hb := (derivNorm_le_sup hcompact ha D.pullbackMetric D.limitMetric D.referenceMetric
    (x := ⟨e x.val, hU ⟨x.val,x.property,rfl⟩⟩) (by exact ⟨x.val,hUB x.property,rfl⟩)).trans_lt hsup
  have heq := metricDerivNorm_fixedDomainPullback e U (metricSourceOpenSubset Phi i) hU
    D.pullbackMetric D.limitMetric D.referenceMetric a x
  rw [canonicalSource_fixedDomain_pullback_eq_induced Phi e U i hU] at heq
  have hlim : fixedDomainPullbackMetric e U (metricSourceOpenSubset Phi i) hU D.limitMetric =
      (Diffeomorph.pullbackMetricCross L.metric e).restrictOpen U :=
    fixedDomainPullbackMetric_restrict e U (metricSourceOpenSubset Phi i) hU L.metric
  have href : D.referenceMetric = D.limitMetric := rfl
  rw [href,hlim] at heq
  exact heq.trans_lt hb


omit [SigmaCompactSpace M] in
theorem exists_eventually_fixed_domain_diffeomorph_capturing_ball
    (Phi : PointedRiemannianConvergenceMaps X L subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (e : M ≃ₘ⟮J, I⟯ L.M)
    (z : L.M) {r R : ℝ} (hr : 0 ≤ r) (hR : 2 * r < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric z R)) :
    ∃ O : TopologicalSpace.Opens M, IsCompact (closure (O : Set M)) ∧
      ∀ p : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        ∃ (V : TopologicalSpace.Opens (X.obj (subseq i)).M) (Ψ : O ≃ₘ⟮J, I⟯ V),
          (∀ x : O, (Ψ x).val = Phi.map i (e x.val)) ∧
          riemannianClosedBallOf (X.obj (subseq i)).metric (Phi.map i z) r ⊆ V ∧
          ∀ y : V, ∀ a : ℕ, a ≤ p →
            metricDerivNorm a (Diffeomorph.pullbackMetricCross ((X.obj (subseq i)).metric.restrictOpen V) Ψ)
              ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen O)
              ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen O) (Ψ.symm y) < eta := by
  let _ : SigmaCompactSpace M := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have hdim : Module.finrank ℝ F = Module.finrank ℝ E :=
    (e.mfderivToContinuousLinearEquiv (by decide) (e.symm z)).toLinearEquiv.finrank_eq
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : LocallyCompactSpace H' := J.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H' M
  let B : Set M := e.symm '' riemannianClosedBallOf L.metric z R
  have hB : IsCompact B := hcompact.image e.symm.continuous
  obtain ⟨U,hU,hBU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hB
  let O : TopologicalSpace.Opens M := ⟨U,hU⟩
  have hconv : metricSourceConvergesOn Phi (CanonicalMetricCompactness.canonicalSourceData Phi)
      (riemannianClosedBallOf L.metric z R) 0 := by
    intro eta heta
    obtain ⟨i,hi⟩ := C.converges _ hcompact 0 eta heta
    refine ⟨i,fun j hj => ?_⟩
    have hh := hi j hj
    rwa [hcanonical j] at hh
  have hcap := pointed_metric_eventually_inverse_ball_capture (Φ := Phi) z hr
    (by norm_num : (1 : ℝ) < 2) hR hcompact hconv
  refine ⟨O,hUc,?_⟩
  intro p eta heta
  have hb := pointedMaps_eventually_fixedDomain_metric_bound Phi C hcanonical e O
    (closure U) hUc subset_closure p heta
  filter_upwards [hb,hcap] with i hi hci
  obtain ⟨f,hf,hmap,hbound⟩ := hi
  obtain ⟨V,Ψ,hV,hΨ,hinv,hmet⟩ := DifferentialGeometry.Geometry.Metric.exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric
    (X.obj (subseq i)).metric hf.isImmersion hf.isEmbedding.injective hdim
  refine ⟨V,Ψ,fun x => (hΨ x).trans (hmap x),?_,?_⟩
  · intro y hy
    obtain ⟨_,_,hpre,hright⟩ := hci.2 y hy
    let t := (Phi.partialDiffeomorph i).symm y
    have ht : t ∈ riemannianClosedBallOf L.metric z R :=
      hpre.trans (ENNReal.ofReal_le_ofReal hR.le)
    have hty : e.symm t ∈ O := hBU ⟨t,ht,rfl⟩
    change y ∈ (V : Set (X.obj (subseq i)).M)
    rw [hV]
    refine ⟨⟨e.symm t,hty⟩,?_⟩
    rw [hmap]
    change Phi.map i (e (e.symm t)) = y
    rw [e.apply_symm_apply]
    exact hright
  · intro y a ha
    rw [hmet]
    exact hbound (Ψ.symm y) a ha

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped ENNReal

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {F H' M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]

theorem exists_eventually_fixed_domain_diffeomorph_capturing_balls
    (Phi : PointedRiemannianConvergenceMaps X L subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (e : M ≃ₘ⟮J, I⟯ L.M) (z : L.M)
    {A r R : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (hR : 2 * (2 * A + r) < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric z R)) :
    ∃ O : TopologicalSpace.Opens M, IsCompact (closure (O : Set M)) ∧
      ∀ p : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        ∃ (V : TopologicalSpace.Opens (X.obj (subseq i)).M) (Ψ : O ≃ₘ⟮J, I⟯ V),
          (∀ x : O, (Ψ x).val = Phi.map i (e x.val)) ∧
          (∀ x ∈ riemannianClosedBallOf L.metric z A,
            riemannianClosedBallOf (X.obj (subseq i)).metric (Phi.map i x) r ⊆ V) ∧
          ∀ y : V, ∀ a : ℕ, a ≤ p →
            metricDerivNorm a (Diffeomorph.pullbackMetricCross ((X.obj (subseq i)).metric.restrictOpen V) Ψ)
              ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen O)
              ((Diffeomorph.pullbackMetricCross L.metric e).restrictOpen O) (Ψ.symm y) < eta := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hconv : metricSourceConvergesOn Phi (CanonicalMetricCompactness.canonicalSourceData Phi)
      (riemannianClosedBallOf L.metric z R) 0 := by
    intro eta heta
    obtain ⟨i,hi⟩ := C.converges _ hcompact 0 eta heta
    refine ⟨i,fun j hj => ?_⟩
    have hh := hi j hj
    rwa [hcanonical j] at hh
  have hquad := pointed_metric_eventually_quadratic_bounds hcompact hconv
    (by norm_num : (0 : ℝ) < 3)
  obtain ⟨O,hO,hcharts⟩ := exists_eventually_fixed_domain_diffeomorph_capturing_ball
    Phi C hcanonical e z (by positivity : 0 ≤ 2 * A + r) hR hcompact
  refine ⟨O,hO,?_⟩
  intro p eta heta
  filter_upwards [hquad,hcharts p eta heta] with i hi hchart
  obtain ⟨V,Ψ,hΨ,hcapture,hjets⟩ := hchart
  refine ⟨V,Ψ,hΨ,?_,hjets⟩
  have hdist (x : L.M) (hx : x ∈ riemannianClosedBallOf L.metric z A) :
      riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i z) (Phi.map i x) ≤
        ENNReal.ofReal (2 * A) := by
    have hd := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      L.metric (X.obj (subseq i)).metric (Phi.partialDiffeomorph i) z z x hA
      (by linarith : 3 * A < R) (by norm_num : (0 : ℝ) < 2) hi.1
      (fun y hy v => by
        change (X.obj (subseq i)).metric.inner (Phi.map i y)
          (mfderiv I I (Phi.map i) y v) (mfderiv I I (Phi.map i) y v) ≤
            2 ^ 2 * L.metric.inner y v v
        convert (hi.2 y hy v).2 using 1
        norm_num)
      (by change riemannianEDistOf L.metric z z ≤ ENNReal.ofReal A; rw [riemannianEDistOf_self]; exact bot_le) hx
    exact hd.trans ((mul_le_mul' le_rfl hx).trans_eq (ENNReal.ofReal_mul (by norm_num)).symm)
  intro x hx y hy
  apply hcapture
  calc
    riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i z) y ≤
        riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i z) (Phi.map i x) +
        riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i x) y :=
      riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal (2 * A) + ENNReal.ofReal r := add_le_add (hdist x hx) hy
    _ = ENNReal.ofReal (2 * A + r) := (ENNReal.ofReal_add (by positivity) hr).symm

end DifferentialGeometry.CheegerGromovCompactness
