import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceLocalRicciFlowLimit
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedPinching

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

section

private theorem exists_canonical_metric_convergence_refl
    (P : PointedRiemannianManifold I3) (G : ℕ → SmoothRiemannianMetric I3 P.M)
    (hconv : MetricCInfConvergenceOnCompacts G P.metric P.metric) :
    let X : PointedRiemannianSeq I3 := ⟨fun i => { P with metric := G i }⟩
    ∃ F : PointedRiemannianConvergenceMaps X P id,
      (∀ i x, F.map i x = x) ∧ ∃ C : MetricConvergenceData F,
        ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let X : PointedRiemannianSeq I3 := ⟨fun i => { P with metric := G i }⟩
  let F : PointedRiemannianConvergenceMaps X P id := {
    partialDiffeomorph := fun _ => PartialDiffeomorph.refl P.M
    source_exhausts := ⟨fun _ => isOpen_univ, fun _ => subset_univ _,
      fun _ _ => ⟨0, fun _ _ => subset_univ _⟩⟩
    base_mem := fun _ => mem_univ _
    basepoint_map := fun _ => rfl }
  obtain ⟨C, hC, _⟩ := exists_canonicalMetricConvergenceData_of_metric_extension F G hconv (by
    intro K _
    refine Eventually.of_forall fun i => ⟨univ, isOpen_univ, subset_univ _, subset_univ _, ?_⟩
    intro x _ v w
    change (G i).inner x v w = (G i).inner x (mfderiv I3 I3 id x v) (mfderiv I3 I3 id x w)
    rw [mfderiv_id]
    rfl)
  exact ⟨F, fun _ _ => rfl, C, hC⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I3 M)]

private theorem metricScalarAt_tendsto_of_metricCInfConvergenceOnCompacts
    (G : ℕ → SmoothRiemannianMetric I3 M) (g r : SmoothRiemannianMetric I3 M)
    (hconv : MetricCInfConvergenceOnCompacts G g r) (x : M) :
    Tendsto (fun i => metricScalarAt (G i) x) atTop (𝓝 (metricScalarAt g x)) := by
  let P : PointedRiemannianManifold I3 := {
    M := M, topology := inferInstance, charted := inferInstance, smooth := inferInstance,
    t2 := inferInstance, sigmaCompact := inferInstance, t2TangentBundle := inferInstance,
    basepoint := x, metric := g }
  obtain ⟨F, hF, C, hC⟩ := exists_canonical_metric_convergence_refl P G (hconv.change_reference g)
  have h := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hC x
  simpa only [hF, id_eq, P] using h

private theorem secLower_zero_of_metricCInf_admissible_pinching
    (G : ℕ → SmoothRiemannianMetric I3 M) (g r : SmoothRiemannianMetric I3 M)
    (hconv : MetricCInfConvergenceOnCompacts G g r)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (A : ℕ → ℝ) (hA : ∀ i, 0 < A i) (hescape : Tendsto A atTop atTop)
    (hpin : ∀ᶠ i in atTop, ∀ x : M, curvatureOperatorLowerBoundAt (G i) x
      (metricAlgebraicCurvatureTensorAt (G i) x)
      (rescalePinchingFunction (A i) Phi (metricScalarAt (G i) x))) :
    SecLower g 0 univ := by
  intro x _ v w
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P : PointedRiemannianManifold I3 := {
    M := M, topology := inferInstance, charted := inferInstance, smooth := inferInstance,
    t2 := inferInstance, sigmaCompact := inferInstance, t2TangentBundle := inferInstance,
    basepoint := x, metric := g }
  obtain ⟨F, hF, C, hC⟩ := exists_canonical_metric_convergence_refl P G (hconv.change_reference g)
  have h := sectional_nonnegative_of_pointed_admissible_pinching_eventually C hC
    hPhi A hA hescape hpin x v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [P, zero_mul, metricRm04StandardAt_apply, hvec] using h


end

theorem RealizedFiniteHorn.exists_original_source_normalized_nonnegative_local_ricci_flow_limit
    {kappa : ℝ} (hkappa : 0 < kappa) (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, ∃ hc : 0 < c, 0 < epsStar ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∃ B : ℕ → ℝ, ∃ eta : ℝ, (∀ m, 0 ≤ B m) ∧ 0 < eta ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ H : RealizedFiniteHorn X.toFlowSequence,
              ∀ ray : EndRay H.horn.endpoint, ∀ d : ℕ → ℝ, ∀ N : ℕ,
                ∀ hQ : ∀ n, 1 ≤ metricScalarAt H.metric (ray.point (d (N + n))),
                  ∀ j : ℕ → ℕ, StrictMono j →
                    ∃ psi : ℕ → ℕ, StrictMono psi ∧ StrictMono (H.subseq ∘ j ∘ psi) ∧
                    let hq := fun n => zero_lt_one.trans_le (hQ n)
                    let Y := H.rescaledSourceSeq ray d N (j ∘ psi) hq
                    ∃ S : ∀ n, SolutionOn (I := I3) (M := (Y.obj n).M)
                      (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                    (∀ n, IsSolutionOn (S n)) ∧
                    (∀ n t, (S n).base.metric t =
                      scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hq n)
                        ((X.term (H.subseq (j (psi n)))).S.base.metric
                          (t / metricScalarAt H.metric (ray.point (d (N + n)))))) ∧
                    (∀ n, (S n).base.metric 0 = (Y.obj n).metric) ∧
                    (∀ n, ∀ t ∈ Icc (-(c / 6)) 0,
                      RiemannianMetricComplete ((S n).base.metric t)) ∧
                    (∀ n, |(S n).scalar 0 (Y.obj n).basepoint - 1| < 1 / ((n : ℝ) + 2)) ∧
                    (∀ n, ∀ y : (Y.obj n).M, ∀ t ∈ Icc (-(c / 6)) 0,
                      y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
                        (c / Real.sqrt 3) →
                      (S n).scalar t y ≤ 12 ∧
                      Real.sqrt (FlowMetricBall.rmNormSq (S n) t y) ≤ C * (3 + 13 * Phi 1)) ∧
                    (∀ n m, ∀ t ∈ Icc (-(c / 24)) 0,
                      ∀ y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
                        (c / (2 * Real.sqrt 3)),
                      curvDerivNorm (I := I3) m ((S n).base.metric t) y ≤ B m) ∧
                    (∀ n, ∀ y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
                      (c / (2 * Real.sqrt 3)), HasInjRadiusAt (Y.obj n) y eta) ∧
                    ∃ phi : ℕ → ℕ, StrictMono phi ∧
                      StrictMono (H.subseq ∘ j ∘ psi ∘ phi) ∧
                      ∃ Q : Type, ∃ top : TopologicalSpace Q, letI := top
                      ∃ charts : ChartedSpace ThreeSpace Q, letI := charts
                      ∃ hman : IsManifold I3 ∞ Q, letI := hman
                      ∃ hT2 : T2Space Q, letI := hT2
                      ∃ hsecond : SecondCountableTopology Q, letI := hsecond
                      ∃ (gQ : SmoothRiemannianMetric I3 Q)
                        (V U : TopologicalSpace.Opens Q) (q : Q)
                        (F : ∀ k, Q → (Y.obj (phi k)).M)
                        (G : ℕ → SmoothRiemannianMetric I3 U),
                        IsCompact (closure (V : Set Q)) ∧ closure (V : Set Q) ⊆ U ∧ q ∈ V ∧
                        (∀ᶠ k in atTop, ∀ (z : U) (v w : TangentSpace I3 z),
                          (G k).inner z v w = (Y.obj (phi k)).metric.inner (F k z)
                            (mfderiv I3 I3 (F k) (z : Q) v)
                            (mfderiv I3 I3 (F k) (z : Q) w)) ∧
                        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen U) (gQ.restrictOpen U) ∧
                        ∃ offset : ℕ,
                          ∃ f : ∀ k, PartialDiffeomorph I3 I3 Q (Y.obj (phi (k + offset))).M ∞,
                            (∀ k, closure (U : Set Q) ⊆ (f k).source ∧
                              EqOn (f k) (F (k + offset)) (f k).source ∧
                              f k q = (Y.obj (phi (k + offset))).basepoint ∧
                              (∀ y : (Y.obj (phi (k + offset))).M,
                                riemannianEDistOf (Y.obj (phi (k + offset))).metric
                                  (Y.obj (phi (k + offset))).basepoint y ≤
                                    ENNReal.ofReal (c / (4 * Real.sqrt 3)) →
                                y ∈ f k '' closure (V : Set Q)) ∧
                              f k '' closure (V : Set Q) ⊆
                                {y | riemannianEDistOf (Y.obj (phi (k + offset))).metric
                                  (Y.obj (phi (k + offset))).basepoint y <
                                    ENNReal.ofReal (c / (2 * Real.sqrt 3))}) ∧
                            ∃ hVU : V ≤ U,
                              ∃ T : ℕ → SolutionOn (I := I3) (M := V)
                                (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                              (∀ k, IsSolutionOn (T k)) ∧
                              (∀ k t (z : V) (v w : TangentSpace I3 z),
                                ((T k).base.metric t).inner z v w =
                                  ((S (phi (k + offset))).base.metric t).inner (f k z)
                                    (mfderiv I3 I3 (f k) z v) (mfderiv I3 I3 (f k) z w)) ∧
                              (∀ k, (T k).base.metric 0 =
                                (G (k + offset)).restrictOpenOfSubset hVU) ∧
                              ∃ rho : ℕ → ℕ, StrictMono rho ∧
                                StrictMono (fun k => H.subseq (j (psi (phi (rho k + offset))))) ∧
                                ∃ g : ℝ → SmoothRiemannianMetric I3 V,
                                  g 0 = gQ.restrictOpen V ∧
                                  IsSolutionOn ({ base.metric := g } : SolutionOn
                                    (I := I3) (M := V)
                                    (RealTimeInterval.closed (-(c / 24)) 0 (by linarith))) ∧
                                  (∀ hqV : q ∈ V, metricScalarAt (g 0) ⟨q, hqV⟩ = 1) ∧
                                  (∀ t ∈ Icc (-(c / 24)) 0, SecLower (g t) 0 univ) ∧
                                  ∀ K : Set V, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ,
                                    0 < epsilon → ∃ k0 : ℕ, ∀ k ≥ k0,
                                      ∀ t ∈ Icc (-(c / 24)) 0,
                                        metricDerivNormSupOn K p ((T (rho k)).base.metric t)
                                          (g t) (gQ.restrictOpen V) < epsilon := by
  classical
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨epsStar, c, C, hc, hepsStar, hC, hlimits⟩ :=
    RealizedFiniteHorn.exists_original_source_local_ricci_flow_limit hkappa hmod
  refine ⟨epsStar, c, C, hc, hepsStar, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi
  obtain ⟨B, eta, hB, heta, hlimits'⟩ :=
    hlimits eps heps hepsStar' sigma hsigma Phi hPhi
  refine ⟨B, eta, hB, heta, ?_⟩
  intro X H ray d N hQ j hj
  obtain ⟨psi, hpsi, horiginal, S, hS, hmetric, hmetric0, hcomplete, hcenter,
    hcurv, hderiv, hinj, phi, hphi, horiginal', Q, top, charts, hman, hT2, hsecond,
    gQ, V, U, q, F, G, hVcompact, hVUclosure, hqV, hG, hGconv, offset, f, hf,
    hVU, T, hT, hTmetric, hterminal, rho, hrho, horiginalFinal, g, hg0, hflow, hconv⟩ :=
      hlimits' X H ray d N hQ j hj
  let := top
  let := charts
  let := hman
  let := hT2
  let := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace ThreeSpace Q
  let _ : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  let nseq : ℕ → ℕ := fun k => phi (rho k + offset)
  let J : ℕ → ℕ := fun k => H.subseq (j (psi (nseq k)))
  let A : ℕ → ℝ := fun k =>
    metricScalarAt H.metric (ray.point (d (N + nseq k))) * X.scale (J k)
  have hnseq : StrictMono nseq := hphi.comp (fun _ _ h => Nat.add_lt_add_right (hrho h) offset)
  have hJ : StrictMono J := horiginalFinal
  have hA : ∀ k, 0 < A k := fun k =>
    mul_pos (zero_lt_one.trans_le (hQ (nseq k))) (X.scale_pos (J k))
  have hescape : Tendsto A atTop atTop := by
    apply tendsto_atTop_mono _ (X.scale_tendsto.comp hJ.tendsto_atTop)
    intro k
    exact le_mul_of_one_le_left (X.scale_pos (J k)).le (hQ (nseq k))
  have hVsource : ∀ k, (V : Set Q) ⊆ (f k).source :=
    fun k _ hz => (hf k).1 (subset_closure (hVU hz))
  have hscalar (k : ℕ) (t : ℝ) (z : V) :
      metricScalarAt ((T (rho k)).base.metric t) z =
        metricScalarAt ((S (nseq k)).base.metric t) (f (rho k) z) :=
    metricScalarAt_eq_of_partialDiffeomorph_restriction (f (rho k)) V
      (hVsource (rho k)) ((T (rho k)).base.metric t) ((S (nseq k)).base.metric t)
      (hTmetric (rho k) t) z
  have hslice (t : ℝ) (ht : t ∈ Icc (-(c / 24)) 0) :
      MetricCInfConvergenceOnCompacts (fun k => (T (rho k)).base.metric t)
        (g t) (gQ.restrictOpen V) := by
    intro K hK p epsilon hepsilon
    obtain ⟨k0, hk0⟩ := hconv K hK p epsilon hepsilon
    exact ⟨k0, fun k hk => hk0 k hk t ht⟩
  have hnormalized : metricScalarAt (g 0) ⟨q, hqV⟩ = 1 := by
    have hlim := metricScalarAt_tendsto_of_metricCInfConvergenceOnCompacts
      (fun k => (T (rho k)).base.metric 0) (g 0) (gQ.restrictOpen V)
      (hslice 0 ⟨by linarith, le_rfl⟩) ⟨q, hqV⟩
    have herr : Tendsto (fun k => 1 / ((nseq k : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 2
          (tendsto_natCast_atTop_atTop.comp hnseq.tendsto_atTop))
    have hone : Tendsto (fun k => metricScalarAt ((T (rho k)).base.metric 0) ⟨q, hqV⟩)
        atTop (𝓝 1) := by
      apply Metric.tendsto_atTop.mpr
      intro epsilon hepsilon
      obtain ⟨k0, hk0⟩ := eventually_atTop.1 (herr.eventually_lt_const hepsilon)
      refine ⟨k0, fun k hk => ?_⟩
      rw [Real.dist_eq, hscalar k 0 ⟨q, hqV⟩, (hf (rho k)).2.2.1]
      exact (hcenter (nseq k)).trans (hk0 k hk)
    exact tendsto_nhds_unique hlim hone
  have hsec : ∀ t ∈ Icc (-(c / 24)) 0, SecLower (g t) 0 univ := by
    intro t ht
    apply secLower_zero_of_metricCInf_admissible_pinching
      (fun k => (T (rho k)).base.metric t) (g t) (gQ.restrictOpen V)
      (hslice t ht) hPhi A hA hescape
    filter_upwards [(X.depth_tendsto.comp hJ.tendsto_atTop).eventually_ge_atTop (-t)]
      with k hk
    intro z
    change -t ≤ X.depth (J k) at hk
    have hq : 0 < metricScalarAt H.metric (ray.point (d (N + nseq k))) :=
      zero_lt_one.trans_le (hQ (nseq k))
    have htime : t / metricScalarAt H.metric (ray.point (d (N + nseq k))) ∈
        (X.interval (J k)).carrier := by
      rw [X.carrier_eq]
      have htdiv : t ≤ t / metricScalarAt H.metric (ray.point (d (N + nseq k))) := by
        apply (le_div_iff₀ hq).2
        nlinarith [mul_nonpos_of_nonpos_of_nonneg ht.2 (sub_nonneg.mpr (hQ (nseq k)))]
      exact ⟨by linarith [X.depth_pos (J k)], div_nonpos_of_nonpos_of_nonneg ht.2 hq.le⟩
    have hpin : curvatureOperatorLowerBoundAt ((S (nseq k)).base.metric t) (f (rho k) z)
        (metricAlgebraicCurvatureTensorAt ((S (nseq k)).base.metric t) (f (rho k) z))
        (rescalePinchingFunction (A k) Phi
          (metricScalarAt ((S (nseq k)).base.metric t) (f (rho k) z))) := by
      rw [hmetric (nseq k) t]
      exact X.curvatureOperatorLowerBoundAt_scaleMetric (J k) hq t htime (f (rho k) z)
    rw [hscalar k t z]
    exact curvatureOperatorLowerBoundAt_of_partialDiffeomorph_restriction
      (f (rho k)) V (hVsource (rho k)) ((T (rho k)).base.metric t)
      ((S (nseq k)).base.metric t) (hTmetric (rho k) t) z _ hpin
  exact ⟨psi, hpsi, horiginal, S, hS, hmetric, hmetric0, hcomplete, hcenter,
    hcurv, hderiv, hinj, phi, hphi, horiginal', Q, top, charts, hman, hT2, hsecond,
    gQ, V, U, q, F, G, hVcompact, hVUclosure, hqV, hG, hGconv, offset, f, hf,
    hVU, T, hT, hTmetric, hterminal, rho, hrho, horiginalFinal, g, hg0, hflow,
    fun _ => hnormalized, hsec, hconv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
