import DifferentialGeometry.Geometry.Neck.FiniteEnd
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLimitNecks

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
                            LocallyFinite (fun n =>
                              (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) ∧
                            ∃ eta : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                              ∃ Ψ : ℕ → PartialDiffeomorph IC I3 Cylinder L.M ∞,
                                (∀ n, (univ ×ˢ Icc (0 : ℝ) 1 ⊆ (Ψ n).source) ∧
                                  (∀ p, Ψ n (p, 0) = (nk n).map (p, 0)) ∧
                                  (∀ p, Ψ n (p, 1) = (nk (n + 1)).map (eta n p, 0)) ∧
                                  IsCompact (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                  (frontier (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                                    (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) ∪
                                      (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                                  (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                                    (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) ∧
                                  Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                                    riemannianClosedBallOf L.metric (g (t n))
                                      ((3 * (2 * alpha)⁻¹ / 100) /
                                        Real.sqrt (metricScalarAt L.metric (g (t n)))) ∩
                                    riemannianClosedBallOf L.metric (g (t (n + 1)))
                                      ((3 * (2 * alpha)⁻¹ / 100) /
                                        Real.sqrt (metricScalarAt L.metric (g (t n))))) ∧
                                (∀ i j, i + 1 < j →
                                  Disjoint (Ψ i '' (univ ×ˢ Icc (0 : ℝ) 1))
                                    (Ψ j '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
                                Pairwise (fun i j =>
                                  Disjoint (interior (Ψ (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)))
                                    (interior (Ψ (j + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)))) ∧
                                (∀ n, (Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
                                  (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                                    (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                                (∀ n, (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ)) ⊆
                                  interior ((Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∪
                                    (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)))) ∧
                                LocallyFinite (fun n => Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                IsClosed (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                IsConnected (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                ¬ IsCompact (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                (frontier (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
                                  ⋃ n, (nk n).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                                IsClosed (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                IsConnected (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                ¬ IsCompact (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                                (frontier (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                                  (nk 1).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                                (∀ v : Ico 0 F.radius, (t 2 : ℝ) ≤ v →
                                  g v ∈ interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
                                (∀ n (x : L.M), x ∈ Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) →
                                  dist q (x : UniformSpace.Completion L.M) ≤
                                    (11 / 5) * (F.radius - (t n : ℝ))) ∧
                                (∀ n (x : L.M), x ∈ Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) →
                                  ((2 * alpha)⁻¹) ^ 2 / 8 ≤ metricScalarAt L.metric x *
                                    dist q (x : UniformSpace.Completion L.M) ^ 2) ∧
                                (∀ᶠ n in atTop,
                                  (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ⊆
                                    interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
                                ∃ E : Sphere 2 × Ici (0 : ℝ) ≃ₜ
                                  (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                                  ∃ theta : ℕ → Sphere 2 ≃ₜ Sphere 2,
                                    theta 0 = Homeomorph.refl (Sphere 2) ∧
                                    (∀ n, theta (n + 1) =
                                      (theta n).trans (eta (n + 1)).toHomeomorph) ∧
                                    (∀ (n : ℕ) (p : Sphere 2) (s : Icc (0 : ℝ) 1),
                                      (E (p, ⟨n + (s : ℝ),
                                        add_nonneg (Nat.cast_nonneg n) s.property.1⟩) : L.M) =
                                          Ψ (n + 1) (theta n p, s)) ∧
                                    (∀ s : Ici (0 : ℝ), Nonempty
                                      (DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
                                        (fun p : Sphere 2 => (E (p, s) : L.M)))) ∧
                                    ∃ D : Sphere 2 × Ioi (0 : ℝ) ≃ₜ
                                      interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                                      (∀ (p : Sphere 2) (s : Ioi (0 : ℝ)),
                                        (D (p, s) : L.M) =
                                          (E (p, Set.inclusion Ioi_subset_Ici_self s) : L.M)) ∧
                                      let W : TopologicalSpace.Opens L.M :=
                                        ⟨interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                                          isOpen_interior⟩
                                      ∃ gW : C(Ico (t 2 : ℝ) F.radius, W),
                                        (∀ v : Ico (t 2 : ℝ) F.radius, (gW v : L.M) =
                                          g ⟨v, (t 2).property.1.trans v.property.1, v.property.2⟩) ∧
                                        (∀ v w : Ico (t 2 : ℝ) F.radius,
                                          riemannianEDistOf (L.metric.restrictOpen W) (gW v) (gW w) =
                                            edist v w) ∧
                                        (∀ᶠ n in atTop, ∃ hn : (t 2 : ℝ) ≤ t n,
                                          ∃ nkW : SpatialNeck (L.metric.restrictOpen W) (2 * alpha)
                                            (gW ⟨t n, hn, (t n).property.2⟩),
                                            nkW.map.source = (nk n).map.source ∩
                                              (nk n).map ⁻¹' (W : Set L.M) ∧
                                            (∀ y ∈ univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
                                              (nkW.map y : L.M) = (nk n).map y) ∧
                                            ∀ y : W, nkW.map.symm y = (nk n).map.symm (y : L.M)) ∧
                                        ∃ hW : PathConnectedSpace W,
                                          let _ : PathConnectedSpace W := hW
                                          let mW : MetricSpace W :=
                                            let _ : PseudoMetricSpace W :=
                                              (L.metric.restrictOpen W).toPseudoMetricSpace
                                            MetricSpace.ofT0PseudoMetricSpace W
                                          let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
                                          let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
                                          let eW : PseudoEMetricSpace W :=
                                            @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
                                          let _ : WeakPseudoEMetricSpace W :=
                                            @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
                                          ∃ qW : UniformSpace.Completion W,
                                            Tendsto (fun v => (gW v : UniformSpace.Completion W))
                                              (comap (Subtype.val : Ico (t 2 : ℝ) F.radius → ℝ)
                                                (𝓝 F.radius)) (𝓝 qW) ∧
                                            (∀ v : Ico (t 2 : ℝ) F.radius,
                                              dist qW (gW v : UniformSpace.Completion W) = F.radius - v) ∧
                                            qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
                                            UniformSpace.Completion.map (Subtype.val : W → L.M) qW = q ∧
                                            Topology.IsOpenEmbedding
                                              (fun x : W => (x : UniformSpace.Completion W)) ∧
                                            (∀ U ∈ 𝓝 qW, ∀ᶠ n in atTop,
                                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                                {x : W | (x : L.M) ∈ Ψ (n + 2) ''
                                                  (univ ×ˢ Icc (0 : ℝ) 1)} ⊆ U) ∧
                                            IsCompact (insert qW (⋃ n,
                                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                                {x : W | (x : L.M) ∈ Ψ (n + 2) ''
                                                  (univ ×ˢ Icc (0 : ℝ) 1)})) ∧
                                            insert qW (⋃ n,
                                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                                {x : W | (x : L.M) ∈ Ψ (n + 2) ''
                                                  (univ ×ˢ Icc (0 : ℝ) 1)}) ∈ 𝓝 qW ∧
                                            Tendsto (fun x : W => metricScalarAt (L.metric.restrictOpen W) x)
                                              (comap (fun x : W => (x : UniformSpace.Completion W))
                                                (𝓝 qW)) atTop ∧
                                            (∀ n (x : W), (x : L.M) ∈ Ψ (n + 2) ''
                                              (univ ×ˢ Icc (0 : ℝ) 1) →
                                              ((2 * alpha)⁻¹) ^ 2 / 8 ≤
                                                metricScalarAt (L.metric.restrictOpen W) x *
                                                  dist qW (x : UniformSpace.Completion W) ^ 2) ∧
                                            (∀ (β : ℝ → UniformSpace.Completion W) (u v w : ℝ),
                                              u < v → v < w →
                                              (∀ s ∈ Icc u w, ∀ t ∈ Icc u w,
                                                dist (β s) (β t) = |s - t|) → β v ≠ qW) ∧
                                            (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
                                              metricScalarAt L.metric (g (t (n + 2))) *
                                                (F.radius - (t (n + 2) : ℝ)) ^ 2 ≤ C) ∧
                                            ∃ delta : ℝ, 0 < delta ∧
                                              IsCompact (Metric.closedBall qW delta) ∧
                                              Metric.closedBall qW delta ⊆ insert qW
                                                (range (fun x : W => (x : UniformSpace.Completion W))) ∧
                                                Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
                                                (∀ eps > 0, ∃ d ∈ Ioo 0 (delta / 3), ∃ A : Finset C(ℝ, UniformSpace.Completion W),
                                                  (∀ ray ∈ A, ray 0 = qW ∧
                                                    ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, dist (ray s) (ray t) = |s - t|) ∧
                                                  ∀ s ∈ Ioc 0 d, ∀ x : W, dist (x : UniformSpace.Completion W) qW = s →
                                                    ∃ ray ∈ A, dist (x : UniformSpace.Completion W) (ray s) < eps * s) ∧
                                                ∀ {ι : Type u} (len : ι → ℝ) (ray : ι → C(ℝ, UniformSpace.Completion W)),
                                                  (∀ i, 0 < len i) → (∀ i, len i < delta / 3) → (∀ i, ray i 0 = qW) →
                                                  (∀ i, ∀ s ∈ Icc 0 (len i), ∀ t ∈ Icc 0 (len i),
                                                    dist (ray i s) (ray i t) = |s - t|) →
                                                  ∃ K : DifferentialGeometry.Toponogov.AngleKernel ι,
                                                    (∀ i j, K.angle i j = DifferentialGeometry.Toponogov.limitingRadialAngle
                                                      len (fun i => ray i) i j) ∧
                                                    let _ := K.metricSpace
                                                    TotallyBounded (univ : Set (Quotient K.setoid)) ∧
                                                      CompactSpace (UniformSpace.Completion (Quotient K.setoid)) := by
  obtain ⟨epsStar, c, hepsStar, hc, hproduce⟩ :=
    exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks.{u}
      hkappa (A := A) hA (alpha := alpha / 2) (by positivity) (by linarith only [hsmall])
  refine ⟨epsStar, c, hepsStar, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, hquant, hnecks⟩ :=
      hproduce eps heps hle sigma hsigma Phi hPhi X hnot
  clear hproduce
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  have hnecks' : ∀ᶠ tau : Ico 0 F.radius in
      comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius),
      Nonempty (SpatialNeck L.metric alpha (g tau)) := by
    simpa only [mul_div_cancel₀ alpha (by norm_num : (2 : ℝ) ≠ 0)] using hnecks
  have hnecksWide : ∀ᶠ tau : Ico 0 F.radius in
      comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius),
      Nonempty (SpatialNeck L.metric (2 * alpha) (g tau)) :=
    hnecks'.mono fun _ hn => hn.map
      (fun nk => nk.mono (by linarith only [ha]) (by linarith only [hsmall]))
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, ?_⟩
  refine ⟨phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow, q, hq, hdist, hmissing,
    hquant, hnecksWide, ?_⟩
  exact exists_spatialNeck_sequence_with_punctured_completion L.metric (fun _ _ => rfl) F.radius_pos ha hsmall
    hsec g hg hblow q hq hnecks'


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
