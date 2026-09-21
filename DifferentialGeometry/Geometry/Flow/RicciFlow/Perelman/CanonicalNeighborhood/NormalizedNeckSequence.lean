import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLimitNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocallyFinite
import DifferentialGeometry.Topology.Homeomorph.CylinderChain
import DifferentialGeometry.Topology.Homeomorph.Interior
import DifferentialGeometry.Topology.LocallyFinite.Frontier
import Mathlib.Topology.Compactness.LocallyFinite
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
                                    ∃ D : Sphere 2 × Ioi (0 : ℝ) ≃ₜ
                                      interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                                      ∀ (p : Sphere 2) (s : Ioi (0 : ℝ)),
                                        (D (p, s) : L.M) =
                                          (E (p, Set.inclusion Ioi_subset_Ici_self s) : L.M) := by
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
  obtain ⟨t, nk, _ht0, hmono, hlim, hstep, _hcover, hgraph, hdisjoint, eta, ann, hannuli, hsep, hinterior, hinter, hseam⟩ :=
    exists_spatialNeck_sequence_along_isometric_curve L.metric har (by linarith) curve hcurve
      (fun tau => (hgood (incl tau) tau.property.1).2) hquant'
  have htend : Tendsto (incl ∘ t) atTop
      (comap (Subtype.val : Ico 0 F.radius → ℝ) (𝓝 F.radius)) :=
    tendsto_comap_iff.mpr hlim
  have hscalar : Tendsto (fun n => metricScalarAt L.metric (g (incl (t n)))) cofinite atTop := by
    rw [Nat.cofinite_eq_atTop]
    exact hblow.comp htend
  have hlocal := SpatialNeck.locallyFinite_of_scalar_tendsto_atTop nk
    (eta := 2 * alpha) (by linarith : 2 * alpha < 1 / 4323) (fun _ => le_rfl) hscalar
  have hsource := fun n => (hannuli n).1
  have hleft := fun n => (hannuli n).2.1
  have hright := fun n => (hannuli n).2.2.1
  have hcann := fun n => (hannuli n).2.2.2.1
  have hfrann := fun n => (hannuli n).2.2.2.2.1
  have hsubann := fun n => (hannuli n).2.2.2.2.2.1
  have hlocalAnn := hlocal.subset hsubann
  have hclosedAnn := hlocalAnn.isClosed_iUnion (fun n => (hcann n).isClosed)
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  have hconnAnn (n : ℕ) : IsConnected (ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    (isConnected_univ.prod (isConnected_Icc zero_le_one)).image _
      ((ann n).contMDiffOn_toFun.continuousOn.mono (hsource n))
  have hmeetAnn (n : ℕ) : ((ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
      (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))).Nonempty := by
    let p : Sphere 2 := Classical.choice inferInstance
    refine ⟨ann n (p, 1), ⟨(p, 1), ⟨mem_univ _, by simp⟩, rfl⟩,
      ⟨(eta n p, 0), ⟨mem_univ _, by simp⟩, ?_⟩⟩
    rw [hleft, hright]
  have hconnUnion := IsConnected.iUnion_of_chain hconnAnn hmeetAnn
  have hlocalShift (k : ℕ) := hlocalAnn.comp_injective
    (g := fun n : ℕ => n + k) (fun _ _ hij => Nat.add_right_cancel hij)
  have hnotCompact (k : ℕ) : ¬ IsCompact (⋃ n, ann (n + k) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    intro hc
    apply (Set.infinite_univ : (univ : Set ℕ).Infinite)
    apply ((hlocalShift k).finite_nonempty_inter_compact hc).subset
    intro n _
    obtain ⟨y, hy⟩ := (hconnAnn (n + k)).nonempty
    exact ⟨y, hy, mem_iUnion.mpr ⟨n, hy⟩⟩
  have hfrontAnn : frontier (⋃ n, ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
      ⋃ n, (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) := by
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hlocalAnn.frontier_iUnion_subset hy)
    rw [hfrann n] at hn
    rcases hn with hn | hn
    · exact mem_iUnion.mpr ⟨n, hn⟩
    · exact mem_iUnion.mpr ⟨n + 1, hn⟩
  have hclosedTail := (hlocalShift 1).isClosed_iUnion (fun n => (hcann (n + 1)).isClosed)
  have hconnTail := IsConnected.iUnion_of_chain (fun n => hconnAnn (n + 1))
    (fun n => hmeetAnn (n + 1))
  have hfrontTail := hlocalAnn.frontier_iUnion_succ_eq_of_chain _
    (fun n => (hcann n).isClosed) hfrann hseam (fun n => hsep 0 (n + 2) (by omega))
  have hstart : g (incl (t 2)) ∈ interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    apply interior_mono (union_subset (subset_iUnion (fun n => ann (n + 1) ''
      (univ ×ˢ Icc (0 : ℝ) 1)) 0) (subset_iUnion (fun n => ann (n + 1) ''
        (univ ×ˢ Icc (0 : ℝ) 1)) 1))
    apply hseam 0
    exact ⟨((nk 2).center, 0), ⟨mem_univ _, rfl⟩, (nk 2).center_eq⟩
  have haxisTail : ∀ v : Ico 0 F.radius, (t 2 : ℝ) ≤ v →
      g v ∈ interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    have hI : IsPreconnected (Ici (incl (t 2))) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have heq : Subtype.val '' Ici (incl (t 2)) = Ico (t 2 : ℝ) F.radius := by
        ext v
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨hw, w.property.2⟩
        · intro hv
          exact ⟨⟨v, (incl (t 2)).property.1.trans hv.1, hv.2⟩, hv.1, rfl⟩
      rw [heq]
      exact isPreconnected_Ico
    have hP : IsPreconnected (g '' Ici (incl (t 2))) :=
      hI.image _ g.continuous.continuousOn
    have havoid : Disjoint (g '' Ici (incl (t 2)))
        (frontier (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨v, hv, rfl⟩ hz
      rw [hfrontTail] at hz
      have hb := (nk 1).central_sphere_subset_closedBall hz
      change edist (g (incl (t 1))) (g v) ≤
        ENNReal.ofReal (7 / Real.sqrt (metricScalarAt L.metric (g (incl (t 1))))) at hb
      have hv' : (t 2 : ℝ) ≤ (v : ℝ) := hv
      have ht12 := hmono (by norm_num : (1 : ℕ) < 2)
      rw [hg.edist_eq, edist_dist, Subtype.dist_eq, Real.dist_eq] at hb
      change ENNReal.ofReal |(t 1 : ℝ) - v| ≤ _ at hb
      rw [abs_of_nonpos (sub_nonpos.mpr (ht12.le.trans hv')), neg_sub] at hb
      have hreal := (ENNReal.ofReal_le_ofReal_iff
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 7) (Real.sqrt_nonneg _))).mp hb
      have hi : (1000000 : ℝ) < (2 * alpha)⁻¹ :=
        (lt_inv_comm₀ (by norm_num) (by positivity : 0 < 2 * alpha)).mpr
          (by norm_num only [one_div]; linarith)
      have hnum : (7 : ℝ) < (2 * alpha)⁻¹ / 40 := by linarith
      have hd := div_lt_div_of_pos_right hnum (Real.sqrt_pos.mpr (nk 1).Q_pos)
      have hstep1 := hstep 1
      change (t 2 : ℝ) - t 1 = ((2 * alpha)⁻¹ / 40) /
        Real.sqrt (metricScalarAt L.metric (g (incl (t 1)))) at hstep1
      change (v : ℝ) - (t 1 : ℝ) ≤ _ at hreal
      change 7 / Real.sqrt (metricScalarAt L.metric (g (incl (t 1)))) <
        ((2 * alpha)⁻¹ / 40) / Real.sqrt (metricScalarAt L.metric (g (incl (t 1)))) at hd
      linarith
    have hsub := DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hP havoid ⟨g (incl (t 2)), ⟨incl (t 2), (show incl (t 2) ≤ incl (t 2) from le_rfl), rfl⟩, hstart⟩
    exact fun v hv => hsub ⟨v, hv, rfl⟩
  have hcollapse (n : ℕ) (x : L.M) (hx : x ∈ ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) :
      dist q (x : UniformSpace.Completion L.M) ≤ (11 / 5) * (F.radius - (t n : ℝ)) := by
    have hb := ((hannuli n).2.2.2.2.2.2 hx).1
    change edist (g (incl (t n))) x ≤ ENNReal.ofReal
      ((3 * (2 * alpha)⁻¹ / 100) / Real.sqrt (metricScalarAt L.metric (g (incl (t n))))) at hb
    rw [edist_dist] at hb
    have hD : (3 * (2 * alpha)⁻¹ / 100) /
        Real.sqrt (metricScalarAt L.metric (g (incl (t n)))) =
          (6 / 5) * ((t (n + 1) : ℝ) - t n) := by
      rw [hstep n]
      change _ = (6 / 5) * (((2 * alpha)⁻¹ / 40) /
        Real.sqrt (metricScalarAt L.metric (g (incl (t n)))))
      ring
    rw [hD] at hb
    have hstepNonneg : 0 ≤ (t (n + 1) : ℝ) - t n :=
      sub_nonneg.mpr (hmono.monotone (Nat.le_succ n))
    have hb' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hstepNonneg)).mp hb
    have htriangle := dist_triangle q
      (g (incl (t n)) : UniformSpace.Completion L.M) (x : UniformSpace.Completion L.M)
    rw [hdist, UniformSpace.Completion.dist_eq] at htriangle
    have hremain := (t (n + 1)).property.2
    change _ ≤ F.radius - (t n : ℝ) + dist (g (incl (t n))) x at htriangle
    linarith
  have hip : 0 < (2 * alpha)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) ha)
  have hfrontCompact : IsCompact
      (frontier (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
    rw [hfrontTail]
    apply ((isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod
      (isCompact_singleton : IsCompact ({0} : Set ℝ))).image_of_continuousOn
    apply (nk 1).map.contMDiffOn_toFun.continuousOn.mono
    intro z hz
    apply (nk 1).domain
    refine ⟨mem_univ _, ?_⟩
    have hz' : z.2 = 0 := hz.2
    rw [hz']
    exact ⟨neg_lt_zero.mpr hip, hip⟩
  have hwindowConn : ∀ᶠ n in cofinite, IsPreconnected
      ((nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) := by
    apply Filter.Eventually.of_forall
    intro n
    exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
      ((nk n).map.contMDiffOn_toFun.continuousOn.mono (nk n).domain)
  have hwindowMeet : ∀ᶠ n in cofinite,
      ((nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ∩
        interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))).Nonempty := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact ⟨g (incl (t n)),
      ⟨((nk n).center, 0), ⟨mem_univ _, neg_lt_zero.mpr hip, hip⟩, (nk n).center_eq⟩,
      haxisTail (incl (t n)) (hmono.monotone hn)⟩
  have hwindowCapture := hlocal.eventually_subset_interior_of_isCompact_frontier
    hfrontCompact hwindowConn hwindowMeet
  rw [Nat.cofinite_eq_atTop] at hwindowCapture
  let unit : Sphere 2 × Icc (0 : ℝ) 1 ≃ₜ (univ ×ˢ Icc (0 : ℝ) 1 : Set Cylinder) :=
    (((Homeomorph.Set.univ (Sphere 2)).symm).prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod univ (Icc (0 : ℝ) 1)).symm
  let e (n : ℕ) : Sphere 2 × Icc (0 : ℝ) 1 ≃ₜ
      (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    unit.trans ((ann (n + 1)).toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
      (hsource (n + 1)) rfl)
  have he (n : ℕ) (p : Sphere 2) (s : Icc (0 : ℝ) 1) :
      (e n (p, s) : L.M) = ann (n + 1) (p, s) := rfl
  have hseam' (n : ℕ) (p : Sphere 2) : (e n (p, ⟨1, by simp⟩) : L.M) =
      e (n + 1) ((eta (n + 1)).toHomeomorph p, ⟨0, by simp⟩) := by
    rw [he, he, hright, hleft]
    rfl
  have hinter' (n : ℕ) :
      (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
        (ann (n + 1 + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      range (fun p => (e n (p, ⟨1, by simp⟩) : L.M)) := by
    rw [hinter n]
    ext x
    constructor
    · rintro ⟨⟨p, z⟩, ⟨_, hz⟩, hp⟩
      have hz' : z = 0 := hz
      subst z
      obtain ⟨w, rfl⟩ := (eta (n + 1)).surjective p
      refine ⟨w, ?_⟩
      change (e n (w, ⟨1, by simp⟩) : L.M) = x
      rw [he, hright]
      exact hp
    · rintro ⟨p, hp⟩
      change (e n (p, ⟨1, by simp⟩) : L.M) = x at hp
      rw [he, hright] at hp
      exact ⟨(eta (n + 1) p, 0), ⟨mem_univ _, rfl⟩, hp⟩
  obtain ⟨E, theta, htheta0, htheta, hE⟩ :=
    DifferentialGeometry.Topology.exists_homeomorph_iUnion_of_cylinder_chain
      (fun n => ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) e
      (fun n => (eta (n + 1)).toHomeomorph) (fun n => (hcann (n + 1)).isClosed)
      (hlocalShift 1) hseam' hinter' (fun i j hij => hsep (i + 1) (j + 1) (by omega))
  have hEzero (p : Sphere 2) : (E (p, ⟨0, by norm_num⟩) : L.M) = (nk 1).map (p, 0) := by
    have hz := hE 0 p ⟨0, by simp⟩
    rw [htheta0] at hz
    simpa only [Nat.cast_zero, zero_add, Homeomorph.refl_apply, he, hleft, id_eq] using hz
  have hfrontE : frontier (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      range (fun p => (E (p, ⟨0, by norm_num⟩) : L.M)) := by
    rw [hfrontTail]
    ext x
    constructor
    · rintro ⟨⟨p, z⟩, ⟨_, hz⟩, hp⟩
      have hz' : z = 0 := hz
      subst z
      exact ⟨p, (hEzero p).trans hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, (hEzero p).symm.trans hp⟩
  let D := E.restrictProdIoi hfrontE
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, ?_, hnecks, incl ∘ t, nk, hmono, hlim, hstep, hgraph, hdisjoint,
    hlocal, eta, ann, hannuli, hsep, hinterior, hinter, hseam, hlocalAnn, hclosedAnn,
    hconnUnion, hnotCompact 0, hfrontAnn, hclosedTail, hconnTail, hnotCompact 1, hfrontTail,
    haxisTail, hcollapse, hwindowCapture, E, theta, htheta0, htheta, ?_, D, ?_⟩
  · intro tau hR
    exact (pow_le_pow_left₀ hA (le_max_left A (2 * alpha)⁻¹) 2).trans (hquant tau hR)
  · intro n p s
    exact (hE n p s).trans (he n (theta n p) s)
  · intro p s
    exact E.restrictProdIoi_apply_coe hfrontE p s

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
