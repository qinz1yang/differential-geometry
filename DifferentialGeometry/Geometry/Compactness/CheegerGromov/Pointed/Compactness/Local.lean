import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.RestrictionDistance
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.DirectLimit.Distance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Pullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CompatibleChainLimits
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff Topology
open Set TopologicalSpace Filter Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

open private riemannianEDistOf_restrictOpen_le_pathELength from
  DifferentialGeometry.Geometry.Metric.RestrictionDistance

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [I.Boundaryless] in
private theorem restrict_center_distance
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (g : SmoothRiemannianMetric I N) (U : Opens N) [T2Space U]
    (p : U) {r : ℝ} (hball : riemannianBallOf g p.val r ⊆ U)
    (y : U) (hy : riemannianEDistOf g p.val y.val < ENNReal.ofReal r) :
    riemannianEDistOf (g.restrictOpen U) p y = riemannianEDistOf g p.val y.val := by
  apply le_antisymm
  · let _ : RiemannianBundle (TangentSpace I : N → Type _) := ⟨g.toRiemannianMetric⟩
    by_contra hnot
    have hd : riemannianEDistOf g p.val y.val < riemannianEDistOf (g.restrictOpen U) p y :=
      lt_of_not_ge hnot
    obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt (lt_min hd hy)
    have hshort := hlength.trans_le (min_le_right _ _)
    have hmem : MapsTo γ (Icc 0 1) U := by
      intro t ht
      apply hball
      have hprefix := Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h0 rfl ht.1
      exact (hprefix.trans (Manifold.pathELength_mono le_rfl ht.2)).trans_lt hshort
    have hh := riemannianEDistOf_restrictOpen_le_pathELength g U hγ hmem h0 h1
    exact (not_lt_of_ge hh) (hlength.trans_le (min_le_left _ _))
  · exact riemannianEDistOf_le_restrictOpen g U p y

omit [I.Boundaryless] in
private theorem metricCInf_inner_le
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    (G : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts G gInf gRef)
    (x : M) (v w : TangentSpace I x) (B : ℝ)
    (hbound : ∀ᶠ k in atTop, (G k).inner x v w ≤ B) : gInf.inner x v w ≤ B :=
  le_of_tendsto (metricCInf_inner G gInf gRef hconv x v w) hbound

omit [I.Boundaryless] in
private theorem chain_limit_inner_upper_of_approximation
    {M : ℕ → Type*} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (g : ∀ j, SmoothRiemannianMetric I (M j)) {j : ℕ} (U : Opens (M j))
    (hU : ∀ l, (U : Set (M j)) ⊆ (chainComp Ψ j l).source)
    {K : Set (M j)} (hUK : (U : Set (M j)) ⊆ K) (eta : ℝ)
    (happrox : ∀ l, Nonempty (PartialDiffeomorphMetricApproximation K eta 0
      (chainComp Ψ j l) (g j) (g (j + l))))
    (φ : ℕ → ℕ) (gInf gRef : SmoothRiemannianMetric I U)
    (hconv : MetricCInfConvergenceOnCompacts
      (fun k => chainPullbackSeq Ψ g U hU (φ k - j)) gInf gRef)
    (x : U) (v : TangentSpace I x) :
    gInf.inner x v v ≤ (1 + eta) * ((g j).restrictOpen U).inner x v v := by
  apply metricCInf_inner_le _ gInf gRef hconv x v v
  apply Filter.Eventually.of_forall
  intro k
  obtain ⟨D⟩ := happrox (φ k - j)
  exact pullback_metric_inner_upper (chainComp Ψ j (φ k - j)) U (hU (φ k - j))
    hUK (g j) (g (j + (φ k - j))) D.forward x v


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pointed_convergence_within_radius_and_radial_bound
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) {rho : ℝ} (hrho : 0 < rho)
    (hB : ∀ r : ℝ, 0 < r → r < rho → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : ℕ → ℝ,
      (∀ k, 0 < r k ∧ r k < rho) ∧ Tendsto r atTop (nhds rho) ∧
      ∃ L : PointedRiemannianManifold.{u, uE, uH} (I := I),
      ∃ Φ : PointedRiemannianConvergenceMaps (I := I) X L σ,
        ∃ C : PointedRiemannianConverges (I := I) X L σ Φ,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k) ∧
        (∀ k,
          letI : MetricSpace (X.obj (σ k)).M := (P (σ k)).ms
          Φ.target k = Metric.ball (X.obj (σ k)).basepoint (r k)) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ Φ.source k, ∀ v : TangentSpace I x,
            (1 - ε) * L.metric.inner x v v ≤
              (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
                (mfderiv I I (Φ.partialDiffeomorph k) x v)
                (mfderiv I I (Φ.partialDiffeomorph k) x v) ∧
            (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
                (mfderiv I I (Φ.partialDiffeomorph k) x v)
                (mfderiv I I (Φ.partialDiffeomorph k) x v) ≤
              (1 + ε) * L.metric.inner x v v := by
  classical
  obtain ⟨σ, hσ, r, eta, hr, hrT, _hetaT, hdir⟩ :=
    exists_directed_approximate_isometry_subsequence_within_radius (I := I) P hrho hB
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  obtain ⟨Ψ, hbase, hdata⟩ := hdir
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  let : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  let : ∀ j, RiemannianBundle (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  let : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  have hnorm : ∀ j (x : (X.obj (σ j)).M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)) := by
    intro j x v
    with_unfolding_all exact
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (g j) x v)
  have hrmono : StrictMono r := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hs : 1 ≤ Real.sqrt (1 + eta j) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + eta j by linarith [(hr j).2.2.1])
    exact (show r j ≤ Real.sqrt (1 + eta j) * r j by nlinarith [(hr j).1]).trans_lt
      (hr j).2.2.2.2
  have happrox : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b j) (r j)) δ p
          (chainComp (I := I) Ψ j l) (g j) (g (j + l))) := by
    intro δ hδ hδ1 p
    obtain ⟨J, hJ⟩ := hdata δ hδ hδ1 p
    refine ⟨J, fun j hj l => ?_⟩
    obtain ⟨D⟩ := hJ j hj l
    exact ⟨D.toMetricApproximation hδ hδ1 (min_le_left _ _) le_rfl⟩
  have himages : ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ a : ℕ, 1 ≤ a →
      (chainComp (I := I) Ψ j a : (X.obj (σ j)).M → (X.obj (σ (j + a))).M) ''
        Metric.ball (b j) (r j) ⊆ Metric.ball (b (j + a)) (r (j + a)) := by
    obtain ⟨J, hJ⟩ := hdata (1 / 2) (by norm_num) (by norm_num) 0
    refine ⟨J, fun j hj a ha => ?_⟩
    obtain ⟨D⟩ := hJ j hj a
    have De := D.toMetricApproximationZero (hr j).2.2.1 (hr j).2.2.2.1
      (min_le_right _ _)
    have hR : Real.sqrt (1 + eta j) * r j < r (j + a) :=
      (hr j).2.2.2.2.trans_le (hrmono.monotone (by omega))
    have Dball : MapMetricApproximationOn (I := I)
        (Metric.closedEBall (b j) (ENNReal.ofReal (r j))) (eta j) 0
        (chainComp (I := I) Ψ j a) (g j) (g (j + a)) := by
      rw [Metric.closedEBall_ofReal (hr j).1.le]
      exact De.forward
    have hsource : Metric.closedEBall (b j) (ENNReal.ofReal (r j)) ⊆
        (chainComp (I := I) Ψ j a).source := by
      rw [Metric.closedEBall_ofReal (hr j).1.le]
      exact De.source_sub
    have himg := MapMetricApproximationOn.image_metric_ball_subset (I := I)
      (chainComp (I := I) Ψ j a) (hnorm j) (hnorm (j + a))
      (hr j).1 le_rfl (hr j).2.2.1.le hR Dball hsource
    simpa only [chainComp_base (I := I) Ψ b hbase j a] using himg
  obtain ⟨j₀, _hj₀, _D0, hU, hmap, φ, _hφ, gInf, hconv, hclose, hstep⟩ :=
    exists_compatible_chain_pullback_metric_limits_on_balls (I := I) b Ψ g r
      (fun j => (hr j).1) happrox himages
  let U : ∀ n, Opens (X.obj (σ (j₀ + n))).M := fun n => ballOpen b r (j₀ + n)
  let O : ∀ n, U n := fun n => ⟨b (j₀ + n), Metric.mem_ball_self (hr (j₀ + n)).1⟩
  let : ∀ n, Nonempty (U n) := fun n => ⟨O n⟩
  let : ∀ n, SigmaCompactSpace (U n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
  have hcenter : ∀ n, S.toSeqSystem.map (Nat.zero_le n) (O 0) = O n := by
    intro n
    induction n with
    | zero => exact S.toSeqSystem.map_self 0 (O 0)
    | succ n ih =>
        have hsucc : S.toSeqSystem.map (Nat.le_succ n) =
            PartialDiffeomorph.opensMap (chainComp (I := I) Ψ (j₀ + n) 1) (hmap n) := by
          unfold S chainBallSystem SmoothSeqSystem.ofPartialDiffeomorphs
          apply SmoothSeqSystem.ofSucc_map_succ
        calc
          S.toSeqSystem.map (Nat.zero_le (n + 1)) (O 0) =
              S.toSeqSystem.map (Nat.le_succ n) (S.toSeqSystem.map (Nat.zero_le n) (O 0)) :=
            (S.toSeqSystem.map_map (Nat.zero_le n) (Nat.le_succ n) (O 0)).symm
          _ = S.toSeqSystem.map (Nat.le_succ n) (O n) := by rw [ih]
          _ = O (n + 1) := by
            rw [hsucc]
            apply Subtype.ext
            exact chainComp_base (I := I) Ψ b hbase (j₀ + n) 1
  let hgInf := chain_metric_cocycle (I := I) j₀ U Ψ hU hmap gInf hstep
  let L := pointedDirectLimitOfMetricCocycle S (O 0) gInf hgInf
  let C := chainAmbientPointedRiemannianConvergence (I := I) j₀ U Ψ g hU hmap
    gInf hstep hclose (O 0)
  let σtail := fun n => σ (j₀ + n)
  let XTail := X.subseq σtail
  let bTail : ∀ n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.map (Nat.zero_le n) (O 0) : (X.obj (σtail n)).M)
  let Φr : PointedRiemannianConvergenceMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianConvergenceMaps (I := I)
      (chainAmbientSeq (I := I) j₀ U S (O 0) g) L id
    exact chainAmbientMaps (I := I) j₀ U S (O 0) g gInf hgInf
  have hbase' : ∀ n,
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      let : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    with_unfolding_all
      change ((Function.invFun (S.toSeqSystem.incl n) (S.toSeqSystem.incl 0 (O 0)) : U n) :
        (X.obj (σtail n)).M) = (X.obj (σtail n)).basepoint
    have hfirst := congrArg Subtype.val (S.invIncl_incl_le (Nat.zero_le n) (O 0))
    with_unfolding_all rw [hfirst]
    exact congrArg Subtype.val (hcenter n)
  let Cr : PointedRiemannianConverges (I := I) (XTail.repoint bTail) L id Φr := by
    change PointedRiemannianConverges (I := I)
      (chainAmbientSeq (I := I) j₀ U S (O 0) g) L id
      (chainAmbientMaps (I := I) j₀ U S (O 0) g gInf hgInf)
    exact C
  let Cu := (Cr.unrepoint bTail hbase').ofSubseq σtail
  have hradial : ∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho := by
    obtain ⟨J, hJ⟩ := hdata (1 / 2) (by norm_num) (by norm_num) 0
    intro x
    obtain ⟨m, z, hz⟩ := S.toSeqSystem.exists_incl_eq x
    let n := max m J
    let y : U n := S.toSeqSystem.map (le_max_left m J) z
    have hy : S.toSeqSystem.incl n y = x := (S.toSeqSystem.incl_comp (le_max_left m J) z).trans hz
    have hn : J ≤ j₀ + n := by dsimp [n]; omega
    have hbound (q : U n) (v : TangentSpace I q) :
        (gInf n).inner q v v ≤ (1 + eta (j₀ + n)) *
          ((g (j₀ + n)).restrictOpen (U n)).inner q v v := by
      apply chain_limit_inner_upper_of_approximation Ψ g (U n) (hU n)
        (fun q hq => Metric.ball_subset_closedBall hq) (eta (j₀ + n)) ?_ φ (gInf n)
        ((g (j₀ + n)).restrictOpen (U n)) (hconv n) q v
      intro l
      obtain ⟨D⟩ := hJ (j₀ + n) hn l
      exact ⟨D.toMetricApproximationZero (hr (j₀ + n)).2.2.1 (hr (j₀ + n)).2.2.2.1 (min_le_right _ _)⟩
    have hloc : IsLocalDiffeomorph I I ∞ (S.toSeqSystem.incl n) := fun q =>
      (S.inclPartialDiffeo n).symm.isLocalDiffeomorphAt I I ∞ (show q ∈ Set.univ from Set.mem_univ q)
    have hbaseIncl : S.toSeqSystem.incl n (O n) = L.basepoint := by
      change S.toSeqSystem.incl n (O n) = S.toSeqSystem.incl 0 (O 0)
      rw [← hcenter n]
      exact S.toSeqSystem.incl_comp (Nat.zero_le n) (O 0)
    have hdist := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
      ((g (j₀ + n)).restrictOpen (U n)) L.metric (S.toSeqSystem.incl n) hloc
      (c := 1 + eta (j₀ + n)) (by linarith [(hr (j₀ + n)).2.2.1])
      (fun q v => by rw [S.limitMetric_pullback gInf hgInf n q v v]; exact hbound q v) (O n) y
    rw [hbaseIncl, hy] at hdist
    have hball : riemannianBallOf (g (j₀ + n)) (b (j₀ + n)) (r (j₀ + n)) ⊆ U n := by
      intro q hq
      change dist q (b (j₀ + n)) < r (j₀ + n)
      have hreal := (P (σ (j₀ + n))).realizes (b (j₀ + n)) q
      change riemannianEDistOf (g (j₀ + n)) (b (j₀ + n)) q = ENNReal.ofReal (dist (b (j₀ + n)) q) at hreal
      change riemannianEDistOf (g (j₀ + n)) (b (j₀ + n)) q < ENNReal.ofReal (r (j₀ + n)) at hq
      rw [hreal] at hq
      rw [dist_comm]
      exact (ENNReal.ofReal_lt_ofReal_iff (hr (j₀ + n)).1).mp hq
    have hyball : riemannianEDistOf (g (j₀ + n)) (O n).val y.val < ENNReal.ofReal (r (j₀ + n)) := by
      have hreal := (P (σ (j₀ + n))).realizes (b (j₀ + n)) y.val
      change riemannianEDistOf (g (j₀ + n)) (b (j₀ + n)) y.val = ENNReal.ofReal (dist (b (j₀ + n)) y.val) at hreal
      rw [hreal]
      apply (ENNReal.ofReal_lt_ofReal_iff (hr (j₀ + n)).1).mpr
      have hyprop : dist y.val (b (j₀ + n)) < r (j₀ + n) := y.property
      simpa only [dist_comm] using hyprop
    rw [restrict_center_distance (g (j₀ + n)) (U n) (O n) hball y hyball] at hdist
    apply hdist.trans_lt
    have hsq : 0 < Real.sqrt (1 + eta (j₀ + n)) := Real.sqrt_pos.mpr (by linarith [(hr (j₀ + n)).2.2.1])
    calc
      _ < ENNReal.ofReal (Real.sqrt (1 + eta (j₀ + n))) * ENNReal.ofReal (r (j₀ + n)) :=
        (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr hsq) ENNReal.ofReal_ne_top).mpr hyball
      _ = ENNReal.ofReal (Real.sqrt (1 + eta (j₀ + n)) * r (j₀ + n)) := (ENNReal.ofReal_mul hsq.le).symm
      _ < ENNReal.ofReal rho := (ENNReal.ofReal_lt_ofReal_iff hrho).mpr
        ((hr (j₀ + n)).2.2.2.2.trans (hr (j₀ + n + 1)).2.1)
  have htail : StrictMono (fun n : ℕ => j₀ + n) := fun a b hab => Nat.add_lt_add_left hab j₀
  refine ⟨σtail, hσ.comp htail, fun n => r (j₀ + n),
    fun n => ⟨(hr (j₀ + n)).1, (hr (j₀ + n)).2.1⟩,
    hrT.comp htail.tendsto_atTop, L, _, Cu, (fun n => ?_), (fun n => ?_), hradial, ?_⟩
  · with_unfolding_all rfl
  · change (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).target =
      Metric.ball (b (j₀ + n)) (r (j₀ + n))
    rfl
  · intro ε hε
    obtain ⟨N, hN⟩ := hclose ε hε 0
    refine ⟨N, fun n hn => ?_⟩
    have hb := chain_ambient_map_inner_bounds (I := I) j₀ U S (O 0) g gInf hgInf n
      (fun x => by
        simpa only [chain_pullback_zero] using hN n hn 0 0 le_rfl x)
    with_unfolding_all exact hb


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pointed_convergence_within_radius
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) {rho : ℝ} (hrho : 0 < rho)
    (hB : ∀ r : ℝ, 0 < r → r < rho → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : ℕ → ℝ,
      (∀ k, 0 < r k ∧ r k < rho) ∧ Tendsto r atTop (nhds rho) ∧
      ∃ L : PointedRiemannianManifold.{u, uE, uH} (I := I),
      ∃ Φ : PointedRiemannianConvergenceMaps (I := I) X L σ,
        ∃ C : PointedRiemannianConverges (I := I) X L σ Φ,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k) ∧
        (∀ k,
          letI : MetricSpace (X.obj (σ k)).M := (P (σ k)).ms
          Φ.target k = Metric.ball (X.obj (σ k)).basepoint (r k)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ Φ.source k, ∀ v : TangentSpace I x,
            (1 - ε) * L.metric.inner x v v ≤
              (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
                (mfderiv I I (Φ.partialDiffeomorph k) x v)
                (mfderiv I I (Φ.partialDiffeomorph k) x v) ∧
            (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
                (mfderiv I I (Φ.partialDiffeomorph k) x v)
                (mfderiv I I (Φ.partialDiffeomorph k) x v) ≤
              (1 + ε) * L.metric.inner x v v := by
  obtain ⟨sigma, hsigma, r, hr, hrlim, L, maps, C, hcanonical, htargets, _, hbounds⟩ :=
    exists_pointed_convergence_within_radius_and_radial_bound P hrho hB
  exact ⟨sigma, hsigma, r, hr, hrlim, L, maps, C, hcanonical, htargets, hbounds⟩

end DifferentialGeometry.CheegerGromovCompactness
