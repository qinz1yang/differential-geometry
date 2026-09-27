import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.AncientPointedFlowLimit

set_option autoImplicit false

noncomputable section
open Set Filter Manifold TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open private mfderiv_codRestrict_restrict isLocalDiffeomorph_codRestrict_restrict from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.AncientPointedFlowLimit

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_local_flow_limits_of_pointed_convergence_of_local_solutions
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hcomplete : MetricComplete P) (hconn : ConnectedSpace P.M)
    (τ c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcτ : ∀ k, c k < τ k)
    (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
    (h : ∀ k n, ℝ → SmoothRiemannianMetric I (W k n))
    (hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆ W k n)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr ((hc k).trans (hcτ k)).le))))
    (hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n))
    (hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n t) x ≤ B)
    (hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, t ∈ Icc (-c l) 0 →
      (h k n t).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n t).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n)) :
    ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
      (∀ k, (V k : Set P.M) =
        riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
      (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
      ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
        (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I I ∞ (φ k j hj)),
        (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
          F.map j z) ∧
        ∃ Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric I (V k),
          (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
          (∀ k, IsSolutionOn ({ base.metric := Gloc k } : SolutionOn (I := I) (M := V k)
            (RealTimeInterval.closed (-c k) 0 (neg_nonpos.mpr (hc k).le)))) ∧
          (∀ k l, ∀ t ∈ Icc (-c k) 0, t ∈ Icc (-c l) 0 →
            (Gloc k t).restrictOpenOfSubset (inf_le_left : V k ⊓ V l ≤ V k) =
              (Gloc l t).restrictOpenOfSubset (inf_le_right : V k ⊓ V l ≤ V l)) ∧
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
              ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
                metricDerivNormSupOn K p
                  (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                  (Gloc k t) (P.metric.restrictOpen (V k)) < η := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ∀ k n, SigmaCompactSpace (W k n) := fun k n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I (W k n).isOpen)
  obtain ⟨Cd, hCd, href⟩ := exists_metricConvergenceData_canonicalSourceData F (by
    intro K hK p eps heps
    obtain ⟨k0, hk0⟩ := C.converges K hK p eps heps
    exact ⟨k0, fun k hk => by rw [← hcanonical k]; exact (hk0 k hk).2⟩)
  let r : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) / 2
  have hr (k : ℕ) : 0 ≤ r k := by positivity
  have hrk (k : ℕ) : 3 / 2 * r k ≤ ((k + 1 : ℕ) : ℝ) := by
    dsimp only [r]
    have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hrow (k : ℕ) : ∀ᶠ j in atTop,
      (riemannianClosedBallOf P.metric P.basepoint (r k) ⊆ F.source j ∧
        F.map j '' riemannianClosedBallOf P.metric P.basepoint (r k) ⊆
          riemannianClosedBallOf (X.obj (f j)).metric (F.map j P.basepoint) (3 / 2 * r k)) ∧
      riemannianClosedBallOf (X.obj (f j)).metric (X.obj (f j)).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k (f j) ∧
      IsSolutionOn ({ base.metric := h k (f j) } : SolutionOn (I := I) (M := W k (f j))
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr ((hc k).trans (hcτ k)).le))) ∧
      h k (f j) 0 = (X.obj (f j)).metric.restrictOpen (W k (f j)) :=
    (F.eventually_image_closed_ball_subset Cd href hcomplete P.basepoint (hr k)
      (by norm_num : (1 : ℝ) < 3 / 2)).and
      ((hf.tendsto_atTop.eventually (hball k)).and
        ((hf.tendsto_atTop.eventually (hsol k)).and (hf.tendsto_atTop.eventually (hzero k))))
  choose N hN using fun k => eventually_atTop.mp (hrow k)
  let _ : ConnectedSpace P.M := hconn
  have hVopen (k : ℕ) : IsOpen (riemannianBallOf P.metric P.basepoint (r k)) :=
    isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
  let V : ℕ → Opens P.M := fun k => ⟨riemannianBallOf P.metric P.basepoint (r k), hVopen k⟩
  have hVball (k : ℕ) (z : P.M) (hz : z ∈ V k) :
      z ∈ riemannianClosedBallOf P.metric P.basepoint (r k) := by
    have h1 : riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal (r k) := hz
    exact le_of_lt h1
  have hsrc (k j : ℕ) (hj : N k ≤ j) : (V k : Set P.M) ⊆ F.source j :=
    fun z hz => (hN k j hj).1.1 (hVball k z hz)
  have himg (k j : ℕ) (hj : N k ≤ j) (z : V k) :
      F.map j z ∈ riemannianClosedBallOf (X.obj (f j)).metric (X.obj (f j)).basepoint
        ((k + 1 : ℕ) : ℝ) := by
    have h1 := (hN k j hj).1.2 ⟨z, hVball k z z.property, rfl⟩
    have hb : F.map j P.basepoint = (X.obj (f j)).basepoint := F.basepoint_map j
    rw [hb] at h1
    exact riemannianClosedBallOf_mono _ _ (hrk k) h1
  have hmem (k j : ℕ) (hj : N k ≤ j) (z : V k) : (F.partialDiffeomorph j) z ∈ W k (f j) :=
    (hN k j hj).2.1 (himg k j hj z)
  let φ : ∀ k j, N k ≤ j → V k → W k (f j) := fun k j hj z =>
    ⟨F.partialDiffeomorph j z, hmem k j hj z⟩
  have hφ (k j : ℕ) (hj : N k ≤ j) : IsLocalDiffeomorph I I ∞ (φ k j hj) :=
    isLocalDiffeomorph_codRestrict_restrict (F.partialDiffeomorph j) (V k) (hsrc k j hj)
      (W k (f j)) (hmem k j hj)
  have hdφ (k j : ℕ) (hj : N k ≤ j) (z : V k) (v : TangentSpace I z) :
      mfderiv I I (φ k j hj) z v = mfderiv I I (F.partialDiffeomorph j) z v :=
    mfderiv_codRestrict_restrict (F.partialDiffeomorph j) (V k) (hsrc k j hj) (W k (f j))
      (hmem k j hj) z v
  let D : ℕ → RealTimeInterval := fun k =>
    RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr ((hc k).trans (hcτ k)).le)
  let T : ∀ k j, N k ≤ j → SolutionOn (I := I) (M := V k) (D k) := fun k j hj =>
    SolutionOn.localPullback ({ base.metric := h k (f j) } :
      SolutionOn (I := I) (M := W k (f j)) (D k)) (φ k j hj) (hφ k j hj)
  have hTsol (k j : ℕ) (hj : N k ≤ j) : IsSolutionOn (T k j hj) :=
    (hN k j hj).2.2.1.localPullback _ _
  have hTcongr (k j j' : ℕ) (hj : N k ≤ j) (hj' : N k ≤ j') (hjj : j = j') :
      T k j hj = T k j' hj' := by
    subst hjj
    rfl
  have hinner (k j : ℕ) (hj : N k ≤ j) (t : ℝ) (z : V k) (v w : TangentSpace I z) :
      ((T k j hj).base.metric t).inner z v w =
        (h k (f j) t).inner (φ k j hj z) (mfderiv I I (F.partialDiffeomorph j) z v)
          (mfderiv I I (F.partialDiffeomorph j) z w) := by
    change (localPullMetric (h k (f j) t) (φ k j hj) (hφ k j hj)).inner z v w = _
    rw [localPullMetric_inner, hdφ k j hj, hdφ k j hj]
  let S : ∀ k, ℕ → SolutionOn (I := I) (M := V k) (D k) := fun k i =>
    T k (i + N k) (Nat.le_add_left _ _)
  have hterminal (k : ℕ) : MetricCInfConvergenceOnCompacts (fun i => (S k i).base.metric 0)
      (P.metric.restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
    apply metricCInfConvergenceOnCompacts_of_pointed_pullback F C hcanonical (V k) (N k)
      (fun i => hsrc k (i + N k) (Nat.le_add_left _ _))
    intro i z v w
    change ((T k (i + N k) (Nat.le_add_left _ _)).base.metric 0).inner z v w = _
    rw [hinner k (i + N k) (Nat.le_add_left _ _), (hN k (i + N k) (Nat.le_add_left _ _)).2.2.2]
    rfl
  have hcurv (k : ℕ) (K : Set (V k)) (_ : IsCompact K) (q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-c k) 0, ∀ x ∈ K,
        curvDerivNorm q ((S k i).base.metric t) x ≤ B := by
    obtain ⟨B, hB, hb⟩ := hjets k q
    refine ⟨B, hB, ?_⟩
    have htend : Tendsto (fun i => f (i + N k)) atTop atTop :=
      hf.tendsto_atTop.comp (tendsto_add_atTop_nat (N k))
    filter_upwards [htend.eventually hb] with i hi t ht x _
    change curvDerivNorm q (localPullMetric (h k (f (i + N k)) t)
      (φ k (i + N k) (Nat.le_add_left _ _)) (hφ k (i + N k) (Nat.le_add_left _ _))) x ≤ B
    rw [curvDerivNorm_localPullMetric]
    exact hi t ht _ (himg k (i + N k) (Nat.le_add_left _ _) x)
  have hcompatS : ∀ n m t, t ∈ Icc (-c n) 0 → t ∈ Icc (-c m) 0 →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : V n ⊓ V m ≤ V n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : V n ⊓ V m ≤ V m)) := by
    intro n m t htn htm
    filter_upwards [eventually_ge_atTop (N n), eventually_ge_atTop (N m),
      hf.tendsto_atTop.eventually (hcompat n m)] with i hin him hcp
    have e1 : S n (i - N n) = T n i hin :=
      hTcongr n _ _ (Nat.le_add_left _ _) hin (Nat.sub_add_cancel hin)
    have e2 : S m (i - N m) = T m i him :=
      hTcongr m _ _ (Nat.le_add_left _ _) him (Nat.sub_add_cancel him)
    rw [e1, e2]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    have hz : (h n (f i) t).inner (φ n i hin (Opens.inclusion inf_le_left z))
        (mfderiv I I (F.partialDiffeomorph i) z v) (mfderiv I I (F.partialDiffeomorph i) z w) =
      (h m (f i) t).inner (φ m i him (Opens.inclusion inf_le_right z))
        (mfderiv I I (F.partialDiffeomorph i) z v) (mfderiv I I (F.partialDiffeomorph i) z w) :=
      congrArg (fun q : SmoothRiemannianMetric I ↥(W n (f i) ⊓ W m (f i)) =>
        q.inner ⟨F.partialDiffeomorph i z, hmem n i hin (Opens.inclusion inf_le_left z),
          hmem m i him (Opens.inclusion inf_le_right z)⟩
          (mfderiv I I (F.partialDiffeomorph i) z v) (mfderiv I I (F.partialDiffeomorph i) z w))
        (hcp t htn htm)
    exact (hinner n i hin t (Opens.inclusion inf_le_left z) v w).trans
      (hz.trans (hinner m i him t (Opens.inclusion inf_le_right z) v w).symm)
  obtain ⟨ρ, hρ, g, hg0, hgsol, hgconv, hgcompat⟩ :=
    exists_common_compatible_solution_subsequence_on_open_sets_and_intervals_of_terminal_convergence
      V D S (fun k i => hTsol k (i + N k) (Nat.le_add_left _ _))
      (fun k => P.metric.restrictOpen (V k))
      (fun k => -c k) (fun _ => 0)
      (fun k => neg_neg_of_pos (hc k))
      (fun k t ht => ⟨(neg_le_neg (hcτ k).le).trans ht.1, ht.2⟩)
      (fun k t ht => ⟨(neg_lt_neg (hcτ k)).trans_le ht.1, ht.2⟩) hterminal hcurv N hcompatS
  refine ⟨V, N, fun k => rfl, hsrc, φ, hφ, fun k j hj z => rfl, g, hg0, hgsol, hgcompat, ρ, hρ,
    ?_⟩
  intro k K hK p η hη
  obtain ⟨j, hj⟩ := hgconv k K hK p η hη
  refine ⟨max j (N k), fun i hi => ?_⟩
  have hNi : N k ≤ ρ i := (le_max_right _ _).trans (hi.trans (hρ.id_le i))
  refine ⟨hNi, fun t ht => ?_⟩
  have h1 := hj i ((le_max_left _ _).trans hi) t ht
  rwa [show S k (ρ i - N k) = T k (ρ i) hNi from hTcongr k _ _ (Nat.le_add_left _ _) hNi
      (Nat.sub_add_cancel hNi)] at h1

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

universe v vE vH
variable {E : Type vE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] {H : Type vH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_pointed_local_flow_limits_of_local_solutions
    (X : PointedRiemannianSeq.{v, vE, vH} I)
    (hcompact : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hvol : ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a))
    (τ c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcτ : ∀ k, c k < τ k)
    (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
    (h : ∀ k n, ℝ → SmoothRiemannianMetric I (W k n))
    (hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆ W k n)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr ((hc k).trans (hcτ k)).le))))
    (hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n))
    (hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc (-c k) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n t) x ≤ B)
    (hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-c k) 0, t ∈ Icc (-c l) 0 →
      (h k n t).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n t).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n)) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{v, vE, vH} I) (F : PointedRiemannianConvergenceMaps X P f),
        (∃ C : MetricConvergenceData F,
          ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧
        (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
          riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆ F.target n) ∧
        ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
          (∀ k, (V k : Set P.M) =
            riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
          (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
          ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
            (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I I ∞ (φ k j hj)),
            (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
              F.map j z) ∧
            ∃ Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric I (V k),
              (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
              (∀ k, IsSolutionOn ({ base.metric := Gloc k } : SolutionOn (I := I) (M := V k)
                (RealTimeInterval.closed (-c k) 0 (neg_nonpos.mpr (hc k).le)))) ∧
              (∀ k l, ∀ t ∈ Icc (-c k) 0, t ∈ Icc (-c l) 0 →
                (Gloc k t).restrictOpenOfSubset (inf_le_left : V k ⊓ V l ≤ V k) =
                  (Gloc l t).restrictOpenOfSubset (inf_le_right : V k ⊓ V l ≤ V l)) ∧
              ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                  ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
                    metricDerivNormSupOn K p
                      (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                      (Gloc k t) (P.metric.restrictOpen (V k)) < η := by
  have hjetsX : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p C := by
    intro R _ p
    obtain ⟨k, hk⟩ := exists_nat_ge R
    have hRk : R ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    obtain ⟨B, hB, hb⟩ := hjets k p
    refine ⟨B, hB, ?_⟩
    filter_upwards [hb, hball k, hzero k] with n hn hbn hzn x hx
    have hxk : x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint
        ((k + 1 : ℕ) : ℝ) := riemannianClosedBallOf_mono _ _ hRk hx
    have h1 := hn 0 ⟨neg_nonpos.mpr (hc k).le, le_rfl⟩ ⟨x, hbn hxk⟩ hxk
    rw [hzn, curvDerivNorm_restrictOpen] at h1
    exact h1
  obtain ⟨f, hf, P, F, C, hC, hPc, hPconn, hcapture⟩ :=
    exists_pointed_convergence_on_base_components_of_eventually_compact_balls X hcompact hjetsX
      hvol
  let U := fun i => connectedComponentOpen (I := I) (X.obj i).basepoint
  let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
  let F' := F.liftTargetOpen U hp
  exact ⟨f, hf, P, F', ⟨C, hC⟩, hPc, hPconn, hcapture,
    exists_local_flow_limits_of_pointed_convergence_of_local_solutions hf F' C hC hPc hPconn
      τ c hc hcτ W h hball hsol hzero hjets hcompat⟩

end DifferentialGeometry.PDE.RicciFlow

end
