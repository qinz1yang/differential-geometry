import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.OpenExhaustion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.AncientGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.CompactBalls
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction

set_option autoImplicit false

noncomputable section
open Set Filter Manifold TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

omit [FiniteDimensional ℝ E] in
private theorem mfderiv_codRestrict_restrict {M N : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph I I M N ∞) (V : Opens M)
    (hV : (V : Set M) ⊆ Φ.source) (W : Opens N) (hW : ∀ z : V, Φ z ∈ W) (z : V)
    (v : TangentSpace I z) :
    mfderiv I I (fun y : V => (⟨Φ y, hW y⟩ : W)) z v = mfderiv I I Φ z v := by
  rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp W]
  have hval : MDifferentiableAt I I (Subtype.val : V → M) z :=
    (contMDiff_subtype_val (I := I) (U := V) (n := ∞)).mdifferentiableAt (by decide)
  have hmap := Φ.mdifferentiableAt (by decide) (hV z.property)
  have hc := mfderiv_comp_apply z hmap hval v
  simp only [mfderiv_subtype_val_apply] at hc
  exact hc

omit [FiniteDimensional ℝ E] in
private theorem isLocalDiffeomorph_codRestrict_restrict {M N : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph I I M N ∞) (V : Opens M)
    (hV : (V : Set M) ⊆ Φ.source) (W : Opens N) (hW : ∀ z : V, Φ z ∈ W) :
    IsLocalDiffeomorph I I ∞ (fun y : V => (⟨Φ y, hW y⟩ : W)) := by
  intro z
  apply DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (f := fun y : V => Φ y) hW
  exact DifferentialGeometry.isLocalDiffeomorph_restrict_open V
    (fun y => Φ.isLocalDiffeomorphAt I I ∞ (hV y.property)) z

omit [FiniteDimensional ℝ E] in
private theorem exists_nat_mem_riemannianBallOf_half {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p x : M) :
    ∃ k : ℕ, x ∈ riemannianBallOf g p (((k + 1 : ℕ) : ℝ) / 2) := by
  have hne := riemannianEDistOf_ne_top g p x
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (riemannianEDistOf g p x).toReal)
  refine ⟨k, (ENNReal.lt_ofReal_iff_toReal_lt hne).mpr ?_⟩
  push_cast
  linarith

theorem exists_ancient_flow_limit_of_pointed_convergence_of_local_solutions
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hcomplete : MetricComplete P) (hconn : ConnectedSpace P.M)
    (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
    (h : ∀ k n, ℝ → SmoothRiemannianMetric I (W k n))
    (hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆ W k n)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    (hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n))
    (hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n t) x ≤ B)
    (hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((min k l + 1 : ℕ) : ℝ)) 0,
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
        ∃ G : ℝ → SmoothRiemannianMetric I P.M,
          G 0 = P.metric ∧
          IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := P.M)
            (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
              ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                metricDerivNormSupOn K p
                  (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                  ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
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
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
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
    RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))
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
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x ∈ K,
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
  have hcompatS : ∀ n m t, t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0 → t ∈ Icc (-((m + 1 : ℕ) : ℝ)) 0 →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : V n ⊓ V m ≤ V n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : V n ⊓ V m ≤ V m)) := by
    intro n m t htn htm
    have htmin : t ∈ Icc (-((min n m + 1 : ℕ) : ℝ)) 0 := by
      rcases le_total n m with hnm | hnm
      · rw [min_eq_left hnm]
        exact htn
      · rw [min_eq_right hnm]
        exact htm
    filter_upwards [eventually_ge_atTop (N n), eventually_ge_atTop (N m),
      hf.tendsto_atTop.eventually (hcompat n m)] with i hin him hc
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
        (hc t htmin)
    exact (hinner n i hin t (Opens.inclusion inf_le_left z) v w).trans
      (hz.trans (hinner m i him t (Opens.inclusion inf_le_right z) v w).symm)
  have hk12 (k : ℕ) : -((k + 2 : ℕ) : ℝ) < -((k + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨ρ, hρ, g, hg0, hgsol, hgconv, hgcompat⟩ :=
    exists_common_compatible_solution_subsequence_on_open_sets_and_intervals_of_terminal_convergence
      V D S (fun k i => hTsol k (i + N k) (Nat.le_add_left _ _))
      (fun k => P.metric.restrictOpen (V k))
      (fun k => -((k + 1 : ℕ) : ℝ)) (fun _ => 0)
      (fun k => neg_neg_of_pos (by positivity))
      (fun k t ht => ⟨(hk12 k).le.trans ht.1, ht.2⟩)
      (fun k t ht => ⟨(hk12 k).trans_le ht.1, ht.2⟩) hterminal hcurv N hcompatS
  have hVmono : Monotone V := by
    intro k l hkl z hz
    have h1 : riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal (r k) := hz
    have hrkl : r k ≤ r l := by
      dsimp only [r]
      have : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hkl 1
      linarith
    exact lt_of_lt_of_le h1 (ENNReal.ofReal_le_ofReal hrkl)
  have hcover : ∀ x : P.M, ∃ k, x ∈ V k := fun x =>
    exists_nat_mem_riemannianBallOf_half P.metric P.basepoint x
  obtain ⟨G, hGsol, hG⟩ := exists_ancient_solution_of_compatible_open_cover V hVmono hcover g
    (fun n => hgsol n) (fun n m t htn htm => hgcompat n m t htn htm)
  have hG0 : G 0 = P.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨k, hk⟩ := hcover x
    have heq := (hG k 0 ⟨by push_cast; linarith, le_rfl⟩).trans (hg0 k)
    exact congrArg (fun q : SmoothRiemannianMetric I (V k) => q.inner ⟨x, hk⟩ v w) heq
  refine ⟨V, N, fun k => rfl, hsrc, φ, hφ, fun k j hj z => rfl, G, hG0, hGsol, ρ, hρ, ?_⟩
  intro k K hK p η hη
  obtain ⟨j, hj⟩ := hgconv k K hK p η hη
  refine ⟨max j (N k), fun i hi => ?_⟩
  have hNi : N k ≤ ρ i := (le_max_right _ _).trans (hi.trans (hρ.id_le i))
  refine ⟨hNi, fun t ht => ?_⟩
  have h1 := hj i ((le_max_left _ _).trans hi) t ht
  rw [show S k (ρ i - N k) = T k (ρ i) hNi from hTcongr k _ _ (Nat.le_add_left _ _) hNi
      (Nat.sub_add_cancel hNi),
    ← hG k t ht] at h1
  exact h1

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

universe v vE vH
variable {E : Type vE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] {H : Type vH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_ancient_pointed_flow_limit_of_local_solutions
    (X : PointedRiemannianSeq.{v, vE, vH} I)
    (hcompact : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hvol : ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a))
    (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
    (h : ∀ k n, ℝ → SmoothRiemannianMetric I (W k n))
    (hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆ W k n)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    (hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n))
    (hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n t) x ≤ B)
    (hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((min k l + 1 : ℕ) : ℝ)) 0,
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
            ∃ G : ℝ → SmoothRiemannianMetric I P.M,
              G 0 = P.metric ∧
              IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := P.M)
                (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
              ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                  ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                    metricDerivNormSupOn K p
                      (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                      ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
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
    have h1 := hn 0 ⟨by push_cast; linarith, le_rfl⟩ ⟨x, hbn hxk⟩ hxk
    rw [hzn, curvDerivNorm_restrictOpen] at h1
    exact h1
  obtain ⟨f, hf, P, F, C, hC, hPc, hPconn, hcapture⟩ :=
    exists_pointed_convergence_on_base_components_of_eventually_compact_balls X hcompact hjetsX
      hvol
  let U := fun i => connectedComponentOpen (I := I) (X.obj i).basepoint
  let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
  let F' := F.liftTargetOpen U hp
  exact ⟨f, hf, P, F', ⟨C, hC⟩, hPc, hPconn, hcapture,
    exists_ancient_flow_limit_of_pointed_convergence_of_local_solutions hf F' C hC hPc hPconn
      W h hball hsol hzero hjets hcompat⟩

end DifferentialGeometry.PDE.RicciFlow

end
