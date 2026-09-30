import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Geometry.Curvature.ScalarGradientTransport

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem canonical_bounds_of_canonicalWitness_of_scalar_derivative_bounds {M : Type u}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    [SigmaCompactSpace M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {ε C C1 C2 τ₀ τmin a t : ℝ} {Ctime Cgrad : ℝ≥0} {x : M} (h1 : C ≤ C1) (h2 : C ≤ C2)
    (h3 : C ≤ Ctime) (h4 : C ≤ Cgrad) (hτ : τ₀ ≤ τmin) (hR : 0 ≤ S.scalar t x)
    (hwit : τ₀ ≤ S.scalar t x * (t - a) →
      ∃ K : CanonicalWitness S ε C C x t, K.capTubeHasNeckChart ε)
    (hder : |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ C * S.scalar t x ^ 2)
    (hgrad : ∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
      C * S.scalar t x * Real.sqrt (S.scalar t x) * Real.sqrt ((S.base.metric t).inner x v v)) :
    (τmin ≤ S.scalar t x * (t - a) →
      ∃ K : CanonicalWitness S ε C1 C2 x t, K.capTubeHasNeckChart ε) ∧
    |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ Ctime * S.scalar t x ^ 2 ∧
    ∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
      Cgrad * S.scalar t x * Real.sqrt (S.scalar t x) *
        Real.sqrt ((S.base.metric t).inner x v v) := by
  refine ⟨fun hage => ?_, hder.trans (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)), fun v => ?_⟩
  · obtain ⟨K, hK⟩ := hwit (hτ.trans hage)
    exact ⟨K.enlargeConstants h1 h2, hK.enlarge_constants h1 h2⟩
  · refine (hgrad v).trans ?_
    have hnn : 0 ≤ S.scalar t x * Real.sqrt (S.scalar t x) *
        Real.sqrt ((S.base.metric t).inner x v v) := by positivity
    calc C * S.scalar t x * Real.sqrt (S.scalar t x) * Real.sqrt ((S.base.metric t).inner x v v)
        = C * (S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) := by ring
      _ ≤ Cgrad * (S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) := mul_le_mul_of_nonneg_right h4 hnn
      _ = _ := by ring

section Limit

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem mfderiv_restrict_open_apply {L M : Type u} [TopologicalSpace L]
    [ChartedSpace ThreeSpace L] [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (Φ : PartialDiffeomorph I3 I3 L M ∞)
    (V : Opens L) (hV : (V : Set L) ⊆ Φ.source) (z : V) (v : TangentSpace I3 z) :
    mfderiv I3 I3 (fun y : V => Φ y) z v = mfderiv I3 I3 Φ z v := by
  have hval : MDifferentiableAt I3 I3 (Subtype.val : V → L) z :=
    (contMDiff_subtype_val (I := I3) (U := V) (n := ∞)).mdifferentiableAt (by decide)
  have hmap := Φ.mdifferentiableAt (by decide) (hV z.property)
  have hc := mfderiv_comp_apply z hmap hval v
  simp only [mfderiv_subtype_val_apply] at hc
  exact hc

private theorem isLocalDiffeomorph_restrict_open {L M : Type u} [TopologicalSpace L]
    [ChartedSpace ThreeSpace L] [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (Φ : PartialDiffeomorph I3 I3 L M ∞)
    (V : Opens L) (hV : (V : Set L) ⊆ Φ.source) :
    IsLocalDiffeomorph I3 I3 ∞ (fun y : V => Φ y) :=
  DifferentialGeometry.isLocalDiffeomorph_restrict_open V
    (fun y => Φ.isLocalDiffeomorphAt I3 I3 ∞ (hV y.property))

private theorem localPullMetric_restrictOpen_eq_of_val_comp {L M : Type u} [TopologicalSpace L]
    [ChartedSpace ThreeSpace L] [IsManifold I3 ∞ L] [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [T2Space L]
    (g : SmoothRiemannianMetric I3 M) (V : Opens L) (W : Opens M) (φ : V → W)
    (hφ : IsLocalDiffeomorph I3 I3 ∞ φ) (p : V → M) (hp : IsLocalDiffeomorph I3 I3 ∞ p)
    (heq : ∀ z, ((φ z : W) : M) = p z) :
    localPullMetric (g.restrictOpen W) φ hφ = localPullMetric g p hp := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [localPullMetric_inner, localPullMetric_inner]
  have hfun : p = Subtype.val ∘ φ := funext fun z => (heq z).symm
  have hd : ∀ u, mfderiv I3 I3 p z u = mfderiv I3 I3 φ z u := by
    intro u
    rw [hfun, DifferentialGeometry.Topology.mfderiv_subtypeVal_comp W φ z]
    rfl
  rw [hd, hd, ← heq z]
  rfl

private theorem scaleMetric_restrictOpen_eq {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (W : Opens M) {c : ℝ} (hc : 0 < c) :
    scaleMetric c hc (g.restrictOpen W) = (scaleMetric c hc g).restrictOpen W := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem rescaledMetric_congr_scale {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (t : ℝ) {Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (h : Q = Q') : rescaledMetric S t Q hQ = rescaledMetric S t Q' hQ' := by
  subst h
  rfl

theorem exists_canonicalWitness_of_ancient_pointed_flow_limit
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 11) :
    ∃ C τ₀ : ℝ, 1 ≤ C ∧ 0 < τ₀ ∧
    ∀ (X : PointedRiemannianSeq.{u, 0, 0} I3) (D : ℕ → RealTimeInterval)
      (S : ∀ n, SolutionOn (I := I3) (M := (X.obj n).M) (D n)) (t R : ℕ → ℝ)
      (hR : ∀ n, 0 < R n), (∀ n, IsSolutionOn (S n)) →
      (∀ n, (S n).scalar (t n) (X.obj n).basepoint = R n) →
      (∀ n, (X.obj n).metric = scaleMetric (R n) (hR n) ((S n).base.metric (t n))) →
      (∀ᶠ n in atTop, Icc (t n - τ₀ / R n) (t n) ⊆ (D n).carrier ∧
        Ioo (t n - τ₀ / R n) (t n) ⊆ (D n).regular) →
    ∀ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
        t n + s / R n ∈ (D n).carrier →
        h k n s = scaleMetric (R n) (hR n) (((S n).base.metric (t n + s / R n)).restrictOpen
          (W k n))) →
    ∀ (f : ℕ → ℕ), StrictMono f → ∀ (P : PointedRiemannianManifold.{u, 0, 0} I3)
      (F : PointedRiemannianConvergenceMaps X P f), MetricComplete P →
      (∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
        riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint r ⊆ F.target n) →
    ∀ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
      (∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) →
      (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) →
    ∀ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
      (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)),
      (∀ k j (hj : N k ≤ j) (z : V k),
        ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z) →
    ∀ (G : ℝ → SmoothRiemannianMetric I3 P.M)
      (hG : IsSolutionOn ({ base.metric := G } :
        SolutionOn (I := I3) (M := P.M) ancientTimeInterval)), G 0 = P.metric →
    ∀ ψ : ℕ → ℕ, StrictMono ψ →
      (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) →
    ∀ κ : ℝ, IsAncientKappaSolution κ (flowOfMetric ancientTimeInterval P G hG) →
      PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1 →
      TangentOrientationSection P.M →
      ∀ᶠ i in atTop, ∃ K : CanonicalWitness (S (f (ψ i))) ε C C (X.obj (f (ψ i))).basepoint
        (t (f (ψ i))), K.capTubeHasNeckChart ε := by
  obtain ⟨C, δ, hC, hδ, hδ1, htr⟩ :=
    exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness.{u} hε hsmall
  refine ⟨C, δ⁻¹ + 1, hC, by positivity, ?_⟩
  intro X D S t R hR hS hRdef hX hage W h hid f hf P F hPc hcap V N hV hVF φ hφ hφF G hG hG0
    ψ hψ hconv κ hanc hbase o
  set T : ℝ := δ⁻¹
  set rad : ℝ := modelRadius δ
  have hT : 0 < T := inv_pos.mpr hδ
  have hrad : 0 < rad := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
  have hθ : (0 : ℝ) ≤ T + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (rad + 1) + T + 1)
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hk2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  have hKV : riemannianClosedBallOf P.metric P.basepoint (rad + 1) ⊆ (V k : Set P.M) := by
    rw [hV k]
    intro y hy
    refine lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    rw [hk1]
    linarith
  have hKsub : riemannianClosedBallOf P.metric P.basepoint rad ⊆
      riemannianClosedBallOf P.metric P.basepoint (rad + 1) :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hcomplete : DifferentialGeometry.RiemannianMetricComplete (I := I3) P.metric :=
    ⟨MetricComplete.complete P hPc⟩
  have hKc : IsCompact (riemannianClosedBallOf P.metric P.basepoint rad) :=
    hcomplete.closedEBall_isCompact _ _
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  have hev : ∀ᶠ i in atTop, N k ≤ ψ i ∧
      (Icc (t (f (ψ i)) - (δ⁻¹ + 1) / R (f (ψ i))) (t (f (ψ i))) ⊆ (D (f (ψ i))).carrier ∧
        Ioo (t (f (ψ i)) - (δ⁻¹ + 1) / R (f (ψ i))) (t (f (ψ i))) ⊆ (D (f (ψ i))).regular) ∧
      (∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, t (f (ψ i)) + s / R (f (ψ i)) ∈ (D (f (ψ i))).carrier →
        h k (f (ψ i)) s = scaleMetric (R (f (ψ i))) (hR _)
          (((S (f (ψ i))).base.metric (t (f (ψ i)) + s / R (f (ψ i)))).restrictOpen
            (W k (f (ψ i))))) ∧
      riemannianClosedBallOf (X.obj (f (ψ i))).metric (X.obj (f (ψ i))).basepoint rad ⊆
        F.target (ψ i) := by
    refine ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hfψ.eventually hage).and ((hfψ.eventually (hid k)).and
        (hψ.tendsto_atTop.eventually (hcap rad hrad))))).mono ?_
    intro i hi
    exact hi
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hev
  set m : ℕ → ℕ := fun i => ψ (i + i₀)
  have hm : ∀ i, i₀ ≤ i + i₀ := fun i => Nat.le_add_left _ _
  have hsrc : ∀ i, (V k : Set P.M) ⊆ (F.partialDiffeomorph (m i)).source :=
    fun i => hVF k (m i) (hi₀ _ (hm i)).1
  let p : ∀ i, V k → (X.obj (f (m i))).M := fun i y => F.partialDiffeomorph (m i) y
  have hp : ∀ i, IsLocalDiffeomorph I3 I3 ∞ (p i) := fun i =>
    isLocalDiffeomorph_restrict_open (F.partialDiffeomorph (m i)) (V k) (hsrc i)
  have hcarw : ∀ i, Icc (t (f (m i)) - (T + 1) / R (f (m i))) (t (f (m i))) ⊆
      (D (f (m i))).carrier := fun i => (hi₀ _ (hm i)).2.1.1
  have hregw : ∀ i, Ioo (t (f (m i)) - (T + 1) / R (f (m i))) (t (f (m i))) ⊆
      (D (f (m i))).regular := fun i => (hi₀ _ (hm i)).2.1.2
  let Sw : ∀ i, SolutionOn (I := I3) (M := V k)
      (RealTimeInterval.closed (-(T + 1)) 0 (neg_nonpos.mpr hθ)) := fun i =>
    ((S (f (m i))).parabolicClosedWindow (t (f (m i))) (R (f (m i))) (T + 1) (hR _)
      hθ).localPullback (p i) (hp i)
  have hSw : ∀ i, IsSolutionOn (Sw i) := fun i =>
    (isSolutionOn_parabolicClosedWindow (S (f (m i))) (hS _) (hR _) hθ (hcarw i)
      (hregw i)).localPullback (p i) (hp i)
  let Glim : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.closed (-(T + 1)) 0 (neg_nonpos.mpr hθ)) :=
    ({ base.metric := G } : SolutionOn (I := I3) (M := P.M) ancientTimeInterval).timeRestrict _
  have hGlim : IsSolutionOn Glim :=
    isSolutionOn_timeRestrict hG (fun s hs => (show s ≤ 0 from hs.2))
      (fun s hs => (show s < 0 from hs.2))
  have hpair : ∀ i s, ∀ x : V k, ∀ v w : TangentSpace I3 x,
      ((Sw i).base.metric s).inner x v w =
        (rescaledMetric (S (f (m i))) (t (f (m i))) (R (f (m i))) (hR _) s).inner
          (F.partialDiffeomorph (m i) x)
          (mfderiv I3 I3 (F.partialDiffeomorph (m i)) (x : P.M) v)
          (mfderiv I3 I3 (F.partialDiffeomorph (m i)) (x : P.M) w) := by
    intro i s x v w
    change (localPullMetric _ (p i) (hp i)).inner x v w = _
    rw [localPullMetric_inner, mfderiv_restrict_open_apply _ _ (hsrc i),
      mfderiv_restrict_open_apply _ _ (hsrc i)]
    rfl
  have hconvW : ∀ K : Set (V k), IsCompact K → ∀ r : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N' : ℕ, ∀ i ≥ N', ∀ s ∈ Icc (-T) 0,
        metricDerivNormSupOn K r ((Sw i).base.metric s)
          ((Glim.base.metric s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < e := by
    intro K hK r e he
    obtain ⟨j₀, hj⟩ := hconv k K hK r e he
    refine ⟨j₀, fun i hi s hs => ?_⟩
    obtain ⟨hk', hb⟩ := hj (i + i₀) (by omega)
    have hRi := hR (f (m i))
    have hs' : s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := ⟨by rw [hk1]; linarith [hs.1], hs.2⟩
    have hs2 : s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0 := ⟨by rw [hk2]; linarith [hs.1], hs.2⟩
    have hmem : t (f (m i)) + s / R (f (m i)) ∈ (D (f (m i))).carrier := by
      apply hcarw i
      have h1 : -(T + 1) / R (f (m i)) ≤ s / R (f (m i)) :=
        div_le_div_of_nonneg_right (by linarith [hs.1]) hRi.le
      have h2 : s / R (f (m i)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hRi.le
      rw [neg_div] at h1
      constructor <;> linarith
    have heqh := (hi₀ _ (hm i)).2.2.1 s hs2 hmem
    have heq : (Sw i).base.metric s =
        localPullMetric (h k (f (m i)) s) (φ k (m i) hk') (hφ k (m i) hk') := by
      rw [heqh, scaleMetric_restrictOpen_eq]
      exact (localPullMetric_restrictOpen_eq_of_val_comp _ (V k) (W k (f (m i))) _ _ (p i)
        (hp i) (fun z => hφF k (m i) hk' z)).symm
    rw [heq]
    exact hb s hs'
  have hcmp := eventually_metricComparisonOn_of_local_flow_convergence (V k) Sw hSw Glim hGlim
    (a := -(T + 1)) (c := -T) (b := 0) (by linarith) (by linarith) rfl (fun _ hx => hx)
    (P.metric.restrictOpen (V k)) hconvW
    (fun i => rescaledMetric (S (f (m i))) (t (f (m i))) (R (f (m i))) (hR _))
    (fun i => (F.partialDiffeomorph (m i) : P.M → (X.obj (f (m i))).M)) hpair
    (uniqueDiffOn_Icc (show -T < 0 by linarith)) subset_rfl hKc (hKsub.trans hKV)
    (modelOrder δ) hδ
  have hwit : ∀ i, Nonempty (MetricComparisonOn Glim.base.metric
      (rescaledMetric (S (f (m i))) (t (f (m i))) (R (f (m i))) (hR _))
      (F.partialDiffeomorph (m i) : P.M → (X.obj (f (m i))).M)
      (riemannianClosedBallOf P.metric P.basepoint rad) (Icc (-T) 0) (modelOrder δ) δ) →
      ∃ K : CanonicalWitness (S (f (m i))) ε C C (X.obj (f (m i))).basepoint (t (f (m i))),
        K.capTubeHasNeckChart ε := by
    rintro i ⟨cmp⟩
    have hRn := hR (f (m i))
    have hQ : 0 < (S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint := by
      rw [hRdef]
      exact hRn
    have hresc : rescaledMetric (S (f (m i))) (t (f (m i)))
        ((S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint) hQ =
        rescaledMetric (S (f (m i))) (t (f (m i))) (R (f (m i))) hRn :=
      rescaledMetric_congr_scale _ _ _ _ (hRdef _)
    have hwin : (δ * (S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint)⁻¹ ≤
        (T + 1) / R (f (m i)) := by
      rw [hRdef, mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hRn.le)
    have hwin' : Icc (t (f (m i)) -
        (δ * (S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint)⁻¹) (t (f (m i))) ⊆
        Icc (t (f (m i)) - (T + 1) / R (f (m i))) (t (f (m i))) :=
      Icc_subset_Icc_left (by linarith)
    have hreg' : Ioo (t (f (m i)) -
        (δ * (S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint)⁻¹) (t (f (m i))) ⊆
        (D (f (m i))).regular :=
      (Ioo_subset_Ioo_left (by linarith)).trans (hregw i)
    have hbase0 : rescaledMetric (S (f (m i))) (t (f (m i))) (R (f (m i))) hRn 0 =
        (X.obj (f (m i))).metric := by
      rw [hX]
      simp only [rescaledMetric, parabolicTime, zero_div, add_zero]
    have hT1 : 0 ≤ (T + 1) / R (f (m i)) := div_nonneg hθ hRn.le
    let Wit : WindowedModelWitness δ κ (S (f (m i))) (X.obj (f (m i))).basepoint
        (t (f (m i))) :=
      { eps_pos := hδ
        eps_lt_one := hδ1
        time_mem := hcarw i ⟨by linarith, le_rfl⟩
        scalar_pos := hQ
        window_mem := hwin'.trans (hcarw i)
        model := flowOfMetric ancientTimeInterval P G hG
        model_ancient := hanc
        model_scalar_base := hbase
        embedding := F.partialDiffeomorph (m i)
        buffered_ball := by
          change riemannianClosedBallOf (G 0) P.basepoint (modelRadius δ + 1) ⊆ _
          rw [hG0]
          exact hKV.trans (hsrc i)
        base_map := F.basepoint_map (m i)
        comparison := by
          rw [hresc]
          change MetricComparisonOn G _ _
            (riemannianClosedBallOf (G 0) P.basepoint (modelRadius δ))
            (Icc (-modelDepth δ) 0) (modelOrder δ) δ
          rw [hG0]
          exact cmp
        source_capture := by
          rw [hresc, hbase0]
          intro y hy
          have hyT : y ∈ (F.partialDiffeomorph (m i)).target :=
            (hi₀ _ (hm i)).2.2.2 (le_trans (le_of_lt hy) (ENNReal.ofReal_le_ofReal (by linarith)))
          exact ⟨(F.partialDiffeomorph (m i)).toPartialEquiv.symm y,
            (F.partialDiffeomorph (m i)).toPartialEquiv.map_target hyT,
            (F.partialDiffeomorph (m i)).toPartialEquiv.right_inv hyT⟩ }
    exact htr κ (X.obj (f (m i))).M (D (f (m i))) (S (f (m i))) (hS _) δ
      (X.obj (f (m i))).basepoint (t (f (m i))) Wit le_rfl hreg' o
  obtain ⟨i₁, hi₁⟩ := eventually_atTop.1 (hcmp.mono fun i hi => hwit i hi)
  refine eventually_atTop.2 ⟨i₁ + i₀, fun i hi => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, i = l + i₀ := ⟨i - i₀, by omega⟩
  exact hi₁ l (by omega)

private noncomputable def opensInclusion {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] (U : Opens M) (x : U) :
    PartialDiffeomorph I3 I3 U M ∞ := by
  classical
  let F : M → U := fun y => if h : y ∈ U then (⟨y, h⟩ : U) else x
  exact
    { toPartialEquiv :=
        { toFun := Subtype.val
          invFun := F
          source := univ
          target := (U : Set M)
          map_source' := fun y _ => y.2
          map_target' := fun _ _ => mem_univ _
          left_inv' := fun y _ => by
            simp only [F]
            split_ifs with h
            · rfl
            · exact absurd y.2 h
          right_inv' := fun y hy => by
            simp only [F]
            split_ifs with h
            · rfl
            · exact absurd hy h }
      open_source := isOpen_univ
      open_target := U.2
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff (U := U) (f := F) (s := (U : Set M)) y]
        exact (contMDiffWithinAt_id (I := I3) (s := (U : Set M)) (x := y)).congr
          (f₁ := fun z : M => (F z : M))
          (fun z hz => by
            simp only [F]
            split_ifs with h
            · rfl
            · exact absurd hz h)
          (by
            simp only [F]
            split_ifs with h
            · rfl
            · exact absurd hy h) }

private theorem opensInclusion_symm_apply {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] (U : Opens M) (x : U) {y : M}
    (hy : y ∈ U) : (opensInclusion U x).symm y = ⟨y, hy⟩ := by
  classical
  change (if h : y ∈ U then (⟨y, h⟩ : U) else x) = _
  rw [dite_eq_left hy]

private noncomputable def windowedModelWitnessOfLimitComparison {N : Type u}
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] {L : ℝ} (hL : -L ≤ 0)
    (h : ℝ → SmoothRiemannianMetric I3 N) (x : N)
    (hQ1 : ({ base.metric := h } : SolutionOn (I := I3) (M := N)
      (RealTimeInterval.closed (-L) 0 hL)).scalar 0 x = 1)
    {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hδL : δ⁻¹ ≤ L)
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (G : ℝ → SmoothRiemannianMetric I3 P.M)
    (hG : IsSolutionOn ({ base.metric := G } :
      SolutionOn (I := I3) (M := P.M) ancientTimeInterval)) (hG0 : G 0 = P.metric)
    (hanc : IsAncientKappaSolution κ (flowOfMetric ancientTimeInterval P G hG))
    (hbase : PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1)
    (E : PartialDiffeomorph I3 I3 P.M N ∞)
    (hsrc : riemannianClosedBallOf P.metric P.basepoint (modelRadius δ + 1) ⊆ E.source)
    (hmap : E P.basepoint = x)
    (cmp : MetricComparisonOn G h E (riemannianClosedBallOf P.metric P.basepoint (modelRadius δ))
      (Icc (-δ⁻¹) 0) (modelOrder δ) δ)
    (hcap : riemannianBallOf (h 0) x (modelRadius δ - 1) ⊆ E '' E.source) :
    WindowedModelWitness δ κ ({ base.metric := h } : SolutionOn (I := I3) (M := N)
      (RealTimeInterval.closed (-L) 0 hL)) x 0 := by
  set Sh : SolutionOn (I := I3) (M := N) (RealTimeInterval.closed (-L) 0 hL) :=
    { base.metric := h }
  have hQ : 0 < Sh.scalar 0 x := by
    rw [hQ1]
    exact one_pos
  have hresc : rescaledMetric Sh 0 (Sh.scalar 0 x) hQ = h := by
    rw [rescaledMetric_congr_scale Sh 0 hQ one_pos hQ1]
    funext s
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [rescaledMetric, parabolicTime, zero_add, div_one, scaleMetric_inner, one_mul]
    rfl
  exact
    { eps_pos := hδ
      eps_lt_one := hδ1
      time_mem := ⟨hL, le_rfl⟩
      scalar_pos := hQ
      window_mem := by
        rw [hQ1, mul_one]
        intro s hs
        exact ⟨by linarith [hs.1], hs.2⟩
      model := flowOfMetric ancientTimeInterval P G hG
      model_ancient := hanc
      model_scalar_base := hbase
      embedding := E
      buffered_ball := by
        change riemannianClosedBallOf (G 0) P.basepoint (modelRadius δ + 1) ⊆ _
        rw [hG0]
        exact hsrc
      base_map := hmap
      comparison := by
        rw [hresc]
        change MetricComparisonOn G _ _
          (riemannianClosedBallOf (G 0) P.basepoint (modelRadius δ))
          (Icc (-modelDepth δ) 0) (modelOrder δ) δ
        rw [hG0]
        exact cmp
      source_capture := by
        rw [hresc]
        exact hcap }

private theorem scalar_derivative_bounds_of_local_canonicalWitness {M : Type u}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) {t R η L ε C : ℝ} (hR : 0 < R) (hη : 0 < η) (hL0 : 0 < L)
    {y : M} (hRy : S.scalar t y = R) (hηs : Icc (t - η) t ⊆ D.carrier) (W : Opens M)
    (hyW : y ∈ W) [SigmaCompactSpace W] (h : ℝ → SmoothRiemannianMetric I3 W)
    (hid : ∀ s ∈ Icc (-L) 0, t + s / R ∈ D.carrier →
      h s = scaleMetric R hR ((S.base.metric (t + s / R)).restrictOpen W)) (hL : -L ≤ 0)
    (K : CanonicalWitness ({ base.metric := h } : SolutionOn (I := I3) (M := W)
      (RealTimeInterval.closed (-L) 0 hL)) ε C C ⟨y, hyW⟩ 0) :
    |derivWithin (fun v => S.scalar v y) (Iic t) t| ≤ C * S.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y, |scalarDifferential S t y v| ≤
        C * S.scalar t y * Real.sqrt (S.scalar t y) *
          Real.sqrt ((S.base.metric t).inner y v v) := by
  set Sh : SolutionOn (I := I3) (M := W) (RealTimeInterval.closed (-L) 0 hL) :=
    { base.metric := h }
  set x : W := ⟨y, hyW⟩
  have hids : ∀ s ∈ Icc (-L) 0, t + s / R ∈ D.carrier →
      h s = localPullMetric (scaleMetric R hR (S.base.metric (t + s / R))) Subtype.val
        (isLocalDiffeomorph_subtype_val W) := by
    intro s hs hmem
    rw [hid s hs hmem, scaleMetric_restrictOpen_eq, localPullMetric_subtype_val]
  have hscal : ∀ s ∈ Icc (-L) 0, t + s / R ∈ D.carrier →
      Sh.scalar s x = R⁻¹ * S.scalar (t + s / R) y := by
    intro s hs hmem
    change metricScalarAt (h s) x = _
    rw [hids s hs hmem, metricScalarAt_localPull, Geometry.Curvature.metricScalarAt_scaleMetric]
    rfl
  have ht0 : t + 0 / R ∈ D.carrier := by
    rw [zero_div, add_zero]
    exact hηs ⟨by linarith, le_rfl⟩
  have h0mem : (0 : ℝ) ∈ Icc (-L) 0 := ⟨hL, le_rfl⟩
  have hQ1 : Sh.scalar 0 x = 1 := by
    rw [hscal 0 h0mem ht0, zero_div, add_zero, hRy, inv_mul_cancel₀ hR.ne']
  have hdiff : DifferentiableWithinAt ℝ (fun v => S.scalar v y) (Iic t) t :=
    (hS.scalarTime (K := Icc (t - η) t) ⟨by linarith, le_rfl⟩ hηs y).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE (by linarith))
  have hev0 : (fun s => Sh.scalar s x) =ᶠ[𝓝[Iic 0] 0] fun s => R⁻¹ * S.scalar (t + s / R) y := by
    filter_upwards [Icc_mem_nhdsLE (show -min (η * R) L < 0 by
      linarith [lt_min (mul_pos hη hR) hL0])] with s hs
    have h1 : -(η * R) ≤ s := le_trans (neg_le_neg (min_le_left _ _)) hs.1
    have h2 : -L ≤ s := le_trans (neg_le_neg (min_le_right _ _)) hs.1
    have h3 : -η ≤ s / R := by
      rw [le_div_iff₀ hR]
      linarith
    have h4 : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
    exact hscal s ⟨h2, hs.2⟩ (hηs ⟨by linarith, by linarith⟩)
  have hderiv : derivWithin (fun s => Sh.scalar s x) (Iic 0) 0 =
      R⁻¹ ^ 2 * derivWithin (fun v => S.scalar v y) (Iic t) t := by
    rw [hev0.derivWithin_eq (hscal 0 h0mem ht0)]
    exact derivWithin_parabolic_scalar_Iic _ _ _ hR hdiff
  have hK := K.time_derivative
  rw [hderiv, hQ1, abs_mul, abs_of_pos (by positivity)] at hK
  refine ⟨?_, ?_⟩
  · rw [hRy]
    have hR2 : 0 < R ^ 2 := by positivity
    calc |derivWithin (fun v => S.scalar v y) (Iic t) t|
        = R ^ 2 * (R⁻¹ ^ 2 * |derivWithin (fun v => S.scalar v y) (Iic t) t|) := by
          field_simp
      _ ≤ R ^ 2 * (C * 1 ^ 2) := mul_le_mul_of_nonneg_left hK hR2.le
      _ = C * R ^ 2 := by ring
  · have hids0 : h 0 = localPullMetric (scaleMetric R hR (S.base.metric t)) Subtype.val
        (isLocalDiffeomorph_subtype_val W) := by
      have := hids 0 h0mem ht0
      simp only [zero_div, add_zero] at this
      exact this
    have hb : ∀ v : TangentSpace I3 x,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (localPullMetric
          (scaleMetric R hR (S.base.metric t)) Subtype.val
          (isLocalDiffeomorph_subtype_val W))) x v)| ≤
          C * metricScalarAt (localPullMetric (scaleMetric R hR (S.base.metric t)) Subtype.val
            (isLocalDiffeomorph_subtype_val W)) x *
          Real.sqrt (metricScalarAt (localPullMetric (scaleMetric R hR (S.base.metric t))
            Subtype.val (isLocalDiffeomorph_subtype_val W)) x) *
          Real.sqrt ((localPullMetric (scaleMetric R hR (S.base.metric t)) Subtype.val
            (isLocalDiffeomorph_subtype_val W)).inner x v v) := by
      intro v
      have hg := K.gradient v
      change |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (h 0)) x v)| ≤
        C * metricScalarAt (h 0) x * Real.sqrt (metricScalarAt (h 0) x) *
          Real.sqrt ((h 0).inner x v v) at hg
      rw [hids0] at hg
      exact hg
    exact scalar_gradient_bound_of_localPull_scaleMetric _ Subtype.val
      (isLocalDiffeomorph_subtype_val W) hR x hb

theorem eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (X : PointedRiemannianSeq.{u, 0, 0} I3) (D : ℕ → RealTimeInterval)
      (S : ∀ n, SolutionOn (I := I3) (M := (X.obj n).M) (D n)) (t R : ℕ → ℝ)
      (hR : ∀ n, 0 < R n), (∀ n, IsSolutionOn (S n)) →
      (∀ n, (S n).scalar (t n) (X.obj n).basepoint = R n) →
      (∀ n, (X.obj n).metric = scaleMetric (R n) (hR n) ((S n).base.metric (t n))) →
      (∀ n, ∃ η : ℝ, 0 < η ∧ Icc (t n - η) (t n) ⊆ (D n).carrier) →
    ∀ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
        SolutionOn (I := I3) (M := W k n)
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))))) →
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, t n + s / R n ∈ (D n).carrier →
          h k n s = scaleMetric (R n) (hR n) (((S n).base.metric (t n + s / R n)).restrictOpen
            (W k n))) →
    ∀ (f : ℕ → ℕ), StrictMono f → ∀ (P : PointedRiemannianManifold.{u, 0, 0} I3)
      (F : PointedRiemannianConvergenceMaps X P f), MetricComplete P →
      (∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
        riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint r ⊆ F.target n) →
    ∀ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
      (∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) →
      (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) →
    ∀ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
      (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)),
      (∀ k j (hj : N k ≤ j) (z : V k),
        ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z) →
    ∀ (G : ℝ → SmoothRiemannianMetric I3 P.M)
      (hG : IsSolutionOn ({ base.metric := G } :
        SolutionOn (I := I3) (M := P.M) ancientTimeInterval)), G 0 = P.metric →
    ∀ ψ : ℕ → ℕ, StrictMono ψ →
      (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) →
    ∀ κ : ℝ, IsAncientKappaSolution κ (flowOfMetric ancientTimeInterval P G hG) →
      PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1 →
      TangentOrientationSection P.M →
      ∀ᶠ i in atTop,
        |derivWithin (fun v => (S (f (ψ i))).scalar v (X.obj (f (ψ i))).basepoint)
            (Iic (t (f (ψ i)))) (t (f (ψ i)))| ≤
          C * (S (f (ψ i))).scalar (t (f (ψ i))) (X.obj (f (ψ i))).basepoint ^ 2 ∧
        ∀ v : TangentSpace I3 (X.obj (f (ψ i))).basepoint,
          |scalarDifferential (S (f (ψ i))) (t (f (ψ i))) (X.obj (f (ψ i))).basepoint v| ≤
            C * (S (f (ψ i))).scalar (t (f (ψ i))) (X.obj (f (ψ i))).basepoint *
              Real.sqrt ((S (f (ψ i))).scalar (t (f (ψ i))) (X.obj (f (ψ i))).basepoint) *
              Real.sqrt (((S (f (ψ i))).base.metric (t (f (ψ i)))).inner _ v v) := by
  obtain ⟨C, δ, hC, hδ, hδ1, htr⟩ :=
    exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness.{u} hε hsmall
  refine ⟨C, hC, ?_⟩
  intro X D S t R hR hS hRdef hX hleft W h hsolh hid f hf P F hPc hcap V N hV hVF φ hφ hφF G
    hG hG0 ψ hψ hconv κ hanc hbase o
  let _ : ∀ k n, SigmaCompactSpace (W k n) := fun k n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (W k n).isOpen)
  set T : ℝ := δ⁻¹
  set rad : ℝ := modelRadius δ
  have hT : 0 < T := inv_pos.mpr hδ
  have hrad : 0 < rad := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
  have hθ : (0 : ℝ) ≤ T + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (rad + 1) + T + 1)
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hk2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  have hk3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hKV : riemannianClosedBallOf P.metric P.basepoint (rad + 1) ⊆ (V k : Set P.M) := by
    rw [hV k]
    intro y hy
    refine lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    rw [hk1]
    linarith
  have hKsub : riemannianClosedBallOf P.metric P.basepoint rad ⊆
      riemannianClosedBallOf P.metric P.basepoint (rad + 1) :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hcomplete : DifferentialGeometry.RiemannianMetricComplete (I := I3) P.metric :=
    ⟨MetricComplete.complete P hPc⟩
  have hKc : IsCompact (riemannianClosedBallOf P.metric P.basepoint rad) :=
    hcomplete.closedEBall_isCompact _ _
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  have hev : ∀ᶠ i in atTop, N k ≤ ψ i ∧
      IsSolutionOn ({ base.metric := h k (f (ψ i)) } :
        SolutionOn (I := I3) (M := W k (f (ψ i)))
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
      ((W k (f (ψ i)) : Set (X.obj (f (ψ i))).M) =
          riemannianBallOf (X.obj (f (ψ i))).metric (X.obj (f (ψ i))).basepoint
            ((k + 3 : ℕ) : ℝ) ∧
        ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
          t (f (ψ i)) + s / R (f (ψ i)) ∈ (D (f (ψ i))).carrier →
          h k (f (ψ i)) s = scaleMetric (R (f (ψ i))) (hR _)
            (((S (f (ψ i))).base.metric (t (f (ψ i)) + s / R (f (ψ i)))).restrictOpen
              (W k (f (ψ i))))) ∧
      riemannianClosedBallOf (X.obj (f (ψ i))).metric (X.obj (f (ψ i))).basepoint rad ⊆
        F.target (ψ i) :=
    (hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hfψ.eventually (hsolh k)).and ((hfψ.eventually (hid k)).and
        (hψ.tendsto_atTop.eventually (hcap rad hrad))))
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hev
  set m : ℕ → ℕ := fun i => ψ (i + i₀)
  have hm : ∀ i, i₀ ≤ i + i₀ := fun i => Nat.le_add_left _ _
  have hNk : ∀ i, N k ≤ m i := fun i => (hi₀ _ (hm i)).1
  have hyW : ∀ i, (X.obj (f (m i))).basepoint ∈ W k (f (m i)) := by
    intro i
    change (X.obj (f (m i))).basepoint ∈ (W k (f (m i)) : Set (X.obj (f (m i))).M)
    rw [(hi₀ _ (hm i)).2.2.1.1]
    change riemannianEDistOf _ _ _ < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.2 (by rw [hk3]; positivity)
  let E : ∀ i, PartialDiffeomorph I3 I3 P.M (W k (f (m i))) ∞ := fun i =>
    (F.partialDiffeomorph (m i)).trans (opensInclusion (W k (f (m i))) ⟨_, hyW i⟩).symm
  have hsrcE : ∀ i, (V k : Set P.M) ⊆ (E i).source := by
    intro i z hz
    refine ⟨hVF k (m i) (hNk i) hz, ?_⟩
    have h1 := (φ k (m i) (hNk i) ⟨z, hz⟩).2
    rw [hφF] at h1
    exact h1
  have hEφ : ∀ i (z : V k), (E i) z = φ k (m i) (hNk i) z := by
    intro i z
    have hmem : (F.partialDiffeomorph (m i)) z ∈ W k (f (m i)) := by
      have h1 := (φ k (m i) (hNk i) z).2
      rw [hφF] at h1
      exact h1
    change (opensInclusion (W k (f (m i))) ⟨_, hyW i⟩).symm ((F.partialDiffeomorph (m i)) z) = _
    rw [opensInclusion_symm_apply _ _ hmem]
    exact Subtype.ext (hφF k (m i) (hNk i) z).symm
  let Sw : ∀ i, SolutionOn (I := I3) (M := V k)
      (RealTimeInterval.closed (-(T + 1)) 0 (neg_nonpos.mpr hθ)) := fun i =>
    (({ base.metric := h k (f (m i)) } : SolutionOn (I := I3) (M := W k (f (m i)))
      (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg _)))).timeRestrict
      (RealTimeInterval.closed (-(T + 1)) 0 (neg_nonpos.mpr hθ))).localPullback
      (φ k (m i) (hNk i)) (hφ k (m i) (hNk i))
  have hSw : ∀ i, IsSolutionOn (Sw i) := fun i =>
    (isSolutionOn_timeRestrict
      (D' := RealTimeInterval.closed (-(T + 1)) 0 (neg_nonpos.mpr hθ)) (hi₀ _ (hm i)).2.1
      (fun s (hs : s ∈ Icc (-(T + 1)) 0) => (⟨by rw [hk2]; linarith [hs.1], hs.2⟩ :
        s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0))
      (fun s (hs : s ∈ Ioo (-(T + 1)) 0) => (⟨by rw [hk2]; linarith [hs.1], hs.2⟩ :
        s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0))).localPullback _ _
  let Glim : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.closed (-(T + 1)) 0 (neg_nonpos.mpr hθ)) :=
    ({ base.metric := G } : SolutionOn (I := I3) (M := P.M) ancientTimeInterval).timeRestrict _
  have hGlim : IsSolutionOn Glim :=
    isSolutionOn_timeRestrict hG (fun s hs => (show s ≤ 0 from hs.2))
      (fun s hs => (show s < 0 from hs.2))
  have hpair : ∀ i s, ∀ x : V k, ∀ v w : TangentSpace I3 x,
      ((Sw i).base.metric s).inner x v w =
        (h k (f (m i)) s).inner (E i x) (mfderiv I3 I3 (E i) (x : P.M) v)
          (mfderiv I3 I3 (E i) (x : P.M) w) := by
    intro i s x v w
    have hfun : φ k (m i) (hNk i) = fun z : V k => E i z := funext fun z => (hEφ i z).symm
    change (localPullMetric (h k (f (m i)) s) (φ k (m i) (hNk i)) (hφ k (m i) (hNk i))).inner
      x v w = _
    rw [localPullMetric_inner, hfun, mfderiv_restrict_open_apply _ _ (hsrcE i),
      mfderiv_restrict_open_apply _ _ (hsrcE i)]
  have hconvW : ∀ K : Set (V k), IsCompact K → ∀ r : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N' : ℕ, ∀ i ≥ N', ∀ s ∈ Icc (-T) 0,
        metricDerivNormSupOn K r ((Sw i).base.metric s)
          ((Glim.base.metric s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < e := by
    intro K hK r e he
    obtain ⟨j₀, hj⟩ := hconv k K hK r e he
    refine ⟨j₀, fun i hi s hs => ?_⟩
    obtain ⟨_, hb⟩ := hj (i + i₀) (by omega)
    exact hb s ⟨by rw [hk1]; linarith [hs.1], hs.2⟩
  have hcmp := eventually_metricComparisonOn_of_local_flow_convergence (V k) Sw hSw Glim hGlim
    (a := -(T + 1)) (c := -T) (b := 0) (by linarith) (by linarith) rfl (fun _ hx => hx)
    (P.metric.restrictOpen (V k)) hconvW (fun i => h k (f (m i)))
    (fun i => (E i : P.M → W k (f (m i)))) hpair
    (uniqueDiffOn_Icc (show -T < 0 by linarith)) subset_rfl hKc (hKsub.trans hKV)
    (modelOrder δ) hδ
  have hwit : ∀ i, Nonempty (MetricComparisonOn Glim.base.metric (h k (f (m i)))
      (E i : P.M → W k (f (m i)))
      (riemannianClosedBallOf P.metric P.basepoint rad) (Icc (-T) 0) (modelOrder δ) δ) →
      |derivWithin (fun v => (S (f (m i))).scalar v (X.obj (f (m i))).basepoint)
          (Iic (t (f (m i)))) (t (f (m i)))| ≤
        C * (S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint ^ 2 ∧
      ∀ v : TangentSpace I3 (X.obj (f (m i))).basepoint,
        |scalarDifferential (S (f (m i))) (t (f (m i))) (X.obj (f (m i))).basepoint v| ≤
          C * (S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint *
            Real.sqrt ((S (f (m i))).scalar (t (f (m i))) (X.obj (f (m i))).basepoint) *
            Real.sqrt (((S (f (m i))).base.metric (t (f (m i)))).inner _ v v) := by
    rintro i ⟨cmp⟩
    have hRn := hR (f (m i))
    obtain ⟨η, hη, hηs⟩ := hleft (f (m i))
    have hid' := (hi₀ _ (hm i)).2.2.1.2
    have hL : -(((k + 2 : ℕ) : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg _)
    have ht0 : t (f (m i)) + 0 / R (f (m i)) ∈ (D (f (m i))).carrier := by
      rw [zero_div, add_zero]
      exact hηs ⟨by linarith, le_rfl⟩
    have h0mem : (0 : ℝ) ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0 := ⟨hL, le_rfl⟩
    have hh0 : h k (f (m i)) 0 = (X.obj (f (m i))).metric.restrictOpen (W k (f (m i))) := by
      rw [hid' 0 h0mem ht0]
      simp only [zero_div, add_zero]
      rw [hX, scaleMetric_restrictOpen_eq]
    have hQ1 : ({ base.metric := h k (f (m i)) } : SolutionOn (I := I3) (M := W k (f (m i)))
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 hL)).scalar 0 ⟨_, hyW i⟩ = 1 := by
      change metricScalarAt (h k (f (m i)) 0) ⟨_, hyW i⟩ = 1
      rw [hh0, metricScalarAt_restrictOpen, hX, Geometry.Curvature.metricScalarAt_scaleMetric]
      change (R (f (m i)))⁻¹ * (S (f (m i))).scalar (t (f (m i))) _ = 1
      rw [hRdef, inv_mul_cancel₀ hRn.ne']
    have hbV : P.basepoint ∈ V k := hKV (by
      change riemannianEDistOf _ _ _ ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le)
    have hcapW : riemannianBallOf (h k (f (m i)) 0) ⟨_, hyW i⟩ (modelRadius δ - 1) ⊆
        (E i) '' (E i).source := by
      rw [hh0]
      intro w hw
      have hamb := lt_of_le_of_lt (riemannianEDistOf_le_restrictOpen _ _ ⟨_, hyW i⟩ w) hw
      have hwT : (w : (X.obj (f (m i))).M) ∈ (F.partialDiffeomorph (m i)).target :=
        (hi₀ _ (hm i)).2.2.2 (le_trans hamb.le (ENNReal.ofReal_le_ofReal (by linarith)))
      have hzw := (F.partialDiffeomorph (m i)).toPartialEquiv.right_inv hwT
      have hmem : (F.partialDiffeomorph (m i))
          ((F.partialDiffeomorph (m i)).toPartialEquiv.symm w) ∈ W k (f (m i)) := by
        rw [hzw]
        exact w.2
      refine ⟨(F.partialDiffeomorph (m i)).toPartialEquiv.symm w,
        ⟨(F.partialDiffeomorph (m i)).toPartialEquiv.map_target hwT, hmem⟩, ?_⟩
      change (opensInclusion _ _).symm ((F.partialDiffeomorph (m i))
        ((F.partialDiffeomorph (m i)).toPartialEquiv.symm w)) = w
      rw [opensInclusion_symm_apply _ _ hmem]
      exact Subtype.ext hzw
    let Wit := windowedModelWitnessOfLimitComparison hL (h k (f (m i)))
      ⟨_, hyW i⟩ hQ1 (κ := κ) hδ hδ1 (by rw [hk2]; linarith) P G hG hG0 hanc hbase (E i)
      (hKV.trans (hsrcE i))
      ((hEφ i ⟨_, hbV⟩).trans
        (Subtype.ext ((hφF k (m i) (hNk i) ⟨_, hbV⟩).trans (F.basepoint_map (m i))))) cmp hcapW
    have hregh : Ioo (0 - (δ * ({ base.metric := h k (f (m i)) } :
        SolutionOn (I := I3) (M := W k (f (m i)))
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 hL)).scalar 0 ⟨_, hyW i⟩)⁻¹) 0 ⊆
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 hL).regular := by
      rw [hQ1, mul_one]
      intro s hs
      exact ⟨by rw [hk2]; linarith [hs.1], hs.2⟩
    obtain ⟨K, -⟩ := htr κ (W k (f (m i))) _ _ (hi₀ _ (hm i)).2.1 δ _ 0 Wit le_rfl hregh o
    exact scalar_derivative_bounds_of_local_canonicalWitness (S (f (m i))) (hS _) hRn hη
      (show (0 : ℝ) < ((k + 2 : ℕ) : ℝ) by positivity) (hRdef _) hηs (W k (f (m i))) (hyW i)
      (h k (f (m i))) hid' hL K
  obtain ⟨i₁, hi₁⟩ := eventually_atTop.1 (hcmp.mono fun i hi => hwit i hi)
  refine eventually_atTop.2 ⟨i₁ + i₀, fun i hi => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, i = l + i₀ := ⟨i - i₀, by omega⟩
  exact hi₁ l (by omega)

end Limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
