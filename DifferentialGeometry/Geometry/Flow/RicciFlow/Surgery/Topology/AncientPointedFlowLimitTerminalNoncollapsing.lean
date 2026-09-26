import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitNoncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.TerminalTime

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private opensInclusion opensInclusion_symm_apply mfderiv_restrict_open_apply from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitCanonicalWitness

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem isKappaNoncollapsed_of_local_flow_limit_of_time_lt
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)}
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    {κ : ℝ} (hκ : 0 < κ) {radii : ℕ → ℝ} (hradii : Tendsto radii atTop atTop)
    (hnc : ∀ k : ℕ, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, σ < 0 → ∀ᶠ n in atTop, ∀ z : W k n,
      ∀ r : ℝ, 0 < r → r ≤ radii n → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
      IsCompact (riemannianClosedBallOf (h k n σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
        r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 (W k n) (h k n σ) (riemannianBallOf (h k n σ) z r))
    {f : ℕ → ℕ} (hf : StrictMono f) (F : PointedRiemannianConvergenceMaps X P f)
    {V : ℕ → Opens P.M} (hVmono : Monotone V) (hVcover : ∀ x : P.M, ∃ k, x ∈ V k)
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    (φ : ∀ k j, N k ≤ j → V k → W k (f j))
    (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj))
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hG : IsSolutionOn ({ base.metric := G } :
      SolutionOn (I := I3) (M := P.M) ancientTimeInterval))
    (hcomplete : ∀ t ≤ 0, RiemannianMetricComplete (G t))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {time : ancientTimeInterval.FlowTime}
    (B : FlowMetricBall ({ base.metric := G } :
      SolutionOn (I := I3) (M := P.M) ancientTimeInterval) time)
    (hB : B.IsParabolicallyRmControlled) (htime : (time : ℝ) < 0) :
    B.IsKappaNoncollapsed (κ / 250) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  set t : ℝ := (time : ℝ)
  set r : ℝ := B.radius
  set p : P.M := B.center
  have hr : 0 < r := B.radius_pos
  have ht0 : t ≤ 0 := time.2
  have hcpt : ∀ ρ : ℝ, IsCompact (riemannianClosedBallOf (G t) p ρ) :=
    fun ρ => (hcomplete t ht0).closedEBall_isCompact p ρ
  obtain ⟨k₁, hk₁⟩ := (hcpt r).elim_directed_cover (fun k => (V k : Set P.M))
    (fun k => (V k).isOpen) (fun x _ => mem_iUnion.2 (hVcover x)) hVmono.directed_le
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge (r ^ 2 - t)
  set k : ℕ := max k₁ k₂
  have hKV : riemannianClosedBallOf (G t) p r ⊆ (V k : Set P.M) :=
    hk₁.trans (hVmono (le_max_left k₁ k₂))
  have hk : r ^ 2 - t ≤ (k : ℝ) :=
    hk₂.trans (Nat.cast_le.mpr (le_max_right k₁ k₂))
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hk2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  have hpK : p ∈ riemannianClosedBallOf (G t) p r := by
    change riemannianEDistOf _ _ _ ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hpV : p ∈ (V k : Set P.M) := hKV hpK
  set eps : ℝ := min (1 / 10) (1 / (40 * r ^ 2))
  have hr2 : 0 < r ^ 2 := by positivity
  have heps : 0 < eps := lt_min (by norm_num) (by positivity)
  have heps10 : eps ≤ 1 / 10 := min_le_left _ _
  have hepsK : 40 * eps ≤ 1 / r ^ 2 := by
    have h1 : eps ≤ 1 / (40 * r ^ 2) := min_le_right _ _
    have h2 : 40 * (1 / (40 * r ^ 2)) = 1 / r ^ 2 := by field_simp
    linarith
  have htk : t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := ⟨by rw [hk1]; linarith, ht0⟩
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  have hev : ∀ᶠ i in atTop, N k ≤ ψ i ∧
      IsSolutionOn ({ base.metric := h k (f (ψ i)) } :
        SolutionOn (I := I3) (M := W k (f (ψ i)))
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
            (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
      r / 5 ≤ radii (f (ψ i)) ∧
      ∀ z : W k (f (ψ i)),
        ∀ r' : ℝ, 0 < r' → r' ≤ radii (f (ψ i)) →
        Icc (t - r' ^ 2) t ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
        IsCompact (riemannianClosedBallOf (h k (f (ψ i)) t) z r') →
        (∀ s ∈ Icc (t - r' ^ 2) t, ∀ w ∈ riemannianBallOf (h k (f (ψ i)) t) z r',
          r' ^ 4 * curvDerivNormSq 0 (h k (f (ψ i)) s) w ≤ 1) →
        ENNReal.ofReal (κ * r' ^ 3) ≤
          riemannianVolumeMeasure I3 (W k (f (ψ i))) (h k (f (ψ i)) t)
            (riemannianBallOf (h k (f (ψ i)) t) z r') :=
    (hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hfψ.eventually (hsol k)).and (((hradii.comp hfψ).eventually_ge_atTop (r / 5)).and
        (hfψ.eventually (hnc k t htk htime))))
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hev
  set m : ℕ → ℕ := fun i => ψ (i + i₀)
  have hm : ∀ i, i₀ ≤ i + i₀ := fun i => Nat.le_add_left _ _
  have hNk : ∀ i, N k ≤ m i := fun i => (hi₀ _ (hm i)).1
  let E : ∀ i, PartialDiffeomorph I3 I3 P.M (W k (f (m i))) ∞ := fun i =>
    (F.partialDiffeomorph (m i)).trans
      (opensInclusion (W k (f (m i))) (φ k (m i) (hNk i) ⟨p, hpV⟩)).symm
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
    change (opensInclusion (W k (f (m i))) _).symm ((F.partialDiffeomorph (m i)) z) = _
    rw [opensInclusion_symm_apply _ _ hmem]
    exact Subtype.ext (hφF k (m i) (hNk i) z).symm
  let Sw : ∀ i, SolutionOn (I := I3) (M := V k)
      (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))) :=
    fun i => ({ base.metric := h k (f (m i)) } : SolutionOn (I := I3) (M := W k (f (m i)))
      (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg _)))).localPullback
      (φ k (m i) (hNk i)) (hφ k (m i) (hNk i))
  have hSw : ∀ i, IsSolutionOn (Sw i) := fun i =>
    (hi₀ _ (hm i)).2.1.localPullback _ _
  let Glim : SolutionOn (I := I3) (M := P.M)
      (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))) :=
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
  have hconvW : ∀ K : Set (V k), IsCompact K → ∀ q : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N' : ℕ, ∀ i ≥ N', ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K q ((Sw i).base.metric s)
          ((Glim.base.metric s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < e := by
    intro K hK q e he
    obtain ⟨j₀, hj⟩ := hconv k K hK q e he
    refine ⟨j₀, fun i hi s hs => ?_⟩
    obtain ⟨_, hb⟩ := hj (i + i₀) (by omega)
    exact hb s hs
  have hJ : Icc (t - r ^ 2) t ⊆ Icc (-((k + 1 : ℕ) : ℝ)) 0 := by
    intro s hs
    refine ⟨?_, hs.2.trans ht0⟩
    rw [hk1]
    linarith [hs.1]
  have hcmp := eventually_metricComparisonOn_of_local_flow_convergence (V k) Sw hSw Glim hGlim
    (a := -((k + 2 : ℕ) : ℝ)) (c := -((k + 1 : ℕ) : ℝ)) (b := 0)
    (by rw [hk1, hk2]; linarith) (by rw [hk1]; linarith) rfl (fun _ hx => hx)
    (P.metric.restrictOpen (V k)) hconvW (fun i => h k (f (m i)))
    (fun i => (E i : P.M → W k (f (m i)))) hpair
    (uniqueDiffOn_Icc (show t - r ^ 2 < t by linarith)) hJ (hcpt r) hKV 2 heps
  obtain ⟨i, ⟨C⟩⟩ := hcmp.exists
  have hti := hi₀ _ (hm i)
  have hwin5 : Icc (t - (r / 5) ^ 2) t ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 := by
    intro s hs
    refine ⟨?_, hs.2.trans ht0⟩
    nlinarith only [hs.1, hr, hk, hk2]
  have hcurvG : ∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ riemannianBallOf (G t) p r,
      r ^ 4 * normSq0S (G s) y 4 (metricRm04At (G s) y) ≤ 1 := by
    intro s hs y hy
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply] using
      hB.2 s hs y hy
  refine ⟨by positivity, ?_⟩
  rw [hdim]
  exact C.volume_ball_ge_of_image_parabolic_volume_bound hr (hcomplete t ht0)
    (hKV.trans (hsrcE i)) heps heps10 hepsK hκ.le hcurvG
    (hti.2.2.2 (E i p) (r / 5) (by positivity) hti.2.2.1 hwin5)

theorem parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)}
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    {κ : ℝ} (hκ : 0 < κ) {R : ℕ → ℝ} (hRlim : Tendsto R atTop atTop) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hnc : ∀ k : ℕ, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, σ < 0 → ∀ᶠ n in atTop, ∀ z : W k n,
      ∀ r : ℝ, 0 < r → r ≤ ρ₀ * Real.sqrt (R n) →
      Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
      IsCompact (riemannianClosedBallOf (h k n σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
        r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 (W k n) (h k n σ) (riemannianBallOf (h k n σ) z r))
    {f : ℕ → ℕ} (hf : StrictMono f) (F : PointedRiemannianConvergenceMaps X P f)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    (φ : ∀ k j, N k ≤ j → V k → W k (f j))
    (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj))
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric)
    (hG : IsSolutionOn ({ base.metric := G } :
      SolutionOn (I := I3) (M := P.M) ancientTimeInterval))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x)))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } :
      SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (κ / 250) ρ := by
  have hmono : Monotone V := by
    intro k l hkl z hz
    change z ∈ (V l : Set P.M)
    have hz' : z ∈ (V k : Set P.M) := hz
    rw [hV] at hz' ⊢
    refine riemannianBallOf_mono _ _ ?_ hz'
    have : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hkl 1
    linarith
  have hcover : ∀ x : P.M, ∃ k, x ∈ V k := by
    intro x
    have hne := riemannianEDistOf_ne_top P.metric P.basepoint x
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (riemannianEDistOf P.metric P.basepoint x).toReal)
    refine ⟨k, ?_⟩
    change x ∈ (V k : Set P.M)
    rw [hV]
    refine (ENNReal.lt_ofReal_iff_toReal_lt hne).mpr ?_
    push_cast
    linarith
  have hcomplete := (ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete hf hPc
    hconn hV hG0 hG hψ hconv hQ hPhi hpinch).2
  have hradii : Tendsto (fun n => ρ₀ * Real.sqrt (R n)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hRlim).const_mul_atTop hρ₀
  refine parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt hG ?_ hρ (fun _ hs => hs)
    fun time B htime _ hB => isKappaNoncollapsed_of_local_flow_limit_of_time_lt hsol hκ hradii
      hnc hf F hmono hcover hVF φ hφ hφF hG hcomplete hψ hconv B hB htime
  change interior (Iic (0 : ℝ)) ⊆ Iio 0
  rw [interior_Iic]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
