import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProjection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PartialDiffeomorph (image_riemannianBall_eq_of_isometric_on_compact_ball)
open KappaSolutions

open private opensInclusion opensInclusion_symm_apply windowedModelWitnessOfLimitComparison
  mfderiv_restrict_open_apply scaleMetric_restrictOpen_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitCanonicalWitness

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

section Limit

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem eventually_exists_canonicalWitness_survivor_of_ancient_pointed_flow_limit
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
      ∃ k : ℕ, 2 * C + 1 < ((k + 3 : ℕ) : ℝ) ∧ ∀ᶠ i in atTop,
        ∃ hy : (X.obj (f (ψ i))).basepoint ∈ W k (f (ψ i)),
        ∃ K : CanonicalWitness ({ base.metric := h k (f (ψ i)) } :
            SolutionOn (I := I3) (M := W k (f (ψ i)))
              (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))))
            ε C C ⟨_, hy⟩ 0, K.capTubeHasNeckChart ε := by
  obtain ⟨C, δ, hC, hδ, hδ1, htr⟩ :=
    exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness.{u} hε hsmall
  refine ⟨C, hC, ?_⟩
  intro X D S t R hR hS hRdef hX hleft W h hsolh hid f hf P F hPc hcap V N hV hVF φ hφ hφF G
    hG hG0 ψ hψ hconv κ hanc hbase o
  set T : ℝ := δ⁻¹
  set rad : ℝ := modelRadius δ
  have hT : 0 < T := inv_pos.mpr hδ
  have hrad : 0 < rad := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
  have hθ : (0 : ℝ) ≤ T + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (rad + 1) + T + 1 + 2 * C)
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hk2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  have hk3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  refine ⟨k, by rw [hk3]; linarith, ?_⟩
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
      ∃ hy : (X.obj (f (m i))).basepoint ∈ W k (f (m i)),
      ∃ K : CanonicalWitness ({ base.metric := h k (f (m i)) } :
          SolutionOn (I := I3) (M := W k (f (m i)))
            (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))))
          ε C C ⟨_, hy⟩ 0, K.capTubeHasNeckChart ε := by
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
    exact ⟨hyW i, htr κ (W k (f (m i))) _ _ (hi₀ _ (hm i)).2.1 δ _ 0 Wit le_rfl hregh o⟩
  obtain ⟨i₁, hi₁⟩ := eventually_atTop.1 (hcmp.mono fun i hi => hwit i hi)
  refine eventually_atTop.2 ⟨i₁ + i₀, fun i hi => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, i = l + i₀ := ⟨i - i₀, by omega⟩
  exact hi₁ l (by omega)

end Limit

section Conversion

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem exists_neck_of_cast_metric {g g' : SmoothRiemannianMetric I3 M} (hg : g = g')
    {ε C1 C2 : ℝ} {x : M} (W : SpatialCanonicalWitness g ε C1 C2 x)
    (hW : W.capTubeHasNeckChart ε) :
    ∃ W' : SpatialCanonicalWitness g' ε C1 C2 x, W'.capTubeHasNeckChart ε ∧
      ((∃ n, W'.alternative = .neck n) → ∃ n, W.alternative = .neck n) ∧
      W'.radius = W.radius := by
  subst hg
  exact ⟨W, hW, id, rfl⟩

private theorem exists_neck_of_cast_point {g : SmoothRiemannianMetric I3 M} {ε C1 C2 : ℝ}
    {p q : M} (hpq : p = q) (W : SpatialCanonicalWitness g ε C1 C2 p)
    (h : ∃ n, (hpq ▸ W : SpatialCanonicalWitness g ε C1 C2 q).alternative = .neck n) :
    ∃ n, W.alternative = .neck n := by
  subst hpq
  exact h

omit [SigmaCompactSpace M] in
private theorem exists_neck_of_alternative_pushforward_eq_neck
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
    [T2Space N] {g : SmoothRiemannianMetric I3 M}
    {h : SmoothRiemannianMetric I3 N} {eps C : ℝ} {x : N} {V : Set N}
    {A : SpatialCanonicalAlternative h eps C x V} {e : PartialDiffeomorph I3 I3 N M ∞}
    {hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w}
    {hV : V ⊆ e.source} {hVc : IsCompact V}
    {hdist : ∀ y ∈ V, metricDistance h x y ≤ metricDistance g (e x) (e y)}
    {hneck : ∀ n, A = .neck n → ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source}
    {hcap : ∀ c d, A = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source}
    {n : SpatialLocalNeck g eps (e x) (e '' V)}
    (heq : A.pushforward e hiso hV hVc hdist hneck hcap = .neck n) :
    ∃ n', A = .neck n' := by
  cases A with
  | neck data => exact ⟨data, rfl⟩
  | cap data deep => cases heq
  | positive whole data sec => cases heq
  | round whole data => cases heq

private theorem domain_subset_of_ball_subset {N : Type u} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
    {h : SmoothRiemannianMetric I3 N} {eps C1 C2 : ℝ} {x : N}
    (W : SpatialCanonicalWitness h eps C1 C2 x) {S : Set N} {R : ℝ} (hR : 2 * W.radius < R)
    (hsrc : riemannianClosedBallOf h x R ⊆ S) : W.domain.carrier ⊆ S := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  refine W.inside_ball.trans (fun y hy => hsrc ?_)
  exact le_of_lt (lt_trans hy ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR))

omit [SigmaCompactSpace M] in
private theorem metricDistance_le_image {N : Type u} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric I3 M} {h : SmoothRiemannianMetric I3 N} {eps C1 C2 : ℝ} {x : N}
    (W : SpatialCanonicalWitness h eps C1 C2 x) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source) :
    ∀ y ∈ W.domain.carrier, metricDistance h x y ≤ metricDistance g (e x) (e y) := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  have hdom := domain_subset_of_ball_subset W hR hsrc
  have hB2 := image_riemannianBall_eq_of_isometric_on_compact_ball h g e x
    (by linarith : 0 < 2 * W.radius) hR hcpt hsrc (fun z hz v => hiso z (hsrc hz) v v)
  intro y hy
  apply metricDistance_le_of_isometryOn e hiso hcpt hsrc (hdom hy)
  have hy2 : e y ∈ riemannianBallOf g (e x) (2 * W.radius) := by
    rw [← hB2]
    exact ⟨y, W.inside_ball hy, rfl⟩
  exact lt_trans hy2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR)

private theorem exists_neck_of_witness_pushforward_eq_neck
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
    [T2Space N] [SigmaCompactSpace N] {g : SmoothRiemannianMetric I3 M}
    {h : SmoothRiemannianMetric I3 N} {eps C1 C2 : ℝ} {x : N}
    (W : SpatialCanonicalWitness h eps C1 C2 x) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source)
    {n : SpatialLocalNeck g eps (e x) (W.pushforward e hiso hR hcpt hsrc hneck hcap).domain.carrier}
    (heq : (W.pushforward e hiso hR hcpt hsrc hneck hcap).alternative = .neck n) :
    ∃ n', W.alternative = .neck n' := by
  change W.alternative.pushforward e hiso (domain_subset_of_ball_subset W hR hsrc)
    W.domain.compact (metricDistance_le_image W e hiso hR hcpt hsrc) hneck hcap = _ at heq
  exact exists_neck_of_alternative_pushforward_eq_neck heq

omit [SigmaCompactSpace M] in
private theorem exists_neck_of_alternative_scaleMetric_eq_neck
    {g : SmoothRiemannianMetric I3 M} {eps C : ℝ} {x : M} {V : Set M} {c : ℝ} {hc : 0 < c}
    {A : SpatialCanonicalAlternative g eps C x V}
    {n : SpatialLocalNeck (scaleMetric c hc g) eps x V}
    (heq : A.scaleMetric c hc = .neck n) : ∃ n', A = .neck n' := by
  cases A with
  | neck data => exact ⟨data, rfl⟩
  | cap data deep => cases heq
  | positive whole data sec => cases heq
  | round whole data => cases heq

private theorem exists_neck_of_toSpatial_eq_neck {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 t : ℝ} {x : M}
    (K : CanonicalWitness S eps C1 C2 x t)
    (h : ∃ n, K.toSpatial.alternative = .neck n) : ∃ n, K.alternative = .neck n := by
  obtain ⟨n, hn⟩ := h
  change K.alternative.toSpatial = SpatialCanonicalAlternative.neck n at hn
  cases halt : K.alternative with
  | neck data => exact ⟨data, rfl⟩
  | cap data deep =>
    rw [halt] at hn
    cases hn
  | positive whole data sec =>
    rw [halt] at hn
    cases hn
  | round whole data =>
    rw [halt] at hn
    cases hn

theorem exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen [CompactSpace M]
    (g : SmoothRiemannianMetric I3 M) {R : ℝ} (hR : 0 < R) (U : Opens M) (x : U)
    (hQ : metricScalarAt g x.val = R) {L : ℝ} (hL : -L ≤ 0)
    (h : ℝ → SmoothRiemannianMetric I3 U) (hh0 : h 0 = scaleMetric R hR (g.restrictOpen U))
    {ε C : ℝ}
    (K : CanonicalWitness ({ base.metric := h } : SolutionOn (I := I3) (M := U)
      (RealTimeInterval.closed (-L) 0 hL)) ε C C x 0)
    (hK : K.capTubeHasNeckChart ε)
    (hball : riemannianClosedBallOf (scaleMetric R hR g) x.val (2 * C + 1) ⊆ U) :
    ∃ W : SpatialCanonicalWitness g ε C C x.val, W.capTubeHasNeckChart ε ∧
      ((∃ n, W.alternative = .neck n) → ∃ n, K.alternative = .neck n) := by
  set g' : SmoothRiemannianMetric I3 M := scaleMetric R hR g with hg'
  have hpull : h 0 = localPullMetric g' Subtype.val (isLocalDiffeomorph_subtype_val U) := by
    rw [hh0, scaleMetric_restrictOpen_eq, localPullMetric_subtype_val]
  have hscal : metricScalarAt (h 0) x = 1 := by
    rw [hh0, Geometry.Curvature.metricScalarAt_scaleMetric, metricScalarAt_restrictOpen, hQ,
      inv_mul_cancel₀ hR.ne']
  have hrad0 : K.toSpatial.radius ≤ C := by
    have h1 := K.radius_upper
    change K.radius ≤ C / Real.sqrt (metricScalarAt (h 0) x) at h1
    rw [hscal, Real.sqrt_one, div_one] at h1
    exact h1
  obtain ⟨W₀, hW₀, hn₀, hrad⟩ : ∃ W₀ : SpatialCanonicalWitness
      (localPullMetric g' Subtype.val (isLocalDiffeomorph_subtype_val U)) ε C C x,
      W₀.capTubeHasNeckChart ε ∧
      ((∃ n, W₀.alternative = .neck n) → ∃ n, K.alternative = .neck n) ∧ W₀.radius ≤ C := by
    obtain ⟨W₀, hW₀, hn₀, hr⟩ := exists_neck_of_cast_metric hpull K.toSpatial
      (K.capTubeHasNeckChart_toSpatial hK)
    exact ⟨W₀, hW₀, fun hn => exists_neck_of_toSpatial_eq_neck K (hn₀ hn), hr ▸ hrad0⟩
  have hR' : 2 * W₀.radius < 2 * C + 1 := by linarith
  have hcl : IsCompact (riemannianClosedBallOf g' x.val (2 * C + 1)) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf g' x.val _).isCompact
  have hpre : IsCompact {z : U | z.val ∈ riemannianClosedBallOf g' x.val (2 * C + 1)} :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcl
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hball)
  have hcpt : IsCompact (riemannianClosedBallOf
      (localPullMetric g' Subtype.val (isLocalDiffeomorph_subtype_val U)) x (2 * C + 1)) := by
    refine hpre.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) ?_
    intro z hz
    change riemannianEDistOf _ _ _ ≤ _ at hz ⊢
    rw [localPullMetric_subtype_val] at hz
    exact (riemannianEDistOf_le_restrictOpen g' U x z).trans hz
  let W₁ := W₀.pushforwardOfInjective (isLocalDiffeomorph_subtype_val U) Subtype.val_injective
    hR' hcpt
  have hW₁ : W₁.capTubeHasNeckChart ε := hW₀.pushforwardOfInjective _ _ hR' hcpt
  have hn₁ : (∃ n, W₁.alternative = .neck n) → ∃ n, K.alternative = .neck n := by
    intro hn
    refine hn₀ ?_
    obtain ⟨n, hn'⟩ := exists_neck_of_cast_point _ _ hn
    exact exists_neck_of_witness_pushforward_eq_neck _ _ _ _ _ _ _ _ hn'
  have heq : scaleMetric R⁻¹ (inv_pos.mpr hR) g' = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [hg', scaleMetric_inner, scaleMetric_inner, inv_mul_cancel_left₀ hR.ne']
  obtain ⟨W, hW, hn, -⟩ := exists_neck_of_cast_metric heq (W₁.scaleMetric R⁻¹ (inv_pos.mpr hR))
    (hW₁.scaleMetric R⁻¹ (inv_pos.mpr hR))
  refine ⟨W, hW, fun hW' => hn₁ ?_⟩
  obtain ⟨n, hn'⟩ := hn hW'
  exact exists_neck_of_alternative_scaleMetric_eq_neck hn'

end Conversion

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
