import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardTimeExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {N M : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

private theorem comparison_jets_eq_on_overlap
    {h₁ h₂ : ℝ → SmoothRiemannianMetric I3 N}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : N → M} {K : Set N}
    {l a s b : ℝ} (hla : l ≤ a) (hsb : s ≤ b)
    {order : ℕ} {eps : ℝ}
    (C₁ : MetricComparisonOn h₁ g F K (Icc l s) order eps)
    (C₂ : MetricComparisonOn h₂ g F K (Icc a b) order eps)
    (heq : EqOn h₁ h₂ (Icc a s)) :
    ∀ q t, t ∈ Ioo a s → ∀ y ∈ K, ∀ v,
      C₁.jet q t y v = C₂.jet q t y v := by
  intro q
  induction q with
  | zero =>
    intro t ht y hy v
    rw [C₁.jet_zero, C₂.jet_zero, C₁.pullback_eq t y hy,
      C₂.pullback_eq t y hy, heq ⟨ht.1.le, ht.2.le⟩]
  | succ q ih =>
    intro t ht y hy v
    rw [C₁.jet_succ q t ⟨hla.trans ht.1.le, ht.2.le⟩ y hy,
      C₂.jet_succ q t ⟨ht.1.le, ht.2.le.trans hsb⟩ y hy,
      derivWithin_of_mem_nhds (Icc_mem_nhds (hla.trans_lt ht.1) ht.2),
      derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 (ht.2.trans_le hsb))]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact ih r hr y hy v

private theorem nonempty_metricComparisonOn_glue
    {h₁ h₂ : ℝ → SmoothRiemannianMetric I3 N}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : N → M} {K : Set N}
    {l a c s b : ℝ} (hla : l ≤ a) (hac : a < c) (hcs : c < s) (hsb : s ≤ b)
    {order : ℕ} {eps : ℝ}
    (C₁ : MetricComparisonOn h₁ g F K (Icc l s) order eps)
    (C₂ : MetricComparisonOn h₂ g F K (Icc a b) order eps)
    (heq : EqOn h₁ h₂ (Icc a s)) :
    Nonempty (MetricComparisonOn (fun t => if t ≤ c then h₁ t else h₂ t)
      g F K (Icc l b) order eps) := by
  classical
  let jet (q : ℕ) (t : ℝ) := if t ≤ c then C₁.jet q t else C₂.jet q t
  refine ⟨{
    pullback := fun t => if t ≤ c then C₁.pullback t else C₂.pullback t
    pullback_eq := ?_
    jet := jet
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }⟩
  · intro t y hy v
    split_ifs <;> [exact C₁.pullback_eq t y hy v; exact C₂.pullback_eq t y hy v]
  · intro t y v
    dsimp [jet]
    split_ifs <;> [exact C₁.jet_zero t y v; exact C₂.jet_zero t y v]
  · intro q t ht y hy v
    by_cases htc : t ≤ c
    · have hnear : (fun r => jet q r y v) =ᶠ[𝓝 t] (fun r => C₁.jet q r y v) := by
        filter_upwards [Iio_mem_nhds (htc.trans_lt hcs)] with r hr
        dsimp [jet]
        split_ifs with hrc
        · rfl
        · exact (comparison_jets_eq_on_overlap hla hsb C₁ C₂ heq
            q r ⟨hac.trans (lt_of_not_ge hrc), hr⟩ y hy v).symm
      have hsets : Icc l b =ᶠ[𝓝 t] Icc l s := by
        filter_upwards [Iio_mem_nhds (htc.trans_lt hcs)] with r hr
        exact propext ⟨fun h => ⟨h.1, hr.le⟩, fun h => ⟨h.1, hr.le.trans hsb⟩⟩
      dsimp [jet]
      rw [ite_eq_left htc, hnear.derivWithin_eq_of_nhds, derivWithin_congr_set hsets]
      exact C₁.jet_succ q t ⟨ht.1, htc.trans hcs.le⟩ y hy v
    · have hct : c < t := lt_of_not_ge htc
      have hnear : (fun r => jet q r y v) =ᶠ[𝓝 t] (fun r => C₂.jet q r y v) := by
        filter_upwards [Ioi_mem_nhds hct] with r hr
        dsimp [jet]
        rw [ite_eq_right (not_le.mpr hr)]
      have hsets : Icc l b =ᶠ[𝓝 t] Icc a b := by
        filter_upwards [Ioi_mem_nhds (hac.trans hct)] with r hr
        exact propext ⟨fun h => ⟨hr.le, h.2⟩, fun h => ⟨hla.trans h.1, h.2⟩⟩
      dsimp [jet]
      rw [ite_eq_right htc, hnear.derivWithin_eq_of_nhds, derivWithin_congr_set hsets]
      exact C₂.jet_succ q t ⟨(hac.trans hct).le, ht.2⟩ y hy v
  · intro t ht y hy v
    split_ifs with htc
    · exact C₁.equivalence t ⟨ht.1, htc.trans hcs.le⟩ y hy v
    · exact C₂.equivalence t ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩ y hy v
  · intro p q hpq t ht y hy
    dsimp [jet]
    split_ifs with htc
    · exact C₁.close p q hpq t ⟨ht.1, htc.trans hcs.le⟩ y hy
    · exact C₂.close p q hpq t ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩ y hy


private theorem nonempty_metricComparisonOn_congr_reference
    {h h' : ℝ → SmoothRiemannianMetric I3 N}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : N → M}
    {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U times order eps)
    (heq : Set.EqOn h' h times) :
    Nonempty (MetricComparisonOn h' g F U times order eps) := by
  let jet : ℕ → ℝ → Tensor0SField (I := I3) (M := N) ∞ 2 := fun b s =>
    match b with
    | 0 => C.pullback s - metricTensorField (h' s)
    | b + 1 => C.jet (b + 1) s
  have hj : ∀ b s, s ∈ times → jet b s = C.jet b s := by
    intro b s hs
    cases b with
    | zero =>
      apply DFunLike.ext
      intro y
      apply DFunLike.ext
      intro v
      change C.pullback s y v - metricTensorField (h' s) y v = C.jet 0 s y v
      rw [metricTensorField_apply, heq hs, C.jet_zero]
    | succ b => rfl
  refine ⟨{ pullback := C.pullback
            pullback_eq := C.pullback_eq
            jet := jet
            jet_zero := ?_
            jet_succ := ?_
            equivalence := ?_
            close := ?_ }⟩
  · intro s y v
    change C.pullback s y v - metricTensorField (h' s) y v = _
    rw [metricTensorField_apply]
  · intro b s hs y hy v
    rw [hj (b + 1) s hs, C.jet_succ b s hs y hy v]
    exact derivWithin_congr (fun a ha => by rw [hj b a ha]) (by rw [hj b s hs])
  · intro s hs y hy v
    rw [heq hs]
    exact C.equivalence s hs y hy v
  · intro a b hab s hs y hy
    rw [hj b s hs, heq hs]
    exact C.close a b hab s hs y hy



universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem backwardExtension_of_overlapping_flow
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {l a s : ℝ} (hla : l < a) (has : a < s) (hs : s < 0)
    (B : BackwardExtension L (RealTimeInterval.closed a 0 (has.trans hs).le))
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (T : SolutionOn (I := I3) (M := L.space.M)
      (RealTimeInterval.closed l s (hla.trans has).le))
    (hT : IsSolutionOn T)
    (hTnonneg : ∀ t ∈ Icc l s, SecLower (T.base.metric t) 0 univ)
    (hTcomplete : ∀ t ∈ Icc l s, RiemannianMetricComplete (T.base.metric t))
    (hTconv : ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ rho)
      (B.strictMono.comp hrho)) T)
    (hTbound : ∃ C : ℝ, ∀ t ∈ Icc l s, ∀ x : L.space.M,
      FlowMetricBall.rmNormSq T t x ≤ C)
    (heq : EqOn T.base.metric B.solution.base.metric (Icc a s)) :
    ∃ E : BackwardExtension L (RealTimeInterval.closed l 0 (hla.trans (has.trans hs)).le),
      E.subseq = B.subseq ∘ rho ∧
      EqOn E.solution.base.metric B.solution.base.metric (Icc a 0) ∧
      EqOn E.solution.base.metric T.base.metric (Icc l s) := by
  classical
  let c := (a + s) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcs : c < s := by dsimp [c]; linarith
  let g : ℝ → SmoothRiemannianMetric I3 L.space.M :=
    fun t => if t ≤ c then T.base.metric t else B.solution.base.metric t
  have hgT : EqOn g T.base.metric (Icc l s) := by
    intro t ht
    dsimp [g]
    split_ifs with htc
    · rfl
    · exact (heq ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩).symm
  have hgB : EqOn g B.solution.base.metric (Icc a 0) := by
    intro t ht
    dsimp [g]
    split_ifs with htc
    · exact heq ⟨ht.1, htc.trans hcs.le⟩
    · rfl
  let D := RealTimeInterval.closed l 0 (hla.trans (has.trans hs)).le
  let V : SolutionOn (I := I3) (M := L.space.M) D := { base.metric := g }
  have hVT : IsSolutionOn (V.timeRestrict
      (RealTimeInterval.closed l s (hla.trans has).le)) := by
    exact hT.congr_metric (fun t ht => (hgT ht).symm)
  have hVB : IsSolutionOn (V.timeRestrict
      (RealTimeInterval.closed a 0 (has.trans hs).le)) := by
    exact B.isSolution.congr_metric (fun t ht => (hgB ht).symm)
  have hV : IsSolutionOn V := by
    apply isSolutionOn_of_local_time_restrictions V
    intro t ht
    by_cases htc : t ≤ c
    · refine ⟨Iio s, isOpen_Iio, htc.trans_lt hcs,
        RealTimeInterval.closed l s (hla.trans has).le, ?_, ?_, hVT⟩
      · intro r hr
        exact ⟨hr.1.1, hr.2.le⟩
      · intro r hr
        exact ⟨hr.1.1, hr.2⟩
    · refine ⟨Ioi a, isOpen_Ioi, hac.trans (lt_of_not_ge htc),
        RealTimeInterval.closed a 0 (has.trans hs).le, ?_, ?_, hVB⟩
      · intro r hr
        exact ⟨hr.2.le, hr.1.2⟩
      · intro r hr
        exact ⟨hr.2, hr.1.2⟩
  have hconv : ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ rho)
      (B.strictMono.comp hrho)) V := by
    intro K hK u v huv hsub order eta heta
    by_cases hvs : v ≤ c
    · have hsubT : Icc u v ⊆ Icc l s := fun t ht =>
        ⟨(hsub ht).1, ht.2.trans (hvs.trans hcs.le)⟩
      filter_upwards [hTconv K hK u v huv hsubT order eta heta] with i hi
      obtain ⟨Ci⟩ := hi.2.2
      exact ⟨hi.1, hi.2.1,
        nonempty_metricComparisonOn_congr_reference Ci (fun t ht => hgT (hsubT ht))⟩
    · by_cases hcu : c ≤ u
      · have hsubB : Icc u v ⊆ Icc a 0 := fun t ht =>
          ⟨hac.le.trans (hcu.trans ht.1), (hsub ht).2⟩
        filter_upwards [hrho.tendsto_atTop.eventually
          (B.convergence K hK u v huv hsubB order eta heta)] with i hi
        obtain ⟨Ci⟩ := hi.2.2
        exact ⟨hi.1, hi.2.1,
          nonempty_metricComparisonOn_congr_reference Ci (fun t ht => hgB (hsubB ht))⟩
      · have huc : u < c := lt_of_not_ge hcu
        have hcv : c < v := lt_of_not_ge hvs
        let a' := max a u
        let s' := min s v
        have hac' : a' < c := max_lt hac huc
        have hcs' : c < s' := lt_min hcs hcv
        have hus' : u ≤ s' := huc.le.trans hcs'.le
        have ha'v : a' ≤ v := hac'.le.trans hcv.le
        have hleft : Icc u s' ⊆ Icc l s := fun t ht =>
          ⟨(hsub (left_mem_Icc.mpr huv)).1.trans ht.1, ht.2.trans (min_le_left _ _)⟩
        have hright : Icc a' v ⊆ Icc a 0 := fun t ht =>
          ⟨(le_max_left _ _).trans ht.1, ht.2.trans (hsub (right_mem_Icc.mpr huv)).2⟩
        filter_upwards [hTconv K hK u s' hus' hleft order eta heta,
          hrho.tendsto_atTop.eventually
            (B.convergence K hK a' v ha'v hright order eta heta)] with i hi hj
        obtain ⟨Ci⟩ := hi.2.2
        obtain ⟨Cj⟩ := hj.2.2
        refine ⟨?_, hi.2.1, ?_⟩
        · intro t ht
          by_cases htc : t ≤ c
          · exact hi.1 ⟨ht.1, htc.trans hcs'.le⟩
          · exact hj.1 ⟨hac'.le.trans (lt_of_not_ge htc).le, ht.2⟩
        · exact nonempty_metricComparisonOn_glue (le_max_right a u) hac' hcs'
            (min_le_right s v) Ci Cj (fun t ht =>
              heq ⟨(le_max_left a u).trans ht.1, ht.2.trans (min_le_left s v)⟩)
  obtain ⟨CT, hCT⟩ := hTbound
  obtain ⟨CB, hCB⟩ := B.compact_time_bound a 0 (has.trans hs).le Subset.rfl
  have hbound : ∀ t ∈ Icc l 0, ∀ x : L.space.M,
      FlowMetricBall.rmNormSq V t x ≤ max CT CB := by
    intro t ht x
    by_cases htc : t ≤ c
    · change FlowMetricBall.rmNormSq (flowOn D g) t x ≤ _
      change DifferentialGeometry.Tensor0SBundle.normSq0S (g t) x 4
        (metricRm04At (g t) x) ≤ _
      rw [hgT ⟨ht.1, htc.trans hcs.le⟩]
      exact (hCT t ⟨ht.1, htc.trans hcs.le⟩ x).trans (le_max_left _ _)
    · change DifferentialGeometry.Tensor0SBundle.normSq0S (g t) x 4
        (metricRm04At (g t) x) ≤ _
      rw [hgB ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩]
      exact (hCB t ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩ x).trans (le_max_right _ _)
  refine ⟨{ solution := V
            isSolution := hV
            terminal := ?_
            subseq := B.subseq ∘ rho
            strictMono := B.strictMono.comp hrho
            convergence := hconv
            complete := ?_
            nonnegative := ?_
            compact_time_bound := fun u v _huv hsub =>
              ⟨max CT CB, fun t ht x => hbound t (hsub ht) x⟩ }, rfl, hgB, hgT⟩
  · exact (hgB ⟨(has.trans hs).le, le_rfl⟩).trans B.terminal
  · intro t ht
    change MetricComplete { L.space with metric := g t }
    by_cases htc : t ≤ c
    · rw [hgT ⟨ht.1, htc.trans hcs.le⟩]
      exact (hTcomplete t ⟨ht.1, htc.trans hcs.le⟩).complete
    · rw [hgB ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩]
      exact B.complete t ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩
  · intro t ht
    change SecLower (g t) 0 univ
    by_cases htc : t ≤ c
    · rw [hgT ⟨ht.1, htc.trans hcs.le⟩]
      exact hTnonneg t ⟨ht.1, htc.trans hcs.le⟩
    · rw [hgB ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩]
      exact B.nonnegative t ⟨(hac.trans (lt_of_not_ge htc)).le, ht.2⟩


theorem exists_backwardExtension_before_left_endpoint_of_model_curvature_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (a : ℝ) (ha : a < 0)
        (B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le)),
        ∃ b : ℝ, ∃ hb : b < a, ∃ rho : ℕ → ℕ, StrictMono rho ∧
          ∃ E : BackwardExtension L (RealTimeInterval.closed b 0 (hb.trans ha).le),
            E.subseq = B.subseq ∘ rho ∧
            ∀ t ∈ Icc a 0, E.solution.base.metric t = B.solution.base.metric t := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_convergent_backward_flow_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L a ha B
  obtain ⟨C, hC⟩ := B.compact_time_bound a 0 ha.le Subset.rfl
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C
  have hscalar : ∀ t ∈ Icc a 0, ∀ x : L.space.M, B.solution.scalar t x ≤ A := by
    intro t ht x
    exact (le_abs_self _).trans ((scalar_abs_le_rm (B.solution.base.metric t) x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hC t ht x)) (by positivity)))
  obtain ⟨width, hw, hwidth⟩ := hflow eps heps hle A
  let s := a + min (width / 2) (-a / 2)
  have has : a < s := by
    dsimp [s]
    have : 0 < min (width / 2) (-a / 2) := lt_min (by positivity) (by linarith)
    linarith
  have hs : s < 0 := by
    dsimp [s]
    linarith [min_le_right (width / 2) (-a / 2)]
  have hleft : s - width < a := by
    dsimp [s]
    linarith [min_le_left (width / 2) (-a / 2)]
  obtain ⟨rho, hrho, T, hT, _hterminal, hnonneg, hcomplete, hconv,
    ⟨C', _hC', hbound⟩, hoverlap⟩ :=
      hwidth X L _ B s ⟨has.le, hs.le⟩ (hscalar s ⟨has.le, hs.le⟩)
  obtain ⟨E, hsubseq, hagree, _hTmetric⟩ := backwardExtension_of_overlapping_flow
    hleft has hs B rho hrho T hT hnonneg hcomplete hconv ⟨C', hbound⟩
    (fun t ht => hoverlap t ⟨hleft.le.trans ht.1, ht.2⟩ ⟨ht.1, ht.2.trans hs.le⟩)
  exact ⟨s - width, hleft, rho, hrho, E, hsubseq, hagree⟩

theorem exists_backwardExtension_before_limit_of_scalar_le
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A : ℝ, ∃ width : ℝ, 0 < width ∧
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (a : ℕ → ℝ) (ha : ∀ n, a n < 0)
          (B : ∀ n, BackwardExtension L (RealTimeInterval.closed (a n) 0 (ha n).le))
          (s : ℕ → ℝ) (aStar : ℝ) (hleft : ∀ n, aStar < a n),
          (∀ n, s n ∈ Ioo (a n) 0) → Tendsto s atTop (𝓝 aStar) →
          (∀ n x, (B n).solution.scalar (s n) x ≤ A) →
          ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
            ∃ b : ℝ, ∃ hb : b < aStar, b ≤ aStar - width / 2 ∧
              ∃ rho : ℕ → ℕ, StrictMono rho ∧
                ∃ E : BackwardExtension L (RealTimeInterval.closed b 0
                  (hb.trans ((hleft n).trans (ha n))).le),
                  E.subseq = (B n).subseq ∘ rho ∧
                  ∀ t ∈ Icc (a n) 0,
                    E.solution.base.metric t = (B n).solution.base.metric t := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_convergent_backward_flow_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle A
  obtain ⟨width, hw, hwidth⟩ := hflow eps heps hle A
  refine ⟨width, hw, ?_⟩
  intro X L a ha B s aStar hleft hs hlimit hscalar N
  have hnear : ∀ᶠ n in atTop, s n < aStar + width / 2 :=
    hlimit.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨n, hN, hn⟩ := ((eventually_ge_atTop N).and hnear).exists
  let b := s n - width
  have hb : b < aStar := by dsimp [b]; linarith
  have hbwidth : b ≤ aStar - width / 2 := by dsimp [b]; linarith
  have hba : b < a n := hb.trans (hleft n)
  obtain ⟨rho, hrho, T, hT, _hterminal, hnonneg, hcomplete, hconv,
      ⟨C, _hC, hbound⟩, hoverlap⟩ :=
    hwidth X L _ (B n) (s n) ⟨(hs n).1.le, (hs n).2.le⟩ (hscalar n)
  obtain ⟨E, hsubseq, hagree, _hearlier⟩ := backwardExtension_of_overlapping_flow
    hba (hs n).1 (hs n).2 (B n) rho hrho T hT hnonneg hcomplete hconv ⟨C, hbound⟩
    (fun t ht => hoverlap t ⟨hba.le.trans ht.1, ht.2⟩ ⟨ht.1, ht.2.trans (hs n).2.le⟩)
  exact ⟨n, hN, b, hb, hbwidth, rho, hrho, E, hsubseq, hagree⟩

theorem exists_backwardExtension_before_left_endpoint_of_uniform_scalar_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ A : ℝ, ∃ width : ℝ, 0 < width ∧
          ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
            (a : ℝ) (ha : a < 0)
            (B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le)),
            (∀ t ∈ Icc a 0, ∀ x : L.space.M, B.solution.scalar t x ≤ A) →
            ∃ b : ℝ, ∃ hb : b < a, b ≤ a - width / 2 ∧
              ∃ rho : ℕ → ℕ, StrictMono rho ∧
                ∃ E : BackwardExtension L
                    (RealTimeInterval.closed b 0 (hb.trans ha).le),
                  E.subseq = B.subseq ∘ rho ∧
                  ∀ t ∈ Icc a 0,
                    E.solution.base.metric t = B.solution.base.metric t := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_convergent_backward_flow_before_time_of_scalar_le hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle A
  obtain ⟨width, hw, hwidth⟩ := hflow eps heps hle A
  refine ⟨width, hw, ?_⟩
  intro X L a ha B hscalar
  let s := a + min (width / 2) (-a / 2)
  have has : a < s := by
    dsimp [s]
    have hmin : 0 < min (width / 2) (-a / 2) :=
      lt_min (by positivity) (by linarith)
    linarith
  have hs : s < 0 := by
    dsimp [s]
    linarith [min_le_right (width / 2) (-a / 2)]
  have hleft : s - width < a := by
    dsimp [s]
    linarith [min_le_left (width / 2) (-a / 2)]
  have hdecrease : s - width ≤ a - width / 2 := by
    dsimp [s]
    linarith [min_le_left (width / 2) (-a / 2)]
  obtain ⟨rho, hrho, T, hT, _hterminal, hnonneg, hcomplete, hconv,
      ⟨C, _hC, hbound⟩, hoverlap⟩ :=
    hwidth X L _ B s ⟨has.le, hs.le⟩ (hscalar s ⟨has.le, hs.le⟩)
  obtain ⟨E, hsubseq, hagree, _hTmetric⟩ := backwardExtension_of_overlapping_flow
    hleft has hs B rho hrho T hT hnonneg hcomplete hconv ⟨C, hbound⟩
    (fun t ht => hoverlap t ⟨hleft.le.trans ht.1, ht.2⟩
      ⟨ht.1, ht.2.trans hs.le⟩)
  exact ⟨s - width, hleft, hdecrease, rho, hrho, E, hsubseq, hagree⟩

theorem exists_backwardExtension_before_time_of_uniform_scalar_bound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (a₀ : ℝ) (ha₀ : a₀ < 0)
          (B₀ : BackwardExtension L (RealTimeInterval.closed a₀ 0 ha₀.le)) (T A : ℝ),
          (∀ (a : ℝ) (ha : a < 0)
            (B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le)),
            T ≤ a → a ≤ a₀ →
            (∃ q : ℕ → ℕ, StrictMono q ∧ B.subseq = B₀.subseq ∘ q) →
            (∀ t ∈ Icc a₀ 0, B.solution.base.metric t = B₀.solution.base.metric t) →
            ∀ t ∈ Icc a 0, ∀ x : L.space.M, B.solution.scalar t x ≤ A) →
          ∃ b : ℝ, ∃ hb : b < 0, b < T ∧ b ≤ a₀ ∧
            ∃ q : ℕ → ℕ, StrictMono q ∧
              ∃ E : BackwardExtension L (RealTimeInterval.closed b 0 hb.le),
                E.subseq = B₀.subseq ∘ q ∧
                ∀ t ∈ Icc a₀ 0,
                  E.solution.base.metric t = B₀.solution.base.metric t := by
  obtain ⟨epsStar, hepsStar, hstep⟩ :=
    exists_backwardExtension_before_left_endpoint_of_uniform_scalar_bound hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L a₀ ha₀ B₀ T A hscalar
  classical
  obtain ⟨width, hw, hstep⟩ := hstep eps heps hle A
  let State := (a : {a : ℝ // a < 0}) ×
    BackwardExtension L (RealTimeInterval.closed a.1 0 a.2.le)
  let Good : State → Prop := fun d => d.1.1 ≤ a₀ ∧
    ∃ q : ℕ → ℕ, StrictMono q ∧ d.2.subseq = B₀.subseq ∘ q ∧
      ∀ t ∈ Icc a₀ 0, d.2.solution.base.metric t = B₀.solution.base.metric t
  by_contra hnot
  have hlower (d : State) (hd : Good d) : T ≤ d.1.1 := by
    by_contra hn
    obtain ⟨hda, q, hq, hsubseq, hagree⟩ := hd
    exact hnot ⟨d.1.1, d.1.2, lt_of_not_ge hn, hda, q, hq, d.2, hsubseq, hagree⟩
  have hiter : ∀ n : ℕ, ∃ d : State, Good d ∧
      d.1.1 ≤ a₀ - (n : ℝ) * (width / 2) := by
    intro n
    induction n with
    | zero =>
        refine ⟨⟨⟨a₀, ha₀⟩, B₀⟩, ?_, ?_⟩
        · exact ⟨le_rfl, id, strictMono_id, rfl, fun _ _ => rfl⟩
        · simp
    | succ n ih =>
        obtain ⟨d, hd, hdn⟩ := ih
        have hlow := hlower d hd
        obtain ⟨hda, q, hq, hsubseq, hagree⟩ := hd
        obtain ⟨b, hb, hdec, rho, hrho, E, hEsubseq, hEagree⟩ :=
          hstep X L d.1.1 d.1.2 d.2
            (hscalar d.1.1 d.1.2 d.2 hlow hda ⟨q, hq, hsubseq⟩ hagree)
        refine ⟨⟨⟨b, hb.trans d.1.2⟩, E⟩, ?_, ?_⟩
        · refine ⟨hb.le.trans hda, q ∘ rho, hq.comp hrho, ?_, ?_⟩
          · rw [hEsubseq, hsubseq]
            rfl
          · intro t ht
            exact (hEagree t ⟨hda.trans ht.1, ht.2⟩).trans (hagree t ht)
        · change b ≤ a₀ - ((n + 1 : ℕ) : ℝ) * (width / 2)
          push_cast
          linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((a₀ - T) / (width / 2))
  have hn' : a₀ - T < (n : ℝ) * (width / 2) :=
    (div_lt_iff₀ (half_pos hw)).mp hn
  obtain ⟨d, hd, hdn⟩ := hiter n
  have hlow := hlower d hd
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_cofinal_backwardExtensions_of_scalar_bounds
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (a₀ : ℝ) (ha₀ : a₀ < 0)
          (B₀ : BackwardExtension L (RealTimeInterval.closed a₀ 0 ha₀.le)),
          (∀ T : ℝ, ∃ A : ℝ,
            ∀ (a : ℝ) (ha : a < 0)
              (B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le)),
              T ≤ a → a ≤ a₀ →
              (∃ q : ℕ → ℕ, StrictMono q ∧ B.subseq = B₀.subseq ∘ q) →
              (∀ t ∈ Icc a₀ 0, B.solution.base.metric t = B₀.solution.base.metric t) →
              ∀ t ∈ Icc a 0, ∀ x : L.space.M, B.solution.scalar t x ≤ A) →
          ∃ a : ℕ → ℝ, ∃ ha : ∀ n, a n < 0,
            ∃ B : ∀ n, BackwardExtension L (RealTimeInterval.closed (a n) 0 (ha n).le),
              a 0 = a₀ ∧ StrictAnti a ∧ Tendsto a atTop atBot ∧
              (B 0).subseq = B₀.subseq ∧
              (∀ n t, t ∈ Icc a₀ 0 →
                (B n).solution.base.metric t = B₀.solution.base.metric t) ∧
              ∃ rho : ℕ → ℕ → ℕ, (∀ n, StrictMono (rho n)) ∧
                (∀ n, (B (n + 1)).subseq = (B n).subseq ∘ rho n) ∧
                (∀ n t, t ∈ Icc (a n) 0 →
                  (B (n + 1)).solution.base.metric t = (B n).solution.base.metric t) ∧
                (∀ n m t, t ∈ Icc (a n) 0 → t ∈ Icc (a m) 0 →
                  (B n).solution.base.metric t = (B m).solution.base.metric t) ∧
                ∃ q : ℕ → ℕ → ℕ, (∀ n, StrictMono (q n)) ∧
                  (∀ n, (B n).subseq = B₀.subseq ∘ q n) ∧
                  ∀ n, range (q (n + 1)) ⊆ range (q n) := by
  obtain ⟨epsStar, hepsStar, hreach⟩ :=
    exists_backwardExtension_before_time_of_uniform_scalar_bound hmod hsigma hPhi
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X L a₀ ha₀ B₀ hscalar
  classical
  let State := (a : {a : ℝ // a < 0}) ×
    BackwardExtension L (RealTimeInterval.closed a.1 0 a.2.le)
  let Good : State → Prop := fun d => d.1.1 ≤ a₀ ∧
    ∃ q : ℕ → ℕ, StrictMono q ∧ d.2.subseq = B₀.subseq ∘ q ∧
      ∀ t ∈ Icc a₀ 0, d.2.solution.base.metric t = B₀.solution.base.metric t
  let d₀ : {d : State // Good d} :=
    ⟨⟨⟨a₀, ha₀⟩, B₀⟩, le_rfl, id, strictMono_id, rfl, fun _ _ => rfl⟩
  have hnext : ∀ n : ℕ, ∀ d : {d : State // Good d},
      ∃ e : {d : State // Good d}, e.1.1.1 < min d.1.1.1 (-((n + 1 : ℕ) : ℝ)) ∧
        ∃ rho : ℕ → ℕ, StrictMono rho ∧ e.1.2.subseq = d.1.2.subseq ∘ rho ∧
          ∀ t ∈ Icc d.1.1.1 0, e.1.2.solution.base.metric t = d.1.2.solution.base.metric t := by
    intro n d
    let T := min d.1.1.1 (-((n + 1 : ℕ) : ℝ))
    obtain ⟨A, hA⟩ := hscalar T
    obtain ⟨hda, q, hq, hsubseq, hagree⟩ := d.2
    have hbound : ∀ (a : ℝ) (ha : a < 0)
        (B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le)),
        T ≤ a → a ≤ d.1.1.1 →
        (∃ r : ℕ → ℕ, StrictMono r ∧ B.subseq = d.1.2.subseq ∘ r) →
        (∀ t ∈ Icc d.1.1.1 0, B.solution.base.metric t = d.1.2.solution.base.metric t) →
        ∀ t ∈ Icc a 0, ∀ x : L.space.M, B.solution.scalar t x ≤ A := by
      intro a ha B hTa had ⟨r, hr, hBr⟩ hBg
      apply hA a ha B hTa (had.trans hda)
      · refine ⟨q ∘ r, hq.comp hr, ?_⟩
        rw [hBr, hsubseq]
        rfl
      · intro t ht
        exact (hBg t ⟨hda.trans ht.1, ht.2⟩).trans (hagree t ht)
    obtain ⟨b, hb, hbT, hbd, rho, hrho, E, hEsub, hEg⟩ :=
      hreach eps heps hle X L d.1.1.1 d.1.1.2 d.1.2 T A hbound
    have hgood : Good (⟨⟨b, hb⟩, E⟩ : State) := by
      refine ⟨hbd.trans hda, q ∘ rho, hq.comp hrho, ?_, ?_⟩
      · rw [hEsub, hsubseq]
        rfl
      · intro t ht
        exact (hEg t ⟨hda.trans ht.1, ht.2⟩).trans (hagree t ht)
    exact ⟨⟨⟨⟨b, hb⟩, E⟩, hgood⟩, hbT, rho, hrho, hEsub, hEg⟩
  choose next hnext using hnext
  let seq : ℕ → {d : State // Good d} :=
    fun n => Nat.rec d₀ (fun n d => next n d) n
  let a : ℕ → ℝ := fun n => (seq n).1.1.1
  have ha : ∀ n, a n < 0 := fun n => (seq n).1.1.2
  let B : ∀ n, BackwardExtension L (RealTimeInterval.closed (a n) 0 (ha n).le) :=
    fun n => (seq n).1.2
  have hstep : ∀ n, a (n + 1) < min (a n) (-((n + 1 : ℕ) : ℝ)) :=
    fun n => (hnext n (seq n)).1
  have hmaps : ∀ n, ∃ rho : ℕ → ℕ, StrictMono rho ∧
      (B (n + 1)).subseq = (B n).subseq ∘ rho ∧
        ∀ t ∈ Icc (a n) 0,
          (B (n + 1)).solution.base.metric t = (B n).solution.base.metric t :=
    fun n => (hnext n (seq n)).2
  choose rho hrho hsubseq hagree using hmaps
  have hanti : StrictAnti a := strictAnti_nat_of_succ_lt (fun n =>
    (hstep n).trans_le (min_le_left _ _))
  have hlimit : Tendsto a atTop atBot := by
    apply tendsto_atBot.2
    intro T
    obtain ⟨N, hN⟩ := exists_nat_gt (-T)
    filter_upwards [eventually_ge_atTop (N + 1)] with n hn
    have hn0 : n ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hsmall := (hstep k).trans_le (min_le_right _ _)
    have hNk : (N : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (by omega : N ≤ k + 1)
    linarith
  have hagree_le : ∀ n m, n ≤ m → ∀ t, t ∈ Icc (a n) 0 →
      (B m).solution.base.metric t = (B n).solution.base.metric t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m hnm ih =>
        intro t ht
        exact (hagree m t ⟨(hanti.antitone hnm).trans ht.1, ht.2⟩).trans (ih t ht)
  have hcompatible : ∀ n m t, t ∈ Icc (a n) 0 → t ∈ Icc (a m) 0 →
      (B n).solution.base.metric t = (B m).solution.base.metric t := by
    intro n m t hn hm
    rcases le_total n m with hnm | hmn
    · exact (hagree_le n m hnm t hn).symm
    · exact hagree_le m n hmn t hm
  let q : ℕ → ℕ → ℕ := fun n => Nat.rec id (fun n q => q ∘ rho n) n
  have hq : ∀ n, StrictMono (q n) := by
    intro n
    induction n with
    | zero => exact strictMono_id
    | succ n ih => exact ih.comp (hrho n)
  have hqsubseq : ∀ n, (B n).subseq = B₀.subseq ∘ q n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [hsubseq n, ih]
        rfl
  have hnest : ∀ n, range (q (n + 1)) ⊆ range (q n) := by
    intro n x hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨rho n i, rfl⟩
  refine ⟨a, ha, B, rfl, hanti, hlimit, rfl, ?_, rho, hrho, hsubseq, hagree,
    hcompatible, q, hq, hqsubseq, hnest⟩
  intro n t ht
  exact (seq n).2.2.choose_spec.2.2 t ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
