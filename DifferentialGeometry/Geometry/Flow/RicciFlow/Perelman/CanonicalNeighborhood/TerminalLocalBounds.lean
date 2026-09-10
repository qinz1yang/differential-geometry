import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCarrierBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompleteGlobal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance terminalLocalC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance terminalLocalC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [I.Boundaryless] in
theorem closedBall_isCompact_subset_of_local_metric_lower
    (h g : SmoothRiemannianMetric I M) (p : M) {R L r : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hlower : ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I y, h.inner y v v ≤ L ^ 2 * g.inner y v v) :
    IsCompact (riemannianClosedBallOf (I := I) g p r) ∧
      riemannianClosedBallOf (I := I) g p r ⊆ riemannianClosedBallOf (I := I) h p R := by
  let F := PartialDiffeomorph.refl (I := I) M
  have hsub := closedBall_subset_image_of_metric_lower h g F p hR hL hr hcpt
    (Set.subset_univ _) (fun y hy v => by
      change h.inner y v v ≤ L ^ 2 * g.inner y
        (mfderiv I I (id : M → M) y v) (mfderiv I I (id : M → M) y v)
      simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using hlower y hy v)
  have hsub' : riemannianClosedBallOf (I := I) g p r ⊆
      riemannianClosedBallOf (I := I) h p R := by
    change riemannianClosedBallOf (I := I) g p r ⊆
      (id : M → M) '' riemannianClosedBallOf (I := I) h p R at hsub
    simpa only [Set.image_id] using hsub
  refine ⟨hcpt.of_isClosed_subset ?_ hsub', hsub'⟩
  exact isClosed_le (continuous_riemannianEDist g p) continuous_const

omit [CompleteSpace E] [I.Boundaryless] in
theorem fixed_inner_ball_subset_of_local_metric_bounds
    (h g : SmoothRiemannianMetric I M) (p : M) {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hlower : ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I y, h.inner y v v ≤ L ^ 2 * g.inner y v v)
    (hupper : ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I y, g.inner y v v ≤ L ^ 2 * h.inner y v v) :
    IsCompact (riemannianClosedBallOf (I := I) g p (R / (2 * L))) ∧
      riemannianClosedBallOf (I := I) g p (R / (2 * L)) ⊆
        riemannianClosedBallOf (I := I) h p R ∧
      riemannianClosedBallOf (I := I) h p (R / (8 * L ^ 2)) ⊆
        riemannianClosedBallOf (I := I) g p (R / (4 * L)) := by
  have hhalf : R / (2 * L) < R / L := by
    apply div_lt_div_of_pos_left hR hL
    linarith
  have hquarter : R / (4 * L) < R / L := by
    apply div_lt_div_of_pos_left hR hL
    linarith
  obtain ⟨hfull, hfullsub⟩ := closedBall_isCompact_subset_of_local_metric_lower
    h g p hR hL hhalf hcpt hlower
  obtain ⟨hsmall, hsmallsub⟩ := closedBall_isCompact_subset_of_local_metric_lower
    h g p hR hL hquarter hcpt hlower
  have hinner : R / (8 * L ^ 2) < (R / (4 * L)) / L := by
    rw [div_div]
    apply div_lt_div_of_pos_left hR (by positivity)
    nlinarith [sq_pos_of_pos hL]
  exact ⟨hfull, hfullsub,
    (closedBall_isCompact_subset_of_local_metric_lower g h p (by positivity) hL hinner
      hsmall (fun y hy v => hupper y (hsmallsub hy) v)).2⟩

section Flow

variable [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]

omit [I.Boundaryless] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
private theorem curvature_normSq_timeRestrict
    {D D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (k : ℕ) (t : ℝ) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (S.timeRestrict D') k t x =
      nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  simp only [nablaKRm04NormSqIntrinsic, nablaKRm_eq_iterCov, SolutionOn.timeRestrict]

theorem shi_bound_on_sliding_regular_window
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b tau K R t : ℝ} (hab : a < b) (htau : 0 < tau) (hK : 0 < K) (hR : 0 < R)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ Set.Ioo (a + tau) b) (p : M)
    (hball : IsCompact {y : M | riemannianEDistOf (I := I)
      (S.base.metric (t - tau)) p y ≤ ENNReal.ofReal (R / Real.sqrt K)})
    (hcurv : ∀ s ∈ Set.Icc (t - tau) t, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric (t - tau)) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) →
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric (t - tau)) p x ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K)) →
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiLocalUniformBound (Module.finrank ℝ E) m (K * tau) R * K / Real.sqrt tau ^ m := by
  let Sco := S.timeRestrict (RealTimeInterval.closedOpen a b hab)
  have hSco : IsSolutionOn Sco := isSolutionOn_timeRestrict hS
    (fun s hs => hslab ⟨hs.1, hs.2.le⟩) hreg
  let F := timeShiftSolution (I := I) Sco (t - tau)
  have hF : IsSolutionOn F := isSolutionOn_timeShiftSolution hSco (t - tau)
  have hleft : a - (t - tau) < 0 := by linarith [ht.1]
  have hright : tau < b - (t - tau) := by linarith [ht.2]
  have h0 : (0 : ℝ) ∈
      (RealTimeInterval.closedOpen (a - (t - tau)) (b - (t - tau))
        (sub_lt_sub_right hab (t - tau))).carrier := ⟨hleft.le, htau.trans hright⟩
  have hmetric : F.base.metric 0 = S.base.metric (t - tau) := by
    change S.base.metric (0 + (t - tau)) = _
    rw [zero_add]
  have hnorm (k : ℕ) (s : ℝ) (x : M) :
      nablaKRm04NormSqIntrinsic (I := I) F k s x =
        nablaKRm04NormSqIntrinsic (I := I) S k (s + (t - tau)) x := by
    dsimp only [F]
    rw [nablaKRm04NormSqIntrinsic_timeShiftSolution, curvature_normSq_timeRestrict]
  have hball' : IsCompact {y : M | riemannianEDistOf (I := I) (F.base.metric 0) p y ≤
      ENNReal.ofReal (R / Real.sqrt K)} := by simpa only [hmetric] using hball
  have hcurv' : ∀ s ∈ Set.Icc (0 : ℝ) tau, ∀ y : M,
      riemannianEDistOf (I := I) (F.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) →
      nablaKRm04NormSqIntrinsic (I := I) F 0 s y ≤ K ^ 2 := by
    intro s hs y hy
    rw [hnorm]
    exact hcurv _ ⟨by linarith [hs.1], by linarith [hs.2]⟩ y (hmetric ▸ hy)
  intro m x hx
  have hh := (shi_local_all_orders_curvature_scale_of_solution_uniform F hF p
    hleft hK htau hright hR h0 hball' hcurv' m tau ⟨htau, le_rfl⟩ x
      (by simpa only [hmetric] using hx)).2
  simpa only [hnorm, show tau + (t - tau) = t by ring] using hh

theorem curvature_derivative_bound_on_fixed_inner_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b tau K R L : ℝ} (hab : a < b) (htau : 0 < tau) (hK : 0 < K)
    (hR : 0 < R) (hL : 0 < L)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (h : SmoothRiemannianMetric I M) (p : M)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hlower : ∀ s ∈ Set.Icc a b, ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I y, h.inner y v v ≤ L ^ 2 * (S.base.metric s).inner y v v)
    (hupper : ∀ s ∈ Set.Icc a b, ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I y, (S.base.metric s).inner y v v ≤ L ^ 2 * h.inner y v v)
    (hcurv : ∀ s ∈ Set.Icc a b, ∀ y ∈ riemannianClosedBallOf (I := I) h p R,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioo (a + tau) b,
      ∀ x ∈ riemannianClosedBallOf (I := I) h p (R / (8 * L ^ 2)),
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiLocalUniformBound (Module.finrank ℝ E) m (K * tau)
          (R * Real.sqrt K / (2 * L)) * K / Real.sqrt tau ^ m := by
  intro m t ht x hx
  have hstart : t - tau ∈ Set.Icc a b := by
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨hball, hcapture, hinner⟩ := fixed_inner_ball_subset_of_local_metric_bounds
    h (S.base.metric (t - tau)) p hR hL hcpt (hlower _ hstart) (hupper _ hstart)
  have hsk : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
  have hfull : (R * Real.sqrt K / (2 * L)) / Real.sqrt K = R / (2 * L) := by
    field_simp [hsk, hL.ne']
  have hhalf : (R * Real.sqrt K / (2 * L)) / (2 * Real.sqrt K) = R / (4 * L) := by
    field_simp [hsk, hL.ne']
    ring
  apply shi_bound_on_sliding_regular_window S hS hab htau hK (by positivity)
    hslab hreg ht p
    (by simpa only [hfull, riemannianClosedBallOf] using hball) ?_ m x
    (by simpa only [hhalf, riemannianClosedBallOf, Set.mem_ofPred_eq] using hinner hx)
  intro s hs y hy
  apply hcurv s ⟨hstart.1.trans hs.1, hs.2.trans ht.2.le⟩ y
  exact hcapture (by simpa only [hfull, riemannianClosedBallOf, Set.mem_ofPred_eq] using hy)

theorem exists_local_curvature_derivative_bounds_before_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ (U : Set M) (c : ℝ) (C : ℕ → ℝ), IsOpen U ∧ p ∈ U ∧
      IsCompact (closure U) ∧ a < c ∧ c < b ∧
      ∀ m : ℕ, ∀ t ∈ Set.Ioo c b, ∀ x ∈ U,
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C m := by
  obtain ⟨h, _V, hcomplete, _hV, _hpV, _heq, _hdom⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (I := I)
      (S.base.metric b) (K := {p}) isCompact_singleton
  have hcpt : IsCompact (riemannianClosedBallOf (I := I) h p 1) :=
    hcomplete.closedEBall_isCompact p 1
  obtain ⟨L, K, hL, hK, hmetric, hcurv⟩ :=
    solution_compact_carrier_metric_curvature_bounds S hS hslab h hcpt
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let tau := (b - a) / 4
  have htau : 0 < tau := by dsimp [tau]; linarith
  let r := 1 / (8 * L ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  let U := riemannianBallOf (I := I) h p r
  have hU : IsOpen U := isOpen_lt (continuous_riemannianEDist h p) continuous_const
  have hp : p ∈ U := by
    change riemannianEDistOf (I := I) h p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hUclosed : U ⊆ {x : M | riemannianEDistOf (I := I) h p x ≤ ENNReal.ofReal r} := by
    intro x hx
    change riemannianEDistOf (I := I) h p x ≤ ENNReal.ofReal r
    exact le_of_lt hx
  have hclosure : IsCompact (closure U) :=
    (hcomplete.closedEBall_isCompact p r).of_isClosed_subset isClosed_closure
      (closure_minimal hUclosed
        (isClosed_le (continuous_riemannianEDist h p) continuous_const))
  let C : ℕ → ℝ := fun m => shiLocalUniformBound (Module.finrank ℝ E) m (K * tau)
    (1 * Real.sqrt K / (2 * L)) * K / Real.sqrt tau ^ m
  refine ⟨U, a + 2 * tau, C, hU, hp, hclosure, by linarith,
    by dsimp [tau]; linarith, ?_⟩
  intro m t ht x hx
  apply curvature_derivative_bound_on_fixed_inner_ball S hS hab htau hK zero_lt_one
    hLp hslab hreg h p hcpt
    (fun s hs y hy v => (hmetric s hs y hy v).1)
    (fun s hs y hy v => (hmetric s hs y hy v).2)
    (fun s hs y hy => by
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero] using hcurv s hs y hy)
    m t ⟨by linarith [ht.1], ht.2⟩ x
  change riemannianEDistOf (I := I) h p x ≤ ENNReal.ofReal r
  change riemannianEDistOf (I := I) h p x < ENNReal.ofReal r at hx
  exact le_of_lt hx

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
