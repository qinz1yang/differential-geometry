import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthAnchorDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingWindowAnchorBound

/-!
# O-CH11-FIX3 port of astra `BirthWindowAnchorBound`（`PortC11P`）

来源：donor
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/BirthWindowAnchorBound.lean`
（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。修补（elaboration only；no statement / definition /
proof idea altered）：
* `open private RetainedCoreHistory.exists_spatialCanonicalWitness_before_birth
  RetainedCoreHistory.curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched from …` 的模块名
  `BirthTimeZeroBound` → `BirthTimeZeroBoundPortC11P`（private 名字在 port 模块里）；
* 两处调用写全名 `RetainedCoreHistory.…`（短名不再解析到 opened private 声明）。

原路径 `BirthWindowAnchorBound` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn

open private depth_schedule_facts opensSigmaCompactAnchor from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingWindowAnchorBound
open private RetainedCoreHistory.exists_spatialCanonicalWitness_before_birth
  RetainedCoreHistory.curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBoundPortC11P

attribute [local instance] opensSigmaCompactAnchor

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {ε C1 C2 κ ρ : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D q R : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {t : ∀ n, Icc (0 : ℝ) (H n).toHistory.horizon}
  {y : ∀ n, ((H n).toHistory.stageAt (t n)).Carrier}
  (hεcone : ε ≤ coneAccuracy) (hκ : 0 < κ) (hρ : 0 < ρ)
  (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n ∧ q n < R n)
  (hbirth : ∀ n, (H n).time ((H n).toHistory.activeStage (t n)) = (t n : ℝ))
  (hne : ∀ n, (H n).toHistory.activeStage (t n) ≠ 0)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * q n ≤ ((records n i).static b).neck.scale)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi)
  (hlast : ∀ n, (H n).toHistory.activeStage (t n) = Fin.last (H n).eventCount →
    ∃ h : (H n).time (Fin.last (H n).eventCount) < (H n).horizon,
      Perelman.PhiAlmostNonnegative ((H n).finalSlab h).flow
        (Icc ((H n).time (Fin.last (H n).eventCount)) (H n).horizon) phi)
  (hslabs : ∀ n,
    (H n).EventSlabsSpatiallyCanonical ε C1 C2 (q n) ((H n).toHistory.activeStage (t n)) ∧
    (H n).EventSlabsDerivative Ctime (q n) ((H n).toHistory.activeStage (t n)) ∧
    (H n).EventSlabsGradient Cgrad (q n) ((H n).toHistory.activeStage (t n)))
  (hnc : ∀ n, (H n).NoncollapsedBefore κ ρ (t n))

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact in
include hεcone hκ hρ hphi hinit hrec hq hbirth hne hpar hscale hpinch
  hlast hslabs hnc in
/-- Actual traced regions at every smaller depth produce one scalar anchor
bound, uniform in both depth and spatial radius, along a further subsequence.
The closed birth metric and all backward traces belong to the supplied history. -/
theorem exists_subseq_windowAnchorBound_at_birth_of_depthExtendable
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {Tstar : ℝ} (hT : 0 < Tstar)
    (hext : ∀ T : ℝ, 0 < T → T < Tstar →
      ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R σ T) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((H (σ (ψ i))).toHistory.stageMetric
          ((H (σ (ψ i))).toHistory.activeStage (t (σ (ψ i)))) (t (σ (ψ i)))) (y (σ (ψ i)))
          (A / Real.sqrt (R (σ (ψ i)))),
      ∀ (w : Icc (0 : ℝ) (H (σ (ψ i))).toHistory.horizon),
        (w : ℝ) = (t (σ (ψ i)) : ℝ) - T' / R (σ (ψ i)) →
      ∀ (hwt : w ≤ t (σ (ψ i)))
        (Bt : BackwardPointTrace (H (σ (ψ i))).toHistory
          ((H (σ (ψ i))).toHistory.activeStage w)
          ((H (σ (ψ i))).toHistory.activeStage (t (σ (ψ i))))
          ((H (σ (ψ i))).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((H (σ (ψ i))).toHistory.stageMetric
            ((H (σ (ψ i))).toHistory.activeStage w) w)
          (Bt.point ((H (σ (ψ i))).toHistory.activeStage w) le_rfl
            ((H (σ (ψ i))).toHistory.activeStage_mono hwt)) ≤ M * R (σ (ψ i)) := by
  have hRpos : ∀ n, 0 < R n := fun n =>
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hq n).2
  obtain ⟨hτs0, hτsT, hc0, hcτ, hcmono, hcex⟩ := depth_schedule_facts hT
  have hcT' : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < Tstar := fun k => (hcτ k).trans (hτsT k)
  have hcT : ∀ s ∈ Ioc (-Tstar) 0, ∃ k : ℕ, -(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) < s := fun s hs =>
    (hcex (-s) (by linarith [hs.1])).imp fun _ hk => by linarith
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hRσ : Tendsto (fun m => R (σ m)) atTop atTop := hRlim.comp hσ.tendsto_atTop
  have hgapσ : Tendsto (fun m => R (σ m) * ((t (σ m) : ℝ) - (t (σ m) : ℝ)))
      atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨W, h, hblock, hlip, -, hlow, hpinchW, hncW, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn,
      hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hGsol, hGcompat, ψ₁, hψ₁, hconv⟩ :=
    ObservedHistory.exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule
      (fun m => (H (σ m)).toHistory) (fun m => t (σ m)) (fun m => y (σ m))
      (fun m => R (σ m)) (fun m => hRpos (σ m)) hRσ
      (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) hτs0
      (fun k => hext _ (hτs0 k) (hτsT k) _ (by positivity))
      hκ hρ (t₀ := fun m => (t (σ m) : ℝ)) hgapσ
      (fun m v z r hv hr hb => hnc (σ m) v z r hv.le hr hb) hphi
      (fun m v hv z => RetainedCoreHistory.curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched
        (H (σ m)) (hpinch (σ m)) (hlast (σ m)) v hv z)
  let _ : ConnectedSpace P.M := hconn
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  obtain ⟨Gl, hGlsol, hGlres⟩ :=
    exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule hT V hVmono hVcover
      Gloc hGsol hGcompat
  have hGl0 : Gl 0 = P.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨k, hk⟩ := hVcover x
    have heq := (hGlres k 0 ⟨by linarith [hc0 k], le_rfl⟩).trans (hG0 k)
    exact congrArg (fun q : SmoothRiemannianMetric ThreeModel (V k) => q.inner ⟨x, hk⟩ v w) heq
  have hconvG : ∀ k (K' : Set (V k)), IsCompact K' → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ₁ i,
        ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))) 0,
        metricDerivNormSupOn K' p
          (localPullMetric (h k (f (ψ₁ i)) s) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi))
          ((Gl s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
    intro k K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    refine ⟨hi', fun s hs => ?_⟩
    rw [hGlres k s hs]
    exact hb s hs
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-(Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) 0
          (neg_nonpos.mpr (hτs0 k).le))) := fun k => (hblock k).mono fun _ hn => hn.2.1
  let E' : ℕ → Set ℝ := fun m => Iic 0 ∩
    ({s | (t (σ m) : ℝ) ≤ (t (σ m) : ℝ) + s / R (σ m)} ∪
      {s | ∃ i, (t (σ m) : ℝ) + s / R (σ m) =
        (H (σ m)).toHistory.time i})
  have hEs : ∀ m s, s ≤ 0 → s ∉ E' m →
      (t (σ m) : ℝ) + s / R (σ m) < (t (σ m) : ℝ) ∧
        ∀ i, (t (σ m) : ℝ) + s / R (σ m) ≠
          (H (σ m)).toHistory.time i := by
    intro m s hs hsE
    simp only [E', mem_inter_iff, mem_Iic, mem_union, mem_ofPred_eq, not_and, not_or,
      not_exists] at hsE
    obtain ⟨h1, h2⟩ := hsE hs
    exact ⟨not_le.mp h1, h2⟩
  have hE' : ∀ m, (E' m \ Icc (-(R (σ m) *
      ((t (σ m) : ℝ) - (t (σ m) : ℝ)))) 0).Finite := by
    intro m
    refine (Set.finite_range fun i : Fin ((H (σ m)).toHistory.eventCount + 1) =>
      R (σ m) *
        ((H (σ m)).toHistory.time i - t (σ m))).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsI⟩
    have hs0 : s ≤ 0 := hs0
    have hRm := hRpos (σ m)
    rcases hs with hs | ⟨i, hi⟩
    · refine absurd ⟨?_, hs0⟩ hsI
      have hs' : ((t (σ m) : ℝ) - t (σ m)) * R (σ m) ≤ s :=
        (le_div_iff₀ hRm).mp (show (t (σ m) : ℝ) - t (σ m) ≤
            s / R (σ m) by
          have : (t (σ m) : ℝ) ≤ (t (σ m) : ℝ) + s / R (σ m) := hs
          linarith)
      linarith
    · refine ⟨i, ?_⟩
      have hi' : (t (σ m) : ℝ) + s / R (σ m) =
          (H (σ m)).toHistory.time i := hi
      have : s / R (σ m) =
          (H (σ m)).toHistory.time i - t (σ m) := by
        linarith
      change R (σ m) *
        ((H (σ m)).toHistory.time i - t (σ m)) = s
      rw [← this, mul_div_assoc']
      exact mul_div_cancel_left₀ s hRm.ne'
  obtain ⟨Dneck, -, hL1⟩ :=
    ObservedHistory.exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks.{u}
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max (2 * |C1|) C2) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hC0 : max (2 * |C1|) C2 ≤ C := hC ▸ le_max_right _ _
  obtain ⟨qW, hqW⟩ : ∃ qW : ℝ,
      qW = max 1 ((Real.exp 1 * (C + (Dneck + 2 * ε⁻¹) * Real.sqrt C)) ^ 2) := ⟨_, rfl⟩
  have hqWsq : (Real.exp 1 * (C + (Dneck + 2 * ε⁻¹) * Real.sqrt C)) ^ 2 ≤ qW :=
    hqW ▸ le_max_right _ _
  have hqWs : 1 ≤ qW := hqW ▸ le_max_left _ _
  have hqs' : ∀ m, q (σ m) ≤ R (σ m) * qW := fun m =>
    (hq (σ m)).2.le.trans (le_mul_of_one_le_right (hRpos (σ m)).le hqWs)
  have hW := hL1 (Hs := fun m => (H (σ m)).toHistory) (ts := fun m => t (σ m))
    (ys := fun m => y (σ m)) (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hτs0 (fun k => (hcτ k).le)
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.1)
    (fun k => (hblock k).mono fun _ hn => by
      obtain ⟨a, hat, ha, fs, hfs, hinj, -, -, hp⟩ := hn.2.2.2.1
      exact ⟨a, hat, ha, fs, hfs, hinj, hp⟩) hlow (t₀ := fun m => (t (σ m) : ℝ)) (E := E')
    (qs := fun m => q (σ m)) hε hC1 hC0 hqs' hqWsq
    (fun m v hv hvk p hpq => RetainedCoreHistory.exists_spatialCanonicalWitness_before_birth
      (H (σ m)) (hbirth (σ m)) (hslabs (σ m)).1 v hv hvk p hpq) hEs
  have hderiv := ObservedHistory.eventually_abs_derivWithin_scalar_le_of_survivor_blocks
    (Hs := fun m => (H (σ m)).toHistory) (ts := fun m => t (σ m))
    (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (τ := fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
    (fun k => (hblock k).mono fun _ hn => by
      obtain ⟨a, hat, ha, fs, hfs, -, -, -, hp⟩ := hn.2.2.2.1
      exact ⟨a, hat, ha, fs, hfs, hp⟩) (E := E')
    (Ct := (Ctime : ℝ)) (qD := 1) Ctime.coe_nonneg
    (qst := fun m => q (σ m)) (fun m => by simpa only [mul_one] using (hq (σ m)).2.le)
    (fun m v hv hvk p hpq =>
      (H (σ m)).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt
        (t := t (σ m)) (t₀ := (t (σ m) : ℝ)) le_rfl (hslabs (σ m)).2.1
        ((H (σ m)).derivativeBound_inputs_at_birth (hbirth (σ m)) Ctime (q (σ m))).1
        ((H (σ m)).derivativeBound_inputs_at_birth (hbirth (σ m)) Ctime (q (σ m))).2
        v hv hvk p hpq)
    (fun m s hs hsE => (hEs m s hs hsE).2)
  have hX4d := eventually_scalar_le_at_normalized_distance_before_birth
    hεcone hκ hρ hphi hinit hrec hq hbirth hne hpar hscale hpinch hslabs hnc
  have happrox := ObservedHistory.survivor_blocks_scalar_le_at_distance
    (Hs := fun m => (H (σ m)).toHistory) (ts := fun m => t (σ m))
    (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (τ := fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
    (fun k => (hblock k).mono fun _ hn => by
      obtain ⟨a, hat, ha, fs, hfs, -, -, -, hp⟩ := hn.2.2.2.1
      exact ⟨a, hat, ha, fs, hfs, hp⟩)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) (fun k => (hcτ k).le)
    (fun A Dd hA hD => (hX4d A Dd hA hD).imp fun _ hC' s hs =>
      hσ.tendsto_atTop.eventually (hC'.2 s hs))
  have hradii : Tendsto (fun m => ρ * Real.sqrt (R (σ m))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hRσ).const_mul_atTop hρ
  obtain ⟨C₀, hC₀⟩ := exists_uniform_scalar_bound_of_local_flow_limit_on_window hf F Cd hcan hPc
    hconn hV hVF hφF
    (fun k => by
      filter_upwards [hf.tendsto_atTop.eventually (hblock k),
        hballF ((k + 3 : ℕ) : ℝ) (by positivity)] with j hj hb x hx
      have hx' : x ∈ (W k (f j) : Set _) := hx
      rw [hj.1] at hx'
      exact hb (show riemannianEDistOf _ _ _ ≤ _ from le_of_lt hx'))
    hT hτs0 hcτ hcmono hcT hGl0 hGlsol hψ₁ hconvG hsol hRσ hphi
    (fun k => (hpinchW k).mono fun _ hn s hs x => hn s ⟨by linarith [hs.1, hcτ k], hs.2⟩ x)
    hlip hgapσ hE' hεX hC1 (by positivity : (0 : ℝ) < κ / 250) hW hderiv
    (fun hcomplete =>
      parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed
        hT (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
        (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hc0 hcτ hcT' hcmono hcex hsol hκ
        hradii hncW hf F hVmono hVcover hVF φ hφ hφF hGlsol hcomplete hψ₁ hconvG 1 one_pos)
    happrox
  refine ⟨fun i => f (ψ₁ i), hf.comp hψ₁, max C₀ 0 + 1, by positivity,
    fun T' hT' hT'T A hA => ?_⟩
  exact ObservedHistory.eventually_scalar_backwardPointTrace_le_of_window_limit
    (Hs := fun m => (H (σ m)).toHistory) (ts := fun m => t (σ m)) (ys := fun m => y (σ m))
    (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (τ := fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1) hf F Cd hcan hPc hV hφF
    (fun k => (hcτ k).le) hcmono hcT hψ₁ hconvG hC₀ hT' hT'T hA


include hεcone hκ hρ hphi hinit hrec hq hbirth hne hpar hscale hpinch
  hlast hslabs hnc in
/-- The actual positive-depth producer and maximal-depth selector yield either
all depths, or a maximal finite family with its uniform scalar anchor bound.
No traced-depth family or anchor bound is assumed by this receiving theorem. -/
theorem exists_subseq_all_depth_or_maximal_window_at_birth
    (hε : 0 < ε) (hεX : ε ≤ crossingNeckAccuracy.{u})
    (hεW : ε ≤ crossingWindowNeckAccuracy.{u})
    {θcap : ℕ → ℝ}
    (hRscalar : ∀ n, R n = metricScalarAt
      ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) ((H n).toHistory.activeStage (t n))
      (y n) (t n) (D n) (θcap n))
    (σ₀ : ℕ → ℕ) (hσ₀ : StrictMono σ₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ T : ℝ, 0 < T →
        ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R (σ₀ ∘ ψ) T) ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧ ∃ M : ℝ, 0 ≤ M ∧
        (∀ T : ℝ, 0 < T → T < Tstar →
          ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R (σ₀ ∘ ψ) T) ∧
        (∀ χ : ℕ → ℕ, StrictMono χ → ∀ T : ℝ, Tstar < T →
          ¬ ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R
            ((σ₀ ∘ ψ) ∘ χ) T) ∧
        ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
        ∀ x ∈ riemannianBallOf ((H (σ₀ (ψ i))).toHistory.stageMetric
            ((H (σ₀ (ψ i))).toHistory.activeStage (t (σ₀ (ψ i)))) (t (σ₀ (ψ i))))
            (y (σ₀ (ψ i))) (A / Real.sqrt (R (σ₀ (ψ i)))),
        ∀ (w : Icc (0 : ℝ) (H (σ₀ (ψ i))).toHistory.horizon),
          (w : ℝ) = (t (σ₀ (ψ i)) : ℝ) - T' / R (σ₀ (ψ i)) →
        ∀ (hwt : w ≤ t (σ₀ (ψ i)))
          (Bt : BackwardPointTrace (H (σ₀ (ψ i))).toHistory
            ((H (σ₀ (ψ i))).toHistory.activeStage w)
            ((H (σ₀ (ψ i))).toHistory.activeStage (t (σ₀ (ψ i))))
            ((H (σ₀ (ψ i))).toHistory.activeStage_mono hwt) x),
          metricScalarAt ((H (σ₀ (ψ i))).toHistory.stageMetric
              ((H (σ₀ (ψ i))).toHistory.activeStage w) w)
            (Bt.point ((H (σ₀ (ψ i))).toHistory.activeStage w) le_rfl
              ((H (σ₀ (ψ i))).toHistory.activeStage_mono hwt)) ≤ M * R (σ₀ (ψ i))) := by
  let E : (ℕ → ℕ) → ℝ → Prop :=
    ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R
  have hRpos : ∀ n, 0 < R n := fun n =>
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hq n).2
  have hbase := exists_subseq_depthExtendable_pos_at_birth_of_initialIdentification
    hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hpar hscale hθcap hpinch
    hlast hslabs hnc hnot hε hεX σ₀ hσ₀
  obtain ⟨ψ₀, hψ₀, hmax⟩ := DifferentialGeometry.exists_strictMono_maximal_depth E
    (fun _ _ _ hT' hle he => ObservedHistory.DepthExtendable.mono_depth he hRpos hT' hle)
    (fun _ _ _ hψ he => ObservedHistory.DepthExtendable.comp he hψ)
    (fun _ _ _ heq he => ObservedHistory.DepthExtendable.congr he heq) σ₀ hbase
  rcases hmax with hinf | ⟨Tstar, hT, hext, hmax⟩
  · exact ⟨ψ₀, hψ₀, Or.inl hinf⟩
  · obtain ⟨ψ₁, hψ₁, M, hM, hanc⟩ :=
      exists_subseq_windowAnchorBound_at_birth_of_depthExtendable
        hεcone hκ hρ hphi hinit hrec hq hbirth hne hpar hscale hpinch
        hlast hslabs hnc hε hεW (hσ₀.comp hψ₀) hT hext
    refine ⟨ψ₀ ∘ ψ₁, hψ₀.comp hψ₁, Or.inr ⟨Tstar, hT, M, hM, ?_, ?_, ?_⟩⟩
    · intro T hTpos hTT
      simpa only [Function.comp_assoc] using
        ObservedHistory.DepthExtendable.comp (hext T hTpos hTT) hψ₁
    · intro χ hχ T hTT he
      apply hmax (ψ₁ ∘ χ) (hψ₁.comp hχ) T hTT
      simpa only [Function.comp_assoc] using he
    · simpa only [Function.comp_apply] using hanc

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
