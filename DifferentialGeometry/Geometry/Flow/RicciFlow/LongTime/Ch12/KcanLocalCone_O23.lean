import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueLocalCone
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanVolumeLeaf_O14
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Curvature.LocalPullbackRicci

/-!
# CH12-O23, group 2: K-core S1 bottom — the `hvol` interface from the centre volume

`ricci_lower_of_buffer_O23`: inside the escape radius, the normalized terminal metrics have
compact closed balls and `Ric ≥ -2 q₀²` (normalized), from the scalar buffer bound, the backward
traces and the pinching, via the parabolically Rm-controlled terminal balls
(`exists_uniform_parabolically_controlled_incoming_terminal_ball_radius`) at every point.

`hvol_of_buffer_centre_O23`: with a volume lower bound at the CENTRE only (normalized scales
`≤ a₀`), this gives exactly the `hvol` interface of the local KL70.2 chain (O14's leaf
`normalized_ball_volume_of_centre_O14`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance opensSigmaCompact_O23 {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [SigmaCompactSpace X] (U : TopologicalSpace.Opens X) :
    SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

/-- Ricci lower bound transported along a local diffeomorphism (pull-back metric). -/
private theorem ricci_lower_of_localPull_O23 {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric ThreeModel N) (f : M → N)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (p : M) (c : ℝ)
    (h : ∀ v : TangentSpace ThreeModel p,
      -c * (localPullMetric (I := ThreeModel) (J := ThreeModel) g f hf).inner p v v ≤
        ricciTensor (I := ThreeModel) (localPullMetric (I := ThreeModel) (J := ThreeModel) g f hf)
          p v v) :
    ∀ w : TangentSpace ThreeModel (f p),
      -c * g.inner (f p) w w ≤ ricciTensor (I := ThreeModel) g (f p) w w := by
  intro w
  obtain ⟨e, he⟩ := hf.isInvertible_mfderiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) p
  have hw : mfderiv ThreeModel ThreeModel f p (e.symm w) = w := by rw [← he]; simp
  have := h (e.symm w)
  rw [ricciTensor_localPullMetric, localPullMetric_inner, hw] at this
  exact this

/-- **Ricci lower bound and compactness inside the escape radius** (normalized terminal metrics). -/
theorem ricci_lower_of_buffer_O23
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n) :
    ∀ R : ℝ, R < rho → ∃ q₀ : ℝ, 0 ≤ q₀ ∧ ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) R) ∧
      ∀ z ∈ riemannianBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) R,
        ∀ v : TangentSpace ThreeModel z,
        -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * q₀ ^ 2) *
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric).inner z v v ≤
          ricciTensor (I := ThreeModel)
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) z v v := by
  intro R hRrho
  set R' : ℝ := max R (rho / 2) with hR'def
  have hR' : 0 < R' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hR'rho : R' < rho := max_lt hRrho (by linarith)
  have hRR' : R ≤ R' := le_max_left _ _
  obtain ⟨b, A, θ0, hb, -, hA, hθ0, hbudget, hbuf⟩ := hbuffer R' hR' hR'rho
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  set θ : ℝ := min (A * θ0) ((b / 2 * Real.sqrt A) ^ 2) with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθA : θ ≤ A * θ0 := min_le_left _ _
  obtain ⟨α, hα, -, hαθ, hball⟩ :=
    ObservedHistory.exists_uniform_parabolically_controlled_incoming_terminal_ball_radius hPhi hθ
  have hαb : α ≤ b / 2 * Real.sqrt A := by
    have hh : α ^ 2 ≤ (b / 2 * Real.sqrt A) ^ 2 := hαθ.trans (min_le_right _ _)
    nlinarith [mul_pos (half_pos hb) hsqrtA]
  set q₀ : ℝ := Real.sqrt (9 * A / (2 * α ^ 2)) with hq₀def
  have hq₀sq : 2 * q₀ ^ 2 = 9 * (A / α ^ 2) := by
    rw [hq₀def, Real.sq_sqrt (by positivity)]
    field_simp
  refine ⟨q₀, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hbuf] with n hn
  obtain ⟨first, htrace, hstart⟩ := hn.2.2
  have hQp : 0 < Q n := zero_lt_one.trans_le (hQ n)
  have hAQ : 1 ≤ A * Q n := (hQ n).trans (le_mul_of_one_le_left hQp.le hA)
  have hsqrtQ : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQp
  refine ⟨hn.1.of_isClosed_subset
      (isClosed_riemannianClosedBallOf_O14 _ (x n) R)
      (riemannianClosedBallOf_mono _ (x n) (hRR'.trans (le_add_of_nonneg_right hb.le))), ?_⟩
  intro z hz w
  have hz' : z ∈ riemannianClosedBallOf
      (scaleMetric (Q n) hQp (L n).metric) (x n) R' :=
    le_of_lt (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hRR'))
  have hsub : riemannianClosedBallOf (L n).metric z (b / Real.sqrt (Q n)) ⊆
      riemannianClosedBallOf (scaleMetric (Q n) hQp (L n).metric) (x n) (R' + b) := by
    have heq : riemannianClosedBallOf (L n).metric z (b / Real.sqrt (Q n)) =
        riemannianClosedBallOf (scaleMetric (Q n) hQp (L n).metric) z b := by
      rw [← riemannianClosedBallOf_scaleMetric (Q n) hQp]
      congr 1
      field_simp
    rw [heq]
    exact riemannianClosedBallOf_subset_of_add_radius_le _ hR'.le hb.le le_rfl hz'
  have hcompact : IsCompact (riemannianClosedBallOf (L n).metric z (b / Real.sqrt (Q n))) :=
    hn.1.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 _ z _) hsub
  have hstart' : (H n).time first ≤ s n - θ / (A * Q n) := by
    have hh : θ / (A * Q n) ≤ θ0 / Q n := by
      have hh := div_le_div_of_nonneg_right hθA (mul_pos hAp hQp).le
      have heq : A * θ0 / (A * Q n) = θ0 / Q n := by field_simp
      rwa [heq] at hh
    linarith
  have hbudget' : 6 * C * θ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hθA (by positivity)).trans hbudget
  have hradius : α / Real.sqrt (A * Q n) < b / Real.sqrt (Q n) := by
    rw [Real.sqrt_mul hAp.le, div_lt_div_iff₀ (by positivity) hsqrtQ]
    nlinarith [mul_pos hb hsqrtA, mul_pos hsqrtA hsqrtQ]
  obtain ⟨p, S, hfp, -, -, hSs, -, -, B, -, hBr, hB, hBset, -, -, -⟩ :=
    hball (H n).toHistory first (Fin.last (H n).eventCount) (Fin.le_last first) (G n) (L n) z
      hAQ (hinit n) (div_pos hb hsqrtQ) hcompact (hq n)
      ((hqQ n).trans (le_mul_of_one_le_left hQp.le hA))
      (fun j _ _ => hderiv n j) (fun y _ => hfinal n y.val)
      (fun j _ _ => hpinch n j) (hpinchFinal n)
      (fun y hy => hn.2.1 y (hsub hy)) (fun y hy => htrace y (hsub hy)) hstart' hbudget'
      hradius
  have hrpos : 0 < α / Real.sqrt (A * Q n) := div_pos hα (Real.sqrt_pos.mpr (by positivity))
  have hpB : p ∈ B.set := by rw [hBset]; exact mem_riemannianBallOf_self_O13 _ p hrpos
  have hctl : B.radius ^ 4 * Perelman.FlowMetricBall.rmNormSq S (s n) p ≤ 1 :=
    hB.2 (s n) ⟨sub_le_self _ (sq_nonneg _), le_rfl⟩ p hpB
  rw [hBr] at hctl
  have hnorm : Perelman.FlowMetricBall.rmNormSq S (s n) p ≤
      1 / (α / Real.sqrt (A * Q n)) ^ 4 :=
    (le_div_iff₀ (pow_pos hrpos 4)).2 (by simpa only [mul_comm] using hctl)
  have hs2 : Real.sqrt (A * Q n) ^ 2 = A * Q n := Real.sq_sqrt (by positivity)
  have h1 : 1 / (α / Real.sqrt (A * Q n)) ^ 4 = (A * Q n / α ^ 2) ^ 2 := by
    rw [div_pow, one_div_div,
      show Real.sqrt (A * Q n) ^ 4 = (Real.sqrt (A * Q n) ^ 2) ^ 2 by ring, hs2, div_pow]
    ring
  have hroot : Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (I := ThreeModel)
      (S.base.metric (s n)) p 4 (metricRm04At (I := ThreeModel) (S.base.metric (s n)) p)) ≤
      A * Q n / α ^ 2 := by
    have h2 := Real.sqrt_le_sqrt (h := hnorm)
    rw [h1, Real.sqrt_sq (by positivity)] at h2
    simpa only [Perelman.FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply] using h2
  have hR := fun v => Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := ThreeModel)
    (S.base.metric (s n)) hroot v
  rw [hSs] at hR
  have key := ricci_lower_of_localPull_O23 (L n).metric _ _ p _ hR
  have key' := hfp ▸ key
  have hw := key' w
  rw [scaleMetric_inner, ricciTensor_scaleMetric]
  have hfin : (((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ)) = 2 := by simp
  have hfin3 : ((Module.finrank ℝ ThreeSpace : ℕ) : ℝ) = 3 := by simp
  rw [hfin]
  rw [hfin3] at hw
  calc -(2 * q₀ ^ 2) * (Q n * (L n).metric.inner z w w)
      = -((3 : ℝ) ^ 2 * (A * Q n / α ^ 2)) * (L n).metric.inner z w w := by
        rw [hq₀sq]; ring
    _ ≤ _ := hw

/-- **The `hvol` interface of the local KL70.2 chain from the centre volume** (K-can leaf
`normalized_ball_volume_of_centre_O14` + `ricci_lower_of_buffer_O23`). -/
theorem hvol_of_buffer_centre_O23
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ a₀ : ℝ} (hκ : 0 < κ) (ha₀ : 0 < a₀)
    (hvx : ∀ᶠ n in atTop, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            (x n) b)) :
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            y a) :=
  normalized_ball_volume_of_centre_O14 (I := ThreeModel) (M := fun n => (G n).terminalRegularOpen)
    (fun n => scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) x hκ ha₀ hvx
    (ricci_lower_of_buffer_O23 Phi hPhi H s G L hinit x q Q hq hqQ hQ hderiv hfinal hpinch
      hpinchFinal hrho hbuffer)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance pointedLimitRegular_O23 (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- **KL70.2 normalized terminal pointed convergence, K-can form**: the Cone theorem of the O3 chain
with the local volume test `(σ, hσ, hloc)` replaced by the centre volume `hvx`. -/
theorem exists_normalized_terminal_pointed_convergence_kcan_O23
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (_hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ y : ((H n).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n, ∀ y : ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ a₀ : ℝ} (hκ : 0 < κ) (ha₀ : 0 < a₀)
    (hvx : ∀ᶠ n in atTop, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            (x n) b)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
          F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  have hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            y a) :=
    hvol_of_buffer_centre_O23 Phi hPhi H s G L hinit x q Q hq hqQ hQ hderiv hfinal hpinch
      hpinchFinal hrho hbuffer hκ ha₀ hvx
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces
      Phi hPhi (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) s G L hinit
      x q Q hq hqQ hQ (fun n j _ => hderiv n j) hfinal (fun n j _ => hpinch n j)
      hpinchFinal hrho (by
        intro R hR hRrho
        obtain ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, hb⟩ := hbuffer R hR hRrho
        refine ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, ?_⟩
        filter_upwards [hb] with n hn
        obtain ⟨first, htrace, hstart⟩ := hn.2.2
        exact ⟨hn.1, hn.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  have hbase : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M hM (by
      intro n
      change metricScalarAt (scaleMetric (Q (f n)) (zero_lt_one.trans_le (hQ (f n)))
        (L (f n)).metric) (x (f n)) = 1
      rw [metricScalarAt_scaleMetric, ← hscale (f n), inv_mul_cancel₀]
      exact ne_of_gt (zero_lt_one.trans_le (hQ (f n))))
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩

end GC.LongTime.Ch12
