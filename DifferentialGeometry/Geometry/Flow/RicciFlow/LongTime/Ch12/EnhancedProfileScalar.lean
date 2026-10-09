import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceBoundedThreshold

/-!
# CH12-O2, group 2 (W4 / M02): KL70.2 at a fixed scale, constants independent of the history

`exists_scalar_bound_at_distance_explicit_O2` is the kernel
`RetainedCoreHistory.exists_scalar_bound_at_distance_of_bounded_threshold`
(`Surgery/Topology/BoundedCurvatureAtDistanceBoundedThreshold.lean:900`) with its cone tolerance
made explicit (`εKL70_O2`); the proof is the kernel's, verbatim.  This is what allows P4 to be a
plain numerical inequality on the profile's `epsilon`.

`W4_scalar_bound_O2`: from the profile plus P4, for every fixed `κ > 0`, `Ctime` (the P2 constant),
`Cgrad` and admissible `phi`, and for every `A > 0`, `Cq`, the constants `Q, Λ ≥ 1` are chosen
**before** the history `H`; they depend only on `(κ, Hp.C1, Hp.C2, Ctime, Cgrad, phi, A, Cq)`.
The remaining premises (canonical witnesses above `q`, slab derivative/gradient/pinching bounds,
terminal `κ`-noncollapsing at scale `ρ`) are per-instance and stay in the statement.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular_O2 (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem exists_riemannianEDistOf_lt_of_mem_Icc_scalar_O2 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) {f : M → ℝ} (hf : Continuous f) {y z : M}
    {r : ℝ} (hyz : riemannianEDistOf g y z < ENNReal.ofReal r) {c : ℝ}
    (hc : c ∈ Icc (f y) (f z)) :
    ∃ x, f x = c ∧ riemannianEDistOf g x z < ENNReal.ofReal r := by
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hyz)
  have hconn := (isPathConnected_riemannianBallOf g z hr).isConnected.isPreconnected
  have hy : y ∈ riemannianBallOf g z r := by
    change riemannianEDistOf g z y < _
    rwa [riemannianEDistOf_comm]
  have hz : z ∈ riemannianBallOf g z r := by
    change riemannianEDistOf g z z < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨x, hx, hfx⟩ := hconn.intermediate_value hy hz hf.continuousOn hc
  refine ⟨x, hfx, ?_⟩
  have hx' : riemannianEDistOf g z x < ENNReal.ofReal r := hx
  rwa [riemannianEDistOf_comm]

/-- The KL70.2 kernel (`BoundedCurvatureAtDistanceBoundedThreshold.lean:900`) with the explicit
cone tolerance `εKL70_O2`.  Proof copied verbatim from the kernel. -/
theorem exists_scalar_bound_at_distance_explicit_O2
    (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∀ ε : ℝ, ε ≤ εKL70_O2 → ∀ A : ℝ, 0 < A → ∀ Cq : ℝ,
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * S.flow.scalar t y → Λ ≤ S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        H.TerminalNoncollapsedBefore hend (S.restrictIncoming le_rfl S.lt le_rfl) hS κ ρ t →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          S.flow.scalar t z ≤ Q * S.flow.scalar t y := by
  intro ε hεle A hA Cq
  have hεle' : ε ≤ min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) /
      (13000 * 13000) := hεle
  clear hεle
  have hεle := hεle'
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  let K := max Cq 1
  have hK : 1 ≤ K := le_max_right _ _
  by_contra hcon
  push Not at hcon
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  choose H hend t S hS y q ρ hq hqy hΛ hwin hW hderiv hfinal hgrad hpinch hpinchF hnc hρ z hz
    hbad using fun n : ℕ => hcon ((n : ℝ) + K + 1) ((n : ℝ) + K + 1)
      (by linarith [hn0 n]) (by linarith [hn0 n])
  have hRy (n : ℕ) : (n : ℝ) + K + 1 ≤ (S n).flow.scalar (t n) (y n) := hΛ n
  have hRpos (n : ℕ) : 0 < (S n).flow.scalar (t n) (y n) := by linarith [hRy n, hn0 n]
  have hqK (n : ℕ) : q n ≤ K * (S n).flow.scalar (t n) (y n) :=
    (hqy n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hRpos n).le)
  have hcmem (n : ℕ) : max (q n) ((S n).flow.scalar (t n) (y n)) ∈
      Icc ((S n).flow.scalar (t n) (y n)) ((S n).flow.scalar (t n) (z n)) := by
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · nlinarith [hbad n, hqK n, hRpos n, hn0 n]
    · nlinarith [hbad n, hRpos n, hn0 n]
  have hcontR (n : ℕ) : Continuous ((S n).flow.scalar (t n)) :=
    (metricScalar_smooth ((S n).flow.base.metric (t n))).continuous
  choose xc hxc hxz using fun n => exists_riemannianEDistOf_lt_of_mem_Icc_scalar_O2
    ((S n).flow.base.metric (t n)) (hcontR n)
      (show riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) <
        ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) from hz n) (hcmem n)
  let x : ∀ n, ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen := fun n =>
    ⟨xc n, by
      change xc n ∈ ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      trivial⟩
  have hRx (n : ℕ) : (S n).flow.scalar (t n) (x n).val =
      max (q n) ((S n).flow.scalar (t n) (y n)) := hxc n
  have hyx (n : ℕ) : (S n).flow.scalar (t n) (y n) ≤ (S n).flow.scalar (t n) (x n).val := by
    rw [hRx]
    exact le_max_right _ _
  have hxK (n : ℕ) : (S n).flow.scalar (t n) (x n).val ≤ K * (S n).flow.scalar (t n) (y n) := by
    rw [hRx]
    exact max_le (hqK n) (le_mul_of_one_le_left (hRpos n).le hK)
  have hQ (n : ℕ) : 1 ≤ (S n).flow.scalar (t n) (x n).val := by
    linarith [hyx n, hRy n, hn0 n]
  have hqQ (n : ℕ) : q n ≤ (S n).flow.scalar (t n) (x n).val := by
    rw [hRx]
    exact le_max_left _ _
  have hQlim : Tendsto (fun n => (S n).flow.scalar (t n) (x n).val) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    linarith [hyx n, hRy n, hK]
  have hwindow (n : ℕ) : (H n).time (Fin.last (H n).eventCount) ≤
      t n - 1 / (S n).flow.scalar (t n) (x n).val := by
    have h1 : 1 / (S n).flow.scalar (t n) (x n).val ≤ 1 / (S n).flow.scalar (t n) (y n) :=
      one_div_le_one_div_of_le (hRpos n) (hyx n)
    have h2 : 1 / (S n).flow.scalar (t n) (y n) ≤
        ((n : ℝ) + K + 1) / (S n).flow.scalar (t n) (y n) :=
      div_le_div_of_nonneg_right (by linarith [hn0 n]) (hRpos n).le
    linarith [hwin n]
  have hσQ (n : ℕ) : 1 ≤ ρ n * Real.sqrt ((S n).flow.scalar (t n) (x n).val) := by
    have h1 : 1 ≤ ρ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) :=
      le_trans (by linarith [hn0 n]) (hρ n)
    have hρpos : 0 ≤ ρ n := by
      by_contra hneg
      have := mul_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (Real.sqrt_nonneg
        ((S n).flow.scalar (t n) (y n)))
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hyx n)) hρpos)
  obtain ⟨B, hB⟩ :=
    RetainedCoreHistory.exists_normalized_scalar_bound_of_bounded_threshold
    H t S hS (fun n => by rw [← hend n]; exact (S n).lt) Ctime Cgrad q hq
    (fun n j y' t' ht hqy' => hderiv n j (Fin.castSucc_lt_last j) y' t' ht hqy')
    (fun n y' t' ht hqy' => hfinal n y' t' ht hqy')
    (fun n y' t' ht hqy' => hgrad n y' t' ht hqy') x hQ hqQ hQlim one_pos hwindow hphi
    (fun n => hpinch n) (fun n => hpinchF n) ρ hκ one_pos hσQ
    (fun n T hT hTs => by
      intro _ tm yy b _ hbρ hball
      exact hnc n T (by rw [hend n]; exact hT) hTs hTs.le tm yy b le_rfl hbρ hball)
    heps (fun n => hW n) (A * Real.sqrt K + 1) (by positivity)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B * K⌉₊)).exists
  let z' : ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, by
      change z n ∈ ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      trivial⟩
  have hsx := Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ n))
  have hsy := Real.sqrt_pos.mpr (hRpos n)
  have hratio : Real.sqrt ((S n).flow.scalar (t n) (x n).val) ≤
      Real.sqrt K * Real.sqrt ((S n).flow.scalar (t n) (y n)) := by
    rw [← Real.sqrt_mul (zero_le_one.trans hK)]
    exact Real.sqrt_le_sqrt (hxK n)
  have hdist : riemannianEDistOf (scaleMetric ((S n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ n)) ((S n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (A * Real.sqrt K + 1) := by
    rw [DifferentialGeometry.edistOf_scale, (S n).riemannianEDistOf_endpointTerminalLimitMetric]
    change ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val)) *
      riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (z n) < _
    calc ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val)) *
          riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (z n) <
        ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val)) *
          ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsx).ne' ENNReal.ofReal_ne_top (hxz n)
      _ = ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val) *
          (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) :=
          (ENNReal.ofReal_mul hsx.le).symm
      _ ≤ ENNReal.ofReal (A * Real.sqrt K) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc', div_le_iff₀ hsy]
          nlinarith [hratio]
      _ < ENNReal.ofReal (A * Real.sqrt K + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((S n).endpointTerminalLimitMetric _).metric z' =
      (S n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal, div_le_iff₀ (zero_lt_one.trans_le (hQ n))] at hle
  have hceil : B * K ≤ (n : ℝ) := (Nat.le_ceil (B * K)).trans (by exact_mod_cast hnB.le)
  have hbig := hbad n
  have hxKn := hxK n
  have hRyn := hRpos n
  have hn1 := hn0 n
  rcases le_or_gt 0 B with hB0 | hB0
  · have h1 : B * (S n).flow.scalar (t n) (x n).val ≤
        B * (K * (S n).flow.scalar (t n) (y n)) := mul_le_mul_of_nonneg_left hxKn hB0
    have h2 : B * K * (S n).flow.scalar (t n) (y n) ≤ n * (S n).flow.scalar (t n) (y n) :=
      mul_le_mul_of_nonneg_right hceil hRyn.le
    nlinarith
  · have h1 : B * (S n).flow.scalar (t n) (x n).val ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hB0.le (zero_le_one.trans (hQ n))
    nlinarith

/-- **W4 output** (statement shape, used as an argument of the micro-regime glue): KL70.2 at a
fixed scale with the profile's `epsilon, C1, C2`, constants `Q, Λ` chosen before the history. -/
def W4Output_O2 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (κ : ℝ) (Ctime Cgrad : ℝ≥0)
    (phi : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ Cq : ℝ,
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * S.flow.scalar t y → Λ ≤ S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) Hp.epsilon Hp.C1 Hp.C2 x,
            W.capTubeHasNeckChart Hp.epsilon) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        H.TerminalNoncollapsedBefore hend (S.restrictIncoming le_rfl S.lt le_rfl) hS κ ρ t →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          S.flow.scalar t z ≤ Q * S.flow.scalar t y

/-- **W4 / M02.**  Under P4, the fixed-scale KL70.2 bound holds with constants independent of the
history (for every fixed `κ > 0`, the P2 constant `Ctime`, any `Cgrad` and admissible `phi`). -/
theorem W4_scalar_bound_O2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hP4 : P4_O2 Hp) (κ : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    W4Output_O2 Hp κ Ctime Cgrad phi :=
  exists_scalar_bound_at_distance_explicit_O2.{u} κ Hp.C1 Hp.C2 hκ Ctime Cgrad hphi
    Hp.epsilon hP4

end GC.LongTime.Ch12
