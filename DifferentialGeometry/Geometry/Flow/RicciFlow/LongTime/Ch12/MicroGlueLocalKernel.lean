import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueLocalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueLocalBackward
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileScalar
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall

/-!
# CH12-O3, group 1e: the KL70.2 kernel with a LOCAL terminal volume test

* `exists_normalized_scalar_bound_local_O3`: `ST/BoundedCurvatureAtDistanceBoundedThreshold.lean:760`
  with the history test replaced by the local terminal test about the centres `x i`.
* `exists_scalar_bound_at_distance_local_O3`: the kernel `:900` (in the explicit-`εcone` form of
  `exists_scalar_bound_at_distance_explicit_O2`) with `TerminalNoncollapsedBefore κ ρ t` replaced by
  the **terminal-time, local** volume test
  `∀ z, d_t(y, z) < ρ → ∀ b ∈ (0, ρ], vol_t B(z, b) ≥ κ b³`.
  `Q, Λ` are still chosen before the history: they depend only on
  `(κ, C1, C2, Ctime, Cgrad, phi, ε, A, Cq)`.  In the long-time application `κ = κ(w)` comes from
  the volume test of the test ball (Bishop–Gromov), not from the profile's decaying `kappa`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
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

private local instance pointedLimitRegular_O3c (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

theorem exists_normalized_scalar_bound_local_O3
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hQlim : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ)
    (hσlim : Tendsto (fun i => σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val)) atTop atTop)
    (hloc : ∀ i (z : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((A i).endpointTerminalLimitMetric
        ((H i).stage (Fin.last (H i).eventCount))).metric (x i) z < ENNReal.ofReal (σ i) →
      ∀ b : ℝ, 0 < b → b ≤ σ i →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric
            (riemannianBallOf ((A i).endpointTerminalLimitMetric
              ((H i).stage (Fin.last (H i).eventCount))).metric z b))
    {eps C1 C2 : ℝ}
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps) :
    ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) y < ENNReal.ofReal R →
        metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric y /
            (A i).flow.scalar (time i) (x i).val ≤ B := by
  intro R hR
  by_contra hB
  have hL1 := exists_pointed_convergence_at_scalar_escape_local_O3
    H time A hinit hs Ctime Cgrad q hq hderiv hfinal hgradient x hQ hqQ θ₀ hθ₀ hwindow
    ⟨R, hR, hB⟩ Phi hPhi hpinch hpinchFinal κ σ hκ hσlim hloc
  dsimp only at hL1
  obtain ⟨rho, hrho, ind, hind, z, f, hf, r, hr, hrlim, Pl, F₀, M, _, hcan, hradial, hcompact,
      hcapture, hmetric, hfinite, hdist, hescape⟩ := hL1
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun i =>
          { M := ((A (ind i)).restrictIncoming le_rfl (A (ind i)).lt le_rfl).terminalRegularOpen
            basepoint := x (ind i)
            metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (zero_lt_one.trans_le (hQ (ind i)))
              ((A (ind i)).endpointTerminalLimitMetric
                ((H (ind i)).stage (Fin.last (H (ind i)).eventCount))).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x (ind i)))
    (fun i => (mem_connectedComponent : x (ind i) ∈
      connectedComponentOpen (I := ThreeModel) (x (ind i)))) F₀
  have halpha : (0 : ℝ) < 1 / 4000000 := by norm_num
  obtain ⟨g, hg, _, hblow, hnecks⟩ :=
    exists_isometric_ray_with_spatialNecks_of_bounded_threshold
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) Ctime Cgrad (fun i => q (ind i)) (fun i => hfinal (ind i))
    (fun i => hgradient (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i))
    (fun i => hqQ (ind i)) halpha (by norm_num) heps
    (fun i => hW (ind i)) hrho f hf r (fun n => (hr n).1) hrlim Pl F M hcan hradial hcompact
    hcapture (fun ε hε => (hmetric ε hε).mono fun n hn y hy v => (hn y hy v).1)
    (fun n => z (f n)) hfinite hdist hescape
  have hsec := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i)) hPhi
    (fun i => hpinchFinal (ind i)) Pl F M hcan (hQlim.comp (hind.comp hf).tendsto_atTop)
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨qc, hqc, _⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hrho hg
  obtain ⟨W, hWc, hrest⟩ := exists_punctured_cone_end_of_spatial_necks Pl.metric
    (fun _ _ => rfl) hrho halpha (by norm_num) hsec g hg hblow qc hqc hnecks
  let _ : PathConnectedSpace W := hWc
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, _, _, _, hxW, _, hQW, hlowerW, hupperW,
    hcone⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by simpa only [metricScalarAt_restrictOpen] using hlowerW n
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
      dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    exact ⟨B, by simpa only [metricScalarAt_restrictOpen] using hB⟩
  exact final_slab_punctured_cone_end_exclusion_local_O3
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) Ctime (fun i => q (ind i)) (fun i => hq _) (fun i => hderiv (ind i))
    (fun i => hfinal (ind i)) (fun i => x (ind i)) (fun i => hQ _) (fun i => hqQ _)
    hθ₀ (fun i => hwindow _) hPhi (fun i => hpinch _)
    (fun i => hpinchFinal _) (fun i => σ (ind i)) hκ (hσlim.comp hind.tendsto_atTop)
    (fun i => hloc (ind i)) (fun i => hW (ind i)) hf Pl F M hcan hradial hcompact W hWc qW delta
    hdelta hK
    hcover hcone xW hxW hQW' _ (by norm_num) hlower' hupper'


private theorem exists_riemannianEDistOf_lt_of_mem_Icc_scalar_O3 {M : Type*} [TopologicalSpace M]
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

/-- **The KL70.2 kernel with a local terminal volume test** (`ST/BoundedCurvatureAtDistanceBoundedThreshold.lean:900`
in the explicit-`εcone` form, with `TerminalNoncollapsedBefore κ ρ t` replaced by
`∀ z, d_t(y, z) < ρ → ∀ b ∈ (0, ρ], vol_t B(z, b) ≥ κ b³`).  `Q, Λ` precede the history. -/
theorem exists_scalar_bound_at_distance_local_O3
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
        (∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
          riemannianEDistOf (S.flow.base.metric t) y z < ENNReal.ofReal ρ →
          ∀ b : ℝ, 0 < b → b ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
                (S.flow.base.metric t) (riemannianBallOf (S.flow.base.metric t) z b)) →
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
  choose xc hxc hxz using fun n => exists_riemannianEDistOf_lt_of_mem_Icc_scalar_O3
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
  -- the local test transported from `y n` (radius `ρ n`) to `x n` (radius `σ n`)
  let σ : ℕ → ℝ := fun n => ρ n - 2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))
  have hσlim : Tendsto (fun n => σ n * Real.sqrt ((S n).flow.scalar (t n) (x n).val))
      atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + (K + 1 - 2 * A)) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards [eventually_ge_atTop ⌈2 * A⌉₊] with n hn
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have hid : σ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) =
        ρ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) - 2 * A := by
      change (ρ n - 2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) *
        Real.sqrt ((S n).flow.scalar (t n) (y n)) = _
      field_simp
    have h2A : 2 * A ≤ (n : ℝ) := (Nat.le_ceil (2 * A)).trans (by exact_mod_cast hn)
    have hρn := hρ n
    have hlow : (n : ℝ) + (K + 1 - 2 * A) ≤ σ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) := by
      rw [hid]; linarith
    have hσ0 : 0 ≤ σ n := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hsy
      linarith [hK]
    exact hlow.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hyx n)) hσ0)
  have hloc : ∀ n (zz : ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((S n).endpointTerminalLimitMetric
        ((H n).stage (Fin.last (H n).eventCount))).metric (x n) zz < ENNReal.ofReal (σ n) →
      ∀ b : ℝ, 0 < b → b ≤ σ n →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen
            ((S n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            (riemannianBallOf ((S n).endpointTerminalLimitMetric
              ((H n).stage (Fin.last (H n).eventCount))).metric zz b) := by
    intro n zz hzz b hb hbσ
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    set a' := A / Real.sqrt ((S n).flow.scalar (t n) (y n)) with ha'
    have ha'0 : 0 ≤ a' := div_nonneg hA.le hsy.le
    have hσρ : σ n ≤ ρ n := by change ρ n - 2 * a' ≤ ρ n; linarith
    have hσpos : 0 < σ n := hb.trans_le hbσ
    rw [(S n).riemannianEDistOf_endpointTerminalLimitMetric] at hzz
    have hyz : riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) zz.val <
        ENNReal.ofReal (ρ n) := by
      have h1 : riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) <
          ENNReal.ofReal a' := hz n
      have h2 : riemannianEDistOf ((S n).flow.base.metric (t n)) (z n) (xc n) <
          ENNReal.ofReal a' := by
        rw [riemannianEDistOf_comm]; exact hxz n
      calc riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) zz.val
          ≤ riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (xc n) +
              riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) zz.val :=
            riemannianEDistOf_triangle _ _ _ _
        _ ≤ (riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) +
              riemannianEDistOf ((S n).flow.base.metric (t n)) (z n) (xc n)) +
              riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) zz.val :=
            add_le_add_left (riemannianEDistOf_triangle _ _ _ _) _
        _ < (ENNReal.ofReal a' + ENNReal.ofReal a') + ENNReal.ofReal (σ n) :=
            ENNReal.add_lt_add (ENNReal.add_lt_add h1 h2) hzz
        _ = ENNReal.ofReal (ρ n) := by
            rw [← ENNReal.ofReal_add ha'0 ha'0, ← ENNReal.ofReal_add (by positivity) hσpos.le]
            congr 1
            change a' + a' + (ρ n - 2 * a') = ρ n
            ring
    have hv := hnc n zz.val hyz b hb (hbσ.trans hσρ)
    have hU : IsClosed ((((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen :
        TopologicalSpace.Opens ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
          Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) := by
      change IsClosed ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      exact isClosed_univ
    have heq := riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
      ((S n).flow.base.metric (t n))
      ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen hU zz b
    dsimp only at heq
    change _ ≤ riemannianVolumeMeasure ThreeModel
      ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen
      (((S n).flow.base.metric (t n)).restrictOpen
        ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen)
      (riemannianBallOf (((S n).flow.base.metric (t n)).restrictOpen
        ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen) zz b)
    rw [heq]
    exact hv
  obtain ⟨B, hB⟩ :=
    exists_normalized_scalar_bound_local_O3
    H t S hS (fun n => by rw [← hend n]; exact (S n).lt) Ctime Cgrad q hq
    (fun n j y' t' ht hqy' => hderiv n j (Fin.castSucc_lt_last j) y' t' ht hqy')
    (fun n y' t' ht hqy' => hfinal n y' t' ht hqy')
    (fun n y' t' ht hqy' => hgrad n y' t' ht hqy') x hQ hqQ hQlim one_pos hwindow hphi
    (fun n => hpinch n) (fun n => hpinchF n) σ hκ hσlim hloc
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


end GC.LongTime.Ch12
