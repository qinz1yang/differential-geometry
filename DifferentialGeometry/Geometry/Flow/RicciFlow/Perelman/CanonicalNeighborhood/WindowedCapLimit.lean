import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonDistanceConvergence

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem LocalCap.eventually_transport_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha : ℝ} {p : L.M} {U : Set L.M} (cap : LocalCap L.S eps p 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha) :
    ∀ᶠ i in atTop, ∃ cap' : LocalCap (S (phi i)) (2 * alpha)
        ((W (phi i)).embedding (F.map i p)) (t (phi i))
        ((partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' U),
      cap'.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
        (W (phi i)).embedding) '' cap.tube ∧
      cap'.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
        (W (phi i)).embedding) '' cap.core.carrier ∧
      cap'.tube_map = cap.tube_map.trans
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) := by
  classical
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hnecks : ∀ j : Fin cap.chain.count, ∀ᶠ i in atTop,
      ∃ nk : StrongNeck (S (phi i)) (2 * alpha) (Psi i (cap.chain.centers j)) (t (phi i)),
        nk.map = partialDiffeomorphTransMixed (cap.chain.necks j).map (Psi i) := by
    intro j
    exact (cap.chain.necks j).eventually_transport_of_windowed_models hS W hdelta hreg
      L hcomplete hphi F hcmp ha hsmall heps
  have hsource : ∀ᶠ i in atTop, U ⊆ (Psi i).source := by
    have hh := WindowedModelWitness.eventually_composed_comparison hS W hdelta
      (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
      cap.isCompact_carrier zero_lt_one 0 zero_lt_one
    exact hh.mono fun _ hi => hi.1
  have htol : eps ≤ 2 * alpha :=
    heps.le.trans ((neckModelTolerance_le alpha).trans (by linarith))
  filter_upwards [eventually_all.mpr hnecks, hsource] with i hi hsrc
  choose necks hmap using hi
  refine ⟨LocalCap.mapOfNeckFamily (cap.mono_eps htol hsmall) (Psi i) hsrc
    necks (fun j => hmap j), rfl, rfl, rfl⟩

theorem LocalCap.eventually_transport_with_depth_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha : ℝ} {U : Set L.M} (cap : LocalCap L.S eps L.basepoint 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (hfar : ∀ y ∈ cap.tube, 10000 < metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∀ᶠ i in atTop, ∃ cap' : LocalCap (S (phi i)) (2 * alpha) (x (phi i)) (t (phi i))
        ((partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' U),
      (∀ z ∈ cap'.tube,
        10000 / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) ≤
          metricDistance ((S (phi i)).base.metric (t (phi i))) (x (phi i)) z) ∧
      cap'.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
        (W (phi i)).embedding) '' cap.tube ∧
      cap'.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
        (W (phi i)).embedding) '' cap.core.carrier ∧
      cap'.tube_map = cap.tube_map.trans
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) := by
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace ThreeSpace L.M := L.charted
  let _ : IsManifold I3 ∞ L.M := L.smooth
  have hcont : Continuous (fun y : L.M => metricDistance (L.S.base.metric 0) L.basepoint y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal
      (riemannianEDistOf_ne_top (L.S.base.metric 0) L.basepoint y)).comp
        (continuous_riemannianEDist (L.S.base.metric 0) L.basepoint).continuousAt
  let z : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hne : cap.tube.Nonempty := by
    refine ⟨cap.tube_map (z, 0), ?_⟩
    rw [← cap.tube_eq]
    exact ⟨(z, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  obtain ⟨y0, hy0, hmin⟩ := cap.isCompact_tube.exists_isMinOn hne hcont.continuousOn
  let d := metricDistance (L.S.base.metric 0) L.basepoint y0
  have hd : 10000 < d := hfar y0 hy0
  have hd0 : 0 < d := by linarith
  let eta := min (1 / 4 : ℝ) ((d - 10000) / (2 * d))
  have heta : 0 < eta := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have heta4 : eta ≤ 1 / 4 := min_le_left _ _
  have hsurvive : 10000 ≤ Real.sqrt (1 - eta) * d := by
    have hgap := (le_div_iff₀ (by positivity : 0 < 2 * d)).mp
      (min_le_right (1 / 4 : ℝ) ((d - 10000) / (2 * d)))
    have hroot : 1 - eta ≤ Real.sqrt (1 - eta) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_nonneg heta.le (by linarith : 0 ≤ 1 - eta)]
    exact (show 10000 ≤ (1 - eta) * d by nlinarith).trans
      (mul_le_mul_of_nonneg_right hroot hd0.le)
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
  have hcompare (K : Set L.M) (hK : IsCompact K) : ∀ᶠ i in atTop,
      K ⊆ (Psi i).source ∧
        Nonempty (MetricComparisonOn L.S.base.metric (g i) (Psi i) K (Icc (-1 : ℝ) 0) 0 eta) :=
    WindowedModelWitness.eventually_composed_comparison hS W hdelta
      (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
      hK zero_lt_one 0 heta
  have hc : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) hcomplete⟩
  have hdist := eventually_metricDistance_bounds_on_compact_of_comparisons
    L.S.base.metric g Psi (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num)
    heta.le (by linarith : eta < 1)
    hc hcompare (cap.isCompact_tube.insert L.basepoint)
  have hcaps := cap.eventually_transport_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp ha hsmall heps
  filter_upwards [hdist, hcaps] with i hdi hci
  obtain ⟨cap', htube, hcore, hmap⟩ := hci
  have hbase : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb, (W (phi i)).base_map]
  have hdeep : ∀ z ∈ cap'.tube,
      10000 / Real.sqrt ((S (phi i)).scalar (t (phi i)) (Psi i L.basepoint)) ≤
        metricDistance ((S (phi i)).base.metric (t (phi i))) (Psi i L.basepoint) z := by
    intro z hz
    rw [htube] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hlo := (hdi L.basepoint (mem_insert _ _) y (mem_insert_of_mem _ hy)).1
    have hlower : 10000 ≤ metricDistance (g i 0) (Psi i L.basepoint) (Psi i y) :=
      hsurvive.trans ((mul_le_mul_of_nonneg_left (hmin hy) (Real.sqrt_nonneg _)).trans hlo)
    simp only [g, rescaledMetric, parabolicTime_zero, metricDistance, edistOf_scale,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hlower
    rw [hbase] at hlower ⊢
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (W (phi i)).scalar_pos)).mpr (by
      simpa only [mul_comm, metricDistance] using hlower)
  have hout : ∃ cap' : LocalCap (S (phi i)) (2 * alpha) (Psi i L.basepoint)
        (t (phi i)) (Psi i '' U),
      (∀ z ∈ cap'.tube,
        10000 / Real.sqrt ((S (phi i)).scalar (t (phi i)) (Psi i L.basepoint)) ≤
          metricDistance ((S (phi i)).base.metric (t (phi i))) (Psi i L.basepoint) z) ∧
      cap'.tube = Psi i '' cap.tube ∧ cap'.core.carrier = Psi i '' cap.core.carrier ∧
      cap'.tube_map = cap.tube_map.trans (Psi i) :=
    ⟨cap', hdeep, htube, hcore, hmap⟩
  rwa [hbase] at hout

theorem LocalCap.eventually_canonicalAlternative_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha C : ℝ} {U : Set L.M} (cap : LocalCap L.S eps L.basepoint 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (hfar : ∀ y ∈ cap.tube, 20000 ≤ metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∀ᶠ i in atTop, Nonempty (CanonicalAlternative (S (phi i)) (2 * alpha) C
      (x (phi i)) (t (phi i))
      ((partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' U)) := by
  filter_upwards [cap.eventually_transport_with_depth_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp ha hsmall heps (by
      intro y hy
      exact lt_of_lt_of_le (by norm_num : (10000 : ℝ) < 20000) (hfar y hy))] with i hi
  obtain ⟨cap', hdeep, _⟩ := hi
  exact ⟨CanonicalAlternative.cap cap' hdeep⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
