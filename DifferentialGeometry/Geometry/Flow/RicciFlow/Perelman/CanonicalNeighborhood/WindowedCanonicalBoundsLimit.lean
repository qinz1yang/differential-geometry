import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.eventually_scalar_bounds_of_windowed_models
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
    {eps C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1) :
    ∀ᶠ i in atTop, ∀ y ∈ K.domain.carrier,
      (2 * C2)⁻¹ * (S (phi i)).scalar (t (phi i)) (x (phi i)) ≤
        (S (phi i)).scalar (t (phi i)) ((W (phi i)).embedding (F.map i y)) ∧
      (S (phi i)).scalar (t (phi i)) ((W (phi i)).embedding (F.map i y)) ≤
        (2 * C2) * (S (phi i)).scalar (t (phi i)) (x (phi i)) := by
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace ThreeSpace L.M := L.charted
  let _ : IsManifold I3 ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  let E := 486 * C2 * (1 + 9 * C2)
  have hE : 0 < E := by dsimp only [E]; positivity
  let eta := min (1 / 4 : ℝ) E⁻¹
  have heta : 0 < eta := lt_min (by norm_num) (inv_pos.mpr hE)
  have heta4 : eta ≤ 1 / 4 := min_le_left _ _
  have hsmall : 486 * C2 * (1 + 9 * C2) * eta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 / 4 : ℝ) E⁻¹) hE.le
    rwa [mul_inv_cancel₀ hE.ne'] at hh
  have herr : 243 * (1 + 9 * C2) * eta ≤ (2 * C2)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * C2)).mpr
    nlinarith
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  let _ : RegularSpace L.M := inferInstance
  obtain ⟨U, hUopen, hKU, _, hUc⟩ :=
    exists_open_between_and_isCompact_closure K.domain.compact isOpen_univ (subset_univ _)
  let U' : TopologicalSpace.Opens L.M := ⟨U, hUopen⟩
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
  have hcompare := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    hUc zero_lt_one 2 heta
  filter_upwards [hcompare] with i hi
  obtain ⟨hsource, ⟨cmp⟩⟩ := hi
  let _ : IsManifold I3 1 (M (phi i)) := IsManifold.of_le (n := ∞) (by decide)
  intro y hy
  have hrm : normSq0S (L.S.base.metric 0) y 4 (metricRm04At (L.S.base.metric 0) y) ≤ C2 ^ 2 := by
    have hh := K.rm_bound y hy
    rw [hscalar, mul_one] at hh
    exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _) hh
  have hric := ricciSq_le_rm04 (L.S.base.metric 0) (L.S.base.metric 0) y
  change normSq0S (L.S.base.metric 0) y 2 (metricRicciAt (L.S.base.metric 0) y) ≤
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 *
      normSq0S (L.S.base.metric 0) y 4 (metricRm04At (L.S.base.metric 0) y) at hric
  have hricnorm : Real.sqrt (normSq0S (L.S.base.metric 0) y 2
      (metricRicciAt (L.S.base.metric 0) y)) ≤ 9 * C2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace]] at hric
    norm_num only at hric
    nlinarith
  have hRic (v w : TangentSpace I3 y) : |ricciTensor (L.S.base.metric 0) y v w| ≤
      (9 * C2) * Real.sqrt ((L.S.base.metric 0).inner y v v) *
        Real.sqrt ((L.S.base.metric 0).inner y w w) := by
    have hh := abs_apply_le_norm0S (L.S.base.metric 0) y 2
      (metricRicciAt (L.S.base.metric 0) y) (vec2 v w)
    rw [metricRicciAt_apply_eq_ricciTensor] at hh
    have hh' : |ricciTensor (L.S.base.metric 0) y v w| ≤
        Real.sqrt (normSq0S (L.S.base.metric 0) y 2 (metricRicciAt (L.S.base.metric 0) y)) *
          Real.sqrt ((L.S.base.metric 0).inner y v v) *
          Real.sqrt ((L.S.base.metric 0).inner y w w) := by
      simpa [vec2, Fin.prod_univ_two, mul_assoc] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hricnorm (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hdiff := MetricComparisonOn.scalar_sub_le_of_ricci_bound
    (N := L.M) (M := M (phi i)) (h := L.S.base.metric) (g := g i) (F := Psi i)
    cmp U' (subset_closure.trans hsource)
    subset_closure (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) heta.le
    (by linarith) le_rfl (hKU hy) hRic
  have herror : |metricScalarAt (g i 0) (Psi i y) - L.S.scalar 0 y| ≤ (2 * C2)⁻¹ := by
    apply hdiff.trans
    have hh := scalarComparisonC_le (n := 3) heta.le heta4 (by positivity : 0 ≤ 9 * C2)
    norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at hh
    exact hh.trans (by nlinarith [herr])
  have hnorm : metricScalarAt (g i 0) (Psi i y) =
      ((S (phi i)).scalar (t (phi i)) (x (phi i)))⁻¹ *
        (S (phi i)).scalar (t (phi i)) (Psi i y) := by
    simp only [g, rescaledMetric, parabolicTime_zero]
    exact metricScalarAt_scaleMetric ((S (phi i)).scalar (t (phi i)) (x (phi i)))
      (W (phi i)).scalar_pos ((S (phi i)).base.metric (t (phi i))) (Psi i y)
  rw [hnorm] at herror
  have hmod := K.scalar_bounds y hy
  rw [hscalar, mul_one, mul_one] at hmod
  have hinv : C2⁻¹ = 2 * (2 * C2)⁻¹ := by field_simp
  have hbound : (2 * C2)⁻¹ ≤ C2 := by
    have hh := inv_le_one_of_one_le₀ (by linarith [K.one_le_comparison_constant] : 1 ≤ 2 * C2)
    exact hh.trans K.one_le_comparison_constant
  have habs := abs_le.mp herror
  have hlo : (2 * C2)⁻¹ ≤ ((S (phi i)).scalar (t (phi i)) (x (phi i)))⁻¹ *
      (S (phi i)).scalar (t (phi i)) (Psi i y) := by
    rw [hinv] at hmod
    linarith
  have hhi : ((S (phi i)).scalar (t (phi i)) (x (phi i)))⁻¹ *
      (S (phi i)).scalar (t (phi i)) (Psi i y) ≤ 2 * C2 := by linarith
  have hlo' := mul_le_mul_of_nonneg_left hlo (W (phi i)).scalar_pos.le
  have hhi' := mul_le_mul_of_nonneg_left hhi (W (phi i)).scalar_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ (W (phi i)).scalar_pos.ne', one_mul] at hlo' hhi'
  have hmap : Psi i y = (W (phi i)).embedding (F.map i y) := rfl
  rw [hmap] at hlo' hhi'
  exact ⟨by simpa only [mul_comm] using hlo', by simpa only [mul_comm] using hhi'⟩

theorem CanonicalWitness.eventually_volume_lower_bound_of_windowed_models
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
    {eps C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (hv : K.alternative.requiresVolume) :
    ∀ᶠ i in atTop,
      ENNReal.ofReal ((4 * C2)⁻¹ /
        ((S (phi i)).scalar (t (phi i)) (x (phi i)) *
          Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))))) ≤
        riemannianVolumeMeasure I3 (M (phi i)) ((S (phi i)).base.metric (t (phi i)))
          ((partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
            K.domain.carrier) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  let _ : RegularSpace L.M := inferInstance
  obtain ⟨U, hUopen, hKU, _, hUc⟩ :=
    exists_open_between_and_isCompact_closure K.domain.compact isOpen_univ (subset_univ _)
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hmodel : ENNReal.ofReal (C2⁻¹ / ((1 : ℝ) * Real.sqrt 1)) ≤
      riemannianVolumeMeasure I3 L.M (L.S.base.metric 0) K.domain.carrier := by
    simpa only [hscalar] using K.volume hv
  have hcompare := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    hUc zero_lt_one 0 (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hcompare] with i hi
  obtain ⟨hsource, ⟨cmp⟩⟩ := hi
  let cmp' := cmp.freezeTime (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) ({0} : Set ℝ)
  have hge := volume_reserve_image_of_scaled_comparison (Psi i) (W (phi i)).scalar_pos
    cmp' (show (0 : ℝ) ∈ ({0} : Set ℝ) from rfl) (by norm_num) (by norm_num)
    hUopen subset_closure (subset_closure.trans hsource) K.domain.compact hKU hmodel
  simp only [parabolicTime_zero] at hge
  have hroot : (1 / 4 : ℝ) ≤ Real.sqrt ((1 - 1 / 2 : ℝ) ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hconst : (4 * C2)⁻¹ ≤
      (C2 * ((1 : ℝ) * Real.sqrt 1) / Real.sqrt ((1 - 1 / 2 : ℝ) ^ 3))⁻¹ := by
    simp only [Real.sqrt_one, mul_one]
    rw [inv_div, div_eq_mul_inv, mul_inv]
    simpa only [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num] using
      mul_le_mul_of_nonneg_right hroot (inv_nonneg.mpr hC2.le)
  exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hconst
    (mul_nonneg (W (phi i)).scalar_pos.le (Real.sqrt_nonneg _)))).trans hge

theorem CanonicalWitness.eventually_curvature_bound_of_windowed_models
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
    {eps C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1) :
    ∀ᶠ i in atTop, ∀ y ∈ K.domain.carrier,
      Real.sqrt (FlowMetricBall.rmNormSq (S (phi i)) (t (phi i))
        ((W (phi i)).embedding (F.map i y))) ≤
        sourceCurvatureBound 3 C2 * (S (phi i)).scalar (t (phi i)) (x (phi i)) := by
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace ThreeSpace L.M := L.charted
  let _ : IsManifold I3 ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : IsManifold I3 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hrad : 1 ≤ K.radius := by simpa only [hscalar, Real.sqrt_one, inv_one] using K.radius_lower
  let R := 2 * K.radius + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  have hKR : K.domain.carrier ⊆ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R := by
    intro y hy
    exact (K.inside_ball hy).le.trans (ENNReal.ofReal_le_ofReal (by dsimp only [R]; linarith))
  have hc : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) hcomplete⟩
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
  have hcompare := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    (hc.closedEBall_isCompact L.basepoint R) zero_lt_one 2 (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hcompare] with i hi
  obtain ⟨hsource, ⟨cmp⟩⟩ := hi
  let _ : IsManifold I3 1 (M (phi i)) := IsManifold.of_le (n := ∞) (by decide)
  intro y hy
  have hrm : normSq0S (L.S.base.metric 0) y 4 (metricRm04At (L.S.base.metric 0) y) ≤ C2 ^ 2 := by
    have hh := K.rm_bound y hy
    rw [hscalar, mul_one] at hh
    exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _) hh
  have hnorm := MetricComparisonOn.rmNormSq_le_on_closedBall
    (N := L.M) (M := M (phi i)) (L.S.base.metric 0) hc L.basepoint hR
    (h := L.S.base.metric) (g := g i) (F := Psi i) cmp (by norm_num) le_rfl le_rfl hC2.le
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) (hsource (hKR hy)) (hKR hy) hrm
  have hscale := parabolicRmNormSq (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
    (W (phi i)).time_mem 0 (Psi i y)
  change normSq0S (g i 0) (Psi i y) 4 (metricRm04At (g i 0) (Psi i y)) =
    ((S (phi i)).scalar (t (phi i)) (x (phi i)))⁻¹ ^ 2 *
      FlowMetricBall.rmNormSq (S (phi i))
        (parabolicTime (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i))) 0)
        (Psi i y) at hscale
  rw [hscale, parabolicTime_zero] at hnorm
  have hroot := Real.sqrt_le_sqrt hnorm
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr (W (phi i)).scalar_pos.le),
    Real.sqrt_sq (sourceCurvatureBound_pos 3 hC2.le).le] at hroot
  have hh := mul_le_mul_of_nonneg_left hroot (W (phi i)).scalar_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ (W (phi i)).scalar_pos.ne', one_mul] at hh
  have hmap : Psi i y = (W (phi i)).embedding (F.map i y) := rfl
  rw [hmap] at hh
  simpa only [mul_comm] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
