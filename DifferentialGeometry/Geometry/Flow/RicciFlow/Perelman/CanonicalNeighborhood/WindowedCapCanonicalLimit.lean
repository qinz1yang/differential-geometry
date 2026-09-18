import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapDepthDeformation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCapLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomainLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBoundsLimit

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.eventually_image_of_windowed_models_of_cap_with_strict_depth
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
    {eps alpha C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (hfar : ∀ y ∈ cap.tube, 10000 < metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∀ᶠ i in atTop, ∃ K' : CanonicalWitness (S (phi i)) (2 * alpha) (max C1 2)
        (max (sourceCurvatureBound 3 C2)
          (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
        (x (phi i)) (t (phi i)),
      K'.domain.carrier =
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier ∧
      ∃ cap' depth, K'.alternative = CanonicalAlternative.cap cap' depth ∧
        cap'.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
          (W (phi i)).embedding) '' cap.tube ∧
        cap'.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
          (W (phi i)).embedding) '' cap.core.carrier ∧
        cap'.tube_map = cap.tube_map.trans
          (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) := by
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace ThreeSpace L.M := L.charted
  let _ : IsManifold I3 ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let C := max (sourceCurvatureBound 3 C2)
    (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2)))
  have hC4 : 4 * C2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCcurv : sourceCurvatureBound 3 C2 ≤ C := le_max_left _ _
  have hCgrad : 2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCtime : windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2) ≤ C := by
    linarith [windowedGoodPointConstant_pos (18 * sourceCurvatureBound 3 C2)]
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hCinv2 : C⁻¹ ≤ (2 * C2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * C2)
      (by linarith : 2 * C2 ≤ C)
  have hCinv4 : C⁻¹ ≤ (4 * C2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 4 * C2) hC4
  have hv : K.alternative.requiresVolume := by
    obtain ⟨depth, hcap⟩ := hcap
    rw [hcap]
    trivial
  let Psi (i : ℕ) : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ :=
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hsource : ∀ᶠ i in atTop, K.domain.carrier ⊆ (Psi i).source := by
    have hh := WindowedModelWitness.eventually_composed_comparison hS W hdelta
      (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
      K.domain.compact zero_lt_one 0 zero_lt_one
    exact hh.mono fun _ hi => hi.1
  have hballs := K.eventually_image_ball_sandwich_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hscalars := K.eventually_scalar_bounds_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hcurvature := K.eventually_curvature_bound_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hvolume := K.eventually_volume_lower_bound_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar hv
  have hderivatives := K.eventually_scalar_derivative_bounds_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hcaps := cap.eventually_transport_with_depth_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp ha hsmall heps hfar
  filter_upwards [hsource, hballs, hscalars, hcurvature, hvolume, hderivatives, hcaps]
    with i hsrc hball hscal hrm hvol hderiv hcap'
  obtain ⟨r, hrlo, hrhi, hrin, hrout⟩ := hball
  obtain ⟨cap', hdepth, htube, hcore, hmap⟩ := hcap'
  let U := K.domain.map (Psi i) hsrc
  have hbase : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb, (W (phi i)).base_map]
  have hcenter : x (phi i) ∈ interior U.carrier := by
    change x (phi i) ∈ interior (Psi i '' K.domain.carrier)
    rw [← K.domain.image_interior (Psi i) hsrc]
    exact ⟨L.basepoint, K.center_inside, hbase⟩
  let K' : CanonicalWitness (S (phi i)) (2 * alpha) (max C1 2) C (x (phi i)) (t (phi i)) := {
    Q_pos := (W (phi i)).scalar_pos
    time_mem := (W (phi i)).time_mem
    eps_pos := by positivity
    eps_lt_one := by linarith
    domain := U
    center_inside := hcenter
    radius := r
    radius_lower := hrlo
    radius_upper := hrhi
    ball_inside := hrin
    inside_ball := hrout
    scalar_bounds := by
      rintro y ⟨z, hz, rfl⟩
      have hb := hscal z hz
      exact ⟨(mul_le_mul_of_nonneg_right hCinv2 (W (phi i)).scalar_pos.le).trans hb.1,
        hb.2.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * C2 ≤ C) (W (phi i)).scalar_pos.le)⟩
    rm_bound := by
      rintro y ⟨z, hz, rfl⟩
      exact (hrm z hz).trans (mul_le_mul_of_nonneg_right hCcurv (W (phi i)).scalar_pos.le)
    alternative := CanonicalAlternative.cap cap' hdepth
    volume := by
      intro _
      exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCinv4
        (mul_nonneg (W (phi i)).scalar_pos.le (Real.sqrt_nonneg _)))).trans hvol
    gradient := by
      intro v
      exact (hderiv.1 v).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCgrad (W (phi i)).scalar_pos.le)
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    time_derivative := (hderiv.2).trans (mul_le_mul_of_nonneg_right hCtime (sq_nonneg _)) }
  exact ⟨K', rfl, cap', hdepth, rfl, htube, hcore, hmap⟩

theorem CanonicalWitness.eventually_image_of_windowed_models_of_cap
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
    {eps alpha C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance (neckModelTolerance alpha / 4)) :
    ∀ᶠ i in atTop, ∃ K' : CanonicalWitness (S (phi i)) (2 * alpha) (max C1 2)
        (max (sourceCurvatureBound 3 C2)
          (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
        (x (phi i)) (t (phi i)),
      K'.domain.carrier =
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier ∧
      ∃ cap' depth, K'.alternative = CanonicalAlternative.cap cap' depth := by
  let beta := neckModelTolerance alpha / 4
  have hb : 0 < beta := div_pos (neckModelTolerance_pos ha) (by norm_num)
  have hbsmall : 2 * beta < 1 / 11 := by
    have hba := neckModelTolerance_le alpha
    dsimp only [beta]
    linarith
  obtain ⟨K₀, hdomain, _hradius, cap₀, depth₀, hcap₀, hstrict⟩ :=
    K.exists_cap_with_strict_depth L.isSolution cap hcap hb hbsmall heps
  have htol : 2 * beta < neckModelTolerance alpha := by
    dsimp only [beta]
    linarith [neckModelTolerance_pos ha]
  have hfar : ∀ y ∈ cap₀.tube, 10000 < metricDistance (L.S.base.metric 0) L.basepoint y := by
    intro y hy
    simpa only [hscalar, Real.sqrt_one, div_one] using hstrict y hy
  have hh := K₀.eventually_image_of_windowed_models_of_cap_with_strict_depth hS W hdelta hreg L hcomplete
    hphi F hcmp hscalar cap₀ ⟨depth₀, hcap₀⟩ ha hsmall htol hfar
  filter_upwards [hh] with i hi
  obtain ⟨K', himage, cap', depth, halt, _⟩ := hi
  exact ⟨K', by simpa only [hdomain] using himage, cap', depth, halt⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
