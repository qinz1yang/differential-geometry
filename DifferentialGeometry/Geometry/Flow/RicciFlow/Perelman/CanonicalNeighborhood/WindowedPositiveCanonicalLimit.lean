import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBoundsLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomainLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound
import DifferentialGeometry.Topology.Connected.OpenPartialHomeomorph

section

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle
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
theorem CanonicalWitness.eventually_positive_image_of_windowed_models
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
    (hpositive : ∃ whole data sec, K.alternative = CanonicalAlternative.positive whole data sec) :
    ∀ᶠ i in atTop, ∀ tolerance : ℝ, 0 < tolerance → tolerance < 1 →
      ∃ K' : CanonicalWitness (S (phi i)) tolerance (max C1 2)
        (max (sourceCurvatureBound 3 C2)
          (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
        (x (phi i)) (t (phi i)),
        K'.domain.carrier =
          (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' K.domain.carrier ∧
        ∃ whole data sec, K'.alternative = CanonicalAlternative.positive whole data sec := by
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
  obtain ⟨whole, data, sec, hpositive⟩ := hpositive
  have hKuniv : K.domain.carrier = univ := by rw [whole, PreconnectedSpace.connectedComponent_eq_univ]
  have hv : K.alternative.requiresVolume := by rw [hpositive]; trivial
  let c := C2⁻¹
  let B := c + 360 + C2
  let eta := min (1 / 4 : ℝ) (c / (8 * B))
  have hc : 0 < c := inv_pos.mpr hC2
  have hB : 0 < B := by dsimp only [B]; positivity
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hc (by positivity))
  have heta4 : eta ≤ 1 / 4 := min_le_left _ _
  have hmargin : (2 * C2)⁻¹ ≤ c - 4 * eta * (c + 360 + C2) := by
    have hm := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp
      (min_le_right (1 / 4 : ℝ) (c / (8 * B)))
    have heq : (2 * C2)⁻¹ = c / 2 := by dsimp only [c]; field_simp
    rw [heq]
    dsimp only [B] at hm
    change eta * (8 * (c + 360 + C2)) ≤ c at hm
    linarith
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
  have hsectionalCompare := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    K.domain.compact zero_lt_one 2 heta
  filter_upwards [hsource, hballs, hscalars, hcurvature, hvolume, hderivatives, hsectionalCompare]
    with i hsrc hball hscal hrm hvol hderiv hcomparison
  intro tolerance htol htol1
  obtain ⟨r, hrlo, hrhi, hrin, hrout⟩ := hball
  obtain ⟨_hsource', ⟨cmp⟩⟩ := hcomparison
  let U := K.domain.map (Psi i) hsrc
  have hbase : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb, (W (phi i)).base_map]
  have hcenter : x (phi i) ∈ interior U.carrier := by
    change x (phi i) ∈ interior (Psi i '' K.domain.carrier)
    rw [← K.domain.image_interior (Psi i) hsrc]
    exact ⟨L.basepoint, K.center_inside, hbase⟩
  have hopen : IsOpen K.domain.carrier := by rw [hKuniv]; exact isOpen_univ
  have himgopen : IsOpen U.carrier := (Psi i).toOpenPartialHomeomorph.isOpen_image_of_subset_source hopen hsrc
  have hwhole : U.carrier = connectedComponent (x (phi i)) :=
    U.connected.subset_connectedComponent (interior_subset hcenter) |>.antisymm
      ((show IsClopen U.carrier from ⟨U.compact.isClosed, himgopen⟩).connectedComponent_subset (interior_subset hcenter))
  obtain ⟨data'⟩ := positiveComponent_transport_of_partialDiffeomorph data (Psi i) hsrc
  let V : TopologicalSpace.Opens L.M := ⊤
  have hVsrc : (V : Set L.M) ⊆ (Psi i).source := by rw [show (V : Set L.M) = univ from rfl, ← hKuniv]; exact hsrc
  have hVK : (V : Set L.M) ⊆ K.domain.carrier := by rw [hKuniv]; exact subset_univ _
  have hsecmodel : SecLower (L.S.base.metric 0) c V := by
    change SecLower (L.S.base.metric 0) C2⁻¹ univ
    simpa only [hscalar, mul_one, hKuniv] using sec
  have hrmmodel : ∀ y ∈ (V : Set L.M), normSq0S (L.S.base.metric 0) y 4
      (metricRm04At (L.S.base.metric 0) y) ≤ C2 ^ 2 := by
    intro y hy
    have hh := K.rm_bound y (hVK hy)
    rw [hscalar, mul_one] at hh
    exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _) hh
  have hsecimage := cmp.secLower_image V hVsrc hVK
    (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0) (by linarith) le_rfl hc.le hC2.le hsecmodel hrmmodel
  have hsecsource : SecLower ((S (phi i)).base.metric (t (phi i)))
      (C⁻¹ * (S (phi i)).scalar (t (phi i)) (x (phi i))) U.carrier := by
    have hh := hsecimage.mono (hCinv2.trans hmargin)
    simp only [rescaledMetric, parabolicTime_zero] at hh
    apply (secLower_scaleMetric_iff (W (phi i)).scalar_pos _ U.carrier).mp
    change SecLower (scaleMetric ((S (phi i)).scalar (t (phi i)) (x (phi i)))
      (W (phi i)).scalar_pos ((S (phi i)).base.metric (t (phi i)))) C⁻¹
      (Psi i '' K.domain.carrier)
    simpa only [show (V : Set L.M) = univ from rfl, hKuniv] using hh
  let K' : CanonicalWitness (S (phi i)) tolerance (max C1 2) C (x (phi i)) (t (phi i)) := {
    Q_pos := (W (phi i)).scalar_pos
    time_mem := (W (phi i)).time_mem
    eps_pos := htol
    eps_lt_one := htol1
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
    alternative := CanonicalAlternative.positive hwhole data' hsecsource
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
  exact ⟨K', rfl, hwhole, data', hsecsource, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.eventually_image_of_windowed_models_of_positive_component
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
    (hpositive : ∃ whole data sec, K.alternative = CanonicalAlternative.positive whole data sec)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∀ᶠ i in atTop, ∃ K' : CanonicalWitness (S (phi i)) alpha (max C1 2)
        (max (sourceCurvatureBound 3 C2)
          (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
        (x (phi i)) (t (phi i)),
      K'.domain.carrier =
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier ∧
      ∃ whole data sec, K'.alternative = CanonicalAlternative.positive whole data sec := by
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
  obtain ⟨whole, data, sec, hpos⟩ := hpositive
  have hKuniv : K.domain.carrier = univ := by
    rw [whole, PreconnectedSpace.connectedComponent_eq_univ]
  have hv : K.alternative.requiresVolume := by
    rw [hpos]
    trivial
  let c := C2⁻¹
  have hc : 0 < c := inv_pos.mpr hC2
  let B := c + 360 + C2
  have hB : 0 < B := by dsimp only [B]; positivity
  let eta := min (1 / 2) (c / (8 * B))
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hc (by positivity))
  have hetahalf : eta ≤ 1 / 2 := min_le_left _ _
  have hetabound : eta ≤ c / (8 * B) := min_le_right _ _
  let Psi (i : ℕ) : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ :=
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hcomparisons := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    K.domain.compact zero_lt_one 2 heta
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
  filter_upwards [hcomparisons, hballs, hscalars, hcurvature, hvolume, hderivatives]
    with i hcomparison hball hscal hrm hvol hderiv
  obtain ⟨hsrc, ⟨cmp⟩⟩ := hcomparison
  obtain ⟨r, hrlo, hrhi, hrin, hrout⟩ := hball
  let U := K.domain.map (Psi i) hsrc
  have hbase : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb, (W (phi i)).base_map]
  have hwhole : U.carrier = connectedComponent (x (phi i)) := by
    have hh := (Psi i).toOpenPartialHomeomorph.image_eq_connectedComponent_of_isCompact
      K.domain.compact K.domain.connected.isPreconnected
      (by rw [hKuniv]; exact isOpen_univ) hsrc (interior_subset K.center_inside)
    change Psi i '' K.domain.carrier = connectedComponent (Psi i L.basepoint) at hh
    rwa [hbase] at hh
  obtain ⟨data'⟩ := positiveComponent_transport_of_partialDiffeomorph data (Psi i) hsrc
  have hsrcsec : SecLower ((S (phi i)).base.metric (t (phi i)))
      (C⁻¹ * (S (phi i)).scalar (t (phi i)) (x (phi i))) U.carrier := by
    let V : TopologicalSpace.Opens L.M := ⊤
    have hVsource : (V : Set L.M) ⊆ (Psi i).source := by
      rw [show (V : Set L.M) = univ from rfl, ← hKuniv]
      exact hsrc
    have hVA : (V : Set L.M) ⊆ K.domain.carrier := by
      rw [hKuniv]
      exact subset_univ _
    have hsecmodel : SecLower (L.S.base.metric 0) c V := by
      change SecLower (L.S.base.metric 0) C2⁻¹ univ
      simpa only [hscalar, mul_one, hKuniv] using sec
    have hrmmodel : ∀ y ∈ (V : Set L.M), normSq0S (L.S.base.metric 0) y 4
        (metricRm04At (L.S.base.metric 0) y) ≤ C2 ^ 2 := by
      intro y _
      have hb := K.rm_bound y (by rw [hKuniv]; exact mem_univ y)
      rw [hscalar, mul_one] at hb
      change Real.sqrt (L.rmNormSq 0 y) ≤ C2 at hb
      have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg L 0 y)
      change L.rmNormSq 0 y ≤ C2 ^ 2
      nlinarith [Real.sqrt_nonneg (L.rmNormSq 0 y)]
    have hh := cmp.secLower_image (F := Psi i) V hVsource hVA
      (by norm_num : (0 : ℝ) ∈ Icc (-1) 0) hetahalf le_rfl hc.le hC2.le hsecmodel hrmmodel
    have hbound : C⁻¹ ≤ c - 4 * eta * (c + 360 + C2) := by
      have hm := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hetabound
      have hinv : (2 * C2)⁻¹ = c / 2 := by dsimp only [c]; field_simp
      rw [hinv] at hCinv2
      dsimp only [B] at hm
      linarith
    have hscaled : SecLower
        (scaleMetric ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
          ((S (phi i)).base.metric (t (phi i)))) C⁻¹ U.carrier := by
      have hm := hh.mono hbound
      simp only [rescaledMetric, parabolicTime_zero] at hm
      change SecLower
        (scaleMetric ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
          ((S (phi i)).base.metric (t (phi i)))) C⁻¹ (Psi i '' univ) at hm
      change SecLower _ C⁻¹ (Psi i '' K.domain.carrier)
      simpa only [hKuniv] using hm
    exact (secLower_scaleMetric_iff (W (phi i)).scalar_pos
      ((S (phi i)).base.metric (t (phi i))) U.carrier).mp hscaled
  have hcenter : x (phi i) ∈ interior U.carrier := by
    change x (phi i) ∈ interior (Psi i '' K.domain.carrier)
    rw [← K.domain.image_interior (Psi i) hsrc]
    exact ⟨L.basepoint, K.center_inside, hbase⟩
  let K' : CanonicalWitness (S (phi i)) alpha (max C1 2) C (x (phi i)) (t (phi i)) := {
    Q_pos := (W (phi i)).scalar_pos
    time_mem := (W (phi i)).time_mem
    eps_pos := ha
    eps_lt_one := ha1
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
    alternative := CanonicalAlternative.positive hwhole data' hsrcsec
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
  exact ⟨K', rfl, hwhole, data', hsrcsec, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
