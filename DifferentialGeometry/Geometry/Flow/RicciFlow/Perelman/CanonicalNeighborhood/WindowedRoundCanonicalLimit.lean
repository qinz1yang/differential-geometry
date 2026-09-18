import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomainLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBoundsLimit
import DifferentialGeometry.Topology.Connected.OpenPartialHomeomorph

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.eventually_image_of_windowed_models_of_round_component
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
    (hround : ∃ whole R, K.alternative = CanonicalAlternative.round whole R)
    (ha : 0 < alpha) (hahalf : alpha ≤ 1 / 2)
    (heps : eps < alpha)
    (hsmall : eps ≤ backgroundJetSmallness ThreeSpace ⌈alpha⁻¹⌉₊) :
    ∀ᶠ i in atTop, ∃ K' : CanonicalWitness (S (phi i)) alpha (max C1 2)
        (max (sourceCurvatureBound 3 C2)
          (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
        (x (phi i)) (t (phi i)),
      K'.domain.carrier =
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier ∧
      ∃ whole R, K'.alternative = CanonicalAlternative.round whole R := by
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
  obtain ⟨whole, R, _⟩ := hround
  have hKuniv : K.domain.carrier = univ := by
    rw [whole, PreconnectedSpace.connectedComponent_eq_univ]
  let _ : TopologicalSpace R.Z := R.topology
  let _ : ChartedSpace ThreeSpace R.Z := R.charted
  let _ : IsManifold I3 ∞ R.Z := R.smooth
  let _ : T2Space R.Z := R.t2
  let _ : CompactSpace R.Z := R.compact
  let _ : ConnectedSpace R.Z := R.connected
  have htarget : R.map.target = univ := R.target_eq.trans hKuniv
  let Phi : R.Z ≃ₘ⟮I3, I3⟯ L.M := {
    toFun := R.map
    invFun := R.map.symm
    left_inv := fun z => R.map.left_inv' (by rw [R.source_eq]; trivial)
    right_inv := fun y => R.map.right_inv' (by rw [htarget]; trivial)
    contMDiff_toFun := by
      change ContMDiff I3 I3 ∞ (R.map : R.Z → L.M)
      exact contMDiffOn_univ.mp (R.source_eq ▸ R.map.contMDiffOn_toFun)
    contMDiff_invFun := by
      change ContMDiff I3 I3 ∞ (R.map.symm : L.M → R.Z)
      apply contMDiffOn_univ.mp
      have hh := R.map.contMDiffOn_invFun
      rw [htarget] at hh
      exact hh }
  let order := ⌈alpha⁻¹⌉₊
  let B := backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1)
  have hB : 0 < B := mul_pos (backgroundJetConstant_pos ThreeSpace order) (by positivity)
  let eta := (alpha - eps) / B
  have heta : 0 < eta := div_pos (sub_pos.mpr heps) hB
  have herror : backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * eta ≤
      alpha - eps := by
    dsimp only [eta]
    rw [mul_div_cancel₀ _ hB.ne']
  have horder : order ≤ ⌈eps⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ K.eps_pos heps.le)
  let Psi (i : ℕ) : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ :=
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hcomparisons := WindowedModelWitness.eventually_composed_comparison hS W hdelta
    (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
    K.domain.compact zero_lt_one order heta
  have hballs := K.eventually_image_ball_sandwich_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hscalars := K.eventually_scalar_bounds_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hcurvature := K.eventually_curvature_bound_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  have hderivatives := K.eventually_scalar_derivative_bounds_of_windowed_models hS W hdelta hreg
    L hcomplete hphi F hcmp hscalar
  filter_upwards [hcomparisons, hballs, hscalars, hcurvature, hderivatives]
    with i hcomparison hball hscal hrm hderiv
  obtain ⟨hsrc, ⟨cmp⟩⟩ := hcomparison
  have hsrc' : K.domain.carrier ⊆ (Psi i).source := hsrc
  have cmp₀ : MetricComparisonOn L.S.base.metric
      (rescaledMetric (S (phi i)) (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i)))
        (W (phi i)).scalar_pos) (Psi i) K.domain.carrier (Icc (-1) 0) order eta := cmp
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
  have hm : scaleMetric (L.S.scalar 0 L.basepoint) R.Q_pos (L.S.base.metric 0) =
      L.S.base.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    simp only [scaleMetric_inner, hscalar, one_mul]
  have cmp' : MetricComparisonOn
      (fun _ => scaleMetric (L.S.scalar 0 L.basepoint) R.Q_pos (L.S.base.metric 0))
      (fun _ => scaleMetric ((S (phi i)).scalar (t (phi i)) (x (phi i)))
        (W (phi i)).scalar_pos ((S (phi i)).base.metric (t (phi i))))
      (Psi i) K.domain.carrier {0} order eta := by
    simpa only [hm, rescaledMetric, parabolicTime_zero] using
      cmp₀.freezeTime (by norm_num : (0 : ℝ) ∈ Icc (-1) 0) heta.le ({0} : Set ℝ)
  obtain ⟨R'⟩ := roundComponent_transport_of_comparison R (W (phi i)).scalar_pos (Psi i) cmp'
    order alpha horder K.eps_pos hsmall le_rfl heta.le herror le_rfl hahalf hbase
    (by rw [R.target_eq]; exact hsrc') (by rw [R.target_eq]) Phi (fun _ => rfl)
  have hcenter : x (phi i) ∈ interior U.carrier := by
    change x (phi i) ∈ interior (Psi i '' K.domain.carrier)
    rw [← K.domain.image_interior (Psi i) hsrc]
    exact ⟨L.basepoint, K.center_inside, hbase⟩
  let K' : CanonicalWitness (S (phi i)) alpha (max C1 2) C (x (phi i)) (t (phi i)) := {
    Q_pos := (W (phi i)).scalar_pos
    time_mem := (W (phi i)).time_mem
    eps_pos := ha
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
    alternative := CanonicalAlternative.round hwhole R'
    volume := by intro hv; cases hv
    gradient := by
      intro v
      exact (hderiv.1 v).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCgrad (W (phi i)).scalar_pos.le)
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    time_derivative := (hderiv.2).trans (mul_le_mul_of_nonneg_right hCtime (sq_nonneg _)) }
  exact ⟨K', rfl, hwhole, R', rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
