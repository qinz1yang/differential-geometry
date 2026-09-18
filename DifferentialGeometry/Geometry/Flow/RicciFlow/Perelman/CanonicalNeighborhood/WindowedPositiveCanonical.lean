import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceBallSandwich
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedComponentImage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowedModelWitness_canonicalWitness_of_model_positive_component
    {C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 →
        ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
          {delta kappa eta : ℝ} {x : M} {t : ℝ}
          (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
          IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          ∀ K0 : CanonicalWitness W.model.S eta C1 C2 W.model.basepoint 0,
          (∃ whole data sec, K0.alternative = CanonicalAlternative.positive whole data sec) →
          Nonempty (CanonicalWitness S eps (2 * C1) C x t) := by
  let C := max (sourceCurvatureBound 3 C2)
    (max (4 * C2) (2 * windowedGoodPointConstant (2 * C2)))
  have hC4 : 4 * C2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCcurv : sourceCurvatureBound 3 C2 ≤ C := le_max_left _ _
  have hCgrad : 2 * windowedGoodPointConstant (2 * C2) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCtime : windowedGoodPointConstant (2 * C2) ≤ C := by
    linarith [windowedGoodPointConstant_pos (2 * C2)]
  have hC2pos : 0 < C2 := by linarith
  let c := C2⁻¹
  have hc : 0 < c := inv_pos.mpr hC2pos
  let B := c + 360 + C2
  have hB : 0 < B := by dsimp only [B]; positivity
  let E := 486 * C2 * (1 + 3 * C2)
  have hE : 0 < E := by dsimp only [E]; positivity
  let delta0 := min (1 / 16) (min E⁻¹ (min ((4 * C1)⁻¹ ^ 2) (c / (8 * B))))
  refine ⟨C, (by linarith), delta0, lt_min (by norm_num)
    (lt_min (inv_pos.mpr hE) (lt_min (sq_pos_of_pos (inv_pos.mpr (by positivity)))
      (div_pos hc (by positivity)))), ?_⟩
  intro eps heps heps1 M _ _ _ _ _ D S delta kappa eta x t W hdelta hS hregular K0 hpositive
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : ConnectedSpace W.model.M := W.model_ancient.connected
  obtain ⟨whole, data, sec, hpos⟩ := hpositive
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hK0univ : K0.domain.carrier = univ := by rw [whole, PreconnectedSpace.connectedComponent_eq_univ]
  have hd16 : delta ≤ 1 / 16 := hdelta.trans (min_le_left _ _)
  have hdrest := hdelta.trans (min_le_right _ _)
  have hdE : delta ≤ E⁻¹ := hdrest.trans (min_le_left _ _)
  have hdrest' := hdrest.trans (min_le_right _ _)
  have hdradius : delta ≤ (4 * C1)⁻¹ ^ 2 := hdrest'.trans (min_le_left _ _)
  have hdsec : delta ≤ c / (8 * B) := hdrest'.trans (min_le_right _ _)
  have hd4 : delta ≤ 1 / 4 := by linarith
  have hsmall : 486 * C2 * (1 + 3 * C2) * delta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdE hE.le
    rwa [mul_inv_cancel₀ hE.ne'] at hh
  have hbuffer : 2 * (2 * C1) ≤ modelRadius delta := by
    calc
      2 * (2 * C1) = modelRadius ((4 * C1)⁻¹ ^ 2) := by
        rw [modelRadius, Real.sqrt_sq (by positivity), inv_inv]
        ring
      _ ≤ modelRadius delta := modelRadius_anti W.eps_pos hdradius
  let K : CanonicalWitness W.model.S eta (2 * C1) C2 W.model.basepoint 0 :=
    K0.enlarge_constants (by linarith) le_rfl
  have hKuniv : K.domain.carrier = univ := hK0univ
  have hKouter : K.domain.carrier ⊆ riemannianBallOf (W.model.S.base.metric 0)
      W.model.basepoint (2 * C1) := by
    have hr : K0.radius ≤ C1 := by
      simpa only [hbase, Real.sqrt_one, div_one] using K0.radius_upper
    exact K0.inside_ball.trans (riemannianBallOf_mono _ _ (by linarith))
  obtain ⟨r, hrlo, hrhi, hrin, hrout⟩ := W.exists_source_image_radius_of_reserve K
    (a := 2 * C1) (b := 2 * C1) (margin := 1 / 2)
    (by linarith) (by norm_num; exact hd16) (by linarith)
    (le_max_left _ _) (by linarith) (by rw [hKuniv]; exact subset_univ _)
    hKouter (by linarith)
  rw [max_eq_left (by linarith : (2 : ℝ) ≤ 2 * C1)] at hrhi
  let U := W.canonicalDomainImage K hbuffer
  have hwhole : U.carrier = connectedComponent x :=
    W.image_canonical_domain_eq_connectedComponent_of_isOpen K hbuffer
      (by rw [hKuniv]; exact isOpen_univ)
  obtain ⟨data'⟩ := positiveComponent_transport_of_partialDiffeomorph data W.embedding
    (W.canonical_domain_subset_source K hbuffer)
  have hCinv2 : C⁻¹ ≤ (2 * C2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hCinv4 : C⁻¹ ≤ (4 * C2)⁻¹ := inv_anti₀ (by positivity) hC4
  have hsrcsec : SecLower (S.base.metric t) (C⁻¹ * S.scalar t x) U.carrier := by
    let V : TopologicalSpace.Opens W.model.M := ⊤
    have hVsource : (V : Set W.model.M) ⊆ W.embedding.source := by
      rw [show (V : Set W.model.M) = univ from rfl, ← hKuniv]
      exact W.canonical_domain_subset_source K hbuffer
    have hVA : (V : Set W.model.M) ⊆ riemannianClosedBallOf
        (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta) := by
      rw [show (V : Set W.model.M) = univ from rfl, ← hKuniv]
      exact W.canonical_domain_subset_comparison_ball K hbuffer
    have hsecmodel : SecLower (W.model.S.base.metric 0) c V := by
      change SecLower (W.model.S.base.metric 0) C2⁻¹ univ
      simpa only [hbase, mul_one, hK0univ] using sec
    have hrmmodel : ∀ y ∈ (V : Set W.model.M), normSq0S (W.model.S.base.metric 0) y 4
        (metricRm04At (W.model.S.base.metric 0) y) ≤ C2 ^ 2 := by
      intro y _
      have hb := K0.rm_bound y (by rw [hK0univ]; exact mem_univ y)
      rw [hbase, mul_one] at hb
      change Real.sqrt (W.model.rmNormSq 0 y) ≤ C2 at hb
      have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
      change W.model.rmNormSq 0 y ≤ C2 ^ 2
      nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
    have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
      ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
    have horder : 2 ≤ modelOrder delta := by
      have hh := five_le_modelOrder W.eps_pos hd4
      omega
    have hh := W.comparison.secLower_image V hVsource hVA ht0 (by linarith)
      horder hc.le hC2pos.le hsecmodel hrmmodel
    have hbound : C⁻¹ ≤ c - 4 * delta * (c + 360 + C2) := by
      have hm := (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hdsec
      have hinv : (2 * C2)⁻¹ = c / 2 := by dsimp only [c]; field_simp
      rw [hinv] at hCinv2
      dsimp only [B] at hm
      linarith
    have hscaled : SecLower (scaleMetric (S.scalar t x) W.scalar_pos (S.base.metric t))
        C⁻¹ U.carrier := by
      have hm := hh.mono hbound
      simp only [rescaledMetric, parabolicTime_zero] at hm
      change SecLower (scaleMetric (S.scalar t x) W.scalar_pos (S.base.metric t))
        C⁻¹ (W.embedding '' univ) at hm
      simpa only [U, WindowedModelWitness.canonicalDomainImage_carrier, hKuniv] using hm
    exact (secLower_scaleMetric_iff W.scalar_pos (S.base.metric t) U.carrier).mp hscaled
  have hv0 : K0.alternative.requiresVolume := by rw [hpos]; trivial
  have hv : K.alternative.requiresVolume := by
    simpa only [K, CanonicalWitness.enlarge_constants_requiresVolume] using hv0
  have hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ (2 * C2) ^ 2 := by
    intro s hs y _
    have hlim := ancientKappaThree_toKLim W.model W.model_ancient (by simp [ThreeSpace])
    have hscalar := (K0.scalar_bounds y (by rw [hK0univ]; exact mem_univ y)).2
    rw [hbase, mul_one] at hscalar
    have hh := hlim.rmNormSq_le_of_terminal_scalar_le W.model (by simp [ThreeSpace]) hs.2 y hscalar
    nlinarith [sq_nonneg C2]
  refine ⟨{
    Q_pos := W.scalar_pos
    time_mem := W.time_mem
    eps_pos := heps
    eps_lt_one := heps1
    domain := U
    center_inside := W.mem_interior_canonicalDomainImage K hbuffer
    radius := r
    radius_lower := hrlo
    radius_upper := hrhi
    ball_inside := hrin
    inside_ball := hrout
    scalar_bounds := ?_
    rm_bound := ?_
    alternative := CanonicalAlternative.positive hwhole data' hsrcsec
    volume := ?_
    gradient := ?_
    time_derivative := ?_ }⟩
  · rintro y ⟨z, hz, rfl⟩
    have hb := W.scalar_bounds_on_canonical_domain K hd4 hbuffer hsmall hz
    exact ⟨(mul_le_mul_of_nonneg_right hCinv2 W.scalar_pos.le).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * C2 ≤ C) W.scalar_pos.le)⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (W.curvature_bound_on_canonical_domain K hd4 hbuffer hz).trans
      (mul_le_mul_of_nonneg_right hCcurv W.scalar_pos.le)
  · intro _
    exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCinv4
      (mul_nonneg W.scalar_pos.le (Real.sqrt_nonneg _)))).trans
        (W.volume_lower_bound_on_canonical_domain_of_le_half K (by linarith) hbuffer hv)
  · intro v
    have hb := W.scalar_gradient_bound hS hd4 (by positivity : 0 ≤ 2 * C2) hregular hmodel v
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCgrad W.scalar_pos.le) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · exact (W.scalar_left_derivative_bound hS hd4 (by positivity : 0 ≤ 2 * C2) hregular hmodel).trans
      (mul_le_mul_of_nonneg_right hCtime (sq_nonneg _))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
