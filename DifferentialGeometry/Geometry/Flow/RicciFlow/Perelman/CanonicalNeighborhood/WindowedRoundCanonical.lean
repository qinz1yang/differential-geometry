import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedRoundComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelWitness
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

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowedModelWitness_canonicalWitness_of_round_model :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 2 →
        ∃ delta0 : ℝ, 0 < delta0 ∧
          ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
            {delta kappa : ℝ} {x : M} {t : ℝ}
            (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
            IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            IsShrinkingSphericalSpaceFormFlow (I := I3) W.model →
            Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  let A := 2 * (Real.pi / Real.sqrt (1 / 6)) + 1
  let C := max (sourceCurvatureBound 3 2) (max 4 (2 * windowedGoodPointConstant 2))
  have hA : 1 ≤ A := by
    have hDia : 0 ≤ Real.pi / Real.sqrt (1 / 6) := by positivity
    dsimp only [A]
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hC4 : 4 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCcurv : sourceCurvatureBound 3 2 ≤ C := le_max_left _ _
  have hCgrad : 2 * windowedGoodPointConstant 2 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCtime : windowedGoodPointConstant 2 ≤ C := by
    linarith [windowedGoodPointConstant_pos 2]
  refine ⟨max (2 * A) 2, C, (by exact le_trans (by norm_num) (le_max_right _ _)),
    (by linarith), ?_⟩
  intro eps heps hepshalf
  obtain ⟨d, hd, hroundTransfer⟩ := exists_windowedModelWitness_round_component.{u} heps hepshalf
  refine ⟨min d (min (1 / 6804) ((4 * A)⁻¹ ^ 2)),
    lt_min hd (lt_min (by norm_num) (sq_pos_of_pos (inv_pos.mpr (by positivity)))), ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hdelta hS hregular hround
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hdd : delta ≤ d := hdelta.trans (min_le_left _ _)
  have hrest := hdelta.trans (min_le_right _ _)
  have hdsmall : delta ≤ 1 / 6804 := hrest.trans (min_le_left _ _)
  have hdradius : delta ≤ (4 * A)⁻¹ ^ 2 := hrest.trans (min_le_right _ _)
  have hd4 : delta ≤ 1 / 4 := by linarith
  have hd16 : delta ≤ 1 / 16 := by linarith
  have hbuffer : 2 * (2 * A) ≤ modelRadius delta := by
    calc
      2 * (2 * A) = modelRadius ((4 * A)⁻¹ ^ 2) := by
        rw [modelRadius, Real.sqrt_sq (by positivity), inv_inv]
        ring
      _ ≤ modelRadius delta := modelRadius_anti W.eps_pos hdradius
  obtain ⟨K0, hK0⟩ := exists_canonicalWitness_univ_of_shrinkingSphericalSpaceFormFlow
    W.model hround W.model_scalar_base (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let K : CanonicalWitness W.model.S (1 / 2) (2 * A) 2 W.model.basepoint 0 :=
    K0.enlarge_constants (by change A ≤ 2 * A; linarith) le_rfl
  have hKuniv : K.domain.carrier = univ := hK0
  have hKouter : K.domain.carrier ⊆ riemannianBallOf (W.model.S.base.metric 0)
      W.model.basepoint (2 * A) := by
    have hr : K0.radius ≤ A := by
      simpa only [show W.model.S.scalar 0 W.model.basepoint = 1 from W.model_scalar_base,
        Real.sqrt_one, div_one] using K0.radius_upper
    exact K0.inside_ball.trans (riemannianBallOf_mono _ _ (by linarith))
  obtain ⟨r, hrlo, hrhi, hrin, hrout⟩ := W.exists_source_image_radius_of_reserve K
    (a := 2 * A) (b := 2 * A) (margin := 1 / 2)
    (by linarith) (by norm_num; exact hd16) (by linarith)
    (le_max_left _ _) (by linarith) (by rw [hKuniv]; exact subset_univ _)
    hKouter (by linarith)
  let U := W.canonicalDomainImage K hbuffer
  have hwhole : U.carrier = connectedComponent x :=
    W.image_canonical_domain_eq_connectedComponent_of_isOpen K hbuffer
      (by rw [hKuniv]; exact isOpen_univ)
  obtain ⟨R⟩ := hroundTransfer W hdd hround
  have hscalar : ∀ y : W.model.M, W.model.S.scalar 0 y = 1 := by
    intro y
    simpa using scalar_eq_of_normalized_shrinking_spherical_space_form_flow
      W.model hround W.model_scalar_base le_rfl y
  have hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ (2 : ℝ) ^ 2 := by
    intro s hs y _
    have hlim := ancientKappaThree_toKLim W.model W.model_ancient (by simp [ThreeSpace])
    have hb := hlim.rmNormSq_le_of_terminal_scalar_le W.model (by simp [ThreeSpace]) hs.2 y
      (by rw [hscalar y])
    norm_num at hb ⊢
    linarith
  have hCpos : 0 < C := by linarith
  have hCinv : C⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using (inv_le_inv₀ hCpos (by norm_num : (0 : ℝ) < 4)).mpr hC4
  refine ⟨{
    Q_pos := W.scalar_pos
    time_mem := W.time_mem
    eps_pos := heps
    eps_lt_one := by linarith
    domain := U
    center_inside := W.mem_interior_canonicalDomainImage K hbuffer
    radius := r
    radius_lower := hrlo
    radius_upper := hrhi
    ball_inside := hrin
    inside_ball := hrout
    scalar_bounds := ?_
    rm_bound := ?_
    alternative := CanonicalAlternative.round hwhole (hwhole.symm ▸ R)
    volume := by intro hv; cases hv
    gradient := ?_
    time_derivative := ?_ }⟩
  · rintro y ⟨z, hz, rfl⟩
    have hb := W.scalar_bounds_on_canonical_domain K hd4 hbuffer (by norm_num; linarith) hz
    norm_num at hb
    exact ⟨(mul_le_mul_of_nonneg_right hCinv W.scalar_pos.le).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right hC4 W.scalar_pos.le)⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (W.curvature_bound_on_canonical_domain K hd4 hbuffer hz).trans
      (mul_le_mul_of_nonneg_right hCcurv W.scalar_pos.le)
  · intro v
    have hb := W.scalar_gradient_bound hS hd4 (by norm_num : (0 : ℝ) ≤ 2) hregular hmodel v
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCgrad W.scalar_pos.le) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · exact (W.scalar_left_derivative_bound hS hd4 (by norm_num : (0 : ℝ) ≤ 2) hregular hmodel).trans
      (mul_le_mul_of_nonneg_right hCtime (sq_nonneg _))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
