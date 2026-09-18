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

theorem exists_windowedModelWitness_canonicalWitness_of_model_round_component
    {C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 2 →
      ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
          {delta kappa : ℝ} {x : M} {t : ℝ}
          (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
          IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          ∀ K0 : CanonicalWitness W.model.S eta C1 C2 W.model.basepoint 0,
          (∃ whole R, K0.alternative = CanonicalAlternative.round whole R) →
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
  refine ⟨C, (by linarith), ?_⟩
  intro eps heps hepshalf
  obtain ⟨eta, heta, heta1, d, hd, hroundTransfer⟩ :=
    exists_windowedModelWitness_round_component_of_model_round_component.{u} heps hepshalf
  let E := 486 * C2 * (1 + 3 * C2)
  have hE : 0 < E := by dsimp only [E]; positivity
  let delta0 := min d (min (1 / 16) (min E⁻¹ ((4 * C1)⁻¹ ^ 2)))
  refine ⟨eta, heta, heta1, delta0, lt_min hd (lt_min (by norm_num)
    (lt_min (inv_pos.mpr hE) (sq_pos_of_pos (inv_pos.mpr (by positivity))))), ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hdelta hS hregular K0 hround
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : ConnectedSpace W.model.M := W.model_ancient.connected
  obtain ⟨whole, R, _⟩ := hround
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hK0univ : K0.domain.carrier = univ := by rw [whole, PreconnectedSpace.connectedComponent_eq_univ]
  have hdd : delta ≤ d := hdelta.trans (min_le_left _ _)
  have hdrest := hdelta.trans (min_le_right _ _)
  have hd16 : delta ≤ 1 / 16 := hdrest.trans (min_le_left _ _)
  have hdrest' := hdrest.trans (min_le_right _ _)
  have hdE : delta ≤ E⁻¹ := hdrest'.trans (min_le_left _ _)
  have hdradius : delta ≤ (4 * C1)⁻¹ ^ 2 := hdrest'.trans (min_le_right _ _)
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
  have R_univ : RoundComponent W.model.S eta W.model.basepoint 0 univ := hK0univ ▸ R
  obtain ⟨R'⟩ := hroundTransfer W hdd R_univ
  have hCinv2 : C⁻¹ ≤ (2 * C2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
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
    alternative := CanonicalAlternative.round hwhole (hwhole.symm ▸ R')
    volume := by intro hv; cases hv
    gradient := ?_
    time_derivative := ?_ }⟩
  · rintro y ⟨z, hz, rfl⟩
    have hb := W.scalar_bounds_on_canonical_domain K hd4 hbuffer hsmall hz
    exact ⟨(mul_le_mul_of_nonneg_right hCinv2 W.scalar_pos.le).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * C2 ≤ C) W.scalar_pos.le)⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (W.curvature_bound_on_canonical_domain K hd4 hbuffer hz).trans
      (mul_le_mul_of_nonneg_right hCcurv W.scalar_pos.le)
  · intro v
    have hb := W.scalar_gradient_bound hS hd4 (by positivity : 0 ≤ 2 * C2) hregular hmodel v
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCgrad W.scalar_pos.le) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · exact (W.scalar_left_derivative_bound hS hd4 (by positivity : 0 ≤ 2 * C2) hregular hmodel).trans
      (mul_le_mul_of_nonneg_right hCtime (sq_nonneg _))

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
  have hA : 1 ≤ A := by
    have hDia : 0 ≤ Real.pi / Real.sqrt (1 / 6) := by positivity
    dsimp only [A]
    linarith
  obtain ⟨C, hC, htransfer⟩ :=
    exists_windowedModelWitness_canonicalWitness_of_model_round_component.{u} hA (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨2 * A, C, (by linarith), hC, ?_⟩
  intro eps heps hepshalf
  obtain ⟨eta, heta, heta1, delta0, hdelta0, hdelta⟩ := htransfer eps heps hepshalf
  refine ⟨delta0, hdelta0, ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hd hS hregular hround
  obtain ⟨K0, hK0univ⟩ := exists_canonicalWitness_univ_of_shrinkingSphericalSpaceFormFlow
    W.model hround W.model_scalar_base heta heta1
  obtain ⟨R⟩ := roundComponent_of_shrinkingSphericalSpaceFormFlow W.model hround le_rfl
    W.model.basepoint heta
  let _ : ConnectedSpace W.model.M := W.model_ancient.connected
  have hwhole : K0.domain.carrier = connectedComponent W.model.basepoint := by
    rw [hK0univ, PreconnectedSpace.connectedComponent_eq_univ]
  let K : CanonicalWitness W.model.S eta A 2 W.model.basepoint 0 := {
    K0 with
    alternative := CanonicalAlternative.round hwhole (hK0univ.symm ▸ R)
    volume := by intro hv; cases hv }
  exact hdelta W hd hS hregular K ⟨hwhole, hK0univ.symm ▸ R, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
