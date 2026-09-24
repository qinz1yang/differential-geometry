import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceBallSandwich
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalInnerRadius
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

theorem exists_windowedModelWitness_canonicalWitness_of_model_neck_of_radial_reserve
    {C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 16 →
      ∀ a b margin : ℝ, 5 / 4 < a → a ≤ max C1 2 → 0 < margin →
        b < (2 - margin) * a → ∃ delta0 : ℝ, 0 < delta0 ∧
          ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
            {delta kappa : ℝ} {x : M} {t : ℝ}
            (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
            IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            ∀ K : CanonicalWitness W.model.S (neckModelTolerance (eps / 2))
              C1 C2 W.model.basepoint 0,
            (∃ N, K.alternative = CanonicalAlternative.neck N) →
            riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint a ⊆ K.domain.carrier →
            K.domain.carrier ⊆ riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint b →
            Nonempty (CanonicalWitness S eps (max C1 2) C x t) := by
  let C := max (sourceCurvatureBound 3 C2)
    (max (4 * C2) (2 * windowedGoodPointConstant (2 * C2)))
  have hC4 : 4 * C2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCcurv : sourceCurvatureBound 3 C2 ≤ C := le_max_left _ _
  have hCgrad : 2 * windowedGoodPointConstant (2 * C2) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCtime : windowedGoodPointConstant (2 * C2) ≤ C := by
    linarith [windowedGoodPointConstant_pos (2 * C2)]
  refine ⟨C, (by linarith), ?_⟩
  intro eps heps hepssmall a b margin ha haC hmargin hreserve
  obtain ⟨d, hd, hneck⟩ := exists_windowed_neck_transfer_threshold.{u}
    (by linarith : 0 < eps / 2) (by linarith : eps / 2 < 1 / 32)
  let B := max (2 * C1) b + 1
  have hB : 0 < B := by dsimp only [B]; linarith [le_max_left (2 * C1) b]
  let E := 486 * C2 * (1 + 3 * C2)
  have hE : 0 < E := by dsimp only [E]; positivity
  let delta0 := min d (min (1 / 8) (min (margin / 8) (min E⁻¹ (B⁻¹ ^ 2))))
  refine ⟨delta0, lt_min hd (lt_min (by norm_num)
    (lt_min (by positivity) (lt_min (inv_pos.mpr hE) (sq_pos_of_pos (inv_pos.mpr hB))))), ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hdelta hS hregular K hKneck hinner houter
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hdd : delta ≤ d := hdelta.trans (min_le_left _ _)
  have hdrest := hdelta.trans (min_le_right _ _)
  have hd8 : delta ≤ 1 / 8 := hdrest.trans (min_le_left _ _)
  have hdrest' := hdrest.trans (min_le_right _ _)
  have hdmargin : delta ≤ margin / 8 := hdrest'.trans (min_le_left _ _)
  have hdrest'' := hdrest'.trans (min_le_right _ _)
  have hdE : delta ≤ E⁻¹ := hdrest''.trans (min_le_left _ _)
  have hdB : delta ≤ B⁻¹ ^ 2 := hdrest''.trans (min_le_right _ _)
  have hd4 : delta ≤ 1 / 4 := by linarith
  have hrad : B ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdB
    rwa [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hB.le), inv_inv] at hh
  have hbuffer : 2 * C1 ≤ modelRadius delta := by
    have hmax := le_max_left (2 * C1) b
    dsimp only [B] at hrad
    linarith
  have hb : b ≤ modelRadius delta := by
    have hmax := le_max_right (2 * C1) b
    dsimp only [B] at hrad
    linarith
  have hsmall : 486 * C2 * (1 + 3 * C2) * delta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdE hE.le
    rwa [mul_inv_cancel₀ hE.ne'] at hh
  obtain ⟨r, hrlo, hrhi, hrin, hrout⟩ := W.exists_source_image_radius_of_reserve K
    hd8 hdmargin ha haC hb hinner houter hreserve
  let U := W.canonicalDomainImage K hbuffer
  obtain ⟨N, hN⟩ := hKneck
  have htransport := hneck M D S hS delta kappa x t W hdd
    (fun s hs => (W.normalized_window hregular).2 hs) N.strong
  rw [show 2 * (eps / 2) = eps by ring] at htransport
  obtain ⟨nk, hnk⟩ := htransport
  have hregion : nk.region = U.carrier := by
    calc
      nk.region = W.embedding '' (N.strong.map '' (univ ×ˢ Icc (-10 : ℝ) 10)) := by
        rw [StrongNeck.region, hnk, Set.image_image]
        rfl
      _ = U.carrier := congrArg (fun X => W.embedding '' X) N.region_eq.symm
  have hv : K.alternative.requiresVolume := by rw [hN]; trivial
  have hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ (2 * C2) ^ 2 := by
    intro s hs y hy
    have hlim := ancientKappaThree_toKLim W.model W.model_ancient (by simp [ThreeSpace])
    have hyK := K.closedBall_two_subset_of_scalar_one W.model_scalar_base hy
    have hscalar := (K.scalar_bounds y hyK).2
    rw [show W.model.S.scalar 0 W.model.basepoint = 1 from W.model_scalar_base, mul_one] at hscalar
    have hh := hlim.rmNormSq_le_of_terminal_scalar_le W.model (by simp [ThreeSpace]) hs.2 y hscalar
    nlinarith [sq_nonneg C2]
  have hCpos : 0 < C := by linarith
  have hC2pos : 0 < C2 := by linarith
  have hCinv2 : C⁻¹ ≤ (2 * C2)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hCinv4 : C⁻¹ ≤ (4 * C2)⁻¹ := inv_anti₀ (by positivity) hC4
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
    alternative := CanonicalAlternative.neck (hregion ▸ nk.toLocalNeck)
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

theorem exists_windowedModelWitness_canonicalWitness_of_model_neck
    {C2 : ℝ} (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 16 →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
          {delta kappa C1 : ℝ} {x : M} {t : ℝ}
          (W : WindowedModelWitness delta kappa S x t), delta ≤ delta0 →
          IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          ∀ K : CanonicalWitness W.model.S (neckModelTolerance (eps / 2))
            C1 C2 W.model.basepoint 0,
          (∃ N, K.alternative = CanonicalAlternative.neck N) →
          Nonempty (CanonicalWitness S eps 9 C x t) := by
  obtain ⟨C, hC, htransfer⟩ :=
    exists_windowedModelWitness_canonicalWitness_of_model_neck_of_radial_reserve.{u}
      (C1 := 9) (by norm_num) hC2
  refine ⟨C, hC, ?_⟩
  intro eps heps hsmall
  obtain ⟨delta0, hdelta0, hdelta⟩ := htransfer eps heps hsmall 9 17 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M _ _ _ _ _ D S delta kappa C1 x t W hd hS hregular K hneck
  obtain ⟨N, hN⟩ := hneck
  have hscalar : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hinner := K.closedBall_nine_subset_of_scalar_one hscalar
  have houter : K.domain.carrier ⊆
      riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint 17 := by
    simpa only [StrongNeck.region, ← N.region_eq, hscalar, Real.sqrt_one, div_one] using
      N.strong.region_subset_ball
  let K' : CanonicalWitness W.model.S (neckModelTolerance (eps / 2))
      9 C2 W.model.basepoint 0 := {
    K with
    radius := 9
    radius_lower := by simp only [hscalar, Real.sqrt_one, inv_one]; norm_num
    radius_upper := by simp only [hscalar, Real.sqrt_one, div_one, le_refl]
    ball_inside := by
      intro y hy
      apply hinner
      change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y <
        ENNReal.ofReal (9 : ℝ) at hy
      exact hy.le
    inside_ball := houter.trans (riemannianBallOf_mono _ _ (by norm_num : (17 : ℝ) ≤ 2 * 9)) }
  have hneck' : ∃ N, K'.alternative = CanonicalAlternative.neck N := ⟨N, hN⟩
  have hh := hdelta W hd hS hregular K' hneck' hinner houter
  norm_num only [max_eq_left (by norm_num : (2 : ℝ) ≤ 9)] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
