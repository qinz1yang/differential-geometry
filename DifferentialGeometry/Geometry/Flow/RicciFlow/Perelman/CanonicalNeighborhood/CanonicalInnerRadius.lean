import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalRadialReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem CanonicalWitness.closedBall_nine_subset_of_scalar_one
    {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (K : CanonicalWitness S eps C1 C2 x t) (hscalar : S.scalar t x = 1) :
    riemannianClosedBallOf (I := I3) (S.base.metric t) x 9 ⊆ K.domain.carrier := by
  have hcomponent : riemannianClosedBallOf (I := I3) (S.base.metric t) x 9 ⊆
      connectedComponent x := by
    intro y hy
    apply DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen
      (S.base.metric t) x 10
    exact hy.trans_lt (by norm_num : ENNReal.ofReal (9 : ℝ) < ENNReal.ofReal (10 : ℝ))
  cases K.alternative with
  | neck L =>
    have hsmall : 0 < 1 - eps := by linarith [L.strong.eps_small]
    have hsquare := Real.sq_sqrt hsmall.le
    have hroot := Real.sqrt_nonneg (1 - eps)
    have hr : (9 : ℝ) < 10 * Real.sqrt (1 - eps) := by
      nlinarith [L.strong.eps_small]
    have hsub := L.strong.closedBall_subset_region
      (by simpa only [hscalar, Real.sqrt_one, div_one] using hr)
    simpa only [StrongNeck.region, ← L.region_eq] using hsub
  | cap cap deep =>
    let p : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
    let v := cap.tubeMap (p, 0)
    have hv : v ∈ cap.tube := by
      rw [← cap.tube_eq]
      exact ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
    have hvK : v ∈ K.domain.carrier := cap.union_eq.symm ▸ Or.inr hv
    have hdeep : 10000 ≤ metricDistance (S.base.metric t) x v := by
      simpa only [hscalar, Real.sqrt_one, div_one] using deep v hv
    have hr : 1 ≤ K.radius := by
      simpa only [hscalar, Real.sqrt_one, inv_one] using K.radius_lower
    have hball := K.inside_ball hvK
    have hfinite : riemannianEDistOf (S.base.metric t) x v ≠ ⊤ := ne_top_of_lt hball
    have hreal : (riemannianEDistOf (S.base.metric t) x v).toReal < 2 * K.radius := by
      rw [← ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * K.radius)]
      exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hball
    have hnine : (9 : ℝ) < K.radius := by
      change 10000 ≤ (riemannianEDistOf (S.base.metric t) x v).toReal at hdeep
      linarith
    intro y hy
    apply K.ball_inside
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < K.radius)).mpr hnine)
  | positive whole _ _ =>
    rw [whole]
    exact hcomponent
  | round whole _ =>
    rw [whole]
    exact hcomponent

theorem CanonicalWitness.closedBall_two_subset_of_scalar_one
    {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (K : CanonicalWitness S eps C1 C2 x t) (hscalar : S.scalar t x = 1) :
    riemannianClosedBallOf (I := I3) (S.base.metric t) x 2 ⊆ K.domain.carrier :=
  (riemannianClosedBallOf_mono _ _ (by norm_num : (2 : ℝ) ≤ 9)).trans
    (K.closedBall_nine_subset_of_scalar_one hscalar)

theorem CanonicalWitness.exists_normalized_radial_reserve
    {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (K : CanonicalWitness S eps C1 C2 x t) (hscalar : S.scalar t x = 1) :
    ∃ a b margin : ℝ, 5 / 4 < a ∧ a < max C1 2 ∧ 0 < margin ∧
      b < (2 - margin) * a ∧
      riemannianClosedBallOf (I := I3) (S.base.metric t) x a ⊆ K.domain.carrier ∧
      K.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b := by
  let r := max K.radius (3 / 2)
  have hr : 0 < r := (by norm_num : (0 : ℝ) < 3 / 2).trans_le (le_max_right _ _)
  have hradius : K.radius ≤ C1 := by
    simpa only [hscalar, Real.sqrt_one, div_one] using K.radius_upper
  have hrC : r ≤ max C1 2 := max_le_max hradius (by norm_num)
  have hne : K.domain.carrier.Nonempty := ⟨x, interior_subset K.center_inside⟩
  obtain ⟨z, hz, hmax⟩ := K.domain.compact.exists_isMaxOn hne
    (continuous_riemannianEDist (S.base.metric t) x).continuousOn
  have hzball : riemannianEDistOf (S.base.metric t) x z < ENNReal.ofReal (2 * r) :=
    (K.inside_ball hz).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)))
  have hzfinite : riemannianEDistOf (S.base.metric t) x z ≠ ⊤ := ne_top_of_lt hzball
  have hzlt : (riemannianEDistOf (S.base.metric t) x z).toReal < 2 * r := by
    have hh := (ENNReal.toReal_lt_toReal hzfinite ENNReal.ofReal_ne_top).mpr hzball
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)] using hh
  obtain ⟨b, hzb, hbr⟩ := exists_between hzlt
  have hb : 0 < b := ENNReal.toReal_nonneg.trans_lt hzb
  have houter : K.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b := by
    intro y hy
    have hzbound : riemannianEDistOf (S.base.metric t) x z < ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hzfinite]
      exact (ENNReal.ofReal_lt_ofReal_iff hb).mpr hzb
    exact (hmax hy).trans_lt hzbound
  have hsmall : max (5 / 4 : ℝ) (b / 2) < r := by
    apply max_lt_iff.mpr
    exact ⟨(by norm_num : (5 / 4 : ℝ) < 3 / 2).trans_le (le_max_right _ _), by linarith⟩
  obtain ⟨a, hamin, har⟩ := exists_between hsmall
  have haquarter : (5 / 4 : ℝ) < a := (le_max_left _ _).trans_lt hamin
  have hba : b / 2 < a := (le_max_right _ _).trans_lt hamin
  have ha : 0 < a := (by norm_num : (0 : ℝ) < 5 / 4).trans haquarter
  have hinner : riemannianClosedBallOf (I := I3) (S.base.metric t) x a ⊆ K.domain.carrier := by
    by_cases hrr : (3 / 2 : ℝ) ≤ K.radius
    · have haradius : a < K.radius := by simpa only [r, max_eq_left hrr] using har
      intro y hy
      exact K.ball_inside (hy.trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (ha.trans haradius)).mpr haradius))
    · have hatwo : a ≤ (2 : ℝ) := by
        have hh : a < 3 / 2 := by
          simpa only [r, max_eq_right (not_le.mp hrr).le] using har
        linarith
      exact (riemannianClosedBallOf_mono (S.base.metric t) x hatwo).trans
        (K.closedBall_two_subset_of_scalar_one hscalar)
  let margin := (2 * a - b) / (2 * a)
  have hm : 0 < margin := div_pos (by linarith) (by positivity)
  have hmargin : b < (2 - margin) * a := by
    have hmul : margin * a = (2 * a - b) / 2 := by
      dsimp only [margin]
      field_simp [ha.ne']
    nlinarith
  exact ⟨a, b, margin, haquarter, har.trans_le hrC, hm, hmargin, hinner, houter⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
