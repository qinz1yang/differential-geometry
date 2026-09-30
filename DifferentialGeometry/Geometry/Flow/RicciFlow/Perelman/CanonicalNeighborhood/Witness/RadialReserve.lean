import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

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
  {D : RealTimeInterval}


theorem CanonicalWitness.exists_radial_reserve
    {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) :
    ∃ a b margin : ℝ, 0 < a ∧ a < W.radius ∧ 0 < margin ∧
      b < (2 - margin) * a ∧
      riemannianBallOf (I := I3) (S.base.metric t) x a ⊆ W.domain.carrier ∧
      W.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  have hne : W.domain.carrier.Nonempty := ⟨x, interior_subset W.center_inside⟩
  obtain ⟨z, hz, hmax⟩ := W.domain.compact.exists_isMaxOn hne
    (continuous_riemannianEDist (S.base.metric t) x).continuousOn
  have hzball : riemannianEDistOf (S.base.metric t) x z < ENNReal.ofReal (2 * W.radius) :=
    W.inside_ball hz
  have hzfinite : riemannianEDistOf (S.base.metric t) x z ≠ ⊤ :=
    ne_of_lt (hzball.trans ENNReal.ofReal_lt_top)
  have hzlt : (riemannianEDistOf (S.base.metric t) x z).toReal < 2 * W.radius := by
    have hh := (ENNReal.toReal_lt_toReal hzfinite ENNReal.ofReal_ne_top).mpr hzball
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * W.radius)] using hh
  obtain ⟨b, hzb, hbr⟩ := exists_between hzlt
  have hb : 0 < b := (ENNReal.toReal_nonneg).trans_lt hzb
  have houter : W.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b := by
    intro y hy
    have hzb' : riemannianEDistOf (S.base.metric t) x z < ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hzfinite]
      exact (ENNReal.ofReal_lt_ofReal_iff hb).mpr hzb
    exact (hmax hy).trans_lt hzb'
  obtain ⟨a, hba, har⟩ := exists_between (by linarith : b / 2 < W.radius)
  have ha : 0 < a := by linarith
  let margin := (2 * a - b) / (2 * a)
  have hm : 0 < margin := div_pos (by linarith) (by positivity)
  have hmargin : b < (2 - margin) * a := by
    have hmul : margin * a = (2 * a - b) / 2 := by
      dsimp only [margin]
      field_simp [ha.ne']
    nlinarith
  exact ⟨a, b, margin, ha, har, hm, hmargin,
    (riemannianBallOf_mono (S.base.metric t) x har.le).trans W.ball_inside, houter⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem CanonicalWitness.domain_subset_closedBall_of_one_le_scalar
    {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) (hQ : 1 ≤ S.scalar t x) :
    W.domain.carrier ⊆ riemannianClosedBallOf (S.base.metric t) x (2 * C1) := by
  have hsqrt : 1 ≤ Real.sqrt (S.scalar t x) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQ
  have hsqrtpos : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr W.Q_pos
  have hrpos : 0 < W.radius :=
    (inv_pos.mpr hsqrtpos).trans_le W.radius_lower
  have hC1pos : 0 < C1 := by
    have hh := (le_div_iff₀ hsqrtpos).mp W.radius_upper
    exact (mul_pos hrpos hsqrtpos).trans_le hh
  have hrad : W.radius ≤ C1 :=
    W.radius_upper.trans (div_le_self hC1pos.le hsqrt)
  intro y hy
  exact (W.inside_ball hy).le.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hrad (by norm_num)))


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
