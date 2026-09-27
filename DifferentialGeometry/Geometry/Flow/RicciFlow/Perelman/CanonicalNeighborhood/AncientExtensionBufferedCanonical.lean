import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarDiameter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckDiameter

set_option autoImplicit false
noncomputable section
open Bundle Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem isEmpty_strongNeck_of_inv_eleven_le {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ}
    (h : 1 / 11 ≤ eps) : IsEmpty (StrongNeck S eps x t) :=
  ⟨fun neck => absurd neck.eps_small (not_lt.mpr h)⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem isEmpty_strongNeck_two_mul_of_inv_twentytwo_le {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ} {x : M} {t : ℝ}
    (h : 1 / 22 ≤ alpha) : IsEmpty (StrongNeck S (2 * alpha) x t) :=
  isEmpty_strongNeck_of_inv_eleven_le (by linarith)

theorem localCap_tube_metricDistance_lt_two_mul_radiusUpper {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) (cap : LocalCap S eps x t W.domain.carrier)
    {v : M} (hv : v ∈ cap.tube) :
    metricDistance (S.base.metric t) x v < 2 * (C1 / Real.sqrt (S.scalar t x)) := by
  have hQ : 0 < S.scalar t x := W.Q_pos
  have hrpos : 0 < W.radius :=
    lt_of_lt_of_le (inv_pos.mpr (Real.sqrt_pos.mpr hQ)) W.radius_lower
  have htube : cap.tube ⊆ W.domain.carrier :=
    fun _ hy => cap.union_eq.symm ▸ (Or.inr hy)
  have hball : riemannianEDistOf (S.base.metric t) x v < ENNReal.ofReal (2 * W.radius) :=
    W.inside_ball (htube hv)
  have hfinite : riemannianEDistOf (S.base.metric t) x v ≠ ⊤ :=
    ne_top_of_lt hball
  have hreal : (riemannianEDistOf (S.base.metric t) x v).toReal < 2 * W.radius := by
    rw [← ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * W.radius)]
    exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hball
  have hupper : 2 * W.radius ≤ 2 * (C1 / Real.sqrt (S.scalar t x)) :=
    mul_le_mul_of_nonneg_left W.radius_upper (by norm_num)
  exact hreal.trans_le hupper

theorem localCap_tube_depth_lt_two_mul_comparisonConstant {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) (cap : LocalCap S eps x t W.domain.carrier)
    {H : ℝ} (hdepth : ∀ y ∈ cap.tube,
      H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    {v : M} (hv : v ∈ cap.tube) : H < 2 * C1 := by
  have hsqrt : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr W.Q_pos
  have h1 : H / Real.sqrt (S.scalar t x) < 2 * (C1 / Real.sqrt (S.scalar t x)) :=
    (hdepth v hv).trans_lt (localCap_tube_metricDistance_lt_two_mul_radiusUpper W cap hv)
  rw [← mul_div_assoc] at h1
  rw [div_lt_div_iff_of_pos_right hsqrt] at h1
  linarith

theorem goodPointNeckArmFrontier_of_structure {kappa alpha theta epsStar Lmin Lmax : ℝ}
    (h : GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax) :
    ∃ C : ℝ, 0 < C ∧ GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax :=
  goodPointNeckArmFrontier_of_structure_and_coreDiameterBound h neckCoreDiameterBound_holds

theorem goodPointNeckArmFrontier_exists_iff_structure {kappa alpha theta epsStar Lmin Lmax : ℝ} :
    (∃ C : ℝ, 0 < C ∧ GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax) ↔
      GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax :=
  ⟨fun ⟨_C, _hC, hf⟩ => goodPointNeckArmStructure_of_frontier hf,
    fun h => goodPointNeckArmFrontier_of_structure h⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
