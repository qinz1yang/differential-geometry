import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalPrecompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BufferedMixedCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureScaling


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private theorem threeSpace_finrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

private local instance threeSpace_finrank_neZero : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by rw [threeSpace_finrank]; norm_num⟩


def mixedCurvatureWeight (a b : ℕ) : ℝ := 1 + (a : ℝ) / 2 + b


def UniversalMixedJetBound (a b : ℕ) (C : ℝ) : Prop :=
  ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
    IsAncientKappaSolution (I := I3) kappa F → ∀ t ≤ 0, ∀ x : F.M,
      mixedCurvatureNorm F.S a b t x ≤ C * F.S.scalar t x ^ mixedCurvatureWeight a b


def RoundMixedJetBound (a b : ℕ) (C : ℝ) : Prop :=
  ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
    IsAncientKappaSolution (I := I3) kappa F →
    IsShrinkingSphericalSpaceFormFlow (I := I3) F → ∀ t ≤ 0, ∀ x : F.M,
      mixedCurvatureNorm F.S a b t x ≤ C * F.S.scalar t x ^ mixedCurvatureWeight a b


theorem exists_universal_mixed_jet_bound_of_not_round (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F →
        ¬ IsShrinkingSphericalSpaceFormFlow (I := I3) F → ∀ t ≤ 0, ∀ x : F.M,
          mixedCurvatureNorm F.S a b t x ≤ C * F.S.scalar t x ^ mixedCurvatureWeight a b := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_klim_mixed_jet_bound (I := I3)
    threeSpace_finrank universalKappaConstant 0 le_rfl a b
  refine ⟨C, hC, ?_⟩
  intro kappa F hF hnotround t ht x
  set Q : ℝ := F.S.scalar t x with hQdef
  have hQ : 0 < Q := ancientKappa_scalar_pos F hF ht x
  have hG : KLim universalKappaConstant (universalNormalizedFlow F hF ht x) :=
    ancientKappaThree_toKLim (universalNormalizedFlow F hF ht x)
      (universalNormalizedFlow_isAncientKappaSolution_universal F hF hnotround ht x)
      threeSpace_finrank
  have hbase : (universalNormalizedFlow F hF ht x).S.scalar 0
      (universalNormalizedFlow F hF ht x).basepoint = 1 :=
    universalNormalizedFlow_scalarAtBase F hF ht x
  have hnorm := (hbound ancientTimeInterval (universalNormalizedFlow F hF ht x) hG hbase
    0 le_rfl (universalNormalizedFlow F hF ht x).basepoint
    (by simp [riemannianEDistOf_self])).2
  have hnorm' : mixedCurvatureNorm (curvatureNormalizedSolution F.S t Q hQ ht) a b 0 x ≤ C :=
    hnorm
  have hscale := mixedCurvatureNorm_curvatureNormalizedSolution (I := I3) F.S F.isSolution
    hF.carrier_eq hF.regular_eq t Q hQ ht a b (le_refl (0 : ℝ)) x
  have hpt : parabolicTime t Q 0 = t := by simp [parabolicTime]
  rw [hpt] at hscale
  have hexp : (-(1 : ℝ) - (a : ℝ) / 2 - (b : ℝ)) = -(mixedCurvatureWeight a b) := by
    simp only [mixedCurvatureWeight]; ring
  rw [hexp, Real.rpow_neg hQ.le] at hscale
  rw [hscale] at hnorm'
  have hw : 0 < Q ^ mixedCurvatureWeight a b := Real.rpow_pos_of_pos hQ _
  have hfinal := (inv_mul_le_iff₀ hw).1 hnorm'
  linarith [hfinal]


theorem exists_universal_mixed_jet_bound (a b : ℕ) {C₁ : ℝ}
    (hround : RoundMixedJetBound.{u} a b C₁) :
    ∃ C : ℝ, 0 < C ∧ UniversalMixedJetBound.{u} a b C := by
  obtain ⟨C₀, hC₀, hmain⟩ := exists_universal_mixed_jet_bound_of_not_round.{u} a b
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀, ?_⟩
  intro kappa F hF t ht x
  have hR : 0 ≤ F.S.scalar t x ^ mixedCurvatureWeight a b :=
    Real.rpow_nonneg (ancientKappa_scalar_pos F hF ht x).le _
  by_cases hsph : IsShrinkingSphericalSpaceFormFlow (I := I3) F
  · exact (hround kappa F hF hsph t ht x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
  · exact (hmain kappa F hF hsph t ht x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
