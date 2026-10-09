import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactPositiveCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientPositive

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_positive_canonicalWitness_of_compact_ancientKappa
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (data : PositiveComponent (univ : Set F.M)) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ K : CanonicalWitness F.S eps A C x t, K.domain.carrier = univ ∧
        ∃ whole positive lower, K.alternative = CanonicalAlternative.positive whole positive lower := by
  let _ : ConnectedSpace F.M := hF.connected
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hpos := ancientKappa_curvatureOperatorPositive_of_compact F hF hdim
  have hsec : HasPositiveSectionalCurvature (F.S.base.metric t) :=
    fun y v w hvw => ((curvatureOperatorPositiveAt_iff_sectional
      (F.S.base.metric t) y hdim).mp (hpos t ht y)) v w (by
        simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
          Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
            (F.S.base.metric t) y v w hvw)
  obtain ⟨c, hc, hclower⟩ := exists_pos_secLower_of_compact_positive_sectional (F.S.base.metric t) hsec
  exact exists_positive_canonicalWitness_of_compact ht
    (fun y => ancientKappa_scalar_pos F hF ht y) data hc hclower

theorem exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (data : PositiveComponent (univ : Set F.M)) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ alpha : ℝ, 0 < alpha → ∀ H : ℝ,
      Nonempty (BufferedCanonical F.S alpha C H x t) := by
  let _ : ConnectedSpace F.M := hF.connected
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hpos := ancientKappa_curvatureOperatorPositive_of_compact F hF hdim
  have hsec : HasPositiveSectionalCurvature (F.S.base.metric t) :=
    fun y v w hvw => ((curvatureOperatorPositiveAt_iff_sectional
      (F.S.base.metric t) y hdim).mp (hpos t ht y)) v w (by
        simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
          Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
            (F.S.base.metric t) y v w hvw)
  obtain ⟨c, hc, hclower⟩ := exists_pos_secLower_of_compact_positive_sectional (F.S.base.metric t) hsec
  exact exists_bufferedCanonical_of_compact_positive ht
    (fun y => ancientKappa_scalar_pos F hF ht y) data hc hclower

theorem exists_bufferedCanonical_of_compact_ancientKappa_of_projectivePresentation
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (pr : ProjectivePresentation F.M) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ alpha : ℝ, 0 < alpha → ∀ H : ℝ,
      Nonempty (BufferedCanonical F.S alpha C H x t) :=
  exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent F hF
    (positiveComponentOfDiffeomorphProjective F.M pr (Diffeomorph.refl I3 F.M ∞)) ht x

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
