import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NoncompactPositiveCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalCapCanonicalWitness

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.SphereSeparation (axialZero)
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_bufferedCanonical_of_noncompact_ancient_positive
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : HasPositiveSectionalCurvature (F.S.base.metric 0)) (p : F.M)
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ eps : ℝ, 0 < eps ∧ eps < alpha ∧
      ∃ (mark : SpatialNeckSphere) (v : F.M) (strong : StrongNeckWitness F.S mark v 0 eps)
        (nk : StrongNeck F.S eps v 0),
        nk.map.source = spatialNeckBuffer eps ∧ nk.map.target = range strong.embedding ∧
        nk.center = mark ∧ (∀ z : spatialNeckBuffer eps, nk.map z.val = strong.embedding z) ∧
        ∃ (neck : StrongNeck F.S eps v 0) (U : Set F.M) (cap : LocalCap F.S eps p 0 U) (r : ℝ),
          (neck = nk ∨ neck = nk.axialReflection) ∧
          (Real.sqrt (F.S.scalar 0 p))⁻¹ ≤ r ∧
          riemannianBallOf (F.S.base.metric 0) p r ⊆ U ∧
          U ⊆ riemannianBallOf (F.S.base.metric 0) p (2 * r) ∧
          (∀ y ∈ cap.tube, max 10000 H / Real.sqrt (F.S.scalar 0 p) ≤ metricDistance (F.S.base.metric 0) p y) ∧
          cap.tubeMap = neck.map ∧ cap.chain.count = 1 ∧
          (∀ j : Fin cap.chain.count, cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧ v ∈ cap.tube ∧
          ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∃ K : CanonicalWitness F.S eps A C p 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            (∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
            ∃ C' : ℝ, 1 ≤ C' ∧ ∃ B : BufferedCanonical F.S alpha C' H p 0,
              B.tolerance = eps ∧ B.witness.domain.carrier = U ∧ B.witness.radius = r ∧
              ∃ cap' depth, B.witness.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  obtain ⟨eps, heps, hepsa, mark, v, strong, nk, hsrc, htgt, hcenter, hmap, neck, U, cap, r,
      hneck, hr, hinner, houter, hdepth, hcapmap, hcount, hchain, hv⟩ :=
    exists_localCap_ball_sandwich_of_noncompact_ancient_positive F hF hnoncompact hsec p ha H
  have hpositive (y : F.M) (_hy : y ∈ U) : 0 < F.S.scalar 0 y :=
    ancientKappa_scalar_pos F hF le_rfl y
  have h10000 (y : F.M) (hy : y ∈ cap.tube) :
      10000 / Real.sqrt (F.S.scalar 0 p) ≤ metricDistance (F.S.base.metric 0) p y :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans (hdepth y hy)
  obtain ⟨hA, C, hC, K, hKU, hKr, capK, depthK, hKalt, hcapK⟩ :=
    cap.exists_canonicalWitness_of_scalar_pos_of_ball_sandwich hpositive hr hinner houter h10000
  let neckAlpha := neck.mono hepsa.le hasmall
  have hcentralTube : neckAlpha.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ cap.tube := by
    rw [← cap.tube_eq, hcapmap]
    apply image_mono
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    exact ⟨hz.1, by rw [hz0]; norm_num⟩
  have hfar (y : F.M) (hy : y ∈ neckAlpha.map '' (univ ×ˢ ({0} : Set ℝ))) :
      H / Real.sqrt (F.S.scalar 0 p) ≤ metricDistance (F.S.base.metric 0) p y :=
    (div_le_div_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)).trans (hdepth y (hcentralTube hy))
  have hvK : v ∈ capK.tube := by
    cases hKU
    rw [eq_of_heq hcapK]
    exact hv
  obtain ⟨C', hC', B, hBeps, hBK, hBradius, capB, depthB, hBcap, hcapB⟩ := K.exists_bufferedCanonical_of_cap_collar hepsa capK
    ⟨depthK, hKalt⟩ neckAlpha hvK hfar
  exact ⟨eps, heps, hepsa, mark, v, strong, nk, hsrc, htgt, hcenter, hmap, neck, U, cap, r,
    hneck, hr, hinner, houter, hdepth, hcapmap, hcount, hchain, hv,
    r * Real.sqrt (F.S.scalar 0 p), C, hA, hC, K, hKU, hKr,
    ⟨capK, depthK, hKalt, hcapK⟩, C', hC', B, hBeps, hBK.trans hKU, hBradius.trans hKr, capB, depthB, hBcap, hcapB.trans hcapK⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
