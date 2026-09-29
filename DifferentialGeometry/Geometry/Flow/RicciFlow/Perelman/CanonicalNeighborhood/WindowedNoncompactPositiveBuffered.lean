import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCapBufferedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NoncompactPositiveBufferedCap

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem exists_buffered_image_with_cap_neck_charts_of_windowed_models_of_noncompact_positive_limit
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hnoncompact : NoncompactSpace L.M)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (L.S.base.metric 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    (hscalar : L.S.scalar 0 L.basepoint = 1) {alpha : ℝ}
    (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ (eps A C0 C : ℝ), 0 < eps ∧ eps < neckModelTolerance (alpha / 4) ∧ 1 ≤ C ∧
      ∃ K : CanonicalWitness L.S eps A C0 L.basepoint 0,
        ∃ (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier) (v : L.M)
          (neck : StrongNeck L.S eps v 0),
          (∃ depth, K.alternative = CanonicalAlternative.cap cap depth) ∧
          cap.tubeMap = neck.map ∧ v ∈ cap.tube ∧ cap.chain.count = 1 ∧
          (∀ j : Fin cap.chain.count, cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          ∀ᶠ i in atTop,
            ∃ Ki : CanonicalWitness (S (phi i)) (2 * (alpha / 4)) (max A 2)
                (max (sourceCurvatureBound 3 C0)
                  (max (4 * C0) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C0))))
                (x (phi i)) (t (phi i)),
              Ki.domain.carrier =
                (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' K.domain.carrier ∧
              ∃ capi depthi, Ki.alternative = CanonicalAlternative.cap capi depthi ∧
                capi.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.tube ∧
                capi.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.core.carrier ∧
                capi.tubeMap = cap.tubeMap.trans
                  (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
                ∃ ni : StrongNeck (S (phi i)) alpha ((W (phi i)).embedding (F.map i v)) (t (phi i)),
                  ni.map = neck.map.trans
                    (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
                  ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
                    B.tolerance = 2 * (alpha / 4) ∧ B.witness.domain.carrier = Ki.domain.carrier ∧
                    B.witness.radius = Ki.radius ∧
                    (∃ capB depthB, B.witness.alternative = CanonicalAlternative.cap capB depthB ∧ HEq capB capi) ∧
                    B.witness.capTubeHasNeckChart alpha := by
  let _ : ConnectedSpace L.M := hL.connected
  let alpha0 := neckModelTolerance (alpha / 4)
  have halpha0 : 0 < alpha0 := neckModelTolerance_pos (by positivity)
  have halpha0small : alpha0 < 1 / 11 := (neckModelTolerance_le (alpha / 4)).trans_lt (by linarith)
  let Hmodel := max 40000 (2 * max H 0)
  obtain ⟨eps, heps, hepstol, _mark, v, _strong, _nk, _hsrc, _htgt, _hcenter, _hmap,
      neck, U, cap, r, _hneck, _hr, _hinner, _houter, hdepth, hcapmap, _hcount, _hchain, hv,
      A, C0, _hA, _hC0, K, hKU, _hKr, hcapExists, _Cbuffer, _hCbuffer, _B, _hB⟩ :=
    exists_bufferedCanonical_of_noncompact_ancient_positive L hL hnoncompact hsec L.basepoint
      halpha0 halpha0small Hmodel
  obtain ⟨capK, depthK, hKalt, hcapK⟩ := hcapExists
  have hcapKmap : capK.tubeMap = neck.map := by
    cases hKU
    rw [eq_of_heq hcapK]
    exact hcapmap
  have hvK : v ∈ capK.tube := by
    cases hKU
    rw [eq_of_heq hcapK]
    exact hv
  have hmodelchain : capK.chain.count = 1 ∧
      ∀ j : Fin capK.chain.count, capK.chain.centers j = v ∧ HEq (capK.chain.necks j) neck ∧
        capK.chain.lo j = 0 ∧ capK.chain.hi j = 1 := by
    cases hKU
    rw [eq_of_heq hcapK]
    exact ⟨_hcount, _hchain⟩
  have hdepthK : ∀ y ∈ capK.tube,
      max 40000 (2 * max H 0) ≤ metricDistance (L.S.base.metric 0) L.basepoint y := by
    cases hKU
    rw [eq_of_heq hcapK]
    intro y hy
    have hh := hdepth y hy
    rw [hscalar, Real.sqrt_one, div_one] at hh
    exact (le_max_right _ _).trans hh
  obtain ⟨C, hC, hsource⟩ := K.exists_eventually_buffered_image_of_windowed_models_of_cap_with_neck_chart
    hS W hdelta hreg L (hL.complete 0 (by simp)) hphi F hcmp hscalar capK ⟨depthK, hKalt⟩
    neck (fun z => congrArg (fun e => e z) hcapKmap) ha hasmall hepstol hdepthK
  exact ⟨eps, A, C0, C, heps, hepstol, hC, K, capK, v, neck, ⟨depthK, hKalt⟩,
    hcapKmap, hvK, hmodelchain.1, hmodelchain.2, hsource⟩

theorem exists_buffered_image_of_windowed_models_of_noncompact_positive_limit
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hnoncompact : NoncompactSpace L.M)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (L.S.base.metric 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    (hscalar : L.S.scalar 0 L.basepoint = 1) {alpha : ℝ}
    (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ (eps A C0 C : ℝ), 0 < eps ∧ eps < neckModelTolerance (alpha / 4) ∧ 1 ≤ C ∧
      ∃ K : CanonicalWitness L.S eps A C0 L.basepoint 0,
        ∃ (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier) (v : L.M)
          (neck : StrongNeck L.S eps v 0),
          (∃ depth, K.alternative = CanonicalAlternative.cap cap depth) ∧
          cap.tubeMap = neck.map ∧ v ∈ cap.tube ∧ cap.chain.count = 1 ∧
          (∀ j : Fin cap.chain.count, cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          ∀ᶠ i in atTop,
            ∃ Ki : CanonicalWitness (S (phi i)) (2 * (alpha / 4)) (max A 2)
                (max (sourceCurvatureBound 3 C0)
                  (max (4 * C0) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C0))))
                (x (phi i)) (t (phi i)),
              Ki.domain.carrier =
                (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' K.domain.carrier ∧
              ∃ capi depthi, Ki.alternative = CanonicalAlternative.cap capi depthi ∧
                capi.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.tube ∧
                capi.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.core.carrier ∧
                capi.tubeMap = cap.tubeMap.trans
                  (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
                ∃ ni : StrongNeck (S (phi i)) alpha ((W (phi i)).embedding (F.map i v)) (t (phi i)),
                  ni.map = neck.map.trans
                    (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
                  ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
                    B.tolerance = 2 * (alpha / 4) ∧ B.witness.domain.carrier = Ki.domain.carrier ∧
                    B.witness.radius = Ki.radius ∧
                    ∃ capB depthB, B.witness.alternative = CanonicalAlternative.cap capB depthB ∧ HEq capB capi := by
  obtain ⟨eps, A, C0, C, heps, hepsTol, hC, K, cap, v, neck, hKcap, hmap, hv,
    hcount, hchain, hsource⟩ := exists_buffered_image_with_cap_neck_charts_of_windowed_models_of_noncompact_positive_limit
      hS W hdelta hreg L hL hnoncompact hsec hphi F hcmp hscalar ha hasmall H
  refine ⟨eps, A, C0, C, heps, hepsTol, hC, K, cap, v, neck, hKcap, hmap, hv,
    hcount, hchain, hsource.mono ?_⟩
  intro i hi
  obtain ⟨Ki, hKi, capi, depthi, hKiAlt, htubei, hcorei, hmapi, ni, hni,
    B, hBeps, hBU, hBr, hBcap, _⟩ := hi
  exact ⟨Ki, hKi, capi, depthi, hKiAlt, htubei, hcorei, hmapi, ni, hni,
    B, hBeps, hBU, hBr, hBcap⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
