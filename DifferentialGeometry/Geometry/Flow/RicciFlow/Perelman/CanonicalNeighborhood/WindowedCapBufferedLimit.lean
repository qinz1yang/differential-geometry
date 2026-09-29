import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedImageDepth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCapCanonicalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled

section
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

theorem CanonicalWitness.exists_eventually_buffered_image_of_windowed_models_of_cap_collar
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha C1 C2 H : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    {v : L.M} (neck : StrongNeck L.S eps v 0)
    (hcentralTube : neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ cap.tube)
    (hv : v ∈ cap.tube)
    (ha : 0 < alpha) (hasmall : alpha < 1 / 11)
    (heps : eps < neckModelTolerance (alpha / 4))
    (hfar : ∀ y ∈ cap.tube, max 40000 (2 * max H 0) ≤ metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop,
      ∃ Ki : CanonicalWitness (S (phi i)) (2 * (alpha / 4)) (max C1 2)
          (max (sourceCurvatureBound 3 C2)
            (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
          (x (phi i)) (t (phi i)),
        Ki.domain.carrier =
          (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' K.domain.carrier ∧
        ∃ capi depthi, Ki.alternative = CanonicalAlternative.cap capi depthi ∧
          capi.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.tube ∧
          capi.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.core.carrier ∧
          capi.tubeMap = cap.tubeMap.trans
            (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
          ∃ ni : StrongNeck (S (phi i)) alpha
              ((W (phi i)).embedding (F.map i v)) (t (phi i)),
            ni.map = neck.map.trans
              (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
            ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
              B.tolerance = 2 * (alpha / 4) ∧ B.witness.domain.carrier = Ki.domain.carrier ∧
              B.witness.radius = Ki.radius ∧
              ∃ capB depthB, B.witness.alternative = CanonicalAlternative.cap capB depthB ∧ HEq capB capi := by
  let C0 := max (sourceCurvatureBound 3 C2)
    (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2)))
  have hC2 : 1 ≤ C2 := K.one_le_comparison_constant
  have hC0 : 1 ≤ C0 := by
    have hh : 4 * C2 ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  obtain ⟨C, hC, hbuffer⟩ := exists_common_buffer_constant_of_cap_collar.{u} (max C1 2) C0 hC0
  have hqa : 0 < alpha / 4 := by positivity
  have hqsmall : 2 * (alpha / 4) < 1 / 11 := by linarith
  have hfar10000 : ∀ y ∈ cap.tube, 10000 < metricDistance (L.S.base.metric 0) L.basepoint y := by
    intro y hy
    have hh := (le_max_left (40000 : ℝ) (2 * max H 0)).trans (hfar y hy)
    linarith
  have hKi := K.eventually_image_of_windowed_models_of_cap_with_strict_depth
    hS W hdelta hreg L hcomplete hphi F hcmp
    hscalar cap hcap (alpha := alpha / 4) hqa hqsmall heps hfar10000
  have hni := neck.eventually_transport_of_windowed_models hS W hdelta hreg L hcomplete hphi F hcmp
    hqa hqsmall heps
  have hdepth := eventually_image_depth_of_windowed_models hS W hdelta hreg L hcomplete hphi F hcmp
    cap.isCompact_tube (H := H) (fun y hy => (le_max_right _ _).trans (hfar y hy))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hKi, hni, hdepth] with i hKi hni hdepthi
  obtain ⟨Ki, hKiCarrier, capi, depthi, hKiAlt, htubei, hcorei, hmapi⟩ := hKi
  obtain ⟨ns, hns⟩ := hni
  let ni := ns.mono (by linarith : 2 * (alpha / 4) ≤ alpha) hasmall
  let Psi : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ := partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hniMap : ni.map = neck.map.trans Psi := hns
  have hvi : (W (phi i)).embedding (F.map i v) ∈ capi.tube := by
    rw [htubei]
    exact mem_image_of_mem Psi hv
  have hcentral : ni.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ Psi '' cap.tube := by
    rw [hniMap]
    change (Psi ∘ neck.map) '' (univ ×ˢ ({0} : Set ℝ)) ⊆ _
    rw [image_comp]
    exact image_mono hcentralTube
  obtain ⟨B, hBeps, hBdomain, hBradius, capB, depthB, hBcap, hcapB⟩ :=
    hbuffer (M (phi i)) (D (phi i)) (S (phi i)) (2 * (alpha / 4)) alpha H
      (x (phi i)) ((W (phi i)).embedding (F.map i v)) (t (phi i)) Ki
      (by linarith) capi ⟨depthi, hKiAlt⟩ ni hvi (fun y hy => hdepthi y (hcentral hy))
  exact ⟨Ki, hKiCarrier, capi, depthi, hKiAlt, htubei, hcorei, hmapi, ni, hniMap,
    B, hBeps, hBdomain, hBradius, capB, depthB, hBcap, hcapB⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
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

private theorem cap_tube_map_eq_of_heq
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps eps' : ℝ}
    {x : M} {t : ℝ} {U V : Set M} (heps : eps = eps') (hUV : U = V)
    {a : LocalCap S eps x t U} {b : LocalCap S eps' x t V} (h : HEq a b) :
    a.tubeMap = b.tubeMap := by
  cases heps
  cases hUV
  rw [eq_of_heq h]

theorem CanonicalWitness.exists_eventually_buffered_image_of_windowed_models_of_cap_with_neck_chart
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha C1 C2 H : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    {v : L.M} (neck : StrongNeck L.S eps v 0) (hmap : ∀ z, cap.tubeMap z = neck.map z)
    (ha : 0 < alpha) (hasmall : alpha < 1 / 11)
    (heps : eps < neckModelTolerance (alpha / 4))
    (hfar : ∀ y ∈ cap.tube, max 40000 (2 * max H 0) ≤ metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop,
      ∃ Ki : CanonicalWitness (S (phi i)) (2 * (alpha / 4)) (max C1 2)
          (max (sourceCurvatureBound 3 C2)
            (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
          (x (phi i)) (t (phi i)),
        Ki.domain.carrier =
          (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' K.domain.carrier ∧
        ∃ capi depthi, Ki.alternative = CanonicalAlternative.cap capi depthi ∧
          capi.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.tube ∧
          capi.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.core.carrier ∧
          capi.tubeMap = cap.tubeMap.trans
            (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
          ∃ ni : StrongNeck (S (phi i)) alpha
              ((W (phi i)).embedding (F.map i v)) (t (phi i)),
            ni.map = neck.map.trans
              (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
            ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
              B.tolerance = 2 * (alpha / 4) ∧ B.witness.domain.carrier = Ki.domain.carrier ∧
              B.witness.radius = Ki.radius ∧
              (∃ capB depthB, B.witness.alternative = CanonicalAlternative.cap capB depthB ∧ HEq capB capi) ∧
              B.witness.capTubeHasNeckChart alpha := by
  have hv : v ∈ cap.tube := by
    rw [← cap.tube_eq]
    exact ⟨(neck.center, 0), ⟨mem_univ _, by norm_num⟩,
      (hmap (neck.center, 0)).trans neck.center_eq⟩
  obtain ⟨C, hC, hevent⟩ := K.exists_eventually_buffered_image_of_windowed_models_of_cap_collar
    hS W hdelta hreg L hcomplete hphi F hcmp hscalar cap hcap neck
    (by
      rw [← cap.tube_eq]
      rintro y ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz.1, ?_⟩, hmap z⟩
      have hz0 : z.2 = 0 := hz.2
      rw [hz0]
      norm_num)
    hv ha hasmall heps hfar
  refine ⟨C, hC, hevent.mono ?_⟩
  intro i hi
  obtain ⟨Ki, hKi, capi, depthi, hKiAlt, htubei, hcorei, hmapi, ni, hni, B,
    hBeps, hBU, hBr, capB, depthB, hBAlt, hcapB⟩ := hi
  have hvalues : ∀ z, capi.tubeMap z = ni.map z := by
    intro z
    rw [hmapi, hni]
    change (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
      (W (phi i)).embedding) (cap.tubeMap z) =
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
          (W (phi i)).embedding) (neck.map z)
    rw [hmap z]
  have hcapvalues : ∀ z, capB.tubeMap z = ni.map z := by
    rw [cap_tube_map_eq_of_heq hBeps hBU hcapB]
    exact hvalues
  refine ⟨Ki, hKi, capi, depthi, hKiAlt, htubei, hcorei, hmapi, ni, hni,
    B, hBeps, hBU, hBr, ⟨capB, depthB, hBAlt, hcapB⟩, ?_⟩
  intro cap' depth' hcap'
  rw [hBAlt] at hcap'
  cases hcap'
  exact ⟨_, ni, hcapvalues⟩


theorem CanonicalWitness.exists_eventually_buffered_image_of_windowed_models_of_cap
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha C1 C2 H : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (cap : LocalCap L.S eps L.basepoint 0 K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    {v : L.M} (neck : StrongNeck L.S eps v 0) (hmap : cap.tubeMap = neck.map)
    (hv : v ∈ cap.tube)
    (ha : 0 < alpha) (hasmall : alpha < 1 / 11)
    (heps : eps < neckModelTolerance (alpha / 4))
    (hfar : ∀ y ∈ cap.tube, max 40000 (2 * max H 0) ≤ metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop,
      ∃ Ki : CanonicalWitness (S (phi i)) (2 * (alpha / 4)) (max C1 2)
          (max (sourceCurvatureBound 3 C2)
            (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
          (x (phi i)) (t (phi i)),
        Ki.domain.carrier =
          (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' K.domain.carrier ∧
        ∃ capi depthi, Ki.alternative = CanonicalAlternative.cap capi depthi ∧
          capi.tube = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.tube ∧
          capi.core.carrier = (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) '' cap.core.carrier ∧
          capi.tubeMap = cap.tubeMap.trans
            (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
          ∃ ni : StrongNeck (S (phi i)) alpha
              ((W (phi i)).embedding (F.map i v)) (t (phi i)),
            ni.map = neck.map.trans
              (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
            ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
              B.tolerance = 2 * (alpha / 4) ∧ B.witness.domain.carrier = Ki.domain.carrier ∧
              B.witness.radius = Ki.radius ∧
              ∃ capB depthB, B.witness.alternative = CanonicalAlternative.cap capB depthB ∧ HEq capB capi := by
  apply K.exists_eventually_buffered_image_of_windowed_models_of_cap_collar
    hS W hdelta hreg L hcomplete hphi F hcmp hscalar cap hcap neck
    (by
      rw [← hmap, ← cap.tube_eq]
      apply image_mono
      intro z hz
      have hz0 : z.2 = 0 := hz.2
      exact ⟨hz.1, by rw [hz0]; norm_num⟩)
    hv ha hasmall heps hfar

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
