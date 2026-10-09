import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderArmSides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckLimit

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
  [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem exists_frequently_original_arm_opposite_neck_coordinates
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩ (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    (arms : ∀ i, Fin 2 → MinimizingArm ((S (phi i)).base.metric (t (phi i))) (x (phi i)))
    (hlength : ∀ j, Tendsto (fun i => Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
      (arms i j).length) atTop atTop)
    (e : Diffeomorph IC I3 Cylinder L.M ∞) (p : Sphere 2) (hmark : e (p, 0) = L.basepoint)
    (hmetric : Diffeomorph.pullbackMetricCross (L.S.base.metric 0) e = cylinderReferenceMetric 0)
    (hnecks : ∀ beta : ℝ, 0 < beta → beta < 1 / 11 →
      ∃ nk : StrongNeck L.S beta L.basepoint 0, nk.map = e.toPartialDiffeomorph ∧ nk.center = p)
    (rays : Fin 2 × ℝ≥0 → L.M)
    (hradial : ∀ j r, metricDistance (L.S.base.metric 0) L.basepoint (rays (j, r)) = r)
    (hcluster : MapClusterPt rays atTop (fun i z =>
      (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding).symm
        ((arms i z.1).point ((z.2 : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))))
    {theta : ℝ} (htheta : 0 < theta)
    (hangle : ∀ r : ℝ≥0, 0 < r → theta ≤ comparisonAngle r r
      (metricDistance (L.S.base.metric 0) (rays (0, r)) (rays (1, r))))
    {alpha : ℝ} (halpha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (H : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ᶠ i in atTop,
      ∃ nk : StrongNeck (S (phi i)) (2 * alpha) (x (phi i)) (t (phi i)),
        nk.map = partialDiffeomorphTransMixed e.toPartialDiffeomorph
          (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ∧
        (∀ j : Fin 2, (r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) ∈
          Ioo 0 (arms i j).length) ∧
        (∀ j : Fin 2, ∀ s ∈ Icc 0 ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))),
          (arms i j).point s ∈ nk.map.target) ∧
        (((nk.map.symm ((arms i 0).point ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2 < -H ∧
          H < (nk.map.symm ((arms i 1).point ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2) ∨
        ((nk.map.symm ((arms i 1).point ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2 < -H ∧
          H < (nk.map.symm ((arms i 0).point ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2)) := by
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let Q := fun i => (S (phi i)).scalar (t (phi i)) (x (phi i))
  have hQ (i : ℕ) : 0 < Q i := (W (phi i)).scalar_pos
  obtain ⟨r, hr, hsides⟩ := exists_strict_original_inverse_arm_endpoint_sides L
    (fun i => (S (phi i)).base.metric (t (phi i))) (fun i => x (phi i)) Psi Q hQ
    arms hlength e p hmark hmetric rays hradial hcluster htheta hangle H
  have heps : 0 < neckModelTolerance alpha / 2 := half_pos (neckModelTolerance_pos halpha)
  have hepslt : neckModelTolerance alpha / 2 < neckModelTolerance alpha :=
    half_lt_self (neckModelTolerance_pos halpha)
  have hepssmall : neckModelTolerance alpha / 2 < 1 / 11 :=
    hepslt.trans ((neckModelTolerance_le alpha).trans_lt (by linarith))
  obtain ⟨modelNeck, hmodelMap, _hmodelCenter⟩ := hnecks _ heps hepssmall
  have htransport := modelNeck.eventually_transport_of_windowed_models hS W hdelta hreg L hcomplete
    hphi F hcmp halpha hsmall hepslt
  have hsourceNecks : ∀ᶠ i in atTop,
      ∃ nk : StrongNeck (S (phi i)) (2 * alpha) (x (phi i)) (t (phi i)),
        nk.map = partialDiffeomorphTransMixed e.toPartialDiffeomorph (Psi i) := by
    filter_upwards [htransport] with i hi
    have hbase : (W (phi i)).embedding (F.map i L.basepoint) = x (phi i) := by
      rw [show F.map i L.basepoint = (W (phi i)).model.basepoint from F.basepoint_map i]
      exact (W (phi i)).base_map
    rw [hbase] at hi
    obtain ⟨nk, hn⟩ := hi
    refine ⟨nk, ?_⟩
    rw [hn, hmodelMap]
    rfl
  have hcapture := (WindowedModelWitness.eventually_composed_minimizingArm_prefix_capture
    hS W hdelta (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete
    hphi F hcmp (r : ℝ) r.coe_nonneg).2
  have hfreq : ∃ᶠ i in atTop,
      ((r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 0).length ∧
        (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i 1).length) ∧
      (((e.symm ((Psi i).symm ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i))))).2 < -H ∧
          H < (e.symm ((Psi i).symm ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i))))).2) ∨
        ((e.symm ((Psi i).symm ((arms i 1).point ((r : ℝ) / Real.sqrt (Q i))))).2 < -H ∧
          H < (e.symm ((Psi i).symm ((arms i 0).point ((r : ℝ) / Real.sqrt (Q i))))).2)) := by
    rcases hsides with hsides | hsides
    · exact hsides.mono fun _ hi => ⟨⟨hi.1, hi.2.1⟩, Or.inl hi.2.2⟩
    · exact hsides.mono fun _ hi => ⟨⟨hi.1, hi.2.1⟩, Or.inr hi.2.2⟩
  refine ⟨r, hr, ((hfreq.and_eventually hsourceNecks).and_eventually hcapture).mono ?_⟩
  intro i hi
  obtain ⟨nk, hmap⟩ := hi.1.2
  have hmem (j : Fin 2) : (r : ℝ) / Real.sqrt (Q i) ∈ Ioo 0 (arms i j).length := by
    fin_cases j
    · exact hi.1.1.1.1
    · exact hi.1.1.1.2
  have htarget (j : Fin 2) (s : ℝ) (hs : s ∈ Icc 0 ((r : ℝ) / Real.sqrt (Q i))) :
      (arms i j).point s ∈ nk.map.target := by
    have hc := hi.2.2.2 (arms i j) ((r : ℝ) / Real.sqrt (Q i))
      ⟨(hmem j).1.le, (hmem j).2.le⟩
      (by rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr (hQ i)).ne'])
    have hy := (hc.2.2 s hs).1
    rw [hmap]
    exact ⟨hy, mem_univ _⟩
  have hinv (y : M (phi i)) : nk.map.symm y = e.symm ((Psi i).symm y) := by
    rw [hmap]
    rfl
  refine ⟨nk, hmap, hmem, htarget, ?_⟩
  simpa only [hinv] using hi.1.1.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
