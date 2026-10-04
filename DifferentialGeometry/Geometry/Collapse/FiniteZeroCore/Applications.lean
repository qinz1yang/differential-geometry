import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.SoulNormalFlowMap
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CurvatureScale
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.PointedLimit
import DifferentialGeometry.Geometry.Metric.Pullback.TransportedCarrier
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectionalCarrier
import DifferentialGeometry.Geometry.Thurston.Atlas

/-!
# Consumers of the finite zero-core kernels (LFR45–LFR47, LFR49, LFR53)

* LFR45: in dimension three the soul has dimension at most two
  (`exists_soul_strict_outward_tube_of_finrank_three`).
* LFR46: the actual normal-flow map is calibrated inside its seam, `d_S(e z) = |z|` for `|z| ≤ ℓ`
  (`exists_soul_normalFlow_calibrated`).
* LFR47 → LFR50: on a compact carrier transported along a `C^r` diffeomorphism (`r ≥ 3`), the
  unchanged finite metric with `sec ≥ 0` still yields LFR50's auxiliary smooth metric with
  `sec ≥ 0` (`TransportedCarrier.exists_smooth_sectional_nonneg`).
* LFR49 → LC05: supplied bounds `sec ≥ -ε_i` on `L_i`-balls, `L_i → ∞`, `ε_i → 0`, put in LC57's
  form by the curvature scale, feed the central producer at scale one
  (`exists_pointed_limit_of_vanishing_ball_lower_bounds`).
* LFR53 (reduction only): the compact finite classification is the smooth classification U1
  applied to LFR50's smooth metric on the SAME carrier. U1 is not in this tree (it is proved in
  the chapter 5–7 checkout); the `example` below shows the composition against a U1-shaped
  binder. The inherited admission `GC.Geometry.closed_nonnegative_sectional_classification` is not
  used.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

section Soul

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **LFR45, three-dimensional form.** On a complete connected noncompact three-manifold with
`sec ≥ 0` the soul has dimension at most two and strict outward directions off `S`. -/
theorem exists_soul_strict_outward_tube_of_finrank_three [NoncompactSpace M]
    (hdim3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧ relBoundary I S = ∅ ∧
      maxSliceDim I S ≤ 2 ∧
      ∀ q : M, q ∉ S → ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
        ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q v u < 0 := by
  obtain ⟨S, hconv, hB, hSne, hScomp, -, hdim, hstrict, -⟩ :=
    exists_soul_strict_outward_tube g hEnorm hsec p
  exact ⟨S, hSne, hScomp, hconv, hB, by omega, hstrict⟩

/-- **LFR46, calibration of the actual map.** The normal-flow map fixes the soul and is radially
calibrated inside its seam: `d_S(e z) = |z|` for `|z| ≤ ℓ`. -/
theorem exists_soul_normalFlow_calibrated [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
      let _ := embeddedSliceChartedSpace hS
      let a := normalBundlePrebundle g hEnorm hconv hB
      let _ := a.totalSpaceTopology
      let _ := a.toFiberBundle
      let _ := a.toVectorBundle
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S) ≃ₘ⟮
            (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
              𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
        (∀ s : S, e ⟨s, 0⟩ = s.1) ∧
        ∀ z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S),
          Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) ≤ ℓ →
            infDist (e z) S = Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) := by
  obtain ⟨S, hconv, hB, -, -, -, -, -, V, ϕ, ℓ, hℓ, A₂, -, -, -, -, -, -, -, htube, e, -,
    hezero, hinner, -⟩ := exists_soul_normalFlow_map_data g hEnorm hsec p
  refine ⟨S, hconv, hB, ℓ, hℓ, e, hezero, fun z hz => ?_⟩
  obtain ⟨ε, hℓε, Φ, hsource, -, hΦ, hradius⟩ := htube
  have hzs : z ∈ Φ.source := by
    rw [hsource]
    exact lt_of_le_of_lt hz hℓε
  rw [hinner z hz, ← hΦ]
  exact (hradius z hzs).symm

end Soul

section Scale

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LFR49 → LC05.** Complete manifolds with `sec ≥ -ε_i` on `B(p_i, L_i)`, `L_i → ∞`,
`0 ≤ ε_i → 0`: after the curvature-scale normalization (LFR49, first step) the central producer
LC05 applies at scale one, giving a pointed limit with nonnegative four-point comparison. -/
theorem exists_pointed_limit_of_vanishing_ball_lower_bounds
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {L ε : ℕ → ℝ} (hL : Tendsto L atTop atTop) (hε0 : ∀ i, 0 ≤ ε i)
    (hε : Tendsto ε atTop (𝓝 0))
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-ε i)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        @PointedGHConverges (fun i => X (φ i))
          (fun i => (mX (φ i)).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)) Y m
          (fun i => p (φ i)) q ∧
        fourPointComparison 0 (univ : Set Y) := by
  obtain ⟨Hs, hHs, -, hball⟩ := exists_curvature_scale_of_ball_lower_bounds g p hL hε0 hε hsec
  obtain ⟨Y, m, q, φ, hφ, hY, hYp, hconv, -, hfour, -⟩ :=
    exists_rescaled_pointed_limit_of_sectional_buffer (ρ := fun _ => 1) (L := Hs) g hmetric p
      (fun _ => one_pos) hHs (fun i y hy => by
        simp only [mul_one] at hy ⊢
        exact hball i y hy)
  exact ⟨Y, m, q, φ, hφ, hY, hYp, hconv, hfour⟩

end Scale

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ E HX} [IX.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [CompactSpace N] [ConnectedSpace N]

/-- **LFR47 → LFR50.** A compact connected three-manifold `N` with a `C^n` metric (`n ≥ 2`) of
nonnegative sectional curvature, and a `C^r` diffeomorphism (`r ≥ 3`) from a smooth `X`: on the
carrier transported along it, the unchanged metric (order two) still has `sec ≥ 0`, so LFR50
gives a smooth metric with `sec ≥ 0` on the new carrier. -/
theorem TransportedCarrier.exists_smooth_sectional_nonneg (hdim : Module.finrank ℝ E = 3)
    {r : ℕ∞} (F : X ≃ₘ^r⟮IX, I⟯ N) (hr : 3 ≤ r) {n : WithTop ℕ∞} (hn : 2 ≤ n)
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hsec : ∀ (x : N) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric IX (TransportedCarrier F.toHomeomorph),
      Riemannian.SectionalBoundedBelow h 0 := by
  have hmr : (2 : WithTop ℕ∞) + 1 ≤ (r : WithTop ℕ∞) := by
    have h3 : ((3 : ℕ∞) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := WithTop.coe_le_coe.mpr hr
    exact le_of_eq_of_le (by norm_num) h3
  exact MetricSmoothing.exists_smooth_sectional_nonneg_of_finite_metric_of_boundarylessManifold
    hdim le_rfl (TransportedCarrier.metric F g hn hmr)
    (TransportedCarrier.metric_sectionalCurvature_nonneg F g hn hmr hr le_rfl hn hsec)

end Carrier

section Classification

universe v

/-- **LFR53, reduction to the smooth classification (documentation, not an API theorem).** For a
compact connected closed oriented carrier with a `C²` metric of `sec ≥ 0`, LFR50 (B7) produces a
smooth `sec ≥ 0` metric on the SAME carrier, which is exactly the input of the smooth
classification U1 (`closed_nonnegative_sectional_classification_unconditional` of the chapter
5–7 checkout, not in this tree). The binder `hU1` has U1's statement. -/
example (hU1 : ∀ (W : GC.Endpoint.CompactCarrier.{v}) [ConnectedSpace W.Carrier]
      (h : SmoothRiemannianMetric W.model W.Carrier), W.model.boundary W.Carrier = ∅ →
      Riemannian.SectionalBoundedBelow h 0 →
      ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
        G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)
    (W : GC.Endpoint.CompactCarrier.{v}) [ConnectedSpace W.Carrier]
    (hclosed : W.model.boundary W.Carrier = ∅)
    (g : Bundle.ContMDiffRiemannianMetric W.model (2 : WithTop ℕ∞) (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨h, hh⟩ :=
    W.exists_smooth_sectional_nonneg_of_metric2_of_boundary_eq_empty hclosed g hsec
  exact hU1 W h hclosed hh

end Classification

end DifferentialGeometry.Geometry
