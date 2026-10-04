import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.FiniteMetricCompactness
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.OrientedChart
import DifferentialGeometry.Topology.Manifold.OrientedChartTransition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.DeterminantSign
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.OrientedContDiffAtlas
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LimitChartGlue
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CarrierChart
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CarrierChartOrientation

/-!
# I-LIM-OR: the oriented finite-regularity limit chart data (LFR14 steps 1–3)

Blueprint 207A, LFR14 (Theorem 13.97, A:25869–26084), steps 1–3 for oriented sources, in the
shape the oriented assembly (T1) consumes (frozen interface I-LIM-OR of
`build-logs/scratch/D-LFR14/Interfaces.lean`).

The proof binds the ported base theorem `exists_pointed_finite_metric_subsequence_of_curvature_bounds`
(`Limit/FiniteMetricCompactness.lean`) to the aligned sources, with the oriented normal frames
`Q i := orientedEuclideanNormalRotation (g i) (o i)`, and replays the orientation steps of the
team's `OrientedCurvatureAtlas.lean` without its curvature-sign hypotheses (sheet-L-BIND, M1):
* every source chart `Φ j i` is oriented against the standard orientation
  (`isOrientedChart_of_eqOn_pointed`, a wrapper of `isOrientedChart_of_eqOn_intrinsicFramedExp`
  stated in the theorem's own instance block);
* every limit transition `ψ j ≫ (ψ d)⁻¹` has positive Jacobian, as a `C¹` limit of transitions of
  oriented charts with nonzero Jacobian (`det_fderiv_trans_symm_pos_of_orientedCharts`);
* the smooth carrier is then oriented (`SmoothCarrier.exists_of_contDiff_atlas_oriented`), and every
  chart parametrization `σ a` is oriented (`orientation_map_mfderiv_carrierChartParam`).
The remaining clauses are those of I-LIM, proved as in `LimitChartData.lean`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

open DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.NormalCoordinates in
/-- The oriented normal charts of one pointed source, stated in the instance block of the
finite-metric compactness theorem (so that its conclusion applies to the theorem's charts by
unification): a chart that agrees on its source ball with the framed exponential map composed with
the oriented normal rotation is oriented against the standard orientation. -/
theorem isOrientedChart_of_eqOn_pointed {n : ℕ} (hn : 2 ≤ n)
    (P : PointedRiemannianManifold.{u} 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (hcomplete : MetricComplete P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) P.M := P.charted
    letI : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ P.M := P.smooth
    letI : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 P.M :=
      IsManifold.of_le (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      P.riemBundle (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    letI : (x : P.M) → InnerProductSpace Real
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      P.riemInner (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (fun x : P.M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      P.riemBundle_cont (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    letI : EMetricSpace P.M := P.emetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) P hcomplete
    letI : ConnectedSpace P.M := hconn
    letI : MetricSpace P.M :=
      HopfRinow.riemMetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (M := P.M)
    ∀ (hEnorm : ∀ (x : P.M) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (P.metric.inner x v v)))
      (o : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) P.M n) (z : P.M)
      (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n)) P.M ∞) {ρ : ℝ}, 0 < ρ → Φ.source = ball 0 ρ →
      EqOn Φ (intrinsicFramedExp P.metric hEnorm z ∘
        orientedEuclideanNormalRotation (show 0 < n by omega) P.metric o z) (ball 0 ρ) →
      IsOrientedChart o (stdEuclideanOrientation n) Φ := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by simpa using (show n ≠ 0 by omega)⟩
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) P.M := P.charted
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ P.M := P.smooth
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    P.riemBundle (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    P.riemInner (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
  let _ : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : P.M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    P.riemBundle_cont (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
  let _ : EMetricSpace P.M := P.emetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let _ : MetricSpace P.M :=
    HopfRinow.riemMetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (M := P.M)
  intro hEnorm o z Φ ρ hρ hsrc hΦ
  exact isOrientedChart_of_eqOn_intrinsicFramedExp P.metric hEnorm o
    (stdEuclideanOrientation n) (firstCoordinateReflection (show 0 < n by omega))
    (det_firstCoordinateReflection_neg (show 0 < n by omega)) z Φ hρ hsrc hΦ

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates in
/-- A `C¹` limit of chart transitions of oriented charts has positive Jacobian at every point of
its source where it is a limit (the transitions of oriented charts have positive Jacobian, and the
limit Jacobian is nonzero because the limit is a local diffeomorphism). -/
theorem det_fderiv_trans_symm_pos_of_orientedCharts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Type*} [TopologicalSpace Y] {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace E (M i)] [∀ i, IsManifold 𝓘(ℝ, E) ∞ (M i)] {n : ℕ}
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, E) (M i) n) (oE : Orientation ℝ E (Fin n))
    (Φ Ψ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (M i) ∞)
    (hΦ : ∀ i, IsOrientedChart (o i) oE (Φ i)) (hΨ : ∀ i, IsOrientedChart (o i) oE (Ψ i))
    {e e' : OpenPartialHomeomorph E Y}
    (he : ContDiffOn ℝ 1 (e.trans e'.symm) (e.trans e'.symm).source)
    (he' : ContDiffOn ℝ 1 (e'.trans e.symm) (e'.trans e.symm).source)
    {u : E} (hu : u ∈ (e.trans e'.symm).source)
    (hconv : MapCPConvergenceOn {u} 1 (fun i x => (Ψ i).symm (Φ i x)) (e.trans e'.symm))
    (hev : ∀ᶠ i in atTop, u ∈ ((Φ i).trans (Ψ i).symm).source) :
    0 < (fderiv ℝ (e.trans e'.symm) u).det := by
  have hTd : DifferentiableAt ℝ (e.trans e'.symm) u :=
    (he.contDiffAt ((e.trans e'.symm).open_source.mem_nhds hu)).differentiableAt one_ne_zero
  have hRu := DifferentialGeometry.Analysis.trans_symm_apply_mem_source hu
  have hRd : DifferentiableAt ℝ (e'.trans e.symm) ((e.trans e'.symm) u) :=
    (he'.contDiffAt ((e'.trans e.symm).open_source.mem_nhds hRu)).differentiableAt one_ne_zero
  have hne := DifferentialGeometry.Analysis.det_fderiv_trans_symm_ne_zero hu hTd hRd
  refine DifferentialGeometry.Analysis.det_fderiv_pos_of_mapCPConvergenceOn_at hconv
    (mem_singleton u) hTd hne ?_
  filter_upwards [hev] with i hui
  exact ⟨differentiableAt_symm_comp hui,
    det_fderiv_symm_comp_pos (o i) oE (Φ := Φ i) (Ψ := Ψ i) (hΦ i) (hΨ i) hui⟩

/-- **I-LIM-OR.** I-LIM for oriented sources (frames `Q` replaced by the orientations `o`); in
addition an orientation `oN` of the carrier for which every `σ a` and every `d a i` is oriented
against one fixed orientation `oE` of the model.

I-LIM text follows: The limit of LFR14 steps 1–3 (D: `exists_pointed_smooth_carrier_limit_of_curvature_bounds`,
or its oriented form with frames `Q`), on its smooth carrier `N`: the countable limit chart
parametrizations `σ a` (order `K`), the actual smooth normal charts `d a i` of the sources, the
convex buffers `D a`, the `C^K` transition convergence, the `C^{K-1}` coefficient limits `b a`
(= `G` in `σ a` coordinates), and the pointed ball approximations `F i : X (φ i) → N`
with the chart capture. -/
theorem exists_finite_limit_chart_data_oriented
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, DifferentialGeometry.ManifoldOrientation
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) n)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (σ : Option (ℕ × ℕ) → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) N K)
        (d : Option (ℕ × ℕ) → ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) (X (φ i)) ∞)
        (D : Option (ℕ × ℕ) → Set (EuclideanSpace ℝ (Fin n)))
        (b : Option (ℕ × ℕ) → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i)),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
        (∀ x : N, ∃ a, x ∈ (σ a).target) ∧
        0 ∈ (σ none).source ∧ σ none 0 = q ∧ (∀ i, d none i 0 = p (φ i)) ∧
        (∀ a, IsOpen (D a) ∧ Convex ℝ (D a) ∧ (σ a).source ⊆ D a ∧ ∀ i, D a ⊆ (d a i).source) ∧
        (∀ a c (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ ((σ a).trans (σ c).symm).source →
          MapCPConvergenceOn L K (fun i x => (d c i).symm (d a i x)) ((σ a).trans (σ c).symm) ∧
          ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d c i).symm).source) ∧
        (∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (D a) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ D a →
            MapCPConvergenceOn S (K - 1)
              (fun i => pullbackMetricCoefficients (g (φ i)) (d a i)) (b a)) ∧
        (∀ a, ∀ u ∈ (σ a).source, ∀ v w : EuclideanSpace ℝ (Fin n),
          G.inner (σ a u)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (σ a) u v)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (σ a) u w) =
          b a u v w) ∧
        (∀ a (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L → L ⊆ (σ a).source →
          (∀ᶠ i in atTop, MapsTo (d a i) L (closedBall (p (φ i)) (R i))) ∧
          TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (d a i u)) (σ a) atTop L) ∧
        ∃ (oE : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
          (oN : DifferentialGeometry.ManifoldOrientation
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N n),
          (∀ a u (hu : u ∈ (σ a).source), Orientation.map (Fin n)
            (((σ a).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (K : ℕ∞ω) hu).mfderivToContinuousLinearEquiv
              (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK)).toLinearEquiv oE =
            oN.orientation (σ a u)) ∧
          (∀ a i u (hu : u ∈ (d a i).source), Orientation.map (Fin n)
            (((d a i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ hu).mfderivToContinuousLinearEquiv
              (by simp)).toLinearEquiv oE =
            (o (φ i)).orientation (d a i u)) := by
  classical
  obtain ⟨rad, C, hrad, hC, hmain⟩ :=
    exists_pointed_finite_metric_subsequence_of_curvature_bounds.{u} n K hn hK hr hv A hA
  let P : ℕ → PointedRiemannianManifold.{u} 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) := fun i =>
    { M := X i, basepoint := p i, metric := g i }
  have hcomplete : ∀ i, MetricComplete (P i) := fun i =>
    metricComplete_aligned (g i) (hmetric i) (p i)
  have hconn : ∀ i, letI : TopologicalSpace (P i).M := (P i).topology; ConnectedSpace (P i).M :=
    fun i => inferInstanceAs (ConnectedSpace (X i))
  obtain ⟨φ, Y, m, hφ, hYp, hYc, hYpc, hYconn, q, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, qq, z,
    Φ, τ, gg, ψ, hcover, b, hq, hΦ0, hτ, hU, h5, h6, h7, h8, h9, hM, G, ⟨hGb, hRiem⟩, -⟩ :=
    hmain P hcomplete hconn
      (fun i => Riemannian.NormalCoordinates.orientedEuclideanNormalRotation (M := X i)
        (show 0 < n by omega) (g i) (o i)) hvol hcurv
  -- every source chart is oriented against the standard orientation
  have horient : ∀ (j : Option (ℕ × ℕ)) (i : ℕ),
      Riemannian.NormalCoordinates.IsOrientedChart (o (φ (ν i)))
        (Riemannian.NormalCoordinates.stdEuclideanOrientation n) (Φ j i) := by
    intro j i
    have hchart := (h5 j).2.2.2.2.1 i
    exact isOrientedChart_of_eqOn_pointed hn (P (φ (ν i))) (hcomplete (φ (ν i)))
      (hconn (φ (ν i))) _
      (o (φ (ν i))) (z j i) (Φ j i) (by linarith [hrad (j.elim 0 Prod.fst)]) hchart.1 hchart.2.1
  -- every limit transition has positive Jacobian
  have hposψ : ∀ j d, ∀ u ∈ ((ψ j).trans (ψ d).symm).source,
      0 < (fderiv ℝ ((ψ j).trans (ψ d).symm) u).det := by
    intro j d u hu
    obtain ⟨hconvK, s, hs0, hs1, hev⟩ :=
      (h7 j d).2 {u} isCompact_singleton (singleton_subset_iff.mpr hu)
    exact det_fderiv_trans_symm_pos_of_orientedCharts (M := fun i => X (φ (ν (τ i))))
      (fun i => o (φ (ν (τ i)))) (Riemannian.NormalCoordinates.stdEuclideanOrientation n)
      (fun i => Φ j (τ i)) (fun i => Φ d (τ i)) (fun i => horient j (τ i))
      (fun i => horient d (τ i)) ((h7 j d).1.of_le (by exact_mod_cast hK))
      ((h7 d j).1.of_le (by exact_mod_cast hK)) hu (hconvK.mono_order hK)
      (hev.mono fun i hi => hi.1 (mem_singleton u))
  -- the oriented smooth carrier
  obtain ⟨𝒜, κ, hchart, -, hreg, -, hdet, -, hpos, ⟨O, hO⟩, ⟨f, hf, -⟩, -, -, G', hG', hblock⟩ :=
    SmoothCarrier.exists_of_contDiff_atlas_oriented hK ψ hcover (fun j d => (h7 j d).1) hM
      finrank_euclideanSpace_fin hposψ (Riemannian.NormalCoordinates.stdEuclideanOrientation n)
      G hRiem
  have hRiemN := hblock.2.2.2.2.2.2
  have : ProperSpace Y := hYp
  have : ConnectedSpace Y := hYconn
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  -- the per-chart clauses of the theorem
  have hψsrc : ∀ j, (ψ j).source = ball 0 (rad (j.elim 0 Prod.fst) / 16) := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h5 j
    exact h
  have hψ0 : ∀ j, ψ j 0 = qq j := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h5 j
    exact h
  have hΦsrc : ∀ j i, (Φ j i).source = ball 0 (2 * rad (j.elim 0 Prod.fst)) := fun j i =>
    ((h5 j).2.2.2.2.1 i).1
  -- the ball approximations, read with the given metric and post-composed with `ofBase`
  have hFex := fun i => exists_pointedBallApprox_of_metricSpace_eq
    (riemMetricSpace_aligned_eq (g (φ (ν (τ i)))) (hmetric (φ (ν (τ i))))) (F (τ i))
  choose F₁ hF₁ using hFex
  let σ : Option (ℕ × ℕ) → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) (SmoothCarrier 𝒜) K :=
    fun a => carrierChartParam 𝒜 (ψ a) a (κ a) (hchart a) (hreg a).1 (hreg a).2
  refine ⟨fun i => φ (ν (τ i)), hφ.comp (hν.comp hτ), SmoothCarrier 𝒜, inferInstance,
    inferInstance, inferInstance, G', SmoothCarrier.ofBase 𝒜 q, σ, fun a i => Φ a (τ i),
    fun a => ball 0 (rad (a.elim 0 Prod.fst)), b, fun i => R (τ i), fun i => ε (τ i),
    fun i => (F₁ i).mapTargetIsometry (smoothCarrierOfBaseIsometryEquiv 𝒜),
    inferInstance, inferInstanceAs (ConnectedSpace Y), hRiemN, ?_,
    hR.comp hτ.tendsto_atTop, hε.comp hτ.tendsto_atTop, fun x => hcover x, ?_, ?_,
    fun i => hΦ0 (τ i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pointed Gromov–Hausdorff convergence along `ν ∘ τ`, read with the given metrics
    exact pointedGHConverges_comp_of_metricSpace_eq
      (fun i => riemMetricSpace_aligned_eq (g (φ i)) (hmetric (φ i))) (hν.comp hτ) hGH
  · change (0 : EuclideanSpace ℝ (Fin n)) ∈ (ψ none).source
    rw [hψsrc none]
    exact mem_ball_self (div_pos (hrad _) (by norm_num))
  · change SmoothCarrier.ofBase 𝒜 (ψ none 0) = SmoothCarrier.ofBase 𝒜 q
    rw [hψ0 none, hq]
  · intro a
    refine ⟨isOpen_ball, convex_ball _ _, ?_, fun i => ?_⟩
    · change (ψ a).source ⊆ _
      rw [hψsrc a]
      exact ball_subset_ball (by linarith [hrad (a.elim 0 Prod.fst)])
    · change _ ⊆ (Φ a (τ i)).source
      rw [hΦsrc a (τ i)]
      exact ball_subset_ball (by linarith [hrad (a.elim 0 Prod.fst)])
  · intro a c L hL hLsub
    have hLsub' : L ⊆ ((ψ a).trans (ψ c).symm).source := by
      rw [← (carrierChartParam_trans_symm 𝒜 (ψ a) (ψ c) a c (κ a) (κ c) (hchart a) (hchart c)
        (hreg a).1 (hreg a).2 (hreg c).1 (hreg c).2).1]
      exact hLsub
    obtain ⟨hconv, s, hs0, hs1, hev⟩ := (h7 a c).2 L hL hLsub'
    exact ⟨hconv, hev.mono fun i hi => hi.1⟩
  · intro a
    exact ⟨(h6 a).1, fun S hS hSD => (h6 a).2.2.2 S hS hSD⟩
  · intro a u hu v w
    let _ := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
    let _ := hM
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 Y :=
      IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
    have hT : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (SmoothCarrier.toBase 𝒜) := by
      rw [← hf]
      exact f.mdifferentiable hK0
    exact carrierChartParam_inner 𝒜 hK (ψ a) a (κ a) (hchart a) (hreg a).1 (hreg a).2
      (by exact ⟨a, rfl⟩) hT G.inner G'.inner (b a) (fun x hx v w => hGb a x hx v w) hG' hu v w
  · intro a L hL hLsrc
    obtain ⟨-, -, -, -, -, -, -, -, -, hcap, hunif, -, hsrc, -, -, -, -, hψg⟩ := h5 a
    have hLball : ∀ u ∈ L,
        u ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (rad (a.elim 0 Prod.fst) / 16) := by
      intro u hu
      rw [← hsrc]
      exact hLsrc hu
    have hLcb : ∀ u ∈ L,
        u ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (rad (a.elim 0 Prod.fst) / 8) :=
      fun u hu => closedBall_subset_closedBall (by linarith [hrad (a.elim 0 Prod.fst)])
        (ball_subset_closedBall (hLball u hu))
    refine ⟨?_, ?_⟩
    · filter_upwards [hcap] with i hi
      intro u hu
      exact (closedBall_eq_of_metricSpace_eq
        (riemMetricSpace_aligned_eq (g (φ (ν (τ i)))) (hmetric (φ (ν (τ i))))) _ _).subset
          (hi ⟨u, hLcb u hu⟩)
    · have key := hunif.comp (fun u : L => (⟨u, hLcb u u.2⟩ :
          closedBall (0 : EuclideanSpace ℝ (Fin n)) (rad (a.elim 0 Prod.fst) / 8)))
      have e2 : ((σ a) ∘ Subtype.val : L → SmoothCarrier 𝒜) =
          fun u : L => smoothCarrierOfBaseIsometryEquiv 𝒜 (gg a ⟨u, hLcb u u.2⟩) :=
        funext fun u => congrArg (smoothCarrierOfBaseIsometryEquiv 𝒜) (hψg ⟨u, hLball u u.2⟩)
      have key₁ : TendstoUniformly
          (fun i (x : L) => (F₁ i).extendToWholeSpace (Φ a (τ i) (x : EuclideanSpace ℝ (Fin n))))
          (fun x : L => gg a ⟨x, hLcb x x.2⟩) atTop :=
        tendstoUniformly_comp_congr _ (fun i => (F₁ i).extendToWholeSpace)
          (fun i => (hF₁ i).symm) (fun i (x : L) => Φ a (τ i) (x : EuclideanSpace ℝ (Fin n))) key
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, e2]
      exact tendstoUniformly_comp_congr
        (fun i y => smoothCarrierOfBaseIsometryEquiv 𝒜 ((F₁ i).extendToWholeSpace y))
        (fun i => ((F₁ i).mapTargetIsometry (smoothCarrierOfBaseIsometryEquiv 𝒜)).extendToWholeSpace)
        (fun i => funext fun y => (extendToWholeSpace_mapTargetIsometry _ _ y).symm)
        (fun i (x : L) => Φ a (τ i) (x : EuclideanSpace ℝ (Fin n)))
        ((smoothCarrierOfBaseIsometryEquiv 𝒜).isometry.uniformContinuous.comp_tendstoUniformly
          key₁)
  · -- the orientations: `σ a` against the carrier orientation, `d a i` against `o (φ i)`
    exact ⟨Riemannian.NormalCoordinates.stdEuclideanOrientation n, O,
      fun a u hu => orientation_map_mfderiv_carrierChartParam 𝒜 hK (ψ a) a (κ a) (hchart a)
        (hreg a).1 (hreg a).2 (hdet a) hpos O
        (Riemannian.NormalCoordinates.stdEuclideanOrientation n) hO hu,
      fun a i u hu => horient a (τ i) u hu⟩

end DifferentialGeometry.CheegerGromovCompactness
