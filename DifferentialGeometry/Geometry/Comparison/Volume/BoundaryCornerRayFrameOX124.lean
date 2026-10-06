import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartNormalFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonPoleInitialFrame
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Geodesic.ParallelNormal
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Curve.Reparametrization

/-!
# Parallel normal frame along an actual corner ray (O-X124 G1)

For the common original pole family of `exists_boundary_common_pole_initial_frame` (a boundary
pole `p`, its complete chart extension metric `G` and the actual rays in the true interior `U`
for the original metric `k = boundaryInteriorAtlasMetric g`), the chart geodesic through the pole
carries a `G`-parallel orthonormal normal frame starting at any prescribed `G`-orthonormal family
`e` normal to the initial velocity. Through the audited local isometry bridge
`originalCorner_extension_normal_frame` it pulls back to a `k`-parallel orthonormal frame along
the actual phase curve `r ↦ boundaryPhasePoint k σ v r`, normal to its unit velocity, on the
chart part `r ∈ (-a, L - a)` of its life (phase time; the pole is at `r = -a`).

* `boundaryPoleFlowFamily_complete_OX124`: the chart geodesic of a complete `G` is defined and
  smooth for all times, a geodesic everywhere, with initial velocity `v` and constant speed.
* `exists_pole_parallel_normal_frame_of_basis_OX124`: a `G`-parallel orthonormal normal frame along
  a unit-speed `G`-geodesic with prescribed initial value `e` (Codex draft V7 with `e` given).
* `originalCorner_pole_frame_of_basis_OX124`: the revised Codex draft V12 (compile error at its
  line 171 fixed), with the frame aligned to `e` at the pole and given as the pullback of the
  `G`-frame.
* `exists_boundary_corner_ray_pole_frame_OX124`: the binding on the actual common pole data.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.VectorField
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- A complete metric on the model space has its whole geodesic flow domain. -/
theorem geodesicFlowDomain_univ_of_complete_OX124
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (hcomplete : RiemannianMetricComplete G) :
    G.geodesicFlowDomain = univ := by
  let _bundle : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨G.toRiemannianMetric⟩
  let _continuous : IsContinuousRiemannianBundle E (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _metrizable : TopologicalSpace.MetrizableSpace E :=
    Manifold.metrizableSpace (I := 𝓘(ℝ, E)) (M := E)
  let _emetric : PseudoEMetricSpace E :=
    (DifferentialGeometry.inducedEMetricSpace (I := 𝓘(ℝ, E)) G).toPseudoEMetricSpace
  let _uniform : UniformSpace E := ‹PseudoEMetricSpace E›.toUniformSpace
  have hcompleteE : CompleteSpace E := hcomplete.complete
  let _riemannian : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨by intro x z; rfl⟩
  exact Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ_of_isMetricNorm G
    (isMetricNorm_of_riemannianBundle (I := 𝓘(ℝ, E)) G)

/-- The chart geodesic of a complete metric: defined and smooth for all times, a geodesic
everywhere, initial point `y`, initial velocity `v`, constant squared speed. -/
theorem boundaryPoleFlowFamily_complete_OX124
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (hcomplete : RiemannianMetricComplete G)
    (y v : E) :
    (∀ t : ℝ, ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain) ∧
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (boundaryPoleFlowFamily G y v) ∧
    IsGeodesicOn (I := 𝓘(ℝ, E)) G (boundaryPoleFlowFamily G y v) univ ∧
    boundaryPoleFlowFamily G y v 0 = y ∧
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0 1 = v ∧
    ∀ t : ℝ, G.inner (boundaryPoleFlowFamily G y v t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) t 1) =
      G.inner y v v := by
  have hdom := geodesicFlowDomain_univ_of_complete_OX124 G hcomplete
  have hmem (t : ℝ) : ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain := by
    rw [hdom]
    exact mem_univ _
  obtain ⟨_hopen, hF⟩ := boundaryPoleFlowFamily_smooth G y
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (boundaryPoleFlowFamily G y v) := by
    intro t
    have hfq := hF.contMDiffAt (_hopen.mem_nhds (show (v, t) ∈ {q : E × ℝ |
      ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈ G.geodesicFlowDomain} from hmem t))
    exact hfq.comp (f := fun s : ℝ => (v, s)) t
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hgeo : IsGeodesicOn (I := 𝓘(ℝ, E)) G (boundaryPoleFlowFamily G y v) univ := by
    intro t _ht
    have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow G y v
    exact (hi.isGeodesicAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds (hmem t))).hasGeodesicEquationAt
  obtain ⟨hzero, hderiv⟩ := boundaryPoleFlowFamily_initial G y v
  have hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0 1 = v := by
    rw [mfderiv_eq_fderiv, hderiv.hasFDerivAt.fderiv]
    change (1 : ℝ) • v = v
    exact one_smul ℝ v
  refine ⟨hmem, hsmooth, hgeo, hzero, hvel, ?_⟩
  intro t
  have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := 𝓘(ℝ, E)) G (s := univ)
    (t₀ := t) (t₁ := 0) isOpen_univ hgeo (hsmooth.of_le (by norm_num)).contMDiffOn (subset_univ _)
  rw [hconst, hvel, hzero]

end Flow

section Frame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [DecidableEq ι]

/-- A unit-speed geodesic of a metric on the model space carries, on `[0, L]`, a parallel
orthonormal frame normal to its velocity with a prescribed orthonormal normal initial value. -/
theorem exists_pole_parallel_normal_frame_of_basis_OX124
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (τ : ℝ → E) (L : ℝ)
    (hL : 0 < L) (hτ : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) ∞ τ)
    (hgeo : IsGeodesicOn (I := 𝓘(ℝ, E)) G τ (Icc 0 L))
    (e : ι → TangentSpace 𝓘(ℝ, E) (τ 0))
    (heON : ∀ i j, G.inner (τ 0) (e i) (e j) = if i = j then 1 else 0)
    (heperp : ∀ i, G.inner (τ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ 0 1) (e i) = 0) :
    ∃ Z : ι → ∀ t : ℝ, TangentSpace 𝓘(ℝ, E) (τ t),
      (∀ i, Z i 0 = e i) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) L →
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun s => (⟨τ s, Z i s⟩ : TangentBundle 𝓘(ℝ, E) E)) t) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) L → covDerivAlong G τ (Z i) t = 0) ∧
      (∀ t, t ∈ Icc (0 : ℝ) L → ∀ i j,
        G.inner (τ t) (Z i t) (Z j t) = if i = j then 1 else 0) ∧
      (∀ t, t ∈ Icc (0 : ℝ) L → ∀ i,
        G.inner (τ t) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ t 1) (Z i t) = 0) := by
  have hfields : ∀ i : ι,
      ∃ d : ℝ, ∃ V : ∀ t, TangentSpace 𝓘(ℝ, E) (τ t),
        0 < d ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun t => (⟨τ t, V t⟩ : TangentBundle 𝓘(ℝ, E) E))
          (Ioo (-d) (L + d)) ∧
        V 0 = e i ∧
        (∀ t, t ∈ Icc (0 : ℝ) L → covDerivAlong G τ V t = 0) ∧
        (∀ t, t ∈ Icc (0 : ℝ) L →
          G.inner (τ t) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ t 1) (V t) = 0) := by
    intro i
    obtain ⟨d, V, hd, hVsm, hV0, hVpar, _hVunit, hVperp, _hVpt⟩ :=
      exists_smooth_parallel_unit_normal_field G τ hτ hL hgeo (e i)
        (by simpa using heON i i) (heperp i)
    exact ⟨d, V, hd, hVsm, hV0, hVpar, hVperp⟩
  classical
  choose d V hd hVsm hV0 hVpar hVperp using hfields
  have hIcc (i : ι) : Icc (0 : ℝ) L ⊆ Ioo (-d i) (L + d i) := by
    intro t ht
    exact ⟨by linarith [hd i, ht.1], by linarith [hd i, ht.2]⟩
  have hZbundle (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun s => (⟨τ s, V i s⟩ : TangentBundle 𝓘(ℝ, E) E)) t :=
    (hVsm i).contMDiffAt (isOpen_Ioo.mem_nhds (hIcc i ht))
  have hZdiff (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      DifferentiableAt ℝ (chartRepAt (I := 𝓘(ℝ, E)) τ (V i) t) t :=
    chartRepAt_differentiableAt_of_total_contMDiffAt
      ((hZbundle i t ht).of_le (by norm_num))
  have hZON : ∀ t, t ∈ Icc (0 : ℝ) L → ∀ i j,
      G.inner (τ t) (V i t) (V j t) = if i = j then 1 else 0 := by
    intro t ht i j
    have hconst := parallel_transport_preserves_inner_product (I := 𝓘(ℝ, E)) G τ
      (N := 2) le_rfl (hτ.of_le (by norm_num)) (V i) (V j)
      (fun s hs => hZdiff i s hs) (fun s hs => hZdiff j s hs)
      (fun s hs => hVpar i s hs) (fun s hs => hVpar j s hs)
    rw [hV0 i, hV0 j, heON i j] at hconst
    exact hconst t ht
  exact ⟨V, hV0, hZbundle, hVpar, hZON, fun t ht i => hVperp i t ht⟩

end Frame

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} [DecidableEq ι]

private theorem cornerRayFrame_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

/-- Revised Codex draft V12: a chart ray in the original corner interior whose chart image is a
unit-speed geodesic of the extension metric inherits the extension's parallel orthonormal normal
frame started at a prescribed `e`, through the audited local isometry bridge. The frame along
the actual curve is the pullback of the extension frame `Z` by `Φ.symm`, and `Z i 0 = e i`. -/
theorem originalCorner_pole_frame_of_basis_OX124
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y v w)
    (a L : ℝ) (ha : 0 < a) (haL : a < L)
    (ρ : ℝ → DifferentialGeometry.Manifold.intrinsicInterior I ∞
      cornerRayFrame_infty_ne_zero (M := M))
    (τ : ℝ → E)
    (hρchart : ∀ s ∈ Ioo (-a) (L - a), (ρ s : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source)
    (hcoord : ∀ s ∈ Ioo (-a) (L - a), extChartAt I p (ρ s : M) = τ (s + a))
    (hρO : ∀ s ∈ Ioo (-a) (L - a), τ (s + a) ∈ O)
    (hτ : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) ∞ τ)
    (hgeo : IsGeodesicOn (I := 𝓘(ℝ, E)) G τ (Icc 0 L))
    (hunit : ∀ t, t ∈ Icc (0 : ℝ) L →
      G.inner (τ t) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ t 1) = 1)
    (e : ι → TangentSpace 𝓘(ℝ, E) (τ 0))
    (heON : ∀ i j, G.inner (τ 0) (e i) (e j) = if i = j then 1 else 0)
    (heperp : ∀ i, G.inner (τ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ 0 1) (e i) = 0) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      cornerRayFrame_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U E ∞,
    ∃ Z : ι → ∀ t : ℝ, TangentSpace 𝓘(ℝ, E) (τ t),
      Φ.source = {z : U | (z : M) ∈
        (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
          extChartAt I p (z : M) ∈ O} ∧
      (∀ z ∈ Φ.source, Φ z = extChartAt I p (z : M)) ∧
      (∀ z ∈ Φ.source, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
        k.inner z v w = G.inner (Φ z)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w)) ∧
      (∀ i, Z i 0 = e i) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) L →
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun s => (⟨τ s, Z i s⟩ : TangentBundle 𝓘(ℝ, E) E)) t) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) L → covDerivAlong G τ (Z i) t = 0) ∧
      (∀ t, t ∈ Icc (0 : ℝ) L → ∀ i j,
        G.inner (τ t) (Z i t) (Z j t) = if i = j then 1 else 0) ∧
      (∀ s, s ∈ Ioo (-a) (L - a) → Φ.symm (τ (s + a)) = ρ s) ∧
      (∀ i s, s ∈ Ioo (-a) (L - a) →
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun r => (⟨Φ.symm (τ (r + a)),
            mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (r + a)) (Z i (r + a))⟩ :
            TangentBundle 𝓘(ℝ, E) U)) s) ∧
      (∀ i s, s ∈ Ioo (-a) (L - a) →
        covDerivAlong k (fun r => Φ.symm (τ (r + a)))
          (fun r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (r + a)) (Z i (r + a)))
          s = 0) ∧
      (∀ s, s ∈ Ioo (-a) (L - a) → ∀ i j,
        k.inner (Φ.symm (τ (s + a)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (s + a)) (Z i (s + a)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (s + a)) (Z j (s + a))) =
          if i = j then 1 else 0) ∧
      (∀ s, s ∈ Ioo (-a) (L - a) → ∀ i,
        k.inner (Φ.symm (τ (s + a)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (s + a)) (Z i (s + a)))
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (τ (r + a))) s) = 0) ∧
      (∀ s, s ∈ Ioo (-a) (L - a) →
        k.inner (Φ.symm (τ (s + a)))
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (τ (r + a))) s)
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (τ (r + a))) s) = 1) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    cornerRayFrame_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  let J : Set ℝ := Ioo (-a) (L - a)
  have hL : 0 < L := lt_trans ha haL
  have hzero : (0 : ℝ) ∈ J := by
    dsimp [J]
    constructor <;> linarith
  obtain ⟨Z, hZ0, hZbundle, hZpar, hZON, hZperp⟩ :=
    exists_pole_parallel_normal_frame_of_basis_OX124 G τ L hL hτ hgeo e heON heperp
  let W : ι → ∀ s, TangentSpace 𝓘(ℝ, E) (τ (s + a)) := fun i s => Z i (s + a)
  have htime (s : ℝ) (hs : s ∈ J) : s + a ∈ Icc (0 : ℝ) L := by
    dsimp [J] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hshift (s : ℝ) : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ => r + a) s := contMDiffAt_id.add contMDiffAt_const
  have hδ (s : ℝ) :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (fun r => τ (r + a)) s :=
    ((hτ.contMDiffAt (x := s + a)).comp s (hshift s)).mdifferentiableAt (by norm_num)
  have hW (i : ι) (s : ℝ) (hs : s ∈ J) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun r => (⟨τ (r + a), W i r⟩ : TangentBundle 𝓘(ℝ, E) E)) s :=
    (hZbundle i (s + a) (htime s hs)).comp s (hshift s)
  have hZdiff (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      DifferentiableAt ℝ (chartRepAt (I := 𝓘(ℝ, E)) τ (Z i) t) t :=
    chartRepAt_differentiableAt_of_total_contMDiffAt
      ((hZbundle i t ht).of_le (by norm_num))
  have hpar (i : ι) (s : ℝ) (hs : s ∈ J) :
      covDerivAlong G (fun r => τ (r + a)) (W i) s = 0 := by
    have hcomp := covDerivAlong_comp G τ (Z i) (fun r => r + a) s
      ((hτ.contMDiffAt (x := s + a)).mdifferentiableAt (by norm_num))
      (hZdiff i (s + a) (htime s hs)) (differentiableAt_id.add_const a)
    have hder : deriv (fun r : ℝ => r + a) s = 1 :=
      ((hasDerivAt_id s).add_const a).deriv
    rw [hZpar i (s + a) (htime s hs), hder] at hcomp
    simpa only [one_smul, smul_zero] using hcomp
  have hvel (s : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (fun r => τ (r + a)) s 1 =
        mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ (s + a) 1 :=
    DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one s a
      ((hτ.contMDiffAt (x := s + a)).mdifferentiableAt (by norm_num))
  have hWperp (s : ℝ) (hs : s ∈ J) (i : ι) :
      G.inner (τ (s + a))
        (W i s) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (fun r => τ (r + a)) s 1) = 0 := by
    rw [hvel s]
    exact (G.symm (τ (s + a)) (W i s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ (s + a) 1)).trans (hZperp (s + a) (htime s hs) i)
  have hWunit (s : ℝ) (hs : s ∈ J) :
      G.inner (τ (s + a))
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (fun r => τ (r + a)) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (fun r => τ (r + a)) s 1) = 1 := by
    rw [hvel s]
    exact hunit (s + a) (htime s hs)
  obtain ⟨Φ, hΦsource, hΦmap, hΦmetric, hΦinv, hΦpar, hΦON, hΦperp, hΦunit⟩ :=
    originalCorner_extension_normal_frame g p G O hG ρ
      (fun s => τ (s + a)) J hρchart hcoord hρO (fun s _ => hδ s) W
      (fun i s hs => (hW i s hs).of_le (by norm_num)) hpar
      (fun s hs i j => hZON (s + a) (htime s hs) i j) hWperp hWunit
      (ρ 0) (hρchart 0 hzero) (hcoord 0 hzero) (hρO 0 hzero)
  have hS (s : ℝ) (hs : s ∈ J) : ρ s ∈ {z : U | (z : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
        extChartAt I p (z : M) ∈ O} :=
    ⟨hρchart s hs, by rw [hcoord s hs]; exact hρO s hs⟩
  have hsource (s : ℝ) (hs : s ∈ J) : ρ s ∈ Φ.source := by
    rw [hΦsource]
    exact hS s hs
  have htarget (s : ℝ) (hs : s ∈ J) : τ (s + a) ∈ Φ.target := by
    have hmap : Φ (ρ s) = extChartAt I p (ρ s : M) := hΦmap (ρ s) (hS s hs)
    have htarget' : extChartAt I p (ρ s : M) ∈ Φ.target := by
      rw [← hmap]
      exact Φ.map_source (hsource s hs)
    rw [hcoord s hs] at htarget'
    exact htarget'
  have hFbundle (i : ι) (s : ℝ) (hs : s ∈ J) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun r => (⟨Φ.symm (τ (r + a)),
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (r + a)) (Z i (r + a))⟩ :
          TangentBundle 𝓘(ℝ, E) U)) s := by
    have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Φ.symm : E → U) (τ (s + a)) :=
      Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds (htarget s hs))
    have hT : ContMDiffAt (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)).tangent ∞
        (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U))
        (⟨τ (s + a), W i s⟩ : TangentBundle 𝓘(ℝ, E) E) :=
      DifferentialGeometry.VectorField.contMDiffAt_tangentMap hsymm (by norm_num)
    exact hT.comp s (hW i s hs)
  refine ⟨Φ, Z, hΦsource, ?_, ?_, hZ0, hZbundle, hZpar, hZON, hΦinv, hFbundle, hΦpar,
    hΦON, hΦperp, hΦunit⟩
  · intro z hz
    rw [hΦsource] at hz
    exact hΦmap z hz
  · intro z hz v w
    rw [hΦsource] at hz
    exact hΦmetric z hz v w

end Chart

section Binding

open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientDimension : NeZero (Module.finrank ℝ E)]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem cornerRayBinding_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

/-- The common original pole family of `exists_boundary_common_pole_initial_frame` with, for every
unit inward velocity `v` and every `G`-orthonormal family `e` normal to `v`, the `k`-parallel
orthonormal normal frame along the actual phase curve `r ↦ boundaryPhasePoint k σ v r` on
`(-a, L - a)` (the pole is at phase time `-a`), obtained as the pullback of the `G`-parallel frame
`Z` along the chart geodesic, with `Z i 0 = e i` at the pole. -/
theorem exists_boundary_corner_ray_pole_frame_OX124 (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      cornerRayBinding_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ V : Opens (E × ℝ), ∃ ρ : E × ℝ → U,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            (ρ q : M) = (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ δ : ℝ, 0 < δ ∧ ∃ a ∈ Ioo 0 δ,
              ∃ σ : E → TangentBundle 𝓘(ℝ, E) U,
              ∃ W : Opens E, ∃ ε : ℝ, v ∈ W ∧ 0 < ε ∧
                ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
                (∀ u ∈ W, (u, a) ∈ V ∧ (σ u).proj = ρ (u, a)) ∧
                (∀ u ∈ W, ∀ r ∈ Metric.ball (0 : ℝ) ε,
                  (σ u, r) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ u r = ρ (u, r + a) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ u r w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w) ∧
                (∀ t ∈ Ioo 0 δ, (v, t) ∈ V) ∧
                Tendsto (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M))
                  (𝓝[>] (0 : ℝ)) (𝓝 p) ∧
                (∀ u ∈ W, σ u = DifferentialGeometry.velocityLift
                  (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) ∧
                (∀ t ∈ Ioo 0 δ, (σ v, t - a) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ v (t - a) = ρ (v, t) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ v (t - a) w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v t w) ∧
                (∀ e : Fin 2 → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  Tendsto (fun t : ℝ => curveDensity k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2)
                    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) ∧
                (∀ u ∈ W, ∀ t : ℝ, (σ u, t) ∈ k.geodesicFlowDomain →
                  k.inner (boundaryPhasePoint k σ u t)
                      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t)
                      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t) =
                    G.inner (extChartAt I p p) u u ∧
                  (∀ w : E, G.inner (extChartAt I p p) w u = 0 →
                    k.inner (boundaryPhasePoint k σ u t) (boundaryPhaseJacobiLinear k σ u t w)
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t) = 0 ∧
                      k.inner (boundaryPhasePoint k σ u t)
                        (covDerivAlong k (fun r => boundaryPhasePoint k σ u r)
                          (fun r => boundaryPhaseJacobiLinear k σ u r w) t)
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t)
                        = 0) ∧
                  (∀ w z : E, jacobiWronskian k (fun r => boundaryPhasePoint k σ u r)
                    (fun r => boundaryPhaseJacobiLinear k σ u r w)
                    (fun r => boundaryPhaseJacobiLinear k σ u r z) t = 0) ∧
                  ∀ w : E, IsJacobiAt k (fun r => boundaryPhasePoint k σ u r)
                      (fun r => boundaryPhaseJacobiLinear k σ u r w) t ∧
                    ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                      (fun r => (⟨boundaryPhasePoint k σ u r, boundaryPhaseJacobiLinear k σ u r w⟩ :
                        TangentBundle 𝓘(ℝ, E) U)) t) ∧
                (G.inner (extChartAt I p p) v v = 1 →
                  ∀ e : Fin (Module.finrank ℝ E - 1) → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  (∀ i, G.inner (extChartAt I p p) v (e i) = 0) →
                  ∃ L : ℝ, a < L ∧ L < δ ∧
                  ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U E ∞,
                  ∃ Z : Fin (Module.finrank ℝ E - 1) → ∀ t : ℝ,
                    TangentSpace 𝓘(ℝ, E) (boundaryPoleFlowFamily G (extChartAt I p p) v t),
                    Φ.source = {z : U | (z : M) ∈
                      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
                        extChartAt I p (z : M) ∈ O} ∧
                    (∀ z ∈ Φ.source, Φ z = extChartAt I p (z : M)) ∧
                    (∀ z ∈ Φ.source, ∀ x w : TangentSpace 𝓘(ℝ, E) z,
                      k.inner z x w = G.inner (Φ z)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z x)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w)) ∧
                    (∀ i, Z i 0 = e i) ∧
                    (∀ i t, t ∈ Icc (0 : ℝ) L →
                      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
                        (fun s => (⟨boundaryPoleFlowFamily G (extChartAt I p p) v s, Z i s⟩ :
                          TangentBundle 𝓘(ℝ, E) E)) t) ∧
                    (∀ i t, t ∈ Icc (0 : ℝ) L →
                      covDerivAlong G (boundaryPoleFlowFamily G (extChartAt I p p) v)
                        (Z i) t = 0) ∧
                    (∀ t, t ∈ Icc (0 : ℝ) L → ∀ i j,
                      G.inner (boundaryPoleFlowFamily G (extChartAt I p p) v t)
                        (Z i t) (Z j t) = if i = j then 1 else 0) ∧
                    (∀ r ∈ Ioo (-a) (L - a), (σ v, r) ∈ k.geodesicFlowDomain ∧
                      Φ.symm (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) =
                        boundaryPhasePoint k σ v r) ∧
                    (∀ i r, r ∈ Ioo (-a) (L - a) →
                      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
                        (fun q => (⟨boundaryPhasePoint k σ v q,
                          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                            (boundaryPoleFlowFamily G (extChartAt I p p) v (q + a))
                            (Z i (q + a))⟩ : TangentBundle 𝓘(ℝ, E) U)) r) ∧
                    (∀ i r, r ∈ Ioo (-a) (L - a) →
                      covDerivAlong k (fun q => boundaryPhasePoint k σ v q)
                        (fun q => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (q + a))
                          (Z i (q + a))) r = 0) ∧
                    (∀ r, r ∈ Ioo (-a) (L - a) → ∀ i j,
                      k.inner (boundaryPhasePoint k σ v r)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z i (r + a)))
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z j (r + a))) =
                        if i = j then 1 else 0) ∧
                    (∀ r, r ∈ Ioo (-a) (L - a) → ∀ i,
                      k.inner (boundaryPhasePoint k σ v r)
                        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
                          (boundaryPoleFlowFamily G (extChartAt I p p) v (r + a)) (Z i (r + a)))
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun q => boundaryPhasePoint k σ v q) r) =
                        0)) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    cornerRayBinding_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hbirth⟩ :=
    exists_boundary_common_pole_initial_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hv
  obtain ⟨δ, hδ, a, ha, σ, W, ε, hvW, hε, hσ, hWV, hflow, hvV, hpole, hσvel, hphase, hdens,
    hphys⟩ := hbirth v hv
  refine ⟨δ, hδ, a, ha, σ, W, ε, hvW, hε, hσ, hWV, hflow, hvV, hpole, hσvel, hphase, hdens,
    hphys, ?_⟩
  intro hunit e heON heperp
  set y := extChartAt I p p with hy
  obtain ⟨_hmem, hτ, hgeo, hτ0, hτ'0, hspeed⟩ :=
    boundaryPoleFlowFamily_complete_OX124 G hcomplete y v
  set τ := boundaryPoleFlowFamily G y v with hτdef
  set L : ℝ := (a + δ) / 2 with hLdef
  have haL : a < L := by rw [hLdef]; linarith [ha.2]
  have hLδ : L < δ := by rw [hLdef]; linarith [ha.2]
  have hpos : 0 < a := ha.1
  have htime (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) : r + a ∈ Ioo (0 : ℝ) δ :=
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hshift (r : ℝ) : r + a - a = r := by ring
  have hphase' (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) :
      (σ v, r) ∈ k.geodesicFlowDomain ∧ boundaryPhasePoint k σ v r = ρ (v, r + a) := by
    have h := hphase (r + a) (htime r hr)
    rw [hshift r] at h
    exact ⟨h.1, h.2.1⟩
  have hallv (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) :
      τ (r + a) ∈ (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ (v, r + a) : M) = (extChartAt I p).symm (τ (r + a)) := by
    have h := hall (v, r + a) (hvV (r + a) (htime r hr))
    exact ⟨h.2.1, h.2.2.1⟩
  have hρchart (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) :
      ((boundaryPhasePoint k σ v r : U) : M) ∈
        (DifferentialGeometry.Manifold.interiorChart I ∞ p).source := by
    rw [(hphase' r hr).2, (hallv r hr).2]
    exact (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target (hallv r hr).1.2
  have hcoord (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) :
      extChartAt I p ((boundaryPhasePoint k σ v r : U) : M) = τ (r + a) := by
    rw [(hphase' r hr).2, (hallv r hr).2]
    exact (extChartAt I p).right_inv (interior_subset (hallv r hr).1.2)
  have hρO (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) : τ (r + a) ∈ O := (hallv r hr).1.1
  have hunitτ : ∀ t, t ∈ Icc (0 : ℝ) L →
      G.inner (τ t) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ t 1) = 1 := by
    intro t _ht
    rw [hspeed t, hunit]
  have heON' : ∀ i j, G.inner (τ 0) (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [hτ0]
    exact heON i j
  have heperp' : ∀ i, G.inner (τ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) τ 0 1) (e i) = 0 := by
    intro i
    rw [hτ'0, hτ0]
    exact heperp i
  obtain ⟨Φ, Z, hsrc, hmap, hmet, hZ0, hZsm, hZpar, hZON, hinv, hFsm, hFpar, hFON, hFperp,
    _hFunit⟩ :=
    originalCorner_pole_frame_of_basis_OX124 g p G O hG a L hpos haL
      (fun r => boundaryPhasePoint k σ v r) τ hρchart hcoord hρO hτ
      (fun t _ => hgeo t (mem_univ t)) hunitτ (fun i => e i) heON' heperp'
  have hev (r : ℝ) (hr : r ∈ Ioo (-a) (L - a)) :
      (fun q => Φ.symm (τ (q + a))) =ᶠ[𝓝 r] (fun q => boundaryPhasePoint k σ v q) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with q hq
    exact hinv q hq
  have hbase : ∀ {x x' : U}, x = x' → ∀ u w : E, k.inner x u w = k.inner x' u w := by
    intro x x' h u w
    subst h
    rfl
  refine ⟨L, haL, hLδ, Φ, Z, hsrc, hmap, hmet, hZ0, hZsm, hZpar, hZON,
    fun r hr => ⟨(hphase' r hr).1, hinv r hr⟩, ?_, ?_, ?_, ?_⟩
  · intro i r hr
    refine (hFsm i r hr).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hr] with q hq
    exact (congrArg (fun x : U => (⟨x, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
      (τ (q + a)) (Z i (q + a)) : E)⟩ : TangentBundle 𝓘(ℝ, E) U)) (hinv q hq)).symm
  · intro i r hr
    have h := covDerivAlong_congr_curve k (γ := fun q => Φ.symm (τ (q + a)))
      (γ' := fun q => boundaryPhasePoint k σ v q)
      (fun q => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (q + a)) (Z i (q + a)))
      (fun q => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (q + a)) (Z i (q + a)))
      (hev r hr) (Eventually.of_forall fun _ => rfl)
    rw [hFpar i r hr] at h
    exact h.symm
  · intro r hr i j
    exact (hbase (hinv r hr) _ _).symm.trans (hFON r hr i j)
  · intro r hr i
    have hvel : (curveVelocity (I := 𝓘(ℝ, E)) (fun q => Φ.symm (τ (q + a))) r : E) =
        (curveVelocity (I := 𝓘(ℝ, E)) (fun q => boundaryPhasePoint k σ v q) r : E) := by
      unfold curveVelocity
      rw [(hev r hr).mfderiv_eq]
      rfl
    have h := (hbase (hinv r hr)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (τ (r + a)) (Z i (r + a)))
      (curveVelocity (I := 𝓘(ℝ, E)) (fun q => Φ.symm (τ (q + a))) r)).symm.trans
        (hFperp r hr i)
    rw [hvel] at h
    exact h

end Binding

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
