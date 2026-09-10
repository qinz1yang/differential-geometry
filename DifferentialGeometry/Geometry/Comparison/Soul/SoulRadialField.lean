import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance
import DifferentialGeometry.Geometry.Comparison.Soul.RadialFieldPatch
import DifferentialGeometry.Geometry.Comparison.Soul.RadialNormalFlow
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceLevelProduct

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_soul_set_with_radial_outward_field
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      ∃ r₀ > 0,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
          {q | 0 < Metric.infDist q S ∧ Metric.infDist q S < r₀} ∧
        (∀ (p : S) (v : normalSpace g S p.1), g.inner p.1 v.1 v.1 = 1 →
          ∀ t : ℝ, 0 < t → t < r₀ → Metric.infDist (intrinsicGeodesic g hEnorm p.1 v.1 t) S = t) ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯,
          (∀ q, g.inner q (V q) (V q) ≤ 4) ∧
          (∀ᶠ q in 𝓝ˢ {q : M | r / 4 ≤ Metric.infDist q S ∧ Metric.infDist q S ≤ r / 2},
            V q = gradientFun g (fun x => Metric.infDist x S) q) ∧
          ∀ q, r / 8 ≤ Metric.infDist q S → ∀ u : TangentSpace I q,
            g.inner q u u = 1 → intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
            g.inner q (V q) u < 0 := by
  obtain ⟨S, hSne, hScomp, hconv, hB, hdim, hfields⟩ :=
    exists_soul_set_with_smooth_outward_fields g hEnorm hsec p
  obtain ⟨r₀, hr₀, hd, hrad⟩ :=
    exists_smooth_infDist_normal_radial_data g hEnorm hsec hSne hScomp hconv hB
  refine ⟨S, hSne, hScomp, hconv, hB, hdim, r₀, hr₀, hd, hrad, ?_⟩
  intro r hr hrr₀
  obtain ⟨W, hWbound, _, hWout⟩ := hfields (r / 16) (r / 8) (by positivity) (by linarith)
  obtain ⟨V, hVbound, _, hVrad, _, hVout⟩ :=
    exists_radial_outward_field_patch g hEnorm hScomp hSne
      (a := r / 8) (b := r / 4) (c := r / 2) (r := r)
      (by positivity) (by linarith) (by linarith) (by linarith)
      (hd.mono (fun q hq => ⟨hq.1, hq.2.trans_le hrr₀⟩)) W 2 (by norm_num)
      (fun q => by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using (hWbound q).le)
      (fun q hq u hu hend => hWout q hq u ⟨hu, hend⟩)
  refine ⟨V, ?_, hVrad, hVout⟩
  intro q
  simpa only [show max (1 : ℝ) 2 = 2 by norm_num, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using hVbound q

theorem exists_soul_set_with_radial_escape_flow
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      ∃ r₀ > 0,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => Metric.infDist q S)
          {q | 0 < Metric.infDist q S ∧ Metric.infDist q S < r₀} ∧
        (∀ (p : S) (v : normalSpace g S p.1), g.inner p.1 v.1 v.1 = 1 →
          ∀ t : ℝ, 0 < t → t < r₀ → Metric.infDist (intrinsicGeodesic g hEnorm p.1 v.1 t) S = t) ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯,
          (∀ᶠ q in 𝓝ˢ {q : M | r / 4 ≤ Metric.infDist q S ∧ Metric.infDist q S ≤ r / 2},
            V q = gradientFun g (fun x => Metric.infDist x S) q) ∧
          (∀ q, r / 8 ≤ Metric.infDist q S → ∀ u : TangentSpace I q,
            g.inner q u u = 1 → intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
            g.inner q (V q) u < 0) ∧
          ∃ ϕ : Flow ℝ M,
            ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2) ∧
            (∀ q, IsMIntegralCurve (fun t => ϕ t q) V) ∧
            (∀ q, r / 8 ≤ Metric.infDist q S →
              StrictMonoOn (fun t => Metric.infDist (ϕ t q) S) (Ici 0) ∧
              Tendsto (fun t => Metric.infDist (ϕ t q) S) atTop atTop) ∧
            ∀ q, r / 8 ≤ Metric.infDist q S → ∀ s : ℝ, r / 8 ≤ s →
              ∃! t : ℝ, Metric.infDist (ϕ t q) S = s := by
  obtain ⟨S, hSne, hScomp, hconv, hB, hdim, r₀, hr₀, hd, hrad, hfields⟩ :=
    exists_soul_set_with_radial_outward_field g hEnorm hsec p
  refine ⟨S, hSne, hScomp, hconv, hB, hdim, r₀, hr₀, hd, hrad, ?_⟩
  intro r hr hrr₀
  obtain ⟨V, hbound, hVrad, hout⟩ := hfields r hr hrr₀
  have hr8 : 0 < r / 8 := by positivity
  obtain ⟨ϕ, hϕsmooth, hϕ, hescape⟩ := exists_complete_infDist_escape_flow g hEnorm hScomp hSne
    V 2 (by norm_num)
    (fun q => by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hbound q) hr8 hout
  refine ⟨V, hVrad, hout,
    ϕ, hϕsmooth, hϕ, fun q hq => (hescape q hq).2, ?_⟩
  intro q hq s hs
  exact existsUnique_infDist_levelTime g hEnorm hScomp hSne V V.contMDiff.continuous
    ϕ hϕ hr8 hout q hq s hs

end DifferentialGeometry.Geometry.Topology
