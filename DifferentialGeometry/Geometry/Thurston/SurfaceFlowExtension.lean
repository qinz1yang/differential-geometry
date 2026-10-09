import DifferentialGeometry.Geometry.Thurston.SurfaceFlowExtensionSlice
import DifferentialGeometry.Geometry.Thurston.SurfaceFlowExtensionRestart

/-!
# Extension of surface Ricci flows with bounded curvature

Chapter 7, surface lemma U1, route (a), step a1 (lane U1E2): route E2 of the design note D17
(`docs/geometrization/handoffs/20261004-design-u1-ricci-flow-core.md`, §4) as corrected by
review 17 (§3). A Ricci flow on `[0, Tm)` on a closed surface with bounded scalar curvature extends
past `Tm`; no maximality hypothesis is involved.

* `circleProductFlow_extendsPastEndpoint` (T2): the circle product `G(t) = g(t) ⊕ dθ²` on
  `M × S¹` has `|Rm_G|² = R_g²` bounded, so the three-dimensional criterion
  `extends_of_rmBounded` extends it; `ExtendsPastEndpoint` already records the agreement with `G`
  on `[0, Tm)`, so no uniqueness theorem is needed.
* `surfaceFlow_exists_smooth_endpoint_family` (T3): slicing the extension at `θ = 0` gives a
  family of metrics on `M`, jointly smooth on `(0, Tm + ε) × M` and equal to the flow on `[0, Tm)`.
* `surfaceFlow_extendsPastEndpoint_of_scalar_bounded` (a1, D17 §3 signature): the extension
  itself, by `extendsPastEndpoint_of_smooth_endpoint_family` (T4: restart from the endpoint slice
  and glue).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open Bundle Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

theorem circleProductFlow_extendsPastEndpoint (hdim : Module.finrank ℝ E = 2) {Tm : ℝ}
    (hTm : 0 < Tm) (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hbound : ∃ K : ℝ, ∀ t ∈ Ico 0 Tm, ∀ x, |S.scalar t x| ≤ K) :
    ExtendsPastEndpoint (I := circleProductModel I hdim) hTm (circleProductFlow hdim S) := by
  obtain ⟨K, hK⟩ := hbound
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
  refine extends_of_rmBounded (by simp) (isSolutionOn_circleProductFlow hdim S hS)
    (rm04Realizes_metric _) ⟨K ^ 2, fun t p ht1 ht2 => ?_⟩
  rw [circleProductFlow_curvatureNormSq]
  have h := hK t ⟨ht1, ht2⟩ p.1
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem surfaceFlow_exists_smooth_endpoint_family (hdim : Module.finrank ℝ E = 2) {Tm : ℝ}
    (hTm : 0 < Tm) (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hbound : ∃ K : ℝ, ∀ t ∈ Ico 0 Tm, ∀ x, |S.scalar t x| ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ k : ℝ → SmoothRiemannianMetric I M,
      (∀ t ∈ Ico 0 Tm, k t = S.family.metric t) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M => (⟨p.2, (k p.1).inner p.2⟩ :
          TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
        (Ioo 0 (Tm + ε) ×ˢ (univ : Set M)) := by
  obtain ⟨ε, hε, hwide, Shat, hShat, hagree⟩ :=
    circleProductFlow_extendsPastEndpoint hdim hTm S hS hbound
  refine ⟨ε, hε, fun t => sliceMetric hdim 0 (Shat.family.metric t), fun t ht => ?_, ?_⟩
  · change sliceMetric hdim 0 (Shat.family.metric t) = S.family.metric t
    rw [← (hagree t ht).1]
    exact sliceMetric_circleProductFlow hdim 0 S t
  · exact (metricFamilySmoothOn_sliceMetric hdim 0 hShat.smoothMetric).metricCLMSection_contMDiffOn
      subset_rfl

theorem surfaceFlow_extendsPastEndpoint_of_scalar_bounded (hdim : Module.finrank ℝ E = 2)
    {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (hS : IsSolutionOn S)
    (hbound : ∃ K : ℝ, ∀ t ∈ Ico 0 Tm, ∀ x, |S.scalar t x| ≤ K) :
    ExtendsPastEndpoint (I := I) hTm S := by
  obtain ⟨ε, hε, k, hk, hksmooth⟩ := surfaceFlow_exists_smooth_endpoint_family hdim hTm S hS hbound
  exact extendsPastEndpoint_of_smooth_endpoint_family hTm S hS hε k hk hksmooth

end GC.Geometry
