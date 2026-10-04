import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCommonExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.SurfaceSectionalLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRmAlgebra
import DifferentialGeometry.Geometry.Thurston.SurfaceFlowExtension

/-!
# Common existence time and preserved sectional bounds for surface Ricci flows (2D LFR50, B + C)

The two-dimensional analogue of `exists_common_compact_flows_of_initial_rm_bound` and
`exists_common_flows_sectional_exp_lower_bound` (LFR50 parts B and C, dimension three).

* Part B. On a closed surface every smooth metric with `|Rm| ≤ B` has a Ricci flow beyond
  `compactCurvatureControlTime 2 B`, with `|Rm| ≤ √(2B² + 1)` up to that time. The curvature
  control (`curvature_bound_from_initial_compact`) is dimension-free; the three-dimensional
  extension criterion `extends_of_rmBounded` is replaced by the surface criterion
  `GC.Geometry.surfaceFlow_extendsPastEndpoint_of_scalar_bounded` (bounded scalar curvature
  suffices, and `|Rm| = |R|` on a surface), applied to a maximal flow
  (`exists_maximal_flowTo_of_bddAbove`).
* Part C. Every sectional lower bound is preserved without loss
  (`sectionalBoundedBelow_preserved_of_finrank_eq_two`), so `sec ≥ -εₙ` stays `sec ≥ -εₙ`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

/-- On a surface, a flow defined up to a time `τ ≤ compactCurvatureControlTime 2 K` from a metric
with `|Rm| ≤ K` extends past `τ`. -/
theorem flowTo_extendsPastEndpoint_of_le_compactCurvatureControlTime_of_finrank_eq_two
    (hdim : Module.finrank ℝ E = 2) {g₀ : SmoothRiemannianMetric I M} {τ : ℝ}
    (P : FlowTo g₀ τ) (K : ℝ) (hτ : τ ≤ compactCurvatureControlTime 2 K)
    (hinit : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ K) :
    ExtendsPastEndpoint (I := I) P.time_pos P.S := by
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hτ' : τ ≤ compactCurvatureControlTime (Module.finrank ℝ E) K := by rwa [hdim]
  have hi (x : M) : Real.sqrt (normSq0S (P.S.base.metric 0) x 4
      (metricRm04 (P.S.base.metric 0) x)) ≤ K := by
    have he : P.S.base.metric 0 = g₀ := P.start
    rw [he]
    exact hinit x
  refine GC.Geometry.surfaceFlow_extendsPastEndpoint_of_scalar_bounded hdim P.time_pos P.S
    P.isSolution ⟨Real.sqrt (2 * K ^ 2 + 1), fun t ht x => ?_⟩
  have hsub : Icc 0 t ⊆ Ico 0 τ := fun r hr => ⟨hr.1, hr.2.trans_lt ht.2⟩
  have hh := curvature_bound_from_initial_compact t ht.1 K (ht.2.le.trans hτ') _ P.S P.isSolution
    hsub (fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)
    (fun x₀ i j => (P.joint x₀ i j).mono (prod_mono hsub subset_rfl)) hi t ⟨ht.1, le_rfl⟩ x
  have hRm := sqrt_metricRm_normSq_eq_abs_scalar_of_finrank_two (P.S.base.metric t) hdim x
  rw [← metricRm04_apply] at hRm
  rw [hRm] at hh
  exact hh

/-- **2D part B.** On a closed surface a Ricci flow started at a metric with `|Rm| ≤ B` exists
strictly beyond `compactCurvatureControlTime 2 B` and keeps `|Rm| ≤ √(2B² + 1)` up to that
time. -/
theorem exists_flowTo_beyond_compactCurvatureControlTime_of_finrank_eq_two
    (hdim : Module.finrank ℝ E = 2) (g₀ : SmoothRiemannianMetric I M) (B : ℝ)
    (hinit : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ B) :
    ∃ τ : ℝ, compactCurvatureControlTime 2 B < τ ∧
      ∃ F : FlowTo g₀ τ,
        ∀ t ∈ Icc 0 (compactCurvatureControlTime 2 B), ∀ x : M,
          Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
            Real.sqrt (2 * B ^ 2 + 1) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hbeyond : ∃ τ : ℝ, compactCurvatureControlTime 2 B < τ ∧ Nonempty (FlowTo g₀ τ) := by
    by_contra hn
    have hbdd : BddAbove {T : ℝ | Nonempty (FlowTo g₀ T)} :=
      ⟨compactCurvatureControlTime 2 B, fun T hT => le_of_not_gt fun hlt => hn ⟨T, hlt, hT⟩⟩
    obtain ⟨Tm, P, hmax⟩ := exists_maximal_flowTo_of_bddAbove (I := I) g₀ hbdd
    have hTm : Tm ≤ compactCurvatureControlTime 2 B :=
      le_of_not_gt fun hlt => hn ⟨Tm, hlt, ⟨P⟩⟩
    exact hmax (flowTo_extendsPastEndpoint_of_le_compactCurvatureControlTime_of_finrank_eq_two
      hdim P B hTm hinit)
  obtain ⟨τ, hτ, ⟨F⟩⟩ := hbeyond
  refine ⟨τ, hτ, F, ?_⟩
  have hc : compactCurvatureControlTime 2 B = compactCurvatureControlTime (Module.finrank ℝ E) B := by
    rw [hdim]
  have hsub : Icc 0 (compactCurvatureControlTime 2 B) ⊆ Ico 0 τ :=
    fun r hr => ⟨hr.1, hr.2.trans_lt hτ⟩
  have hi (x : M) : Real.sqrt (normSq0S (F.S.base.metric 0) x 4
      (metricRm04 (F.S.base.metric 0) x)) ≤ B := by
    have he : F.S.base.metric 0 = g₀ := F.start
    rw [he]
    exact hinit x
  exact curvature_bound_from_initial_compact _ (compactCurvatureControlTime_pos 2 B).le B hc.le _
    F.S F.isSolution hsub (fun r hr => ⟨hr.1, hr.2.trans hτ⟩)
    (fun x₀ i j => (F.joint x₀ i j).mono (prod_mono hsub subset_rfl)) hi

/-- **2D parts B + C, sequence form.** Metrics `gSeq n` on a closed surface with one bound
`|Rm| ≤ B` and `sec(gSeq n) ≥ -ε n` have Ricci flows on a common interval `[0, T]`, `T > 0`, each
existing beyond `T`, with `|Rm| ≤ √(2B² + 1)` and `sec ≥ -ε n` on `[0, T]`. -/
theorem exists_common_flows_sectional_lower_bound_of_finrank_eq_two
    (hdim : Module.finrank ℝ E = 2) (B : ℝ)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (ε : ℕ → ℝ)
    (hRm : ∀ n x, Real.sqrt (normSq0S (gSeq n) x 4 (metricRm04 (gSeq n) x)) ≤ B)
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ, ∃ τ : ℝ, T < τ ∧ ∃ F : FlowTo (gSeq n) τ,
      ∀ t ∈ Icc 0 T,
        (∀ x : M, Real.sqrt (normSq0S (F.S.base.metric t) x 4
          (metricRm04 (F.S.base.metric t) x)) ≤ Real.sqrt (2 * B ^ 2 + 1)) ∧
        SectionalBoundedBelow (F.S.base.metric t) (-ε n) := by
  refine ⟨compactCurvatureControlTime 2 B, compactCurvatureControlTime_pos 2 B, fun n => ?_⟩
  obtain ⟨τ, hτ, F, hF⟩ :=
    exists_flowTo_beyond_compactCurvatureControlTime_of_finrank_eq_two hdim (gSeq n) B (hRm n)
  have hsec0 : SectionalBoundedBelow (F.S.base.metric 0) (-ε n) := by
    rw [show F.S.base.metric 0 = gSeq n from F.start]
    exact hsec n
  have hpres := sectionalBoundedBelow_preserved_of_finrank_eq_two hdim F.S F.isSolution
    (F.Icc_subset_carrier hτ) (fun r hr => (F.Ioc_subset_regular hτ) ⟨hr.1, hr.2.le⟩) hsec0
  exact ⟨τ, hτ, F, fun t ht => ⟨hF t ht, hpres t ht⟩⟩

end DifferentialGeometry.PDE.RicciFlow
