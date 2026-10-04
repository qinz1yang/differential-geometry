import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3
import DifferentialGeometry.Geometry.Thurston.SurfaceFlowExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow

/-!
# The maximal time of a positively curved surface flow

Chapter 7, surface lemma U1, route (a), step a2 (lane U1E2), the short closure of review 17 §4.4
on the design note D17 (`docs/geometrization/handoffs/20261004-design-u1-ricci-flow-core.md`).
For a Ricci flow on a compact connected surface with positive initial scalar curvature put
`A₀ = Area` and `C₀ = ∫ R dμ` at time `0`, and `T* = A₀ / C₀`.

* `surfaceFlow_maximal_time_eq` (D17 §3 `a2_maximal_time_eq`): a maximal flow on `[0, Tm)` has
  `Tm = T*`. The area formula gives `Tm ≤ T*` (`surfaceFlow_le_extinctionTime`). If `Tm < T*`,
  the normalised upper bound `R (2 (T* - t)) ≤ C` (`surfaceFlow_normalized_scalar_upper`, a3) and
  `R > 0` (`surfaceFlow_scalar_pos`) bound `|R|` by `C / (2 (T* - Tm))`, so the flow extends
  (`surfaceFlow_extendsPastEndpoint_of_scalar_bounded`, a1), against maximality.
* `exists_maximal_surfaceFlow`: from any such initial metric there is a maximal flow
  (`exists_maximal_flowTo_of_bddAbove`, the time set being bounded by `T*`), and its maximal time
  is `T*`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]

theorem surfaceFlow_maximal_time_eq (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (hmax : IsMaximalAtEndpoint (I := I) hTm S) :
    Tm = surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) := by
  set Tst := surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0)
  have hle : Tm ≤ Tst := surfaceFlow_le_extinctionTime hTm S hS hdim hscal
  refine le_antisymm hle (not_lt.mp fun hlt => hmax ?_)
  obtain ⟨C, hC⟩ := surfaceFlow_normalized_scalar_upper hdim S hS hscal
  have hgap : 0 < Tst - Tm := sub_pos.mpr hlt
  refine surfaceFlow_extendsPastEndpoint_of_scalar_bounded hdim hTm S hS
    ⟨C / (2 * (Tst - Tm)), fun t ht x => ?_⟩
  have hpos : 0 < S.scalar t x := surfaceFlow_scalar_pos S hS hscal ht x
  have hmono : 2 * (Tst - Tm) ≤ 2 * (Tst - t) := by linarith [ht.2]
  rw [abs_of_pos hpos, le_div_iff₀ (by positivity)]
  calc S.scalar t x * (2 * (Tst - Tm)) ≤ S.scalar t x * (2 * (Tst - t)) :=
        mul_le_mul_of_nonneg_left hmono hpos.le
    _ ≤ C := hC t ht x

theorem exists_maximal_surfaceFlow (hdim : Module.finrank ℝ E = 2)
    (g0 : SmoothRiemannianMetric I M) (hscal : ∀ x, 0 < metricScalarAt g0 x) :
    ∃ Tm : ℝ, ∃ P : FlowTo (I := I) (M := M) g0 Tm,
      IsMaximalAtEndpoint (I := I) P.time_pos P.S ∧
        Tm = surfaceArea g0 / totalScalarCurvature g0 := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hscalP : ∀ {T : ℝ} (P : FlowTo (I := I) (M := M) g0 T), ∀ x, 0 < P.S.scalar 0 x := by
    intro T P x
    change 0 < metricScalarAt (P.S.family.metric 0) x
    rw [P.start]
    exact hscal x
  have hbdd : BddAbove {T : ℝ | Nonempty (FlowTo (I := I) (M := M) g0 T)} := by
    refine ⟨surfaceArea g0 / totalScalarCurvature g0, fun T hT => ?_⟩
    obtain ⟨P⟩ := hT
    have h := surfaceFlow_le_extinctionTime P.time_pos P.S P.isSolution hdim (hscalP P)
    rwa [P.start] at h
  obtain ⟨Tm, P, hmax⟩ := exists_maximal_flowTo_of_bddAbove (I := I) g0 hbdd
  refine ⟨Tm, P, hmax, ?_⟩
  have h := surfaceFlow_maximal_time_eq hdim P.time_pos P.S P.isSolution (hscalP P) hmax
  rwa [P.start] at h

end GC.Geometry
