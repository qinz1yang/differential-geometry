import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepMain

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.LongTime.CuspP1
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}}

/-- C1: the truncation of `H` at cusp depth `S ≥ 2` (core = old core ∪ collars of depth `≤ S`). -/
def truncationAtLevel_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S) :
    HyperbolicTruncation H :=
  deepenTruncationOf_CPA2 T hS

theorem truncationAtLevel_count_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S) :
    (truncationAtLevel_C1 T hS).count = T.count := rfl

theorem truncationAtLevel_cuspMap_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) (q : CuspHalfSpace) :
    (truncationAtLevel_C1 T hS).cuspMap i q = T.cuspMap i (q.1, halfSpaceOneLift (q.2.val 0 + S)) :=
  rfl

theorem truncationAtLevel_cusp_torusMetric_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) (p : Torus) (v w : TangentSpace torusModel p) :
    ((truncationAtLevel_C1 T hS).cusp i).torusMetric.inner p v w =
      Real.exp (-S) * (T.cusp i).torusMetric.inner p v w :=
  deepCusp_torusMetric_inner_CPA (T.cusp i) S p v w

theorem truncationAtLevel_cusp_zero_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) (x : Torus) :
    (truncationAtLevel_C1 T hS).cuspMap i (x, halfZero) = T.cuspMap i (x, halfSpaceOneLift S) :=
  deepCuspMap_zero_CPA2 T i x

/-- The new core is the old core together with the cusp collars `cuspMap '' (T² × [0,S])`. -/
theorem truncationAtLevel_core_image_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S) :
    range (truncationAtLevel_C1 T hS).inclusion =
      range T.inclusion ∪ ⋃ i, T.cuspMap i '' (univ ×ˢ {u : EuclideanHalfSpace 1 | u.val 0 ≤ S}) := by
  have h := deepSet_eq_CPA2 T (b := S) (by linarith)
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact (Set.ext_iff.mp h x.val).mp x.2
  · intro hp
    have hp' : p ∈ deepSet_CPA2 T S := (Set.ext_iff.mp h p).mpr hp
    exact ⟨⟨p, hp'⟩, rfl⟩

/-- **(1) Existence at every level `S ≥ 2`.** -/
theorem exists_truncation_at_level_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S) :
    ∃ T' : HyperbolicTruncation H, ∃ hc : T'.count = T.count,
      (∀ (i : Fin T.count) (q : CuspHalfSpace),
        T'.cuspMap (Fin.cast hc.symm i) q =
          T.cuspMap i (q.1, halfSpaceOneLift (q.2.val 0 + S))) ∧
      (∀ (i : Fin T.count) (p : Torus) (v w : TangentSpace torusModel p),
        (T'.cusp (Fin.cast hc.symm i)).torusMetric.inner p v w =
          Real.exp (-S) * (T.cusp i).torusMetric.inner p v w) ∧
      range T'.inclusion = range T.inclusion ∪
        ⋃ i, T.cuspMap i '' (univ ×ˢ {u : EuclideanHalfSpace 1 | u.val 0 ≤ S}) :=
  ⟨truncationAtLevel_C1 T hS, rfl, fun i q => truncationAtLevel_cuspMap_C1 T hS i q,
    fun i p v w => truncationAtLevel_cusp_torusMetric_C1 T hS i p v w,
    truncationAtLevel_core_image_C1 T hS⟩

end GC.LongTime.Ch12
