import RicciFlower.GlobalGeometry.Lecture07.Geodesics

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Myers P1: minimizing-geodesic existence (Hopf-Rinow frontier)

In a complete, connected, finite-dimensional Riemannian manifold, any two points
`p q` are joined by a unit-speed smooth geodesic of length exactly `edist p q`.
This is the Hopf-Rinow minimizing-geodesic theorem, which is not available in
Mathlib, so `exists_minimizing_geodesic` is an honest analytic frontier.

Mathlib's `riemannianEDist` is the infimum over `C^1` paths
(`PathELength.lean`, line 208), and `IsRiemannianManifold.out` identifies the
ambient `edist` with this infimum.  The available theorem
`riemannianEDist_le_pathELength` gives only the upper bound by any fixed
smooth path length.  The missing content is that the infimum is achieved by a
smooth unit-speed geodesic under completeness and connectedness.

The output `MinimizingGeodesicData` is the geometric input shared by the parallel
ON frame producer (P2) and the second-variation producer: it records the
distance-realizing length `L` (so `ENNReal.ofReal L = edist p q`), the smooth
unit-speed curve `gamma` with `gamma 0 = p`, `gamma L = q`, and the unit-speed
identity in the index form's metric `g`.  The coherence hypothesis `hg` ties `g`
to the ambient bundle metric defining `edist`; it is what makes `hL_eq` honest.

The minimizing content is exactly `hL_eq` (length = distance); the per-variation
local-minimum used by the second-variation producer is derived later from
`hL_eq` together with the general fact `edist <= path length` for
`IsRiemannianManifold`.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter Lecture07
open scoped Manifold ContDiff Topology BigOperators ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The minimizing-geodesic data joining `p` and `q`: a unit-speed smooth curve
`gamma` from `p` to `q` whose length `L` realizes `edist p q`. -/
structure MinimizingGeodesicData
    (g : SmoothRiemannianMetric I M) (p q : M) where
  L : Real
  hL_pos : 0 < L
  hL_eq : ENNReal.ofReal L = edist p q
  gamma : Curve M
  hsmooth : ContMDiff 𝓘(Real, Real) I ∞ gamma
  hstart : gamma 0 = p
  hend : gamma L = q
  hunit : ∀ t, t ∈ Set.Icc (0 : Real) L ->
    g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1

/-- The Mathlib-supported half of the minimizing-geodesic distance equality:
any `C^1` unit-speed curve from `p` to `q` has endpoint distance at most its
time length.  The reverse inequality, realized by a geodesic minimizer, is the
Hopf-Rinow frontier in `exists_minimizing_geodesic`. -/
theorem edist_le_ofReal_pathLength_of_unitSpeed
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M)
    (hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w)
    {p q : M} {L : Real} (hL : 0 ≤ L) (gamma : Curve M)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    (hstart : gamma 0 = p) (hend : gamma L = q)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1) :
    edist p q ≤ ENNReal.ofReal L := by
  rw [IsRiemannianManifold.out (I := I) p q]
  refine le_trans
    (Manifold.riemannianEDist_le_pathELength (I := I) (γ := gamma) (a := 0) (b := L)
      (x := p) (y := q) hsmooth.contMDiffOn hstart hend hL) ?_
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have h_integrand :
      ∀ t ∈ Set.Icc (0 : ℝ) L, ‖mfderiv% gamma t 1‖ₑ = (1 : ℝ≥0∞) := by
    intro t ht
    let v : TangentSpace I (gamma t) := mfderiv% gamma t 1
    have hv_inner : (inner ℝ v v : ℝ) = 1 := by
      simpa [v, velocityAlong, curveVelocity] using
        (hg (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t)).trans
          (hunit t ht)
    have hv_norm_sq : ‖v‖ ^ 2 = (1 : ℝ) := by
      simpa [real_inner_self_eq_norm_sq] using hv_inner
    have hv_norm : ‖v‖ = (1 : ℝ) := by
      refine (sq_eq_sq₀ (norm_nonneg v) zero_le_one).mp ?_
      simp [hv_norm_sq]
    rw [show mfderiv% gamma t 1 = v from rfl, ← ofReal_norm_eq_enorm, hv_norm]
    simp
  apply le_of_eq
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) L, ‖mfderiv% gamma t 1‖ₑ)
        = ∫⁻ _t in Set.Icc (0 : ℝ) L, (1 : ℝ≥0∞) := by
          exact MeasureTheory.setLIntegral_congr_fun measurableSet_Icc h_integrand
    _ = MeasureTheory.volume (Set.Icc (0 : ℝ) L) := by
          simp
    _ = ENNReal.ofReal L := by
          rw [Real.volume_Icc]
          simp

/-- **Hopf-Rinow minimizing-geodesic frontier.**  A complete connected
Riemannian manifold has, for every pair of points, a distance-realizing
unit-speed geodesic.  Not available in Mathlib; left as a `sorry`. -/
theorem exists_minimizing_geodesic
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (_hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w)
    {p q : M} (_hpq : p ≠ q) :
    Nonempty (MinimizingGeodesicData (I := I) g p q) := by
  sorry

/-- **M5 geometric interface.**

Hopf-Rinow compactness: a complete connected finite-dimensional Riemannian
manifold whose extended diameter is bounded by a finite `C` is compact.

Mathematically this is the Hopf-Rinow theorem (completeness implies properness
for a finite-dimensional Riemannian manifold) combined with the fact that a
bounded proper space is compact.  Mathlib has neither Hopf-Rinow nor the
Riemannian properness statement, so this is left as an honest frontier. -/
theorem compactSpace_of_complete_riemannian_of_ediam_le
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    {C : ℝ≥0∞} (_hC : C ≠ ⊤) (_hbdd : ∀ x y : M, edist x y ≤ C) :
    CompactSpace M := by
  sorry

end GlobalGeometry
end RicciFlower
