import RicciFlower.GlobalGeometry.Myers.HopfRinow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Global-geometry Myers compactness interfaces

This parent module keeps the book-facing Myers compactness endpoints while the
actual metric-space wiring lives in `Myers/HopfRinow.lean`.

The top endpoint is now a checked consumer of two explicit Hopf-Rinow/Myers
frontiers:

* `Myers.exists_myersIndexData`, producing the per-geodesic index data;
* `Myers.properSpace_of_complete_riemannian`, producing metric properness.

The endpoint uses Mathlib's canonical Riemannian-distance setup: a single
`[EMetricSpace M]` whose `edist` is the Riemannian path-length distance of the
ambient `[RiemannianBundle …]` (`IsRiemannianManifold I M`).  The smooth metric
`g` feeding the index form is tied to that bundle by the coherence hypothesis
`hg`, so the diameter bound `edist ≤ π/√k` genuinely controls the manifold.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section RiemannianInterfaces

variable {M : Type*} [EMetricSpace M]
variable [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]
variable [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsRiemannianManifold I M]

/-- Bonnet-Myers/Myers compactness in dimension `n`.

The extra hypothesis `hn : 1 < n` is the dimension condition used by the
index-form diameter estimate, and `hg` records that the manifold's
extended distance is the Riemannian distance of the smooth metric `g`. -/
theorem myers_compactSpace_of_ricci_lower_bound
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    {n : Nat} {k : Real}
    (hn : 1 < n)
    (hdim : Module.finrank Real E = n)
    (hk : 0 < k)
    (hRic : RicciLowerBound (I := I) (M := M) g (Curvature.metricRicci (I := I) g)
      (((n - 1 : Nat) : Real) * k))
    (hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w) :
    CompactSpace M := by
  exact
    Myers.myers_compactSpace_of_ricci_lower_bound_metric
      (I := I) (M := M) g hn hdim hk hRic hg

/-- Three-dimensional Myers interface for Hamilton's positive-Ricci route:
`Ric >= 2 k g`, `k > 0`, completeness, and connectedness imply compactness. -/
theorem myers_compactSpace_three_of_ricci_lower_bound
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    {k : Real}
    (hdim : DimensionThree E)
    (hk : 0 < k)
    (hRic : RicciLowerBound (I := I) (M := M) g (Curvature.metricRicci (I := I) g) (2 * k))
    (hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w) :
    CompactSpace M := by
  exact
    myers_compactSpace_of_ricci_lower_bound
      (I := I) (M := M) g (n := 3) (k := k)
      (by norm_num) hdim hk (by simpa using hRic) hg

/-- Hamilton-tailored compactness interface: a complete connected 3D Einstein
limit with positive scalar curvature is compact.

The explicit `EinsteinScalarTrace` hypothesis is the future bridge from the
existing frame-based scalar trace realization to the positive Einstein
constant needed to feed Myers with `k = lambda / 2`. -/
theorem compactSpace_of_three_einstein_scalar_positive
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (scalar : M -> Real)
    {lambda : Real}
    (hdim : DimensionThree E)
    (hEinstein : EinsteinMetric (I := I) (M := M) g (Curvature.metricRicci (I := I) g) lambda)
    (hScalarTrace : EinsteinScalarTrace (E := E) scalar lambda)
    (hScalarPos : ScalarPositiveSomewhere scalar)
    (hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w) :
    CompactSpace M := by
  rcases hScalarPos with ⟨x, hxpos⟩
  have htrace := hScalarTrace x
  have hfin : Module.finrank Real E = 3 := by
    simpa [DimensionThree] using hdim
  have htrace3 : scalar x = (3 : Real) * lambda := by
    simpa [hfin] using htrace
  have hlambda_pos : 0 < lambda := by
    nlinarith
  have hk : 0 < lambda / 2 := by positivity
  have hRicLower :
      RicciLowerBound (I := I) (M := M) g (Curvature.metricRicci (I := I) g)
        (2 * (lambda / 2)) := by
    intro y v
    rw [hEinstein y v v]
    rw [show 2 * (lambda / 2) = lambda by ring]
  exact
    myers_compactSpace_three_of_ricci_lower_bound
      (I := I) (M := M) g (k := lambda / 2) hdim hk hRicLower hg

end RiemannianInterfaces

end GlobalGeometry
end RicciFlower
