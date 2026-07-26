import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion

/-!
# Reconciliation of the two Levi-Civita connection constructions

The project carries two independent constructions of the Levi-Civita connection of a
smooth Riemannian metric `g`:

* `LeviCivita g` (`Connection/LeviCivita/Defs.lean`) — the *stitched* connection, glued
  from the chart-local Christoffel connection `chartLeviCivita` over the good-set open
  cover.  This drives `ricciTensor`/`ricciEndo` and the chart bridges.
* `leviCivitaConnectionOfMetric g` (`Connection/LeviCivita/KoszulFormula.lean`, aliased
  `metricCov`) — the *direct* Koszul construction.  This drives `metricRicciAt`/`metricRm04`
  and hence the canonical curvature of a folder-level Ricci-flow `SolutionOn`.

Both are torsion-free and metric-compatible, so by Koszul uniqueness
(`koszul_levi_civita_unique_of_torsionFree_metricCompatible`, packaged as `LeviCivita_unique`)
they agree on every differentiable section.  This file records that reconciliation, which
was previously missing — the two curvature worlds (`ricciTensor` vs `metricRicciAt`) had no
bridge between them.

(Structure-level equality `LeviCivita g = leviCivitaConnectionOfMetric g` is *not* expected:
bundled `CovariantDerivative`s are unconstrained on non-differentiable sections, so they may
differ there.  Agreement on differentiable sections is the strongest identification, and is
all that curvature/Ricci depend on.)

The instance block matches `Connection/LeviCivita/Defs.lean`: both `[NormedSpace ℝ E]` and
`[InnerProductSpace ℝ E]` are declared, since the stitched-`LeviCivita`/tangent-bundle
machinery is registered against the explicit `NormedSpace` while the `leviCivitaConnectionOfMetric`
metric-compatibility facts use the inner product.
-/

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The two Levi-Civita constructions agree on differentiable sections.**

For every differentiable tangent-bundle section `σ`, point `x`, and tangent vector `v`,
the direct Koszul Levi-Civita derivative `leviCivitaConnectionOfMetric g` equals the
stitched `LeviCivita g`.  This is the bridge between the `metricRicciAt`/`metricRm04`
curvature world and the `ricciTensor`/`ricciEndo` curvature world. -/
theorem leviCivitaConnectionOfMetric_apply_eq_leviCivita
    (g : Measure.SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (leviCivitaConnectionOfMetric (I := I) g).toFun σ x v
      = (LeviCivita (I := I) g).toFun σ x v := by
  refine LeviCivita_unique g (leviCivitaConnectionOfMetric (I := I) g) ?_ ?_ hσ v
  · funext y
    exact (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g).2 y
  · -- Convert the `_gen` metric-compatibility (section-valued direction) into the
    -- Levi-Civita-layer `IsMetricCompatible` (arbitrary direction `v`), by picking a
    -- smooth section through `v`.
    intro Y Z x hY hZ _ w
    classical
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x w
    have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
    have h := metric_compatible_at_apply
      ((leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) x) X Y Z hX hY hZ
    rw [hXx] at h
    exact h

end Connection
end Integral
end DifferentialGeometry
