import DifferentialGeometry.Integral.Connection.LeviCivitaChartTorsion

/-!
# The metric Christoffel-correction at the basepoint

The CLM-valued metric Christoffel correction `christoffelCorrection g α x Y v`
(`LeviCivitaChartLocal.lean`) is the chart-`α` Levi-Civita symbol contracted against the
section's `α`-trivialised value `Y : E` (second slot) and the tangent-vector argument
`v : TangentSpace I x` (first slot, acting through `trivToE α x v ∈ E`):

  `christoffelCorrection g α x Y v
     = ∑ᵢⱼₖ (b.repr (trivToE α x v))ᵢ · (b.repr Y)ⱼ · Γᵏᵢⱼ(g, α)(φ x) • eₖ`,

where `Γᵏᵢⱼ(g, α)` is the *metric* chart-Christoffel symbol `chartChristoffel`, built from `g`
(`Geometry/Hessian.lean`).

This file isolates the value of this correction at the **basepoint** `x = α`, where the
moving trivialisation degenerates to the identity (`trivToE α α = id` on the chart base set).
There the correction becomes a **symmetric bilinear** contraction of two *raw* model vectors:

  `christoffelCorrection g α α Y w
     = ∑ᵢⱼₖ (b.repr w)ᵢ · (b.repr Y)ⱼ · Γᵏᵢⱼ(g, α)(φ α) • eₖ`              (`christoffelCorrection_basepoint_apply`)

and, by the torsion-free symmetry of `Γ` in its lower indices (`chartChristoffel_symm`),

  `christoffelCorrection g α α Y w = christoffelCorrection g α α w Y`         (`christoffelCorrection_basepoint_symm`).

## Why this is the genuinely metric-dependent building block

The covariant variational identity for the orbit pushforward — `D_s (dΦ_s v) = -∇_{dΦ_s v} X`
— differs from the *Lie-type / flat* derivative of the pushforward by the metric Christoffel
contraction of the orbit velocity (the field value at the basepoint) with the pushforward
slot.  At the basepoint `α := Φ_fam t x`, that contraction is *exactly*
`christoffelCorrection g α α (X̃_α α) w` — the metric term appearing in the connector's
`hsplit` value equation
(`SmoothInSpace/VariationalLiftManifoldFlow.lean`).

`christoffelCorrection_basepoint_symm` records the slot symmetry of that metric term — the
torsion-free property that is the chart-coordinate manifestation of metric-compatibility's
companion (the Levi-Civita connection is symmetric).  It is the `g`-referencing fact the
flat-to-covariant reconciliation uses to commute the field slot and the pushforward slot in
the Christoffel contraction.

The basepoint formula is fully discharged here from `christoffelCorrection_apply` and the
self-trivialisation identity `trivToE α α = id`; the symmetry is the basepoint instance of
`christoffelCorrection_symm_cancel` (the torsion-free Christoffel symmetry,
`LeviCivitaChartTorsion.lean`).  No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style
hypothesis, no hypothesis-packaging: the conclusions are `E`-equations derived from the
Christoffel formula, never an identity asserted as a hypothesis.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Self-trivialisation at the basepoint is the identity.**

The chart trivialisation CLM at `(α, α)` is the identity on the fibre `TangentSpace I α = E`:
`trivToE α α v = v`.  This is the self-`coordChange` triviality of the tangent-bundle core,
evaluated at `α`, routed through `continuousLinearMapAt_trivializationAt_eq_core`. -/
lemma trivToE_basepoint (α : M) (v : TangentSpace I α) :
    trivToE (I := I) α α v = v := by
  classical
  have hcore : trivToE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

/-- **The metric Christoffel correction at the basepoint, as a raw bilinear contraction.**

At `x = α`, the moving trivialisation is the identity (`trivToE α α = id`), so the
Christoffel-correction CLM applied to a tangent vector `w : TangentSpace I α = E` reads as the
symmetric metric chart-Christoffel contraction of the two *raw* model vectors `w` (first slot)
and `Y` (second slot):

  `christoffelCorrection g α α Y w
     = ∑ᵢⱼₖ (b.repr w)ᵢ · (b.repr Y)ⱼ · Γᵏᵢⱼ(g, α)(φ α) • eₖ`.

Genuine content: `christoffelCorrection_apply` followed by the basepoint simplification
`trivToE α α w = w` (`trivToE_basepoint`).  The conclusion is an `E`-equation, never a target
identity. -/
theorem christoffelCorrection_basepoint_apply
    (g : SmoothRiemannianMetric I M) (α : M) (Y : E) (w : TangentSpace I α) :
    christoffelCorrection (I := I) g α α Y w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr w) i *
                ((chartModelBasis E).repr Y) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α α)) •
              (chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply]
  rw [trivToE_basepoint (I := I) α w]

/-- **Slot symmetry of the metric Christoffel correction at the basepoint.**

At the basepoint `α`, where the moving trivialisation is the identity, the metric
Christoffel correction is symmetric under exchange of its section slot `Y` and its
tangent-vector slot `w` (both raw model vectors):

  `christoffelCorrection g α α Y w = christoffelCorrection g α α w Y`.

This is the chart-coordinate manifestation of the torsion-free (symmetric) property of the
Levi-Civita connection: the metric chart-Christoffel symbol `Γᵏᵢⱼ` is symmetric in its lower
indices (`chartChristoffel_symm`).  The proof is the basepoint instance of
`christoffelCorrection_symm_cancel` (the general torsion-free Christoffel symmetry), with the
self-trivialisations `trivToE α α` discharged by `trivToE_basepoint`.

This slot symmetry is the `g`-referencing fact the flat-to-covariant reconciliation of the
orbit variational derivative uses to commute the field (orbit-velocity) slot with the
pushforward slot in the Christoffel contraction.  No hypothesis-packaging: the conclusion is an
`E`-equation derived from the Christoffel symmetry, not an asserted hypothesis. -/
theorem christoffelCorrection_basepoint_symm
    (g : SmoothRiemannianMetric I M) (α : M) (Y w : TangentSpace I α) :
    christoffelCorrection (I := I) g α α Y w =
      christoffelCorrection (I := I) g α α w Y := by
  classical
  have hsym := christoffelCorrection_symm_cancel (I := I) g α α w Y
  rw [trivToE_basepoint (I := I) α Y, trivToE_basepoint (I := I) α w] at hsym
  exact hsym

end Connection
end Integral
end DifferentialGeometry
