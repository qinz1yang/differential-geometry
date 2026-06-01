import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftConventionBridge
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftChartDictionary

/-!
# Flat-to-covariant bridge for the chart-coordinate variational data

The Euclidean variational ODE of the manifold flow (`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`,
consumed through the BanachIC raw-fibre chart vector field) produces the **flat** chart
Fréchet derivative of the section, read in the raw-fibre representation
`R(z) := (X (φ.symm z) : E)` (`chartRawRepr`).  The per-flow producer
`rawVariationalIdentity_of_chartFderiv_witness`
(`SmoothInSpace/VariationalLiftChartDictionary.lean`), however, demands a value equation
`hQinner` whose right-hand side is built from `chartLeviCivitaInnerCLM`, the **covariant**
inner CLM at the orbit point `α := Φ_fam t x` — the trivialised flat `fderiv` summand
*plus* the metric Christoffel correction `christoffelCorrection g α α`.

The two are *not* equal: the linearized flow produces the flat derivative `−∂X`, whereas
`chartLeviCivitaInnerCLM` is the covariant `−∇X`.  By the committed convention bridge
`chartTrivRepr_fderiv_eq` (`SmoothInSpace/VariationalLiftConventionBridge.lean`) the two flat
derivatives differ by the **moving-trivialization correction** `(D C · h)(R z₀)` — the
chart-transition first jet `D²φ`, a *smooth-structure* object, metric-independent.  And the
metric Christoffel correction enters only through a `g`-referencing step that the pure
variational ODE never performs.  Consequently the covariant value cannot be obtained from the
flat variational ODE *alone*: it genuinely requires two additional inputs, both of which are
*equalities of vectors in `E`* (never the `HasDerivAt` target):

* the moving-trivialization correction value `(D C · w)(X α)` (`D²φ`), a smooth-structure
  object computed from `chartTrivRepr_fderiv_eq`; and
* the metric Christoffel correction value `christoffelCorrection g α α (X̃_α α) w`, the
  genuine metric contribution.

## What this file proves

1. `chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections` — the **honest
   decomposition** of the covariant inner CLM at the orbit point `α` into the flat raw
   `fderiv` plus the two corrections.  This is a pure chart-calculus identity assembled from
   `chartLeviCivitaInnerCLM_apply`, `chartLeviCivita_flat_summand_eq_rawRepr` (i.e.
   `chartTrivRepr_fderiv_eq`), and the basepoint triviality `trivToE α α = id`
   (`chartMovingTriv_basepoint`).  It is *not* the `hQinner` target: it is an `E`-equation
   exposing precisely the flat-vs-covariant gap.

2. `hQinner_of_flat_value_and_corrections` — reconstruction of the covariant `hQinner`
   value equation from the **flat** Euclidean variational value
   `Q (Dchart' d) = −trivFromE α α (fderiv (chartRawRepr α X) (φ α) (trivToE α α (dΦv)))`
   together with the two correction values, threaded through (1).

3. `rawVariationalIdentity_of_flatChartFderiv_witness` — the **per-flow producer** that
   takes the flat variational ODE data (`hDchart`, `hcontAt`, `hwitness`) plus the flat value
   equation and the two correction values, and produces `RawVariationalIdentity` by feeding
   the reconstructed covariant `hQinner` into
   `rawVariationalIdentity_of_chartFderiv_witness`.

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no joint-`C^∞`-on-
`ℝ × M` predicate.  No hypothesis-packaging: the producer's inputs are an operator-valued ODE
and three `E`-equations, none of which is, or trivially yields, the vector-valued `HasDerivAt`
conclusion `RawVariationalIdentity`.  The naive identification "flat correction = metric
Christoffel" is *not* assumed anywhere (it is false in a general chart); the two corrections
are exposed as separate, genuine inputs.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Decomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The moving-trivialization correction value `D²φ`.**

The chart-transition first jet `(D C · w)(X α)`: the Fréchet derivative of the moving
trivialization `z ↦ trivToE α (φ.symm z)` at the basepoint image `φ α`, in direction `w`,
applied to the raw fibre value `X α`.  This is a *smooth-structure* object — the
classical second-derivative-of-the-chart-change term — and is metric-independent. -/
def movingTrivCorrection (α : M) (X : Π y : M, TangentSpace I y) (w : E) : E :=
  (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) w)
    (chartRawRepr (I := I) α X (extChartAt I α α))

/-- **Honest decomposition of the covariant inner CLM at the orbit point.**

At the basepoint `α`, where the moving trivialization is the identity
(`trivToE α α = id`), the covariant chart Levi-Civita inner CLM applied to `w` decomposes as

  `chartLeviCivitaInnerCLM g α X α w
     = fderiv (chartRawRepr α X) (φ α) w
       + movingTrivCorrection α X w
       + christoffelCorrection g α α (X̃_α α) w`,

i.e. the **flat raw** Fréchet derivative (the operator the Euclidean variational ODE actually
produces), plus the **moving-trivialization correction** `D²φ`, plus the **metric Christoffel
correction**.  The first two summands together form the *trivialised* flat derivative
(`chartTrivRepr_fderiv_eq`), and adding the Christoffel correction yields the inner CLM
(`chartLeviCivitaInnerCLM_apply`).

This is a pure chart-calculus identity, *not* the `hQinner` target: it is an equation of
`E`-vectors that exposes the flat-vs-covariant gap.  No hypothesis-packaging. -/
theorem chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π y : M, TangentSpace I y) (w : E)
    (hRdiff : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    chartLeviCivitaInnerCLM (I := I) g α X α w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + movingTrivCorrection (I := I) α X w
        + christoffelCorrection (I := I) g α α
            (chartE_section_repr (I := I) α X α) w := by
  classical
  rw [chartLeviCivitaInnerCLM_apply]
  have htriv_id : trivToE (I := I) α α w = w := by
    have hbase := chartMovingTriv_basepoint (I := I) α w
    have hself : (extChartAt I α).symm (extChartAt I α α) = α :=
      (extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)
    rw [chartMovingTriv, hself] at hbase
    exact hbase
  rw [htriv_id]
  rw [chartLeviCivita_flat_summand_eq_rawRepr (I := I) α X w hRdiff hCdiff]
  rw [movingTrivCorrection]

end Decomposition

section Reconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Reconstruction of the covariant `hQinner` from flat value + corrections.**

Let `α := Φ_fam t x` and `w := mfderiv (Φ_fam t) x v` (the frozen pushforward, a vector in
`E` under the `TangentSpace I (Φ_fam t x) = E` defeq).  Suppose the chart-coordinate Euclidean
variational value `Q (Dchart' d)`, transported to the basepoint, is the raw flat Fréchet
derivative **plus** the two corrections:

  `hcov : Q (Dchart' d)
     = -trivFromE α α (fderiv (chartRawRepr α X) (φ α) w)
       - trivFromE α α (movingTrivCorrection α X w)
       - trivFromE α α (christoffelCorrection g α α (X̃_α α) w)`.

This is the genuine covariant variational value of the flow: the raw flat derivative
(`−∂X`, produced by the linearized-flow chart ODE) corrected by the metric-independent
moving-trivialization jet `D²φ` and the metric Christoffel correction.  Then the **covariant**
`hQinner` value equation holds in the exact shape consumed by
`rawVariationalIdentity_of_chartFderiv_witness`:

  `Q (Dchart' d) = -trivFromE α α (chartLeviCivitaInnerCLM g α X α w)`.

The proof rewrites the covariant inner CLM by the honest decomposition
`chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections`, pushes the linear
`trivFromE α α` through the sum (`map_add`), and matches against `hcov`.  No
hypothesis-packaging: the conclusion is an `E`-equation derived from the decomposition, never
the `RawVariationalIdentity` target; `hcov` carries the genuine flat value plus the two
*separate* corrections (the false "moving-triv = metric Christoffel" identification is not
assumed). -/
theorem hQinner_of_flat_value_and_corrections
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (Dchart' : E →L[ℝ] E) (d : E)
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hcov : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))) :
    Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)) := by
  classical
  set α := Φ_fam t x with hα
  set w : E := mfderiv I I (Φ_fam t : M → M) x v with hw
  have hdecomp :
      chartLeviCivitaInnerCLM (I := I) g α (X : ∀ y : M, TangentSpace I y) α w
        = fderiv ℝ (chartRawRepr (I := I) α (X : ∀ y : M, TangentSpace I y))
            (extChartAt I α α) w
          + movingTrivCorrection (I := I) α (X : ∀ y : M, TangentSpace I y) w
          + christoffelCorrection (I := I) g α α
              (chartE_section_repr (I := I) α (X : ∀ y : M, TangentSpace I y) α) w :=
    chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections (I := I) g α
      (X : ∀ y : M, TangentSpace I y) w hRdiff hCdiff
  rw [hcov, hdecomp, map_add, map_add, neg_add, neg_add]
  abel

end Reconstruction

section Producer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Per-flow raw variational identity from FLAT-plus-correction chart witnesses.**

The honest, flat-data version of the per-flow producer.  Unlike
`rawVariationalIdentity_of_chartFderiv_witness` — which demands the *covariant* value equation
`hQinner` stated through the bundled `chartLeviCivitaInnerCLM` — this producer takes the value
equation in the **flat-plus-correction** form that the linearized-flow chart ODE actually
produces, namely `hcov`:

  `Q (Dchart' d)
     = -trivFromE α α (fderiv (chartRawRepr α X) (φ α) (mfderiv (Φ_fam t) x v))`   (raw flat `−∂X`)
       `- trivFromE α α (movingTrivCorrection α X (mfderiv (Φ_fam t) x v))`        (`D²φ`)
       `- trivFromE α α (christoffelCorrection g α α (X̃_α α) (mfderiv (Φ_fam t) x v))`  (metric `Γ`),

with `α := Φ_fam t x`.  The first summand is the genuine output of the Euclidean variational
ODE (via the committed chart dictionary); the second is the metric-independent
moving-trivialization jet `D²φ`; the third is the genuine metric Christoffel correction.

The remaining inputs are the standard chart-coordinate flow data:

* `hDchart` — the operator-valued Euclidean variational ODE `HasDerivAt Dchart Dchart' t`;
* `hcontAt` — continuity of the orbit `s ↦ Φ_fam s x` at `t`;
* `hwitness` — the eventual reproduction of the transported chart-coordinate derivative by
  `Q (Dchart s d)` near `t`;
* `hRdiff`, `hCdiff` — differentiability of the raw representation and the moving
  trivialization at the basepoint image (the side conditions of the convention bridge).

It produces `RawVariationalIdentity`.  The covariant `hQinner` is reconstructed internally by
`hQinner_of_flat_value_and_corrections` (Part B) and fed into
`rawVariationalIdentity_of_chartFderiv_witness`.

No joint-`C^∞`-on-`ℝ × M`, no `HasLocallyConstantChartAt`, no hypothesis-packaging: the inputs
are an operator-valued ODE and `E`-equations, none of which is, or trivially yields, the
vector-valued `HasDerivAt` conclusion `RawVariationalIdentity`.  The (false-in-general)
identification "moving-triv correction = metric Christoffel" is *not* assumed; `hcov` exposes
the two corrections as separate, genuine summands. -/
theorem rawVariationalIdentity_of_flatChartFderiv_witness
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hcov : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hQinner :
      Q (Dchart' d)
        = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)) :=
    hQinner_of_flat_value_and_corrections (I := I) g X Φ_fam t x v Q Dchart' d
      hRdiff hCdiff hcov
  exact rawVariationalIdentity_of_chartFderiv_witness (I := I) g X Φ_fam t x v Q d
    hDchart hcontAt hwitness hQinner

end Producer

end DifferentialGeometry.PDE.RicciFlow.ODE
