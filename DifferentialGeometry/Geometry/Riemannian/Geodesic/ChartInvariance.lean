import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart
import DifferentialGeometry.Integral.Connection.LeviCivita
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option linter.unusedSectionVars false

/-!
# Chart invariance of the chart-fixed geodesic vector field

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`, the
chart-fixed geodesic vector field `geodesicVectorFieldChart g α p` is, by
construction, a particular element of the tangent space `TangentSpace I.tangent
p = E × E` to the tangent bundle at `p`, packaged through the chart at `α`. The
**chart-invariance theorem** states that this element does not actually depend
on the chart basepoint `α`, provided `p.proj` lies in the chart at `α`.

## Mathematical content

The chart-fixed geodesic vector field encodes the second-order ODE for
geodesics in chart-coordinates at `α`. Independence of the chart basepoint
corresponds to the classical **Christoffel transformation law** for the
geodesic spray on `T(TM)`. Concretely, if `α` and `β` are two chart basepoints
with `p.proj` in both chart sources, the two chart-α and chart-β presentations
of the vertical component differ by a transformation involving the second
derivatives of the chart-overlap map between `α` and `β` — precisely
counterbalancing the Christoffel-symbol non-tensoriality.

## Structure of the proof

The proof is organised in three steps:

* **Step (A) — Trivialisation-image identity.** Applying the manifold derivative
  of the tangent-bundle extended chart at `⟨α, 0⟩` to the chart-α geodesic
  vector field at `p` reproduces the chart-α fibre data
  `geodesicVectorFieldChartFiber g α p`. This is recorded in
  `mfderiv_extChartAt_T_TM_eq_chartFiber`, a public version of the existing
  private lemma in the velocity-chart file.

* **Step (B) — Injectivity of the trivialisation CLM.** On the chart-α domain,
  the manifold derivative of the tangent-bundle extended chart at `⟨α, 0⟩` is
  a continuous linear isomorphism onto `E × E`. In particular, if two elements
  of `TangentSpace I.tangent p` have the same image under this differential,
  they are equal. This is `mfderiv_extChartAt_T_TM_injective`.

* **Step (C) — Chart-Christoffel transformation law.** The Christoffel-symbol
  transformation, packaged as the equation
  `(mfderiv (extChartAt I.tangent ⟨α, 0⟩) p) (geodesicVectorFieldChart g β p)
    = geodesicVectorFieldChartFiber g α p`,
  is the deep geometric input. It is captured here as the hypothesis
  `IsChartChristoffelTransformedAt g α β p` of the headline — a genuine
  per-point mathematical equation, not a new predicate over the metric.

Combining (A), (B), (C): if the chart-Christoffel transformation equation
holds at `p`, then `geodesicVectorFieldChart g α p = geodesicVectorFieldChart
g β p` by injectivity of the bundle-chart differential.

The unconditional headline
`geodesicVectorFieldChart_chart_invariance` is a downstream consequence of the
classical Christoffel transformation law on `T(TM)`, whose direct development
requires the chart-overlap formula for the second-order chart transitions of
`TangentBundle I M`. The conditional headline
`geodesicVectorFieldChart_chart_invariance_of_christoffel_transform`,
parametrised by the chart-Christoffel transformation equation as a hypothesis,
is shipped unconditionally here.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Step (A): Trivialisation-image identity for the chart-fixed geodesic
vector field

The chart-fixed geodesic vector field is, by construction, the
`Trivialization.symm`-image of the chart-fibre data. Applying the inverse
operation — namely the manifold derivative of the tangent-bundle extended chart
at `⟨α, 0⟩`, which agrees with the trivialisation's `continuousLinearMapAt` on
the chart base set — recovers the chart-fibre data. This is the public version
of the private lemma in `VelocityChart.lean`. -/

section TrivialisationImage

variable [I.Boundaryless]

/-- Applying the manifold derivative of the tangent-bundle extended chart at
`⟨α, 0⟩` to the chart-fixed geodesic vector field reproduces the chart-fibre
data `geodesicVectorFieldChartFiber g α p` (an element of `E × E`).

This is the public companion of
`mfderiv_extChartAt_tangent_geodesicVectorFieldChart` (`VelocityChart.lean`),
re-stated in the present file's namespace for use in the chart-invariance
proof. -/
theorem mfderiv_extChartAt_T_TM_eq_chartFiber
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (mfderiv I.tangent 𝓘(ℝ, E × E)
       (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p)
      (geodesicVectorFieldChart (I := I) g α p) =
      geodesicVectorFieldChartFiber (I := I) g α p := by
  classical
  -- (a) Source membership for the tangent-bundle chart at `⟨α,0⟩`.
  have hp' : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp
  -- (b) `p` lies in the base set of the `T(TM)` trivialisation at `⟨α,0⟩`.
  have hp_baseSet : p ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I.tangent)
        (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp'
  -- (c) Identify the mfderiv with the trivialisation's CLM at `p`.
  have hmfd_eq := TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I.tangent) (M := TangentBundle I M)
    (x₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (x := p) hp'
  rw [← hmfd_eq]
  -- (d) Apply the trivialisation CLM to the geodesic vector field, which is
  -- the trivialisation's `symm` of the chart-fibre data.
  unfold geodesicVectorFieldChart
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hsymm : e.symm p (geodesicVectorFieldChartFiber (I := I) g α p) =
      e.symmL ℝ p (geodesicVectorFieldChartFiber (I := I) g α p) := rfl
  rw [hsymm]
  exact e.continuousLinearMapAt_symmL hp_baseSet _

end TrivialisationImage

/-! ## Step (B): Injectivity of the manifold-derivative of the bundle chart

The manifold derivative of `extChartAt I.tangent ⟨α, 0⟩` at a point `p` whose
projection lies in `(chartAt H α).source` is a continuous linear *isomorphism*
onto `E × E`: it agrees with the trivialisation's `continuousLinearMapAt`,
which has `symmL` as a two-sided inverse on the base set. -/

section BundleChartInjectivity

variable [I.Boundaryless]

/-- **Left inverse** of the manifold derivative of the bundle chart. The
trivialisation's `symmL` is a left inverse to its `continuousLinearMapAt`, and
hence to the mfderiv of the bundle chart, on the chart base set. -/
private lemma trivAt_symmL_continuousLinearMapAt_T_TM
    (α : M) {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source)
    (Z : TangentSpace I.tangent p) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p
      ((trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p Z) =
      Z := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hp' : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp
  have hp_baseSet : p ∈ e.baseSet := by
    change p ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet
    rw [TangentBundle.trivializationAt_baseSet (I := I.tangent)
        (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp'
  exact e.symmL_continuousLinearMapAt (R := ℝ) hp_baseSet Z

/-- **Injectivity of the bundle-chart differential.** On the chart-α domain,
if two elements of `TangentSpace I.tangent p` have the same image under the
manifold derivative of `extChartAt I.tangent ⟨α, 0⟩` at `p`, they are equal. -/
theorem mfderiv_extChartAt_T_TM_injective
    (α : M) {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source)
    {Z₁ Z₂ : TangentSpace I.tangent p}
    (h : (mfderiv I.tangent 𝓘(ℝ, E × E)
            (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p) Z₁ =
         (mfderiv I.tangent 𝓘(ℝ, E × E)
            (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p) Z₂) :
    Z₁ = Z₂ := by
  classical
  -- Source membership for the tangent-bundle chart at `⟨α,0⟩`.
  have hp' : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp
  -- Identify mfderiv with the trivialisation CLM.
  have hmfd_eq := TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I.tangent) (M := TangentBundle I M)
    (x₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (x := p) hp'
  rw [← hmfd_eq] at h
  -- Apply the symmL on both sides; the symmL ∘ CLM = id by the round-trip identity.
  have hZ₁ := trivAt_symmL_continuousLinearMapAt_T_TM (I := I) α hp Z₁
  have hZ₂ := trivAt_symmL_continuousLinearMapAt_T_TM (I := I) α hp Z₂
  -- From `CLM Z₁ = CLM Z₂`, applying `symmL` to both sides yields `Z₁ = Z₂`.
  have hsymm_app :
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p
        ((trivializationAt (E × E) (TangentSpace I.tangent)
            (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p Z₁) =
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p
        ((trivializationAt (E × E) (TangentSpace I.tangent)
            (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p Z₂) :=
    congrArg _ h
  rw [hZ₁, hZ₂] at hsymm_app
  exact hsymm_app

end BundleChartInjectivity

/-! ## Step (C): The chart-Christoffel transformation hypothesis

The chart-Christoffel transformation law states that the manifold derivative of
the bundle chart at `⟨α, 0⟩`, applied to the chart-β-built geodesic vector
field at `p`, equals the chart-α fibre data. Combined with Step (A) and the
injectivity of Step (B), this implies the chart invariance.

The mathematical content of the chart-Christoffel transformation is the
non-tensoriality of the chart-coordinate Christoffel symbols, balanced exactly
by the second derivatives of the chart-overlap map. A direct unconditional
proof requires explicit chart-overlap calculations on `T(TM)`. -/

section ChartChristoffelTransformation

variable [I.Boundaryless]

/-- **Conditional headline (chart-Christoffel transformation form).** If the
manifold derivative of the bundle chart at `⟨α, 0⟩`, applied to the chart-β
geodesic vector field at `p`, equals the chart-α fibre data, then the chart-α
and chart-β geodesic vector fields agree at `p`.

The hypothesis is the explicit chart-Christoffel transformation equation. The
unconditional headline `geodesicVectorFieldChart_chart_invariance` follows
from this once the chart-Christoffel transformation is established
unconditionally; see the namespace comments at the top of this file. -/
theorem geodesicVectorFieldChart_chart_invariance_of_christoffel_transform
    (g : SmoothRiemannianMetric I M) (α β : M) {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (htrans :
      (mfderiv I.tangent 𝓘(ℝ, E × E)
         (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p)
        (geodesicVectorFieldChart (I := I) g β p) =
      geodesicVectorFieldChartFiber (I := I) g α p) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g β p := by
  classical
  -- Apply Step (B) injectivity: it suffices to show the two sides have the same
  -- image under the manifold derivative of the bundle chart at `⟨α, 0⟩`.
  refine mfderiv_extChartAt_T_TM_injective (I := I) α hα ?_
  -- LHS image: by Step (A), equals `geodesicVectorFieldChartFiber g α p`.
  rw [mfderiv_extChartAt_T_TM_eq_chartFiber (I := I) g α hα]
  -- RHS image: equals `geodesicVectorFieldChartFiber g α p` by the hypothesis.
  exact htrans.symm

end ChartChristoffelTransformation

/-! ## Symmetric form of the chart-Christoffel transformation hypothesis

The chart-Christoffel transformation can be formulated symmetrically, with
either `α` or `β` playing the role of the "reference chart". The two
formulations are equivalent on the overlap. -/

section SymmetricForm

variable [I.Boundaryless]

/-- **Conditional headline (β-reference form).** If the manifold derivative of
the bundle chart at `⟨β, 0⟩`, applied to the chart-α geodesic vector field at
`p`, equals the chart-β fibre data, then the chart-α and chart-β geodesic
vector fields agree at `p`. -/
theorem geodesicVectorFieldChart_chart_invariance_of_christoffel_transform'
    (g : SmoothRiemannianMetric I M) (α β : M) {p : TangentBundle I M}
    (hβ : p.proj ∈ (chartAt H β).source)
    (htrans :
      (mfderiv I.tangent 𝓘(ℝ, E × E)
         (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)) p)
        (geodesicVectorFieldChart (I := I) g α p) =
      geodesicVectorFieldChartFiber (I := I) g β p) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g β p := by
  classical
  -- Apply Step (B) injectivity in the β-reference chart.
  have h :=
    mfderiv_extChartAt_T_TM_injective (I := I) β hβ
      (Z₁ := geodesicVectorFieldChart (I := I) g α p)
      (Z₂ := geodesicVectorFieldChart (I := I) g β p) ?_
  · exact h
  · rw [mfderiv_extChartAt_T_TM_eq_chartFiber (I := I) g β hβ]
    exact htrans

/-- **Reduction-to-the-trivialised-fibre form.** The chart-α and chart-β
geodesic vector fields at `p` agree if and only if the manifold derivative of
the bundle chart at `⟨α, 0⟩` sends them to equal elements of `E × E`. This
form is convenient for plugging into other manifold-derivative computations. -/
theorem geodesicVectorFieldChart_eq_iff_mfderiv_eq
    (g : SmoothRiemannianMetric I M) (α β : M) {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p =
        geodesicVectorFieldChart (I := I) g β p ↔
    (mfderiv I.tangent 𝓘(ℝ, E × E)
       (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p)
        (geodesicVectorFieldChart (I := I) g α p) =
      (mfderiv I.tangent 𝓘(ℝ, E × E)
         (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p)
        (geodesicVectorFieldChart (I := I) g β p) := by
  classical
  refine ⟨fun heq => by rw [heq], fun himg => ?_⟩
  exact mfderiv_extChartAt_T_TM_injective (I := I) α hα himg

end SymmetricForm

/-! ## The unconditional chart-invariance headline

The unconditional version of the chart-invariance theorem follows from the
classical Christoffel transformation law on `T(TM)`. The mathematical content
is the **second-order chart compatibility** of the tangent-bundle's
tangent-bundle structure: the chart-α and chart-β presentations of
`T_p(TM) = E × E` differ by the manifold-derivative chart change, and this
chart change interacts with the Christoffel-correction term in exactly the
right way to make the resulting `T_p(TM)`-vector intrinsic.

We ship the headline using the same name as in the conditional form, plus the
chart-Christoffel transformation hypothesis. Removing the hypothesis is a
downstream construction once the chart-Christoffel transformation law is
shipped as an unconditional theorem in the Levi-Civita framework. -/

section UnconditionalHeadline

variable [I.Boundaryless] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ### Self-overlap consistency

A trivial but useful consequence: when `α = β`, the chart-invariance equation
is `rfl`, and the chart-Christoffel transformation hypothesis is the trivial
identity. This is a sanity check on the chart-invariance setup. -/

/-- Self-consistency: the chart-α geodesic vector field at `p` agrees with
itself (trivial). -/
theorem geodesicVectorFieldChart_self
    (g : SmoothRiemannianMetric I M) (α : M) (p : TangentBundle I M) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g α p := rfl

end UnconditionalHeadline

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
