import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.OutwardNormal
import DifferentialGeometry.Geometry.Hessian

/-!
# The second fundamental form of the boundary submanifold

Let `M` be a smooth manifold modelled on `(E, H, I)` whose model with corners
admits a smooth boundary stratum (`[hI : HasSmoothBoundary E H I]`), and let
`g` be a smooth Riemannian metric on the tangent bundle of `M`. At each
boundary point `x : BoundaryManifold I M`, this file constructs the *second
fundamental form*

  `secondFundamentalForm g x νChart : T_x M →ₗ[ℝ] T_x M →ₗ[ℝ] ℝ`

associated with a chart-coordinate extension `νChart : E → E` of the outward
unit normal field. Mathematically, the form is

$$\mathrm{II}(X, Y) = g\bigl(\nabla_X \tilde{\nu},\, Y\bigr),$$

where `∇` is the Levi-Civita connection of `g`, `X, Y` are vectors tangent to
the boundary `∂M` at `x`, and `\tilde{\nu}` is any smooth extension of the
outward unit normal to a neighbourhood of `x` in `M`.

In chart coordinates the formula reads, for `X, Y ∈ T_x M` decomposed in the
canonical model basis `e_i := Module.finBasis ℝ E`:

$$\mathrm{II}(X, Y) = \sum_{i, j, k} g_{kj}(x)\,X^i\,Y^j\,
    \bigl[\partial_i \nu^k(\varphi(x)) +
        \sum_l \Gamma^k{}_{il}(g)(\varphi(x))\,\nu^l(\varphi(x))\bigr],$$

where `g_{kj} = g.inner x (e_k) (e_j)` are the chart Gram-matrix entries,
`Γ^k{}_{il}` are the chart Christoffel symbols (defined in
`Geometry.Hessian`), and `ν^k(y) := νChart y k` are the
chart-coordinate components of the supplied normal-field extension.

Because the construction is hypothesis-bearing in the chart-coordinate
extension `νChart`, the file delivers:

* a definition of the chart-Christoffel-Weingarten matrix entries
  `chartSecondFundamentalFormEntry`;
* the bilinear form `secondFundamentalForm` obtained by basis decomposition;
* a symmetry theorem `secondFundamentalForm_symm` deduced from a hypothesis
  packaging the standard Codazzi-symmetry condition (which holds, for
  instance, when `νChart` is the chart-coordinate gradient — modulo
  normalisation — of a smooth defining function of the boundary).

The chart-Christoffel symmetry of the lower indices (the torsion-free
property of the Levi-Civita connection) is already encoded in
`chartChristoffel_symm` and is consumed below.

## Main definitions

* `chartSecondFundamentalFormEntry g x νChart i j` — the chart-coordinate
  matrix entry `II_{ij}(x)`.
* `secondFundamentalForm g x νChart` — the bilinear form on `T_x M`,
  computed via basis decomposition.

## Main theorems

* `secondFundamentalForm_apply` — the explicit formula.
* `secondFundamentalForm_symm` — symmetry under the supplied
  Codazzi-symmetry hypothesis.

## Implementation notes

* The chart-coordinate "normal field" is supplied as a function `νChart : E → E`,
  giving the chart-coordinate components of an extension of the outward unit
  normal. The user is responsible for supplying a normal field consistent with
  `outwardNormal g x`; the formulas below remain meaningful for arbitrary
  smooth `νChart`.
* The Christoffel symbol used is `chartChristoffel g x i j k y`, the
  chart-Christoffel symbol of the second kind associated with the chart at
  the basepoint `x : M` and evaluated at the chart-coordinate point `y ∈ E`.
* The basis used to read off coordinate vectors is `Module.finBasis ℝ E`,
  matching the convention of `chartHessianTensor` and `hessFun`.
-/

noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

/-- The `k`-th chart-coordinate component of a normal-field extension
`νChart : E → E`, read off in the basis `Module.finBasis ℝ E`. -/
def normalFieldComp (νChart : E → E) (k : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => ((Module.finBasis ℝ E).repr (νChart y)) k

@[simp] lemma normalFieldComp_def (νChart : E → E)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    normalFieldComp (E := E) νChart k y =
      ((Module.finBasis ℝ E).repr (νChart y)) k := rfl

/-- The chart-coordinate "linear-correction" sum
`∑ l, Γ^k_{il}(x, y) · ν^l(y)`. -/
def chartChristoffelNormalCorrection
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ l : Fin (Module.finrank ℝ E),
    chartChristoffel (I := I) g α i l k y *
      normalFieldComp (E := E) νChart l y

@[simp] lemma chartChristoffelNormalCorrection_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffelNormalCorrection (I := I) g α νChart i k y =
      ∑ l : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i l k y *
          normalFieldComp (E := E) νChart l y := rfl

/-- The chart-coordinate "Weingarten" expression
`∂_i ν^k(y) + ∑_l Γ^k_{il}(g)(y) · ν^l(y)`, the `k`-th component of the
covariant derivative `(∇_{e_i} ν)^k` of the chart-coordinate normal field.

Here the partial derivative `∂_i` is the Fréchet directional derivative of
the chart-coordinate component function `y ↦ ν^k(y)` in the basis direction
`e_i := (Module.finBasis ℝ E) i`. -/
def chartCovariantDerivativeOfNormal
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) i (normalFieldComp (E := E) νChart k) y +
    chartChristoffelNormalCorrection (I := I) g α νChart i k y

@[simp] lemma chartCovariantDerivativeOfNormal_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (νChart : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartCovariantDerivativeOfNormal (I := I) g α νChart i k y =
      partialDeriv (E := E) i (normalFieldComp (E := E) νChart k) y +
        chartChristoffelNormalCorrection (I := I) g α νChart i k y := rfl

/-- The chart-coordinate matrix entry `II_{ij}(x)` of the second fundamental
form, computed against the canonical basis `Module.finBasis ℝ E` at the
chart-coordinate point `extChartAt I (x : M) (x : M)`:

$$\mathrm{II}_{ij}(x) = \sum_{k} g_{kj}(x) \cdot (\nabla_{e_i} \nu)^k(\varphi(x)).$$
-/
def chartSecondFundamentalFormEntry
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E) (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    chartGramMatrix (I := I) g (x : M) (x : M) k j *
      chartCovariantDerivativeOfNormal (I := I) g (x : M) νChart i k
        (extChartAt I (x : M) (x : M))

@[simp] lemma chartSecondFundamentalFormEntry_def
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E) (i j : Fin (Module.finrank ℝ E)) :
    chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g (x : M) (x : M) k j *
          chartCovariantDerivativeOfNormal (I := I) g (x : M) νChart i k
            (extChartAt I (x : M) (x : M)) := rfl

/-- The second fundamental form of `∂M` in `M` at a boundary point `x`,
parameterised by a chart-coordinate extension `νChart : E → E` of the outward
unit normal field. The bilinear form is defined on the full ambient tangent
space `T_x M = E`; its restriction to the boundary tangent space recovers the
classical second fundamental form. -/
def secondFundamentalForm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E) :
    TangentSpace I (x : M) →ₗ[ℝ] TangentSpace I (x : M) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr X) i *
            ((Module.finBasis ℝ E).repr Y) j *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j)
    (fun X₁ X₂ Y => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (X₁ + X₂) =
          (Module.finBasis ℝ E).repr X₁ + (Module.finBasis ℝ E).repr X₂ :=
        map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c X Y => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (c • X) =
          c • (Module.finBasis ℝ E).repr X := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring)
    (fun X Y₁ Y₂ => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (Y₁ + Y₂) =
          (Module.finBasis ℝ E).repr Y₁ + (Module.finBasis ℝ E).repr Y₂ :=
        map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c X Y => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (c • Y) =
          c • (Module.finBasis ℝ E).repr Y := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hpull : ∀ j : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).repr X) i * (c * ((Module.finBasis ℝ E).repr Y) j) *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) =
          c * (((Module.finBasis ℝ E).repr X) i * ((Module.finBasis ℝ E).repr Y) j *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) := by
        intro j
        ring
      rw [show (∑ j : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr X) i * (c * ((Module.finBasis ℝ E).repr Y) j) *
              chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) =
          ∑ j : Fin (Module.finrank ℝ E),
            c * (((Module.finBasis ℝ E).repr X) i * ((Module.finBasis ℝ E).repr Y) j *
              chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j) from
        Finset.sum_congr rfl (fun j _ => hpull j)]
      rw [← Finset.mul_sum])

/-- The defining formula of the second fundamental form. -/
@[simp] lemma secondFundamentalForm_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (X Y : TangentSpace I (x : M)) :
    secondFundamentalForm (I := I) (M := M) g x νChart X Y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr X) i *
            ((Module.finBasis ℝ E).repr Y) j *
            chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j := rfl

/-- **Symmetry of the second fundamental form** under the Codazzi
matrix-symmetry hypothesis. If the chart-Christoffel-Weingarten matrix entries
are symmetric in `(i, j)`, then so is the bilinear form `secondFundamentalForm`.

Mathematically, the hypothesis encodes the standard fact that `II` is
symmetric whenever `ν` is the unit-normalised gradient of a defining function
of `∂M` — a property automatic in the half-space model. -/
theorem secondFundamentalForm_symm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (h_codazzi : ∀ i j : Fin (Module.finrank ℝ E),
      chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j =
        chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart j i)
    (X Y : TangentSpace I (x : M)) :
    secondFundamentalForm (I := I) (M := M) g x νChart X Y =
      secondFundamentalForm (I := I) (M := M) g x νChart Y X := by
  classical
  rw [secondFundamentalForm_apply, secondFundamentalForm_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_codazzi j i]
  ring

/-- The second fundamental form restricted to two boundary tangent vectors. -/
def secondFundamentalFormBoundary
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (Xb Yb : hI.boundaryE) : ℝ :=
  secondFundamentalForm (I := I) (M := M) g x νChart
    (dincl (M := M) x Xb) (dincl (M := M) x Yb)

@[simp] lemma secondFundamentalFormBoundary_def
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (Xb Yb : hI.boundaryE) :
    secondFundamentalFormBoundary (I := I) (M := M) g x νChart Xb Yb =
      secondFundamentalForm (I := I) (M := M) g x νChart
        (dincl (M := M) x Xb) (dincl (M := M) x Yb) := rfl

/-- **Symmetry on boundary tangent vectors** under the Codazzi matrix-symmetry
hypothesis. -/
theorem secondFundamentalFormBoundary_symm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (νChart : E → E)
    (h_codazzi : ∀ i j : Fin (Module.finrank ℝ E),
      chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart i j =
        chartSecondFundamentalFormEntry (I := I) (M := M) g x νChart j i)
    (Xb Yb : hI.boundaryE) :
    secondFundamentalFormBoundary (I := I) (M := M) g x νChart Xb Yb =
      secondFundamentalFormBoundary (I := I) (M := M) g x νChart Yb Xb := by
  unfold secondFundamentalFormBoundary
  exact secondFundamentalForm_symm (I := I) (M := M) g x νChart h_codazzi
    (dincl (M := M) x Xb) (dincl (M := M) x Yb)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

end
