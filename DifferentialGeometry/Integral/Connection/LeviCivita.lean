import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.Integral.Connection.Koszul
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.LeviCivitaChartTorsion
import DifferentialGeometry.Integral.Connection.LeviCivitaChartMetric
import DifferentialGeometry.Integral.Connection.LeviCivitaChartSmooth

/-!
# The Levi-Civita covariant derivative on a smooth Riemannian manifold

Given a smooth Riemannian metric `g : SmoothRiemannianMetric I M` on a smooth manifold
`M` modelled on a finite-dimensional inner product space `E`, this file constructs the
**globally defined** Levi-Civita covariant derivative `LeviCivita g :
CovariantDerivative I E (TangentSpace I)` on the tangent bundle of `M`, and verifies
its three characterising properties:

* `LeviCivita_torsion_eq_zero g : (LeviCivita g).torsion = 0`,
* `LeviCivita_isMetricCompatible g : IsMetricCompatible (LeviCivita g) g`,
* `ContMDiffCovariantDerivative (LeviCivita g) ∞`.

A pointwise uniqueness theorem on differentiable inputs is also provided:

* `LeviCivita_unique` — any other torsion-free metric-compatible covariant derivative
  agrees with `LeviCivita g` on differentiable sections (pointwise).

## Construction

The chart-local Levi-Civita covariant derivative `chartLeviCivita g α` is defined for
each base point `α : M` on its open *good set* `chartLeviCivitaGoodSet α`, and
satisfies on that set the Mathlib `IsCovariantDerivativeOn` axioms together with the
torsion-free, metric-compatibility, and smoothness properties.

Because every point `x : M` lies in `chartLeviCivitaGoodSet x` (under the standing
boundaryless-manifold hypothesis, which guarantees the chart-target interior
membership at the basepoint), the family `{chartLeviCivitaGoodSet α | α : M}` forms an
open cover of `M`. The Koszul identity (uniqueness of the torsion-free
metric-compatible covariant derivative on differentiable sections) shows that any two
chart-local Levi-Civita derivatives agree on the overlap of their good sets. The
pointwise stitch
$$
  (\nabla_v \sigma)(x) := \mathrm{chartLeviCivita}\,g\,x\,\sigma\,x\,v
$$
is therefore independent (on differentiable inputs) of the choice of base point, and
yields a global covariant derivative.

## Hypotheses

In addition to the standing manifold + Riemannian-metric hypotheses, this file
requires:

* `[BoundarylessManifold I M]` — every point of `M` is a manifold-interior point. This
  is needed to verify `α ∈ chartLeviCivitaGoodSet α` for every `α : M` (the third
  conjunct, `extChartAt I α α ∈ interior ((extChartAt I α).target : Set E)`, is the
  defining condition of an interior point), so that the family of chart-local good
  sets covers `M`.

* `[T2Space M]` — needed to invoke `ContMDiffSection.exists_eq_at` (extension of an
  arbitrary fibre vector to a smooth global tangent section), which underlies the
  Koszul-uniqueness step that identifies overlapping chart-local Levi-Civita
  derivatives on differentiable sections.

* `[SigmaCompactSpace M]` — propagated from the `Koszul` file; required at section
  scope to access `koszul_local_uniqueness` and `koszul_levi_civita_unique_of_torsionFree_metricCompatible`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- Every point `α : M` lies in its own chart-local good set
`chartLeviCivitaGoodSet α`. The first two conjuncts (membership in the chart source
and in the trivialization base set at `α`) are the defining "centred-at-`α`"
properties; the third conjunct, `extChartAt I α α ∈ interior ((extChartAt I α).target
: Set E)`, follows from `[BoundarylessManifold I M]` via the equivalence
`isInteriorPoint_iff` and `BoundarylessManifold.isInteriorPoint`. -/
lemma self_mem_chartLeviCivitaGoodSet (α : M) :
    α ∈ chartLeviCivitaGoodSet (I := I) α := by
  classical
  refine mem_chartLeviCivitaGoodSet_iff.mpr ⟨?_, ?_, ?_⟩
  · exact mem_extChartAt_source α
  · exact FiberBundle.mem_baseSet_trivializationAt' α
  · have hint : I.IsInteriorPoint α := BoundarylessManifold.isInteriorPoint
    exact (ModelWithCorners.isInteriorPoint_iff).mp hint

/-- The family `{chartLeviCivitaGoodSet α | α : M}` covers `M`. -/
lemma iUnion_chartLeviCivitaGoodSet :
    (⋃ α : M, chartLeviCivitaGoodSet (I := I) α) = (Set.univ : Set M) := by
  classical
  refine Set.eq_univ_of_forall ?_
  intro x
  refine mem_iUnion.mpr ⟨x, ?_⟩
  exact self_mem_chartLeviCivitaGoodSet (I := I) (α := x)

/-- **Chart-overlap consistency** for the chart-local Levi-Civita derivatives. On any
point `x` lying in both `chartLeviCivitaGoodSet α` and `chartLeviCivitaGoodSet β`, and
for any pair of tangent-bundle sections differentiable at `x`, the two chart-local
derivatives agree pointwise. -/
lemma chartLeviCivita_chart_overlap
    (g : SmoothRiemannianMetric I M) (α β : M)
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hxα : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hxβ : x ∈ chartLeviCivitaGoodSet (I := I) β)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    chartLeviCivita (I := I) g α Y x v =
      chartLeviCivita (I := I) g β Y x v := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
  set s : Set M := {x} with hs
  have hxs : x ∈ s := rfl
  have hTFα : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ s →
      chartLeviCivita (I := I) g α B y (A y) -
        chartLeviCivita (I := I) g α A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB hy
    have hyx : y = x := hy
    subst hyx
    exact chartLeviCivita_torsion_free_on (I := I) g α hA hB hxα
  have hTFβ : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ s →
      chartLeviCivita (I := I) g β B y (A y) -
        chartLeviCivita (I := I) g β A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB hy
    have hyx : y = x := hy
    subst hyx
    exact chartLeviCivita_torsion_free_on (I := I) g β hA hB hxβ
  have hMCα : IsMetricCompatibleOn (chartLeviCivita (I := I) g α) g s :=
    (chartLeviCivita_isMetricCompatibleOn (I := I) g α).mono
      (by intro y hy; have : y = x := hy; subst this; exact hxα)
  have hMCβ : IsMetricCompatibleOn (chartLeviCivita (I := I) g β) g s :=
    (chartLeviCivita_isMetricCompatibleOn (I := I) g β).mono
      (by intro y hy; have : y = x := hy; subst this; exact hxβ)
  have hloc :
      chartLeviCivita (I := I) g α Y x (X x) =
        chartLeviCivita (I := I) g β Y x (X x) :=
    koszul_local_uniqueness (s := s)
      hTFα hTFβ hMCα hMCβ hX hY hxs
  simpa [hXx] using hloc

/-- The stitched Levi-Civita function: at each `x : M` it is the chart-local
Levi-Civita derivative at `x` itself, evaluated at `x`. -/
def leviCivitaStitched (g : SmoothRiemannianMetric I M) :
    (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x => chartLeviCivita (I := I) g x σ x

/-- Pointwise consistency of the stitched function with each chart: on a good-set
point `x ∈ chartLeviCivitaGoodSet α` and a section differentiable at `x`, the
stitched value equals the chart-local value at `α`. -/
lemma leviCivitaStitched_eq_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hxα : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaStitched (I := I) g Y x v =
      chartLeviCivita (I := I) g α Y x v := by
  unfold leviCivitaStitched
  exact chartLeviCivita_chart_overlap (I := I) g x α
    (self_mem_chartLeviCivitaGoodSet (I := I) (α := x)) hxα hY v

/-- Additivity of the stitched function on a chart-local good set. -/
lemma leviCivitaStitched_add_on_goodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    {σ σ' : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    leviCivitaStitched (I := I) g (σ + σ') x =
      leviCivitaStitched (I := I) g σ x + leviCivitaStitched (I := I) g σ' x := by
  classical
  have hsum_at : MDiffAt (T% (σ + σ')) x :=
    mdifferentiableAt_add_section hσ hσ'
  apply ContinuousLinearMap.ext
  intro v
  rw [leviCivitaStitched_eq_chart (I := I) g α hx hsum_at v]
  rw [(chartLeviCivita_isCovariantDerivativeOn (I := I) g α).add hσ hσ' hx]
  rw [ContinuousLinearMap.add_apply,
      ← leviCivitaStitched_eq_chart (I := I) g α hx hσ v,
      ← leviCivitaStitched_eq_chart (I := I) g α hx hσ' v]
  rfl

/-- Leibniz rule for the stitched function on a chart-local good set. -/
lemma leviCivitaStitched_leibniz_on_goodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    {σ : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    leviCivitaStitched (I := I) g (f • σ) x =
      f x • leviCivitaStitched (I := I) g σ x +
        (extDerivFun f x).smulRight (σ x) := by
  classical
  have hsmul_at : MDiffAt (T% (f • σ)) x :=
    hf.smul_section hσ
  apply ContinuousLinearMap.ext
  intro v
  rw [leviCivitaStitched_eq_chart (I := I) g α hx hsmul_at v]
  rw [(chartLeviCivita_isCovariantDerivativeOn (I := I) g α).leibniz hσ hf hx]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,
      ← leviCivitaStitched_eq_chart (I := I) g α hx hσ v]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]

/-- The stitched Levi-Civita function satisfies `IsCovariantDerivativeOn` on each
chart-local good set: it agrees with the chart-local derivative there (on
differentiable inputs), and the chart-local derivative satisfies the axioms. -/
lemma leviCivitaStitched_isCovariantDerivativeOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (leviCivitaStitched (I := I) g) (chartLeviCivitaGoodSet (I := I) α) where
  add hσ hσ' hx := leviCivitaStitched_add_on_goodSet (I := I) g α hσ hσ' hx
  leibniz hσ hf hx := leviCivitaStitched_leibniz_on_goodSet (I := I) g α hσ hf hx

/-- The stitched Levi-Civita function is a covariant derivative on `Set.univ` (viewed
as the union of the chart-local good sets). -/
lemma leviCivitaStitched_isCovariantDerivativeOn_univ
    (g : SmoothRiemannianMetric I M) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (leviCivitaStitched (I := I) g) Set.univ := by
  classical
  rw [← iUnion_chartLeviCivitaGoodSet (I := I) (M := M)]
  exact IsCovariantDerivativeOn.iUnion (s := fun α => chartLeviCivitaGoodSet (I := I) α)
    (fun α => leviCivitaStitched_isCovariantDerivativeOn (I := I) g α)

/-- The **Levi-Civita covariant derivative** on the tangent bundle of a smooth
Riemannian manifold, as a bundled `CovariantDerivative I E (TangentSpace I)`. The
underlying function is the stitched chart-local construction, and the global
`IsCovariantDerivativeOn _ Set.univ` axioms come from gluing the chart-local axioms
over the open cover of chart-local good sets. -/
def LeviCivita (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  CovariantDerivative.of_isCovariantDerivativeOn_of_open_cover
    (s := fun α : M => chartLeviCivitaGoodSet (I := I) α)
    (cov := leviCivitaStitched (I := I) g)
    (fun α => leviCivitaStitched_isCovariantDerivativeOn (I := I) g α)
    (iUnion_chartLeviCivitaGoodSet (I := I) (M := M))

@[simp] lemma LeviCivita_toFun (g : SmoothRiemannianMetric I M) :
    (LeviCivita (I := I) g).toFun = leviCivitaStitched (I := I) g := rfl

/-- **Chart-overlap formula** for the bundled Levi-Civita derivative: at any point
`x ∈ chartLeviCivitaGoodSet α` and any section `σ` differentiable at `x`, the bundled
Levi-Civita value coincides with the chart-local value at `α`. -/
theorem LeviCivita_chart_apply (g : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {σ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun σ x v = chartLeviCivita (I := I) g α σ x v := by
  rw [LeviCivita_toFun]
  exact leviCivitaStitched_eq_chart (I := I) g α hx hσ v

/-- The bundled Levi-Civita covariant derivative is **torsion-free**: its torsion
tensor vanishes identically. This follows from the chart-local torsion-free identity
and the chart-overlap formula. -/
theorem LeviCivita_torsion_eq_zero (g : SmoothRiemannianMetric I M) :
    (LeviCivita (I := I) g).torsion = 0 := by
  classical
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  have hx : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  rw [LeviCivita_chart_apply (I := I) g x hx hY (X x),
      LeviCivita_chart_apply (I := I) g x hx hX (Y x)]
  exact chartLeviCivita_torsion_free_on (I := I) g x hX hY hx

/-- The bundled Levi-Civita covariant derivative is **metric-compatible** with `g`.
This follows from gluing the chart-local metric-compatibility via
`IsMetricCompatibleOn.iUnion`, after rewriting the stitched function on each
chart-local good set as the chart-local Levi-Civita derivative there (on
differentiable inputs). -/
theorem LeviCivita_isMetricCompatible (g : SmoothRiemannianMetric I M) :
    IsMetricCompatible (LeviCivita (I := I) g) g := by
  classical
  change IsMetricCompatibleOn (LeviCivita (I := I) g).toFun g Set.univ
  rw [show (Set.univ : Set M) = ⋃ α : M, chartLeviCivitaGoodSet (I := I) α from
    (iUnion_chartLeviCivitaGoodSet (I := I) (M := M)).symm]
  refine IsMetricCompatibleOn.iUnion (s := fun α => chartLeviCivitaGoodSet (I := I) α) ?_
  intro α Y Z x hY hZ hxα v
  rw [LeviCivita_chart_apply (I := I) g α hxα hY v,
      LeviCivita_chart_apply (I := I) g α hxα hZ v]
  exact chartLeviCivita_isMetricCompatibleOn (I := I) g α hY hZ hxα v

/-- Local-to-global smoothness of the Levi-Civita as a section of `Hom(TM, TM)`:
for any smooth tangent-bundle section `σ`, the section `fun x => (LeviCivita g) σ x`
is smooth on `Set.univ`. This is the body of the
`ContMDiffCovariantDerivativeOn ... univ` field. -/
lemma LeviCivita_section_contMDiffOn_univ (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) Set.univ := by
  classical
  apply contMDiffOn_of_locally_contMDiffOn
  intro x _hx
  refine ⟨chartLeviCivitaGoodSet (I := I) x,
    chartLeviCivitaGoodSet_isOpen (I := I) x,
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x), ?_⟩
  have hσ_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ)
      (chartLeviCivitaGoodSet (I := I) x) :=
    hσ.mono (Set.subset_univ _)
  have hchart :=
    (chartLeviCivita_contMDiffCovariantDerivativeOn (I := I) g x).contMDiff
      (σ := σ) hσ_on
  rw [Set.univ_inter]
  refine hchart.congr ?_
  intro y hy
  have hσ_at : MDiffAt (T% σ) y := by
    have h1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) y :=
      hσ.contMDiffAt Filter.univ_mem
    have h2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) y := by
      have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by
        rw [ENat.coe_top_add_one]
      exact h1.of_le h_le
    exact h2.mdifferentiableAt (by simp)
  have hfib :
      (LeviCivita (I := I) g).toFun σ y = chartLeviCivita (I := I) g x σ y := by
    apply ContinuousLinearMap.ext
    intro v
    exact LeviCivita_chart_apply (I := I) g x hy hσ_at v
  simp [hfib]

/-- The bundled Levi-Civita covariant derivative is `C^∞` as a covariant derivative:
for any smooth tangent-bundle section `σ`, the section `fun x => (LeviCivita g) σ x`
of `Hom(TM, TM)` is smooth on `M`. -/
instance LeviCivita_isContMDiff (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (LeviCivita (I := I) g) ∞ where
  contMDiff :=
    { contMDiff := fun hσ => LeviCivita_section_contMDiffOn_univ (I := I) g hσ }

/-- **Uniqueness of the Levi-Civita covariant derivative.** Any other torsion-free
metric-compatible covariant derivative on the tangent bundle agrees pointwise with
`LeviCivita g` on every differentiable section.

Note: bundled `CovariantDerivative` structures are not constrained on
non-differentiable inputs, so equality on differentiable inputs is the strongest
identification one can extract from the Koszul identity. -/
theorem LeviCivita_unique (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0) (hmc : IsMetricCompatible cov g)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov.toFun σ x v = (LeviCivita (I := I) g).toFun σ x v :=
  koszul_levi_civita_unique_of_torsionFree_metricCompatible cov (LeviCivita (I := I) g)
    htor (LeviCivita_torsion_eq_zero (I := I) g)
    hmc (LeviCivita_isMetricCompatible (I := I) g)
    hσ v

end Connection
end Integral
end DifferentialGeometry
