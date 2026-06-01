import DifferentialGeometry.Integral.Connection.RawConnLapChartCoeffsUniformBound
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartPrimitives
import DifferentialGeometry.Geometry.Curvature.Riemann

/-!
# Uniform-over-compact-`M` bound on the chart-`α` Riemann curvature data

For a smooth closed Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the chart-`α` Riemann tensor coefficients
`chartRiemannTensor g α i j k l (ϕ_α b)` are the chart-coordinate components of
the Levi-Civita curvature in the chart at `α`. By the chart Riemann formula
`R = ∂Γ − ∂Γ + ΓΓ`, they are polynomial in the chart Christoffel symbols
`chartChristoffel g α · · ·` and their first Euclidean partial derivatives.
The Christoffel symbols are `C^∞` on the interior of the chart target
(`chartChristoffel_contDiffOn_interior`), hence so are their partials and the
Riemann coefficients. A `C^∞` function on the chart-target interior is
continuous there, hence bounded on the compact chart-`α` image of the
partition-of-unity tsupport.

This file ships two uniform bounds, both **chart-locality-free** (no
`HasLocallyConstantChartAt`, no chart-trivialisation operator-norm scalar
`A(x)`; the only chart objects are the bounded chart Christoffel data):

* `exists_chartRiemannData_uniform_bound_pouTsupport` — a single non-negative
  constant `C`, depending only on `g`, `α`, such that for every base point `b`
  in the chart-`α` partition-of-unity tsupport (intersected with the chart-`α`
  Levi-Civita good set) and all chart indices `i j k l`, the absolute value of
  the chart-`α` Riemann coefficient at `ϕ_α b` is bounded by `C`.

* `exists_chartRiemannData_uniform_bound_compact` — a single non-negative
  constant `C_g`, depending only on `g`, that bounds every chart-`α` Riemann
  coefficient at `ϕ_α b`, uniformly over the finite partition-of-unity index
  set `chartAtlasPOU_finset` and over all base points `b` in the respective
  chart-`α` tsupport ∩ good set, for all chart indices.

These are the curvature-DATA uniformity facts on which a fully uniform
intrinsic-fibre-norm curvature operator bound rests: every chart-coordinate
component of the Levi-Civita curvature is uniformly bounded on the (compact)
chart supports that cover `M`.

The quantifier order is `∃ C, ∀ b, ∀ i j k l`: the constant is uniform across
all base points and all chart indices. No chart-locality predicate is required.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The chart-`α` Riemann coefficient `R^l{}_{ijk}(g, α)` viewed as a function on
the standard Euclidean model space, by precomposition with `toEuclidean.symm`.
This is the Euclidean-side analogue of `chartChristoffelEuclid` for the
curvature data. -/
def chartRiemannEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartRiemannTensor (I := I) g α i j k l (toEuclidean.symm y)

@[simp] lemma chartRiemannEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartRiemannEuclid (I := I) g α i j k l y =
      chartRiemannTensor (I := I) g α i j k l (toEuclidean.symm y) := rfl

/-- The first model-basis partial derivative of a function that is `C^∞` on the
chart-target interior is again `C^∞` on the chart-target interior. -/
private lemma partialDeriv_contDiffOn_interior_of_contDiffOn
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior ((extChartAt I α).target : Set E)))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f)
      (interior ((extChartAt I α).target : Set E)) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hrw : (partialDeriv (E := E) a f) =
      fun y => fderiv ℝ f y ((chartModelBasis E) a) := rfl
  rw [hrw]
  exact hfderiv.clm_apply contDiffOn_const

/-- The chart-`α` Riemann coefficient `chartRiemannTensor g α i j k l` is `C^∞`
on the interior of the chart target. It is the polynomial `∂Γ − ∂Γ + ΓΓ` in the
chart Christoffel symbols, each of which is `C^∞` there. -/
theorem chartRiemannTensor_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      (interior ((extChartAt I α).target : Set E)) := by
  classical
  set U : Set E := interior ((extChartAt I α).target : Set E) with hU_def
  have hΓ : ∀ p q r : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α p q r) U :=
    fun p q r => chartChristoffel_contDiffOn_interior (I := I) g α p q r
  have hdΓ1 : ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hΓ i k l) j
  have hdΓ2 : ContDiffOn ℝ ∞
      (partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hΓ i j l) k
  have hΓΓ : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l y *
            chartChristoffel (I := I) g α i k m y -
          chartChristoffel (I := I) g α k m l y *
            chartChristoffel (I := I) g α i j m y)) U := by
    refine ContDiffOn.sum (fun m _ => ?_)
    exact ((hΓ j m l).mul (hΓ i k m)).sub ((hΓ k m l).mul (hΓ i j m))
  have hrw : (chartRiemannTensor (I := I) g α i j k l) =
      fun y : E =>
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y) +
        (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) := by
    funext y; rw [chartRiemannTensor_def]
  rw [hrw]
  exact (hdΓ1.sub hdΓ2).add hΓΓ

/-- `chartRiemannEuclid` is `C^∞` on the Euclidean chart target. It is the
composite of `chartRiemannTensor` (`C^∞` on the `E`-chart-target interior, which
equals the full `E`-chart-target under `[I.Boundaryless]`) with the smooth
isometry `toEuclidean.symm`. -/
theorem chartRiemannEuclid_contDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRiemannEuclid (I := I) g α i j k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE_int : ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      (interior ((extChartAt I α).target : Set E)) :=
    chartRiemannTensor_contDiffOn_interior (I := I) g α i j k l
  have htarget_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target (I := I) α
  have hE : ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      ((extChartAt I α).target) := by
    rw [show ((extChartAt I α).target : Set E) =
        interior ((extChartAt I α).target : Set E) from
      htarget_open.interior_eq.symm]
    exact hE_int
  have hcomp :
      ContDiffOn ℝ ∞
        (chartRiemannTensor (I := I) g α i j k l ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) hy
  exact hcomp

/-- **Uniform bound on the chart-`α` Riemann data over the chart-`α`
partition-of-unity tsupport.**

For a smooth closed Riemannian manifold `(M, g)` and a chart base point `α : M`,
there is a non-negative constant `C`, depending only on `g` and `α`, such that
for every base point `b` in the intersection of the chart-`α`
partition-of-unity tsupport with the chart-`α` Levi-Civita good set, and all
chart indices `i j k l`,
```
|chartRiemannTensor g α i j k l (ϕ_α b)| ≤ C.
```

The chart-`α` Riemann data is `C^∞` on the chart target (the polynomial
`∂Γ − ∂Γ + ΓΓ` in the chart Christoffel symbols, all `C^∞`), hence continuous,
hence bounded on the compact chart-`α` image of the partition-of-unity
tsupport. The constant is the finite sup of the per-index sup-bounds over the
(finitely many) chart-index quadruples.

The bound is unconditional in the chart atlas: no chart-locality predicate is
required, and the right-hand constant involves no chart-trivialisation
operator-norm scalar — only the bounded chart Christoffel data. -/
theorem exists_chartRiemannData_uniform_bound_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ∀ (i j k l : Fin (Module.finrank ℝ E)),
          |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤ C := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set K_set : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_image_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouTsupport_image_subset_chartTargetEuclid (I := I) (M := M) α
  have h_each : ∀ q : (Fin n × Fin n) × (Fin n × Fin n), ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ K_set,
        |chartRiemannEuclid (I := I) g α q.1.1 q.1.2 q.2.1 q.2.2 y| ≤ C := by
    intro q
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (chartRiemannEuclid_contDiffOn (I := I) (M := M) g α q.1.1 q.1.2 q.2.1 q.2.2)
  choose C_fn hC_fn_nn hC_fn_bd using h_each
  set C : ℝ :=
    (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).sup'
      Finset.univ_nonempty C_fn with hC_def
  have hC_nn : 0 ≤ C := by
    rcases Finset.univ_nonempty
      (α := (Fin n × Fin n) × (Fin n × Fin n)) with ⟨q₀, _⟩
    exact (hC_fn_nn q₀).trans
      (Finset.le_sup'_of_le C_fn (Finset.mem_univ q₀) (le_refl _))
  refine ⟨C, hC_nn, ?_⟩
  intro b hb_inter i j k l
  have hb_tsupp : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb_inter.1
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hy_K : y ∈ K_set := ⟨b, hb_tsupp, rfl⟩
  have hval : chartRiemannEuclid (I := I) g α i j k l y =
      chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b) := by
    rw [chartRiemannEuclid_def, hy_def]
    congr 1
    exact toEuclidean.symm_apply_apply ((extChartAt I α) b)
  have hbd_q := hC_fn_bd ((i, j), (k, l)) y hy_K
  have hq_le : C_fn ((i, j), (k, l)) ≤ C :=
    Finset.le_sup'_of_le C_fn (Finset.mem_univ ((i, j), (k, l))) (le_refl _)
  calc |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)|
      = |chartRiemannEuclid (I := I) g α i j k l y| := by rw [hval]
    _ ≤ C_fn ((i, j), (k, l)) := hbd_q
    _ ≤ C := hq_le

/-- **Uniform-over-compact-`M` bound on the chart-`α` Riemann data.**

For a smooth closed Riemannian manifold `(M, g)`, there is a single
non-negative constant `C_g`, depending only on `g`, such that for every
partition-of-unity index `α` in the finite cover `chartAtlasPOU_finset`, every
base point `b` in the intersection of the chart-`α` partition-of-unity tsupport
with the chart-`α` Levi-Civita good set, and all chart indices `i j k l`,
```
|chartRiemannTensor g α i j k l (ϕ_α b)| ≤ C_g.
```

The constant is the finite maximum of the per-chart constants from
`exists_chartRiemannData_uniform_bound_pouTsupport`, over the finite
partition-of-unity index set. Since the chart-`α` tsupports cover `M`
(`chartAtlasPOU_finset` is a finite cover), this is a genuinely
uniform-over-`M` bound on every chart-coordinate component of the Levi-Civita
curvature, with no chart-locality predicate and no chart-trivialisation
operator-norm scalar. -/
theorem exists_chartRiemannData_uniform_bound_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C_g : ℝ, 0 ≤ C_g ∧
      ∀ {α : M}, α ∈ chartAtlasPOU_finset (I := I) (M := M) →
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          ∀ (i j k l : Fin (Module.finrank ℝ E)),
            |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤
              C_g := by
  classical
  have h_each : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ∀ (i j k l : Fin (Module.finrank ℝ E)),
          |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤ C :=
    fun α => exists_chartRiemannData_uniform_bound_pouTsupport (I := I) (M := M) g α
  choose C_fn hC_fn_nn hC_fn_bd using h_each
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  set C_g : ℝ := ∑ α ∈ S, C_fn α with hC_g_def
  have hC_g_nn : 0 ≤ C_g :=
    Finset.sum_nonneg (fun α _ => hC_fn_nn α)
  refine ⟨C_g, hC_g_nn, ?_⟩
  intro α hα b hb_inter i j k l
  have hbd : |chartRiemannTensor (I := I) g α i j k l ((extChartAt I α) b)| ≤
      C_fn α := hC_fn_bd α hb_inter i j k l
  have hα_S : α ∈ S := hα
  have h_le : C_fn α ≤ C_g := by
    rw [hC_g_def]
    exact Finset.single_le_sum (f := C_fn) (fun a _ => hC_fn_nn a) hα_S
  exact hbd.trans h_le

end Connection
end Integral
end DifferentialGeometry

end
