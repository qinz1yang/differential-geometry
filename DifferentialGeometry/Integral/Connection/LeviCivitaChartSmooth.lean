import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal

/-!
# Smoothness of the chart-local Levi-Civita covariant derivative

The chart-local Levi-Civita covariant derivative `chartLeviCivita g α`, defined
chart-by-chart in `LeviCivitaChartLocal.lean`, is a smooth covariant derivative
on its open *good set* `chartLeviCivitaGoodSet α` in the sense of Mathlib's
`ContMDiffCovariantDerivativeOn`: for any smooth section `σ` of the tangent
bundle, the section `(fun x => chartLeviCivita g α σ x)` of `Hom(TM, TM)` is
smooth on the good set.

## Construction

The proof unfolds in chart coordinates. Recall

  `chartLeviCivita g α σ x =`
    `trivFromE α x ∘L (fderiv (σ̃ ∘ φ.symm)(φ x) ∘L trivToE α x +`
                       `christoffelCorrection g α x (σ̃ x))`,

with `σ̃ := chartE_section_repr α σ` and `φ := extChartAt I α`. The hom-bundle
trivialization at `α` reads off the section's pointwise CLM in chart coordinates
as a CLM `E →L[ℝ] E` via Mathlib's `inCoordinates`. Substituting the
chart-coordinate formula and using the round-trip identities
`trivToE α x ∘L trivFromE α x = id_E`, this chart-coordinate CLM equals the
sum of:

* the chart-level Fréchet derivative `fderiv ℝ (σ̃ ∘ φ.symm) (φ x)`, and
* a finite sum `∑ᵢⱼₖ ((b.repr σ̃(x))ⱼ Γᵏᵢⱼ(φ x)) • Cᵢⱼₖ` of scalar-times-
  constant-CLM terms, each smooth in `x` on the good set.

Both summands are `C^∞` in `x` on the good set, and the chart-side sum
identifies (via `inCoordinates`) with the trivialization second component of the
section `(fun x => chartLeviCivita g α σ x)` of the hom-bundle. A
`congr_of_eventuallyEq` rewrite through `Bundle.contMDiffWithinAt_section`
yields the desired chart-local smoothness statement.

## Main result

* `chartLeviCivita_contMDiffCovariantDerivativeOn` —
  `ContMDiffCovariantDerivativeOn (V := TangentSpace I) E ∞
    (chartLeviCivita g α) (chartLeviCivitaGoodSet α)`. Together with the
  `IsCovariantDerivativeOn` axioms verified in `LeviCivitaChartLocal.lean`,
  this completes the smoothness profile of the chart-local Levi-Civita
  derivative on its good set.
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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- The chart-target image of the good set is open in `E`. -/
lemma chartLeviCivitaGoodSet_image_isOpen (α : M) :
    IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set S : Set M := chartLeviCivitaGoodSet (I := I) α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have heq :
      (extChartAt I α) '' S =
        interior ((extChartAt I α).target : Set E) ∩ (extChartAt I α).symm ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      refine ⟨chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxS, ?_⟩
      change (extChartAt I α).symm (extChartAt I α x) ∈ S
      have hxsrc : x ∈ (extChartAt I α).source :=
        chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hxS
      rw [(extChartAt I α).left_inv hxsrc]
      exact hxS
    · rintro ⟨hy_int, hy_pre⟩
      refine ⟨(extChartAt I α).symm y, hy_pre, ?_⟩
      have hy_tgt : y ∈ (extChartAt I α).target := interior_subset hy_int
      exact (extChartAt I α).right_inv hy_tgt
  rw [heq]
  have hS_open : IsOpen S := chartLeviCivitaGoodSet_isOpen (I := I) α
  have hsymm_cont : ContinuousOn (extChartAt I α).symm
      (interior ((extChartAt I α).target : Set E)) := by
    have htgt_cont : ContinuousOn (extChartAt I α).symm
        ((extChartAt I α).target : Set E) :=
      continuousOn_extChartAt_symm α
    exact htgt_cont.mono interior_subset
  exact hsymm_cont.isOpen_inter_preimage hint_open hS_open

/-- Constant building-block CLM `E →L[ℝ] E` indexed by basis triples
`(i, j, k)`: `Cᵢⱼₖ : w ↦ (b.repr w)ᵢ • bⱼ`, used for the Christoffel-
correction expansion. The `j`-index of the basis vector encodes the
section-component subscript; the contraction is built outside via the scalar
factor `(b.repr σ̃(x))ⱼ * Γᵏᵢⱼ(φ x)`.

Note: the basis vector chosen here is `(chartModelBasis E) k`, the `k`-th
target-basis element corresponding to the upper Christoffel index. -/
def christoffelBlockCLM (i k : Fin (Module.finrank ℝ E)) : E →L[ℝ] E :=
  (((chartModelBasis E).coord i).toContinuousLinearMap).smulRight
    ((chartModelBasis E) k)

/-- The chart-side Christoffel correction CLM as a function of `x : M`,
expressed as a CLM `E →L[ℝ] E`. The map sends `w ↦ ∑ᵢⱼₖ (b.repr w)ᵢ
(b.repr (σ̃ x))ⱼ Γᵏᵢⱼ(φ x) eₖ` and equals `∑ᵢⱼₖ (scalar(x)) • Cᵢₖ`,
factored to expose smoothness. -/
def christoffelCorrectionCLM (g : SmoothRiemannianMetric I M)
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) : E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr
              (chartE_section_repr (I := I) α σ x) j *
            chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
          christoffelBlockCLM (E := E) i k)

/-- Pointwise formula for `christoffelCorrectionCLM`. -/
lemma christoffelCorrectionCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) (x : M) (w : E) :
    christoffelCorrectionCLM (I := I) g α σ x w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr w) i *
                ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) α σ x)) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
              (chartModelBasis E) k := by
  classical
  unfold christoffelCorrectionCLM
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smul_apply]
  change ((chartModelBasis E).repr (chartE_section_repr (I := I) α σ x) j *
        chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
      christoffelBlockCLM (E := E) i k w =
    _
  unfold christoffelBlockCLM
  rw [ContinuousLinearMap.smulRight_apply]
  change ((chartModelBasis E).repr (chartE_section_repr (I := I) α σ x) j *
        chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
      (((chartModelBasis E).repr w) i • (chartModelBasis E) k) = _
  rw [smul_smul]
  congr 1
  ring

/-- Identification: applying `christoffelCorrection g α x Y` precomposed with
`trivFromE α x` to `w : E` (on the baseset, so `trivToE α x (trivFromE α x w) =
w`) yields the same as `christoffelCorrectionCLM g α σ x w` with
`Y := chartE_section_repr α σ x`. -/
lemma christoffelCorrection_eq_christoffelCorrectionCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : E) :
    christoffelCorrection (I := I) g α x
        (chartE_section_repr (I := I) α σ x)
        (trivFromE (I := I) α x w) =
      christoffelCorrectionCLM (I := I) g α σ x w := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrectionCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hround :
      trivToE (I := I) α x (trivFromE (I := I) α x w) = w :=
    trivToE_trivFromE (I := I) α hx w
  rw [hround]

/-- Chart-side smoothness of `chartE_section_repr α σ ∘ (extChartAt I α).symm`
on the chart-target image of the good set. Built from a local
`ContMDiffOn`-of-section hypothesis. -/
lemma chartE_pullback_contDiffOn_goodSet
    (α : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (chartLeviCivitaGoodSet (I := I) α)) :
    ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hxS, rfl⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hxS
  have hx_base :
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hxS
  have hfE_at : ContMDiffAt I 𝓘(ℝ, E) ∞
      (chartE_section_repr (I := I) α σ) x := by
    have hσ_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) x :=
      hσ.contMDiffAt (hgood_open.mem_nhds hxS)
    exact (contMDiffAt_section_iff_chartE I α σ (k := (⊤ : ℕ∞)) hx_base).mp hσ_at
  set φ := extChartAt I α
  have hxφ_src : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target (φ x) := by
    have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
    exact hsymm_on (φ x) hxφ_tgt
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (chartE_section_repr (I := I) α σ ∘ φ.symm) φ.target (φ x) := by
    have hfE_at' : ContMDiffAt I 𝓘(ℝ, E) ∞
        (chartE_section_repr (I := I) α σ) (φ.symm (φ x)) := by
      rw [hxφ_inv]; exact hfE_at
    exact hfE_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

/-- Smoothness of `chartE_section_repr α σ` on the good set. -/
lemma chartE_section_repr_contMDiffOn_goodSet
    (α : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (chartLeviCivitaGoodSet (I := I) α)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun x : M => chartE_section_repr (I := I) α σ x)
      (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro x hx
  have hx_base :
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hσ_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) x :=
    hσ.contMDiffAt (hgood_open.mem_nhds hx)
  have h := (contMDiffAt_section_iff_chartE I α σ (k := (⊤ : ℕ∞)) hx_base).mp hσ_at
  exact h.contMDiffWithinAt

/-- Smoothness of the basis component `(b.repr σ̃)_j` as a scalar function of
`x : M` on the good set. -/
lemma chartE_section_repr_basis_component_contMDiffOn
    (α : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (chartLeviCivitaGoodSet (I := I) α))
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ((chartModelBasis E).repr (chartE_section_repr (I := I) α σ x)) j)
      (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hbase :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun x : M => chartE_section_repr (I := I) α σ x)
        (chartLeviCivitaGoodSet (I := I) α) :=
    chartE_section_repr_contMDiffOn_goodSet (I := I) α hσ
  have hcoord_clm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((chartModelBasis E).coord j).toContinuousLinearMap) :=
    (((chartModelBasis E).coord j).toContinuousLinearMap).contMDiff
  intro x hx
  exact (hcoord_clm.contMDiffAt).comp_contMDiffWithinAt x (hbase x hx)

/-- `chartChristoffel`, viewed as a function on `M` (precomposed with
`extChartAt I α`), is `ContMDiffOn` on the good set. -/
lemma chartChristoffel_contMDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartChristoffel (I := I) g α i j k (extChartAt I α x))
      (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  intro x hx
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hφ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) x :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hx_src
  have hΓ_chart : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (extChartAt I α x) := by
    have hΓ_on : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α i j k
    have hxint :
        extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
    exact hΓ_on.contDiffAt (isOpen_interior.mem_nhds hxint)
  exact (hΓ_chart.comp_contMDiffAt hφ_at).contMDiffWithinAt

/-- Smoothness of the Christoffel-correction CLM as a CLM-valued function of
`x : M` on the good set. -/
lemma christoffelCorrectionCLM_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (chartLeviCivitaGoodSet (I := I) α)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α σ)
      (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  unfold christoffelCorrectionCLM
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun i _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun j _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun k _ => ?_)
  have hrepr_smooth :=
    chartE_section_repr_basis_component_contMDiffOn (I := I) α (j := j) hσ
  have hΓ_smooth :=
    chartChristoffel_contMDiffOn_goodSet (I := I) g α i j k
  have hscalar : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ((chartModelBasis E).repr (chartE_section_repr (I := I) α σ x)) j *
        chartChristoffel (I := I) g α i j k (extChartAt I α x))
      (chartLeviCivitaGoodSet (I := I) α) :=
    hrepr_smooth.mul hΓ_smooth
  have hblock_const : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun (_ : M) => christoffelBlockCLM (E := E) i k)
      (chartLeviCivitaGoodSet (I := I) α) :=
    contMDiffOn_const
  exact hscalar.smul hblock_const

/-- The Fréchet derivative of the chart-pulled-back section is `C^∞` on the
chart-target image of the good set, viewed as a CLM-valued function. -/
lemma fderiv_chartE_pullback_contDiffOn_goodSet
    (α : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (chartLeviCivitaGoodSet (I := I) α)) :
    ContDiffOn ℝ ∞
      (fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hpull : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hσ
  have himg_open := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    rw [ENat.coe_top_add_one]
  exact hpull.fderiv_of_isOpen himg_open h_le

/-- The Fréchet derivative piece, pulled back through `extChartAt I α`,
viewed as a CLM-valued function on `M`, is `ContMDiffOn` on the good set. -/
lemma fderiv_chartE_pullback_contMDiffOn
    (α : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (chartLeviCivitaGoodSet (I := I) α)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun x : M =>
        fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x))
      (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have h_fd_on := fderiv_chartE_pullback_contDiffOn_goodSet (I := I) α hσ
  have himg_open := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  intro x hx
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hφ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) x :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hx_src
  have hfd_chart : ContDiffAt ℝ ∞
      (fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm))
      (extChartAt I α x) :=
    h_fd_on.contDiffAt (himg_open.mem_nhds (Set.mem_image_of_mem _ hx))
  exact (hfd_chart.comp_contMDiffAt hφ_at).contMDiffWithinAt

/-- On the good set, the `inCoordinates` form of `chartLeviCivita g α σ x`
equals the sum of the chart-pulled-back Fréchet derivative and the
Christoffel-correction CLM. -/
lemma inCoordinates_chartLeviCivita_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
      α x α x (chartLeviCivita (I := I) g α σ x) =
      fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) +
      christoffelCorrectionCLM (I := I) g α σ x := by
  classical
  have hx_base := chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  ext w
  have hLHS_unfold :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        α x α x (chartLeviCivita (I := I) g α σ x) w =
      trivToE (I := I) α x
        ((chartLeviCivita (I := I) g α σ x) (trivFromE (I := I) α x w)) := rfl
  rw [hLHS_unfold]
  rw [chartLeviCivita_apply (I := I) g α σ hx (trivFromE (I := I) α x w)]
  rw [trivToE_trivFromE (I := I) α hx_base]
  rw [trivToE_trivFromE (I := I) α hx_base]
  rw [show christoffelCorrection (I := I) g α x
        (chartE_section_repr (I := I) α σ x) (trivFromE (I := I) α x w) =
      christoffelCorrectionCLM (I := I) g α σ x w from
    christoffelCorrection_eq_christoffelCorrectionCLM (I := I) g α σ hx_base w]
  rw [ContinuousLinearMap.add_apply]

/-- **Smoothness of the chart-local Levi-Civita as a covariant derivative.**
For any smooth section `σ` of the tangent bundle (as `ContMDiff` of `T% σ`),
the section `(fun x => chartLeviCivita g α σ x)` of the hom-bundle
`Hom(TM, TM)` is `ContMDiffOn` on the open good set at `α`, packaged in
Mathlib's `ContMDiffCovariantDerivativeOn` form. -/
theorem chartLeviCivita_contMDiffCovariantDerivativeOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffCovariantDerivativeOn (V := (TangentSpace I : M → Type _))
      E (∞ : WithTop ℕ∞) (chartLeviCivita (I := I) g α)
      (chartLeviCivitaGoodSet (I := I) α) where
  contMDiff := by
    intro σ hσ
    classical
    have hσ_inf : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
        (chartLeviCivitaGoodSet (I := I) α) := by
      have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by
        rw [ENat.coe_top_add_one]
      exact hσ.of_le h_le
    have h_fd_on :=
      fderiv_chartE_pullback_contMDiffOn (I := I) α hσ_inf
    have h_χ_on :=
      christoffelCorrectionCLM_contMDiffOn (I := I) g α hσ_inf
    have h_sum : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun x : M =>
          fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) +
          christoffelCorrectionCLM (I := I) g α σ x)
        (chartLeviCivitaGoodSet (I := I) α) :=
      h_fd_on.add h_χ_on
    intro x hx
    have hx_base :
        x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
    have hx_hom_base :
        x ∈ (trivializationAt (E →L[ℝ] E)
              (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b) α).baseSet := by
      change x ∈ (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet
      exact ⟨hx_base, hx_base⟩
    rw [(trivializationAt (E →L[ℝ] E)
          (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b) α).contMDiffWithinAt_section
      (chartLeviCivitaGoodSet (I := I) α) hx_hom_base]
    refine ((h_sum x hx).congr_of_eventuallyEq ?_ ?_)
    · filter_upwards
        [self_mem_nhdsWithin (s := chartLeviCivitaGoodSet (I := I) α)] with x' hx'
      symm
      have hcov :
          ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
            α x' α x' (chartLeviCivita (I := I) g α σ x') =
          fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x') +
          christoffelCorrectionCLM (I := I) g α σ x' :=
        inCoordinates_chartLeviCivita_eq (I := I) g α σ hx'
      have htriv :
          (trivializationAt (E →L[ℝ] E)
              (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b) α
              ⟨x', chartLeviCivita (I := I) g α σ x'⟩).2 =
            ContinuousLinearMap.inCoordinates E (TangentSpace I) E
              (TangentSpace I) α x' α x'
              (chartLeviCivita (I := I) g α σ x') := rfl
      rw [htriv, hcov]
    · symm
      have hcov :=
        inCoordinates_chartLeviCivita_eq (I := I) g α σ hx
      have htriv :
          (trivializationAt (E →L[ℝ] E)
              (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b) α
              ⟨x, chartLeviCivita (I := I) g α σ x⟩).2 =
            ContinuousLinearMap.inCoordinates E (TangentSpace I) E
              (TangentSpace I) α x α x
              (chartLeviCivita (I := I) g α σ x) := rfl
      rw [htriv, hcov]

end Connection
end Integral
end DifferentialGeometry
