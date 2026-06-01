import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.LeviCivitaChartTorsion

/-!
# Chart Levi-Civita applied to a chart-parallel-extended vector

Given a smooth Riemannian metric `g`, a chart center `α : M`, a basepoint `b : M`
in the chart Levi-Civita good set, a tangent vector `v ∈ TangentSpace I b` and a
tangent vector field `X`, this file establishes that

  `chartLeviCivita g α (chartParallelExtend α b v) b (X b)
    = trivFromE α b (christoffelCorrection g α b (trivToE α b v) (X b))`.

In other words, when the section input to `chartLeviCivita` is the chart-α-parallel
extension of a single tangent vector `v`, the Fréchet-derivative term in the
chart Levi-Civita formula vanishes (because the chart-trivialised representation
of `chartParallelExtend α b v` is locally constant on the trivialisation base
set), and only the Christoffel-correction term survives.

## Main results

* `chartParallelExtend_repr_eventuallyEq_const`: the chart-trivialised
  representation of `chartParallelExtend α b v`, pulled back through
  `(extChartAt I α).symm`, is eventually equal to the constant
  `trivToE α b v ∈ E` in a neighbourhood of `extChartAt I α b`.
* `chartParallelExtend_repr_pullback_fderiv_eq_zero`: as a consequence, the
  Fréchet derivative of `chartE_section_repr α (chartParallelExtend α b v) ∘
  (extChartAt I α).symm` at `extChartAt I α b` is zero.
* `chartLeviCivita_chartParallelExtend`: the headline identity, reducing
  `chartLeviCivita g α (chartParallelExtend α b v) b (X b)` to the pure
  Christoffel correction.
* `chartLeviCivita_chartParallelExtend_symm`: the same identity expressed in
  the swapped form (using torsion-free symmetry of the Christoffel correction).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Local constancy of the chart pullback.** For `b` in the chart Levi-Civita
good set, the chart-trivialised representation of `chartParallelExtend α b v`,
pulled back through `(extChartAt I α).symm`, is eventually equal to the
constant `trivToE α b v` in a neighbourhood of `extChartAt I α b`. -/
lemma chartParallelExtend_repr_eventuallyEq_const
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    (chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v)) ∘ (extChartAt I α).symm
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun _ : E => trivToE (I := I) α b v) := by
  classical
  set U : Set M := (trivializationAt E (TangentSpace I) α).baseSet with hU_def
  have hU_open : IsOpen U :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hb_U : b ∈ U :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hsymm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α b) :=
    continuousAt_extChartAt_symm' hb_src
  have hU_preim_nhds :
      (extChartAt I α).symm ⁻¹' U ∈ 𝓝 (extChartAt I α b) := by
    apply hsymm_cont.preimage_mem_nhds
    have hxφ_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv hb_src
    rw [hxφ_inv]
    exact hU_open.mem_nhds hb_U
  have hint_nhds : interior ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α b) :=
    hint_open.mem_nhds hb_int
  filter_upwards [hU_preim_nhds, hint_nhds] with y hy_U hy_int
  change chartE_section_repr (I := I) α (chartParallelExtend (I := I) α b v)
      ((extChartAt I α).symm y) = trivToE (I := I) α b v
  exact chartE_section_repr_chartParallelExtend (I := I) α b v hy_U

/-- **Vanishing Fréchet derivative.** For `b` in the chart Levi-Civita good
set, the Fréchet derivative at `extChartAt I α b` of
`chartE_section_repr α (chartParallelExtend α b v) ∘ (extChartAt I α).symm`
is the zero CLM. -/
lemma chartParallelExtend_repr_pullback_fderiv_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    fderiv ℝ (chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
      (extChartAt I α b) = 0 := by
  classical
  have hev :=
    chartParallelExtend_repr_eventuallyEq_const (I := I) α hb v
  rw [Filter.EventuallyEq.fderiv_eq hev]
  exact fderiv_const_apply _

/-- **Vanishing Fréchet derivative, applied form.** Applying the zero CLM to
any tangent vector argument gives zero. -/
lemma chartParallelExtend_repr_pullback_fderiv_apply_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) (w : E) :
    fderiv ℝ (chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
      (extChartAt I α b) w = 0 := by
  rw [chartParallelExtend_repr_pullback_fderiv_eq_zero (I := I) α hb v]
  rfl

/-- **Chart Levi-Civita on a chart-parallel-extended vector reduces to the
Christoffel correction.** For `b` in the chart Levi-Civita good set, the chart
Levi-Civita derivative of `chartParallelExtend α b v` at `b` along `X b`
equals the chart-α Christoffel correction transported back to the tangent
space. -/
theorem chartLeviCivita_chartParallelExtend
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    chartLeviCivita (I := I) g α (chartParallelExtend (I := I) α b v) b (X b) =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b v) (X b)) := by
  classical
  rw [chartLeviCivita_apply (I := I) g α
        (chartParallelExtend (I := I) α b v) hb (X b)]
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hrepr :
      chartE_section_repr (I := I) α (chartParallelExtend (I := I) α b v) b =
        trivToE (I := I) α b v :=
    chartE_section_repr_chartParallelExtend (I := I) α b v hb_base
  have hfderiv :
      fderiv ℝ (chartE_section_repr (I := I) α
          (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b)) = 0 :=
    chartParallelExtend_repr_pullback_fderiv_apply_eq_zero
      (I := I) α hb v (trivToE (I := I) α b (X b))
  rw [hfderiv, hrepr]
  rw [zero_add]

/-- **Symmetric form of the headline identity.** Using torsion-free Christoffel
symmetry, the same identity can be expressed with the input vector `v` in the
CLM-argument position. -/
theorem chartLeviCivita_chartParallelExtend_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    chartLeviCivita (I := I) g α (chartParallelExtend (I := I) α b v) b (X b) =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v) := by
  classical
  rw [chartLeviCivita_chartParallelExtend (I := I) g α hb v X]
  congr 1
  exact (christoffelCorrection_symm_cancel (I := I) g α b v (X b)).symm

/-- **Manifold-differentiability of `chartParallelExtend α b v` as a section** at
the basepoint `b`, on the chart Levi-Civita good set. The proof uses the fact
that the chart-trivialised representation of the parallel extension is
constantly equal to `trivToE α b v` on the trivialisation base set, and then
applies the section-differentiability criterion through the trivialisation. -/
lemma chartParallelExtend_mdifferentiableAt
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) b'
        (chartParallelExtend (I := I) α b v b')) b := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he_def
  have hb_base : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hbase_open : IsOpen e.baseSet := e.open_baseSet
  have hbase_nhds : e.baseSet ∈ 𝓝 b := hbase_open.mem_nhds hb_base
  have hconst :
      (fun b' : M => (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2) =ᶠ[𝓝 b]
        (fun _ : M => trivToE (I := I) α b v) := by
    filter_upwards [hbase_nhds] with b' hb'
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := b') hb'
    have happ := congrFun hcoe (chartParallelExtend (I := I) α b v b')
    change (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2 = trivToE (I := I) α b v
    rw [← happ]
    change (trivToE (I := I) α b') (chartParallelExtend (I := I) α b v b') = trivToE (I := I) α b v
    change (trivToE (I := I) α b') (trivFromE (I := I) α b' (trivToE (I := I) α b v)) =
      trivToE (I := I) α b v
    exact trivToE_trivFromE (I := I) α hb' _
  have hrep_diff :
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun b' : M => (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2) b :=
    (mdifferentiableAt_const (c := trivToE (I := I) α b v)).congr_of_eventuallyEq hconst
  exact (Trivialization.mdifferentiableAt_section_iff (IB := I) e
    (fun b' : M => chartParallelExtend (I := I) α b v b') hb_base).mpr hrep_diff

end Connection
end Integral
end DifferentialGeometry
