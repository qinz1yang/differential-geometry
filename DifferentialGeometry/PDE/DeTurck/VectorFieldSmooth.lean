import DifferentialGeometry.PDE.DeTurck.MetricTrace

/-!
# Smoothness of the DeTurck vector field

Given two smooth Riemannian metrics `g` and `g'` on a smooth manifold `M`, the
**DeTurck vector field** `deTurckFun g g'` is the metric `g`-trace of the
connection-difference tensor `connDiff g g'` (see `MetricTrace.lean`).  This
file proves that `deTurckFun g g'` is a smooth global section of the tangent
bundle:
$$
  x \;\longmapsto\; W(x) = \sum_{j,k} G^{jk}(x)\; A\bigl(e_j(x), e_k(x)\bigr)
$$
is `C^∞` on all of `M`, where `A = connDiff g g'`, `G^{jk}` is the inverse Gram
matrix of `g` in a chart coordinate frame `{e_j}`, and the sum is the metric
trace.

## Strategy

Smoothness is a local property, so it suffices to exhibit `deTurckFun g g'`
chart by chart.  In the chart at a basepoint `α`, the chart-local
representative `deTurckChartLocal g g' α` is a finite double sum of terms
`G^{jk} • A(e_j, e_k)`:

* each inverse-Gram-matrix entry `x ↦ chartInvGramMatrix g α x j k` is `C^∞` on
  the chart base set (`chartInvGramMatrix_entry_contMDiffOn`);
* each coordinate frame vector `chartBasisVecFiber α j` is a `C^∞`
  tangent-bundle section on the chart base set (`chartBasisVec_contMDiffOn`);
* hence `x ↦ A(e_j(x), e_k(x))` is `C^∞` on the chart base set.

The last point is the only subtlety.  The connection-difference smoothness
lemma `connDiff_contMDiffOn` requires its *first* section slot to be globally
`C^∞` on all of `M` — a limitation inherited from Mathlib's covariant-derivative
smoothness API — whereas `chartBasisVecFiber α j` is smooth only on the chart
base set.  The fix is a **bump cutoff**: at each base-set point `x₀` we choose a
smooth bump function `χ` centred at `x₀` with `χ ≡ 1` near `x₀` and
`tsupport χ` inside the chart base set; then `χ • (chartBasisVecFiber α j)` is a
*globally* smooth section, agreeing with the un-cut frame vector on the
neighbourhood where `χ ≡ 1`.  Feeding the cut section as the first slot of
`connDiff_contMDiffOn` and transferring along the equality on that
neighbourhood produces the required `ContMDiffAt`.  This localized form is
packaged once as the reusable lemma `connDiff_contMDiffOn_local`, in which
*both* section slots may be merely smooth on the open set.

## Main results

* `connDiff_contMDiffOn_local` — the connection-difference tensor applied to two
  tangent vector fields, *both* smooth on an open set `U`, yields a tangent
  vector field smooth on `U`.
* `deTurckChartLocal_contMDiffOn` — the chart-`α` representative of the DeTurck
  vector field is a smooth tangent-bundle section on the chart-`α` source.
* `deTurckFun_contMDiff_total` — the DeTurck vector field `deTurckFun g g'` is a
  smooth global section of the tangent bundle.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **A smooth bump function near `x₀` with support inside an open set `U`.**

For a point `x₀` of an open set `U`, the set `U` is a neighbourhood of `x₀`, so
by `SmoothBumpFunction.nhds_basis_support` there is a smooth bump function
centred at `x₀` whose topological support is contained in `U`.  We package the
chosen bump together with the support containment. -/
private lemma exists_bump_tsupport_subset {U : Set M} (hU : IsOpen U) {x₀ : M}
    (hx₀ : x₀ ∈ U) :
    ∃ χ : SmoothBumpFunction I x₀, tsupport (χ : M → ℝ) ⊆ U := by
  have hUnhds : U ∈ 𝓝 x₀ := hU.mem_nhds hx₀
  exact (SmoothBumpFunction.nhds_basis_support (I := I) (c := x₀) hUnhds).ex_mem

/-- **Smoothness of the connection-difference tensor with both section slots
locally smooth.**

For two tangent vector fields `σ` and `τ`, *both* smooth on an open set `U`, the
vector field `x ↦ connDiff g g' x (σ x) (τ x)` is smooth on `U`.

This is the localized form of `connDiff_contMDiffOn`, which (because of a
limitation of Mathlib's covariant-derivative smoothness API) requires the
differentiated slot `σ` to be globally `C^∞`.  Here both slots are merely
`ContMDiffOn U`.  The proof works pointwise: smoothness is local, so it suffices
to prove `ContMDiffAt` at each `x₀ ∈ U`.  Near `x₀` we replace `σ` by the
globally smooth section `χ • σ`, where `χ` is a smooth bump with `χ ≡ 1` near
`x₀` and `tsupport χ ⊆ U`; on the open neighbourhood where `χ ≡ 1` the cut
section agrees with `σ`, so the value of `connDiff g g'` is unchanged. -/
theorem connDiff_contMDiffOn_local (g g' : SmoothRiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) U)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% τ) U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U := by
  classical
  intro x₀ hx₀
  obtain ⟨χ, hχ_tsupport⟩ := exists_bump_tsupport_subset (I := I) hU hx₀
  set ψ : M → ℝ := (χ : M → ℝ) with hψ_def
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ U :=
    χ.contMDiff.contMDiffOn
  have hcut : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (ψ • σ)) :=
    ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (V := fun x : M => TangentSpace I x) hψ_smooth hU hχ_tsupport hσ
  have hConn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U :=
    connDiff_contMDiffOn (I := I) g g' hcut hτ
  have hConnAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) x₀ :=
    (hConn x₀ hx₀).contMDiffAt (hU.mem_nhds hx₀)
  have hψ_one : ψ =ᶠ[𝓝 x₀] (1 : M → ℝ) := χ.eventuallyEq_one
  have heventuallyEq :
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) =ᶠ[𝓝 x₀]
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) := by
    refine hψ_one.mono (fun x hx => ?_)
    have hx1 : ψ x = 1 := by simpa using hx
    have hσx : (ψ • σ) x = σ x := by
      change ψ x • σ x = σ x
      rw [hx1, one_smul]
    change (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ : TotalSpace E (TangentSpace I)) =
      ⟨x, connDiff (I := I) g g' x ((ψ • σ) x) (τ x)⟩
    rw [hσx]
  have hGoalAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) x₀ :=
    hConnAt.congr_of_eventuallyEq heventuallyEq
  exact hGoalAt.contMDiffWithinAt

/-- For coordinate frame vectors `e_j = chartBasisVecFiber α j` of the chart at
`α`, the vector field `x ↦ connDiff g g' x (e_j x) (e_k x)` is a smooth
tangent-bundle section on the chart-`α` source.

Both frame vectors are smooth tangent-bundle sections on the chart base set
(`chartBasisVec_contMDiffOn`), and the chart base set coincides with the chart
source; `connDiff_contMDiffOn_local` then applies with both section slots local. -/
private lemma connDiff_chartBasis_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    (α : M) (j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x)⟩ :
          TotalSpace E (TangentSpace I)))
      (chartAt H α).source := by
  have hopen : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hbase : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source α
  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun x : M => chartBasisVecFiber (I := I) α i x))
        (chartAt H α).source := by
    intro i
    have h := chartBasisVec_contMDiffOn (I := I) α i
    rw [hbase] at h
    exact h
  exact connDiff_contMDiffOn_local (I := I) g g' hopen (hframe j) (hframe k)

/-- Each inverse-Gram-matrix entry `x ↦ chartInvGramMatrix g α x j k` is `C^∞`
on the chart-`α` source (the trivialization base set coincides with the chart
source). -/
private lemma chartInvGramMatrix_entry_contMDiffOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    (j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x j k)
      (chartAt H α).source := by
  have h := chartInvGramMatrix_entry_contMDiffOn (I := I) g α j k
  rwa [trivializationAt_baseSet_eq_chartAt_source] at h

/-- **Smoothness of the chart-`α` DeTurck representative.**

The chart-`α` representative `deTurckChartLocal g g' α` of the DeTurck vector
field is a smooth tangent-bundle section on the chart-`α` source.

It is the finite double sum `∑_{j,k} G^{jk} • A(e_j, e_k)`.  Each scalar entry
`G^{jk} = chartInvGramMatrix g α · j k` is `C^∞` on the chart source, and each
`A(e_j, e_k) = connDiff g g' · (e_j ·) (e_k ·)` is a `C^∞` tangent-bundle
section there; scaling a smooth section by a smooth scalar and summing finitely
many smooth sections preserves smoothness. -/
theorem deTurckChartLocal_contMDiffOn (g g' : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (deTurckChartLocal (I := I) g g' α x))
      (chartAt H α).source := by
  classical
  have hcoeff : ∀ j k : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x j k)
        (chartAt H α).source :=
    fun j k => chartInvGramMatrix_entry_contMDiffOn_source (I := I) g α j k
  have hterm : ∀ j k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M =>
          (⟨x, connDiff (I := I) g g' x
              (chartBasisVecFiber (I := I) α j x)
              (chartBasisVecFiber (I := I) α k x)⟩ :
            TotalSpace E (TangentSpace I)))
        (chartAt H α).source :=
    fun j k => connDiff_chartBasis_contMDiffOn (I := I) g g' α j k
  have hsmul : ∀ j k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x
          (chartInvGramMatrix (I := I) g α x j k •
            connDiff (I := I) g g' x
              (chartBasisVecFiber (I := I) α j x)
              (chartBasisVecFiber (I := I) α k x)))
        (chartAt H α).source :=
    fun j k => (hcoeff j k).smul_section (hterm j k)
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x
          (∑ k : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α x j k •
              connDiff (I := I) g g' x
                (chartBasisVecFiber (I := I) α j x)
                (chartBasisVecFiber (I := I) α k x)))
        (chartAt H α).source :=
    fun j => ContMDiffOn.sum_section (fun k _ => hsmul j k)
  have houter : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α x j k •
              connDiff (I := I) g g' x
                (chartBasisVecFiber (I := I) α j x)
                (chartBasisVecFiber (I := I) α k x)))
      (chartAt H α).source :=
    ContMDiffOn.sum_section (fun j _ => hinner j)
  refine houter.congr (fun x _hx => ?_)
  rw [deTurckChartLocal_def]

/-- **The DeTurck vector field is a smooth global tangent-bundle section.**

For two smooth Riemannian metrics `g` and `g'`, the DeTurck vector field
`deTurckFun g g'` is `C^∞` as a section of the tangent bundle of `M`.

Smoothness is checked chart by chart: near each point `x` we use the chart at
`x` itself.  The chart-local representative `deTurckChartLocal g g' x` is a
smooth tangent-bundle section on the chart source by
`deTurckChartLocal_contMDiffOn`, and on that source it agrees with the
chart-independent DeTurck vector field `deTurckFun g g'` by
`deTurckChartLocal_eq_deTurckFun_of_mem_source`.  Hence `deTurckFun g g'` is
smooth on the chart source, an open neighbourhood of `x`. -/
theorem deTurckFun_contMDiff_total (g g' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (deTurckFun (I := I) g g' x)) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth_local : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (deTurckChartLocal (I := I) g g' x y))
      (chartAt H x).source :=
    deTurckChartLocal_contMDiffOn (I := I) g g' x
  have hsmooth_local2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (deTurckFun (I := I) g g' y))
      (chartAt H x).source := by
    refine hsmooth_local.congr (fun y hy => ?_)
    have h := deTurckChartLocal_eq_deTurckFun_of_mem_source (I := I) g g' x hy
    change TotalSpace.mk' E y (deTurckFun (I := I) g g' y) =
      TotalSpace.mk' E y (deTurckChartLocal (I := I) g g' x y)
    rw [h]
  exact (hsmooth_local2 x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

end DeTurck
end PDE
end DifferentialGeometry
