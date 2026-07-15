import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.StrictParabolicity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization

/-! # Strict parabolicity of the DeTurck-Ricci right-hand side

The concrete DeTurck-Ricci operator `g ↦ -2 Ric(g) + 𝓛_{X(g, g_bg)} g` is strictly
parabolic at every metric: the chart second-order part of its linearization is the
gauge-cancelled isotropic Laplacian symbol `−|ξ|²_g · id` on the symmetric perturbation
space, yielding `IsStrictlyParabolicMetricRHS` for the abstract short-time-existence
interface. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The Ricci–DeTurck right-hand side is a symmetric bilinear form.**
`deTurckRicciRHS g_bg g x v w = deTurckRicciRHS g_bg g x w v`, because it is a sum of two
symmetric `(0,2)`-tensors: the Ricci tensor (`ricciTensor_symm`) and the metric Lie
derivative (`lieDerivMetric_isPointwiseSymm`). -/
theorem deTurckRicciRHS_isPointwiseSymm
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w =
      deTurckRicciRHS (I := I) g_bg g x w v := by
  simp only [deTurckRicciRHS, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lieDerivMetricClm_apply]
  rw [DifferentialGeometry.Integral.Connection.ricciTensor_symm (I := I)
        (smoothRiemannianMetricToInfty (I := I) g) x v w,
    DeTurck.lieDerivMetric_isPointwiseSymm (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (DeTurck.deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w]

/-- **The chart `∂²h`-coefficient of the Ricci–DeTurck linearization at `g₀`.**

`deTurckRicciRHSChartSecondOrderPart g₀ g_bg` is the canonical chart second-order part of
`D(deTurckRicciRHS g_bg)(g₀)`: the part of the directional derivative carrying two chart
derivatives of the perturbation `h`, assembled from the `-2 Ric + 𝓛_W g` decomposition as
`(-2)·chartRicciSecondOrderPart g₀ + chartDeTurckCorrSecondOrderPart g₀ g_bg`.

This is the abstract `P` whose principal symbol — the `∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}`
substitution — is the bundled Ricci–DeTurck symbol `deTurckSymbol g₀ g_bg`, which the
gauge cancellation makes the isotropic `|ξ|²_{g₀} · t` on the symmetric perturbation
space (`StrictParabolicity.lean`). -/
noncomputable def deTurckRicciRHSChartSecondOrderPart
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → E → ℝ :=
  fun h α i j y =>
    (-2 : ℝ) * chartRicciSecondOrderPart (I := I) g₀ α h i j y +
      chartDeTurckCorrSecondOrderPart (I := I) g₀ g_bg α h i j y

section ReadOff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable [I.Boundaryless]

/-- The chart linear functional `y ↦ ∑_a ξ_a (y − y₀)_a` underlying the symbol test
perturbation has constant first chart partial `∂_p = ξ_p`. -/
private lemma partialDeriv_testLinearForm (x : M) (ξ : E)
    (p : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p
      (fun z : E => ∑ a : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr ξ a *
          (chartModelBasis E).repr (z - extChartAt I x x) a) y =
      (chartModelBasis E).repr ξ p := by
  classical
  have hdiff : ∀ a : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun z : E => (chartModelBasis E).repr ξ a *
        (chartModelBasis E).repr (z - extChartAt I x x) a) y := by
    intro a
    refine (differentiableAt_const _).mul ?_
    have hlin : (fun z : E => (chartModelBasis E).repr (z - extChartAt I x x) a) =
        fun z : E => (chartModelBasis E).coord a (z - extChartAt I x x) := by
      funext z; rw [Module.Basis.coord_apply]
    rw [hlin]
    exact (((chartModelBasis E).coord a).toContinuousLinearMap.differentiableAt).comp y
      ((differentiableAt_id).sub (differentiableAt_const _))
  rw [partialDeriv_sum Finset.univ _ (fun a _ => hdiff a)]
  have hterm : ∀ a : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) p (fun z : E => (chartModelBasis E).repr ξ a *
        (chartModelBasis E).repr (z - extChartAt I x x) a) y =
        (chartModelBasis E).repr ξ a * (if p = a then (1 : ℝ) else 0) := by
    intro a
    rw [partialDeriv_const_mul (E := E) ((chartModelBasis E).repr ξ a)
      (fun z : E => (chartModelBasis E).repr (z - extChartAt I x x) a) (by
        have hlin : (fun z : E => (chartModelBasis E).repr (z - extChartAt I x x) a) =
            fun z : E => (chartModelBasis E).coord a (z - extChartAt I x x) := by
          funext z; rw [Module.Basis.coord_apply]
        rw [hlin]
        exact (((chartModelBasis E).coord a).toContinuousLinearMap.differentiableAt).comp y
          ((differentiableAt_id).sub (differentiableAt_const _)))]
    congr 1

    have hlin : (fun z : E => (chartModelBasis E).repr (z - extChartAt I x x) a) =
        fun z : E => (chartModelBasis E).coord a (z - extChartAt I x x) := by
      funext z; rw [Module.Basis.coord_apply]
    rw [hlin]
    unfold partialDeriv
    have hfd : HasFDerivAt (fun z : E => (chartModelBasis E).coord a (z - extChartAt I x x))
        (((chartModelBasis E).coord a).toContinuousLinearMap) y := by
      have h1 : HasFDerivAt (fun z : E => z - extChartAt I x x)
          (ContinuousLinearMap.id ℝ E) y :=
        (hasFDerivAt_id y).sub_const (extChartAt I x x)
      have h2 := (((chartModelBasis E).coord a).toContinuousLinearMap.hasFDerivAt
        (x := (y - extChartAt I x x))).comp y h1
      have h3 : (⇑((chartModelBasis E).coord a).toContinuousLinearMap ∘
          fun z : E => z - extChartAt I x x) =
          fun z : E => (chartModelBasis E).coord a (z - extChartAt I x x) := rfl
      rw [h3] at h2
      simpa using h2
    rw [hfd.fderiv]
    have hap : ((chartModelBasis E).coord a).toContinuousLinearMap ((chartModelBasis E) p) =
        (chartModelBasis E).coord a ((chartModelBasis E) p) := rfl
    rw [hap, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases hpa : p = a
    · rw [hpa]; simp
    · rw [if_neg hpa, Finsupp.single_eq_of_ne (Ne.symm hpa)]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl]; ring
  · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
  · intro hp; exact absurd (Finset.mem_univ p) hp

/-- **The second iterated chart partial of the symbol test perturbation at the base chart
point reads off the substitution datum `ξ_p ξ_q t_{cd}`.**  Since the test perturbation is
`½·(testLinear)²·t_{cd}` with `testLinear` linear of slope `ξ`, vanishing at `y₀`, the
product rule gives `∂_p∂_q = ξ_p ξ_q t_{cd}` at `y₀`. -/
private lemma partialDeriv_partialDeriv_symbolTestPerturbation_self (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (p q c d : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
        (partialDeriv (E := E) q
          (symbolTestPerturbation (I := I) x x ξ t ht c d)) (extChartAt I x x) =
      (chartModelBasis E).repr ξ p * (chartModelBasis E).repr ξ q *
        formComp (I := I) x t c d := by
  classical
  set y₀ : E := extChartAt I x x with hy₀
  set K : ℝ := formComp (I := I) x t c d with hK
  set L : E → ℝ := fun z : E => ∑ a : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr ξ a * (chartModelBasis E).repr (z - extChartAt I x x) a with hL

  have hfun : (symbolTestPerturbation (I := I) x x ξ t ht c d) =
      fun z : E => ((1 / 2 : ℝ) * K) * (L z * L z) := by
    funext z
    have hval : symbolTestPerturbation (I := I) x x ξ t ht c d z =
        (1 / 2 : ℝ) * (L z) ^ 2 * formComp (I := I) x t c d := rfl
    rw [hval, hK]; ring

  have hL_diff : ∀ z : E, DifferentiableAt ℝ L z := by
    intro z
    rw [hL]
    refine DifferentiableAt.fun_sum (fun a _ => ?_)
    refine (differentiableAt_const _).mul ?_
    have hlin : (fun z : E => (chartModelBasis E).repr (z - extChartAt I x x) a) =
        fun z : E => (chartModelBasis E).coord a (z - extChartAt I x x) := by
      funext w; rw [Module.Basis.coord_apply]
    rw [hlin]
    exact (((chartModelBasis E).coord a).toContinuousLinearMap.differentiableAt).comp z
      ((differentiableAt_id).sub (differentiableAt_const _))

  have hinner : partialDeriv (E := E) q
        (symbolTestPerturbation (I := I) x x ξ t ht c d) =
      fun z : E => ((1 / 2 : ℝ) * K) * (partialDeriv (E := E) q L z * L z +
        L z * partialDeriv (E := E) q L z) := by
    funext z
    rw [hfun]
    rw [partialDeriv_const_mul (E := E) ((1 / 2 : ℝ) * K) (fun z => L z * L z)
      ((hL_diff z).mul (hL_diff z))]
    rw [partialDeriv_mul (E := E) L L (hL_diff z) (hL_diff z)]
  rw [hinner]

  have hLq : ∀ z : E, partialDeriv (E := E) q L z = (chartModelBasis E).repr ξ q := by
    intro z; rw [hL]; exact partialDeriv_testLinearForm x ξ q z
  have hgoal_fun : (fun z : E => ((1 / 2 : ℝ) * K) * (partialDeriv (E := E) q L z * L z +
        L z * partialDeriv (E := E) q L z)) =
      fun z : E => ((1 / 2 : ℝ) * K) *
        ((chartModelBasis E).repr ξ q * L z + L z * (chartModelBasis E).repr ξ q) := by
    funext z; rw [hLq z]
  rw [hgoal_fun]
  rw [partialDeriv_const_mul (E := E) ((1 / 2 : ℝ) * K)
    (fun z => (chartModelBasis E).repr ξ q * L z + L z * (chartModelBasis E).repr ξ q)
    (((differentiableAt_const _).mul (hL_diff _)).add
      ((hL_diff _).mul (differentiableAt_const _)))]
  rw [partialDeriv_add (E := E)
    (fun z => (chartModelBasis E).repr ξ q * L z)
    (fun z => L z * (chartModelBasis E).repr ξ q)
    ((differentiableAt_const _).mul (hL_diff _))
    ((hL_diff _).mul (differentiableAt_const _))]
  rw [partialDeriv_const_mul (E := E) ((chartModelBasis E).repr ξ q) L (hL_diff _)]
  rw [show (fun z : E => L z * (chartModelBasis E).repr ξ q) =
      fun z : E => (chartModelBasis E).repr ξ q * L z from by funext z; ring]
  rw [partialDeriv_const_mul (E := E) ((chartModelBasis E).repr ξ q) L (hL_diff _)]
  rw [hL, partialDeriv_testLinearForm x ξ p (extChartAt I x x)]
  rw [hK]; ring

/-- **The chart Ricci second-order principal symbol on the test perturbation reads off
`ricciSymbolComp`.**  Substituting the `∂_a∂_b h ↦ ξ_aξ_b t` datum of the test
perturbation (`partialDeriv_partialDeriv_symbolTestPerturbation_self`) into the four-term
`∂²h` expression `chartRicciSecondOrderPrincipalSymbol` produces, term by term, the bundled
`ricciSymbolComp`. -/
private lemma chartRicciSecondOrderPrincipalSymbol_symbolTestPerturbation
    (g₀ : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (i k : Fin (Module.finrank ℝ E)) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g₀ x
        (symbolTestPerturbation (I := I) x x ξ t ht) i k (extChartAt I x x) =
      ricciSymbolComp (I := I) g₀ x ξ t i k := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, ricciSymbolComp_def]
  refine congrArg (fun z => (1 / 2 : ℝ) * z) ?_
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht j i l k,
    partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht k l i j,
    partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht j l i k,
    partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht k i l j]

/-- **The chart DeTurck-correction principal-symbol expression on the test perturbation
reads off `deTurckCorrSymbolComp`.**  Same `∂_a∂_b h ↦ ξ_aξ_b t` substitution into the
explicit `∂²h` form of `chartDeTurckCorrPrincipalSymbolExpr`. -/
private lemma chartDeTurckCorrPrincipalSymbolExpr_symbolTestPerturbation
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (i j : Fin (Module.finrank ℝ E)) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g₀ g_bg x
        (symbolTestPerturbation (I := I) x x ξ t ht) i j (extChartAt I x x) =
      deTurckCorrSymbolComp (I := I) g₀ g_bg x ξ t i j := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_eq_explicit, deTurckCorrSymbolComp_def]
  refine congrArg₂ (· + ·) ?_ ?_ <;>
    refine Finset.sum_congr rfl (fun k _ => congrArg (fun z => _ * z)
      (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        congrArg (fun z => _ * z) (congrArg (fun z => (1 / 2 : ℝ) * z)
          (Finset.sum_congr rfl (fun l _ => congrArg (fun z => _ * z) ?_)))))))
  · rw [partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht i a l b,
      partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht i b l a,
      partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht i l a b]
  · rw [partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht j a l b,
      partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht j b l a,
      partialDeriv_partialDeriv_symbolTestPerturbation_self x ξ t ht j l a b]

/-- **The test-perturbation read-off for the chart second-order part of
`deTurckRicciRHS g_bg`.**  Evaluating the chart second-order part
`deTurckRicciRHSChartSecondOrderPart` on the symbol test perturbation at the base chart
point reproduces the negated geometer-sign isotropic symbol — the gauge-cancelled
Ricci–DeTurck symbol with coefficient `−|ξ|²_{g₀}`.

The first-order remainders of both chart second-order parts vanish on the test perturbation
(its value and first chart partials vanish at `y₀`), so the chart second-order part reduces
to the principal symbols `ricciSymbolComp`/`deTurckCorrSymbolComp`, which assemble into the
bundled `deTurckSymbol`; the sibling `deTurckRicciRHS_principal_symbol_equals_deTurckSymbol`
then supplies the sign. -/
private theorem deTurckRicciRHS_test_perturbation_readoff
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg
        (symbolTestPerturbation (I := I) x x ξ t ht) x i j (extChartAt I x x) =
      - (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
            (E := E)
            (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
            (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t)
          ((chartModelBasis E) i) ((chartModelBasis E) j) := by
  classical
  set hh : ChartMetricPerturbation E := symbolTestPerturbation (I := I) x x ξ t ht with hhdef
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x

  have hval : ∀ a b, hh a b (extChartAt I x x) = 0 :=
    fun a b => symbolTestPerturbation_apply_self (I := I) x x ξ t ht a b
  have hjet : ∀ p a b, partialDeriv (E := E) p (hh a b) (extChartAt I x x) = 0 :=
    fun p a b => partialDeriv_symbolTestPerturbation_self (I := I) x x ξ t ht p a b

  have hRicci :
      chartRicciSecondOrderPart (I := I) g₀ x hh i j (extChartAt I x x) =
        ricciSymbolComp (I := I) g₀ x ξ t i j := by
    rw [chartRicciSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
        (I := I) g₀ x hh i j hx_src]
    rw [chartRicciSecondOrderPrincipalSymbol_symbolTestPerturbation g₀ x ξ t ht i j]
    rw [chartRicciFirstOrderRemainder_eq_first_order_sum]
    have hrem : (∑ jj : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (((1 / 2 : ℝ) * partialDeriv (E := E) jj
              (chartInvGramOnE (I := I) g₀ x jj l) (extChartAt I x x)) *
            partialDeriv (E := E) i (hh l j) (extChartAt I x x) +
          ((1 / 2 : ℝ) * partialDeriv (E := E) jj
              (chartInvGramOnE (I := I) g₀ x jj l) (extChartAt I x x)) *
            partialDeriv (E := E) j (hh l i) (extChartAt I x x) +
          (-(1 / 2 : ℝ) * partialDeriv (E := E) jj
              (chartInvGramOnE (I := I) g₀ x jj l) (extChartAt I x x)) *
            partialDeriv (E := E) l (hh i j) (extChartAt I x x) +
          (-(1 / 2 : ℝ) * partialDeriv (E := E) j
              (chartInvGramOnE (I := I) g₀ x jj l) (extChartAt I x x)) *
            partialDeriv (E := E) i (hh l jj) (extChartAt I x x) +
          (-(1 / 2 : ℝ) * partialDeriv (E := E) j
              (chartInvGramOnE (I := I) g₀ x jj l) (extChartAt I x x)) *
            partialDeriv (E := E) jj (hh l i) (extChartAt I x x) +
          ((1 / 2 : ℝ) * partialDeriv (E := E) j
              (chartInvGramOnE (I := I) g₀ x jj l) (extChartAt I x x)) *
            partialDeriv (E := E) l (hh i jj) (extChartAt I x x))) = 0 := by
      refine Finset.sum_eq_zero (fun jj _ => Finset.sum_eq_zero (fun l _ => ?_))
      rw [hjet i l j, hjet j l i, hjet l i j, hjet i l jj, hjet jj l i, hjet l i jj]
      ring
    rw [hrem, add_zero]

  have hCorr :
      chartDeTurckCorrSecondOrderPart (I := I) g₀ g_bg x hh i j (extChartAt I x x) =
        deTurckCorrSymbolComp (I := I) g₀ g_bg x ξ t i j := by
    rw [chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
        (I := I) g₀ g_bg x hh i j hx_src]
    rw [chartDeTurckCorrPrincipalSymbolExpr_symbolTestPerturbation g₀ g_bg x ξ t ht i j]

    have hLCP : ∀ a b k : Fin (Module.finrank ℝ E),
        chartLinearizedChristoffelPrincipal (I := I) g₀ x hh a b k (extChartAt I x x) = 0 := by
      intro a b k
      rw [chartLinearizedChristoffelPrincipal_def]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun l _ => ?_))
      rw [hjet a l b, hjet b l a, hjet l a b]; ring
    have hGDB : ∀ d a b k : Fin (Module.finrank ℝ E),
        chartDeTurckCorrGramDerivBlock (I := I) g₀ g_bg x hh d a b k (extChartAt I x x) = 0 := by
      intro d a b k
      rw [chartDeTurckCorrGramDerivBlock_def]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun l _ => ?_))
      rw [hjet a l b, hjet b l a, hjet l a b]; ring
    have hblock_zero : ∀ (gf : Fin (Module.finrank ℝ E) → ℝ) (d : Fin (Module.finrank ℝ E)),
        (∑ k : Fin (Module.finrank ℝ E),
          gf k *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) d (chartInvGramOnE (I := I) g₀ x a b) (extChartAt I x x) *
                  chartLinearizedChristoffelPrincipal (I := I) g₀ x hh a b k
                    (extChartAt I x x)) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g₀ x a b (extChartAt I x x) *
                  chartDeTurckCorrGramDerivBlock (I := I) g₀ g_bg x hh d a b k
                    (extChartAt I x x)))) = 0 := by
      intro gf d
      refine Finset.sum_eq_zero (fun k _ => mul_eq_zero_of_right _ ?_)
      rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g₀ x a b) (extChartAt I x x) *
              chartLinearizedChristoffelPrincipal (I := I) g₀ x hh a b k
                (extChartAt I x x)) = 0 from
        Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
          rw [hLCP a b k]; ring))]
      rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ x a b (extChartAt I x x) *
              chartDeTurckCorrGramDerivBlock (I := I) g₀ g_bg x hh d a b k
                (extChartAt I x x)) = 0 from
        Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
          rw [hGDB d a b k]; ring))]
      ring
    have hrem : chartDeTurckCorrFirstOrderRemainder (I := I) g₀ g_bg x hh i j
        (extChartAt I x x) = 0 := by
      rw [chartDeTurckCorrFirstOrderRemainder_def,
        hblock_zero (fun k => chartGramOnE (I := I) g₀ x k j (extChartAt I x x)) i,
        hblock_zero (fun k => chartGramOnE (I := I) g₀ x i k (extChartAt I x x)) j, add_zero]
    rw [hrem, add_zero]

  rw [deTurckRicciRHSChartSecondOrderPart, hRicci, hCorr]

  have hLHS : (-2 : ℝ) * ricciSymbolComp (I := I) g₀ x ξ t i j +
        deTurckCorrSymbolComp (I := I) g₀ g_bg x ξ t i j =
      DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ *
        formComp (I := I) x t i j := by
    rw [← ricciSymbol_apply_apply (I := I) g₀ x ξ t i j,
      ← deTurckCorrectionSymbol_apply_apply (I := I) g₀ g_bg x ξ t i j,
      ← DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply (I := I) g₀ g_bg x ξ t]
    exact DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply_eq_isotropic_of_symm
      (I := I) g₀ g_bg x ξ t ht i j

  rw [hLHS, DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply, formComp_def]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The chart `∂²h`-coefficient of `deTurckRicciRHS g_bg` is the genuine chart second
order part of its linearization at `g₀`, and reads off the DeTurck symbol.**

This is the one genuine differential-geometry input that ties the abstract principal-symbol
predicate to the concrete Ricci–DeTurck operator.  It packages the two facts the predicate
needs about `P := deTurckRicciRHSChartSecondOrderPart g₀ g_bg`:

* **(linearization)** `P` is the chart second-order part of `D(deTurckRicciRHS g_bg)(g₀)`:
  along any realising family `gfam` of `g₀ ⊕ s·h`, the `s`-derivative at `0` of the chart
  `(i, j)`-component of `deTurckRicciRHS g_bg (gfam s)` equals `P h α i j y` plus a
  genuinely-first-order remainder (`IsChartLinearizationSecondOrderPart`).  This is the
  abstract analogue of the `-2 Ric + 𝓛_W g` chart linearization computed termwise in
  `chartRicciSecondOrderPart_eq_principalSymbol_add_remainder` and
  `chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder`.

* **(symbol read-off)** the principal-symbol substitution of `P` is the geometer-sign
  isotropic symbol `isotropicSymbol _ (deTurckSymbolCoeff g₀)` (coefficient `−|ξ|²_{g₀}`),
  i.e. evaluating `P` on the symbol test perturbation reproduces the negated symbol
  component (`IsPrincipalSymbolOfSecondOrderPart`).

The two genuine remaining obligations are isolated in
`deTurckRicciRHS_chartLinearization_and_readoff`:

* the chart linearization identity for `deTurckRicciRHS`
  (`(d/ds) [chart component of deTurckRicciRHS(g₀ ⊕ s·h)]|_{s=0} =
  P h + first-order remainder`, the `IsChartLinearizationSecondOrderPart` clause), the
  `s`-derivative bridge between the operator and its termwise chart second-order parts; and

* the test-perturbation read-off
  `P (symbolTestPerturbation x x ξ t) x i j (extChartAt I x x) = |ξ|²_{g₀} · t_{ij}`, the
  `∂_a∂_b h ↦ ξ_aξ_b t` substitution feeding the closed-form gauge cancellation
  `deTurckSymbol_apply_eq_smul_of_symm`.

Both are genuine chart-coordinate computations on the concrete operator.  The chart
linearization clause is supplied by the metric-family chart-linearization tower
(`hasDerivAt_chartFComponentOnE_deTurckRicciRHS` together with
`metricFamilyDeTurckRicciFirstOrderRemainder_vanish`); the test-perturbation read-off is
the `∂_a∂_b h ↦ ξ_aξ_b t` substitution into the chart second-order parts, identified with
the bundled `ricciSymbolComp`/`deTurckCorrSymbolComp` and gauge-cancelled by
`deTurckSymbol_apply_apply_eq_isotropic_of_symm`.  The **strict-parabolicity** half of the
principal-symbol clause — `σ x ξ t = −|ξ|²_{g₀}·t` with `0 < |ξ|²_{g₀}` — is proven
outright below from `isotropicSymbol_apply_apply` and `metricCovectorNormSq_pos`. -/
theorem deTurckRicciRHS_chartLinearization_and_readoff
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsChartLinearizationSecondOrderPart (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀
        (deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg) ∧
      ∀ (x : M) (ξ : E), ξ ≠ 0 →
        ∀ t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ,
          (∀ ht : ∀ v w, t v w = t w v, ∀ i j : Fin (Module.finrank ℝ E),
            deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg
                (symbolTestPerturbation (I := I) x x ξ t ht) x i j (extChartAt I x x) =
              - (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
                    (E := E)
                    (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
                    (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t)
                  ((chartModelBasis E) i) ((chartModelBasis E) j)) := by
  refine ⟨?_, ?_⟩
  · -- conjunct 1: the chart linearization
    refine ⟨fun h α i j y => metricFamilyDeTurckRicciFirstOrderRemainder (I := I)
      g₀ g_bg α h i j y, ?_, ?_⟩
    · -- the remainder is first order in the perturbation
      intro α h i j y hy hval hjet
      exact metricFamilyDeTurckRicciFirstOrderRemainder_vanish (I := I) hy hval hjet i j
    · -- the s-derivative reads off P + remainder
      intro α h gfam hfam i j y hy
      have hderiv := hasDerivAt_chartFComponentOnE_deTurckRicciRHS (I := I) hfam g_bg i j hy
      rw [hderiv.deriv]
      rw [deTurckRicciRHSChartSecondOrderPart]
  · -- conjunct 2: the test-perturbation read-off
    intro x ξ hξ t ht i j
    exact deTurckRicciRHS_test_perturbation_readoff (I := I) g₀ g_bg x ξ t ht i j

end ReadOff

/-- **The chart second-order part `deTurckRicciRHSChartSecondOrderPart g₀ g_bg` is the
chart `∂²h`-coefficient of `D(deTurckRicciRHS g_bg)(g₀)` and has the geometer-sign
isotropic Ricci–DeTurck symbol as its principal symbol.**

The chart-linearization clause and the test-perturbation read-off are supplied by
`deTurckRicciRHS_chartLinearization_and_readoff`; the strict-parabolicity clause
(`isotropicSymbol _ (deTurckSymbolCoeff g₀)` acts as `−|ξ|²_{g₀}·t`, `0 < |ξ|²_{g₀}`) is
proven here from `isotropicSymbol_apply_apply`, `deTurckSymbolCoeff_apply`, and
`metricCovectorNormSq_pos`. -/
theorem deTurckRicciRHS_chartSecondOrderPart_spec [I.Boundaryless]
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsChartLinearizationSecondOrderPart (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀
        (deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg) ∧
      IsPrincipalSymbolOfSecondOrderPart (I := I) g₀
        (deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg)
        (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
          (E := E)
          (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
          (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀)) := by
  obtain ⟨hlin, hreadoff⟩ := deTurckRicciRHS_chartLinearization_and_readoff (I := I) g₀ g_bg
  refine ⟨hlin, ?_⟩
  intro x ξ hξ t ht
  refine ⟨hreadoff x ξ hξ t, ?_, metricCovectorNormSq_pos (I := I) g₀ x hξ⟩
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]

/-- **Symbol-form identification on a symmetric input.**  The strictly-parabolic isotropic
symbol witness for `deTurckRicciRHS g_bg` at `g₀` (the isotropic symbol with coefficient
`-|ξ|²_{g₀}`) is the **negation** of the bundled Ricci–DeTurck linearized symbol
`DeTurck.deTurckSymbol g₀ g_bg`, on a **symmetric** input bilinear form `t`
(`t v w = t w v`).

The bundled `deTurckSymbol g₀ g_bg` is the linear combination
`-2 • ricciSymbol g₀ + deTurckCorrectionSymbol g₀ g_bg` whose gauge cancellation
(`DeTurck.deTurckSymbol_apply_eq_smul_of_symm`) reads, on symmetric `t`, as the action
`t ↦ |ξ|²_{g₀} · t` — the *positive* isotropic scaling, the substitution
`∂_a ∂_b ↦ +ξ_a ξ_b`.  The strictly-parabolic isotropic symbol used as the principal-symbol
witness in `deTurckRicciRHS_hasPrincipalSymbol_at_self` is its geometer-sign counterpart
`t ↦ -|ξ|²_{g₀} · t` (the substitution `∂_a ∂_b ↦ -ξ_a ξ_b`, consistent with the
geometer's Laplacian `Δ = div ∘ grad` having spectrum `⊆ (-∞, 0]`).  So the two agree up to
an overall sign on the symmetric input that downstream parabolic consumption actually uses. -/
theorem deTurckRicciRHS_principal_symbol_equals_deTurckSymbol
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t := by
  classical
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]
  rw [DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm
    (I := I) g₀ g_bg x ξ t ht]
  rw [neg_smul]

/-- The Ricci–DeTurck right-hand side `g ↦ -2 Rc(g) + 𝓛_{W(g, g_bg)} g` has the geometer-sign
isotropic Ricci–DeTurck symbol as the principal symbol of its linearization at its own base
metric `g₀`.

The witness symbol is the isotropic Ricci–DeTurck symbol with coefficient `-|ξ|²_{g₀}`
(see `DeTurck.isotropicSymbol` with `DeTurck.deTurckSymbolCoeff g₀`).  Its chart second order
part is `deTurckRicciRHSChartSecondOrderPart g₀ g_bg = -2·chartRicciSecondOrderPart +
chartDeTurckCorrSecondOrderPart` (`deTurckRicciRHS_chartSecondOrderPart_spec`), whose
gauge-cancelled principal symbol is the geometer-sign isotropic symbol. -/
theorem deTurckRicciRHS_hasPrincipalSymbol_at_self [I.Boundaryless]
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    HasPrincipalSymbol (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀
      (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀)) :=
  ⟨deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg,
    (deTurckRicciRHS_chartSecondOrderPart_spec (I := I) g₀ g_bg).1,
    (deTurckRicciRHS_chartSecondOrderPart_spec (I := I) g₀ g_bg).2⟩

/-- The Ricci–DeTurck right-hand side `g ↦ -2 Rc(g) + 𝓛_{W(g, g_bg)} g` is strictly
parabolic at its own base metric `g₀`, in the sense of `IsStrictlyParabolicMetricRHS`:
it has a principal symbol there (`deTurckRicciRHS_hasPrincipalSymbol_at_self`). -/
theorem deTurckRicciRHS_isStrictlyParabolic_at_self [I.Boundaryless]
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsStrictlyParabolicMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ :=
  ⟨DifferentialGeometry.PDE.DeTurck.isotropicSymbol
      (E := E)
      (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
      (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀),
    deTurckRicciRHS_hasPrincipalSymbol_at_self g₀ g_bg⟩

/-- **Bridge from a principal-symbol witness to strict parabolicity of the metric RHS.**

If an operator `F` on smooth Riemannian metrics has *some* principal symbol `σ` at the
metric `g₀` (the existence of `σ` such that `HasPrincipalSymbol F g₀ σ`), then it is
strictly parabolic at `g₀` in the sense of `IsStrictlyParabolicMetricRHS`.

This is the trivial repackaging the downstream parabolic-existence consumer expects:
`IsStrictlyParabolicMetricRHS` is, by definition, the existence statement
`∃ σ, HasPrincipalSymbol F g₀ σ` — so any witness `(σ, h)` packages directly.  The
content of strict parabolicity is then carried by `HasPrincipalSymbol`'s body, namely the
chart second-order part data `IsChartLinearizationSecondOrderPart F g₀ P` and the
strictly-parabolic principal symbol `IsPrincipalSymbolOfSecondOrderPart g₀ P σ`. -/
theorem bridge_symbol_equality_to_is_strictly_parabolic_metric_rhs
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M)
    (h : HasPrincipalSymbol F g₀ σ) :
    IsStrictlyParabolicMetricRHS (I := I) F g₀ :=
  ⟨σ, h⟩

end DifferentialGeometry.PDE.RicciFlow
