import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism

/-!
# Off-centre chart-`α` frame expansion of the differentiated base curvature `∇R`

`Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre` establishes the off-centre
chart-`α` basis identity for the base Riemann operator: at `x ∈ chartLeviCivitaGoodSet α`,
```
riemannOp (LeviCivita g) x (e^α_j x) (e^α_k x) (e^α_i x)
  = ∑ l, R^l{}_{ijk}(g, α)(ϕ_α x) • e^α_l x.
```

This file pushes that identity **one covariant-derivative order higher**, expanding the
differentiated base curvature `nablaBaseSlotCurv g X Y Z x u = (∇_X R^{TM})(Y, Z) u`
(`DifferentiatedRicciEndomorphism`) on chart-`α` frame vectors, for globally-smooth fields
agreeing with the chart-`α` frame near `x`:
```
(∇_{e^α_p} R)(e^α_q, e^α_r)(e^α_s x)
  = ∑ l, (∂_p R^l{}_{srq}(g, α)(ϕ_α x)
            + Γ-corrections in chartChristoffel · chartRiemannTensor) • e^α_l x.
```
The coefficient is a **fixed polynomial** in the chart Christoffel symbols `chartChristoffel`,
the chart Riemann coefficients `chartRiemannTensor`, and their first Euclidean partials, all of
which are `C^∞` on the chart-target interior. The exact coefficient is irrelevant downstream;
the file records that `(∇_{e^α} R)(e^α, e^α)(e^α)` expands in the chart-`α` frame with a
coefficient `nablaChartRiemannCoeff` that is `C^∞` on the chart-target interior — hence
uniformly bounded on the compact partition-of-unity supports — which is what the compact-uniform
differentiated-curvature `g`-norm bound rests on.

## Strategy

The differentiated curvature unfolds (`nablaCurvSec_def`) into four Leibniz terms:
`∇_p(R(e_q, e_r) e_s) − R(∇_p e_q, e_r) e_s − R(e_q, ∇_p e_r) e_s − R(e_q, e_r)(∇_p e_s)`.

* The leading term `∇_p(R(e_q, e_r) e_s)` is the covariant derivative of the curvature section
  `b ↦ R(e_q, e_r) e_s (b)`, which on the good set equals `∑_m R^m{}_{srq}(g, α)(ϕ_α b) • e^α_m b`
  (`riemannOp_chartBasisVec_alpha_eq` pointwise). Its covariant derivative along `e^α_p` is
  computed by the Leibniz rule, exactly as in `LeviCivita_chartBasisVec_secondCovDeriv_alpha`:
  the partial derivative of the chart Riemann coefficient times the frame, plus the coefficient
  times the chart-Christoffel first covariant derivative of the frame.
* The three correction curvatures `R(∇_p e_q, e_r) e_s`, etc., substitute the chart-Christoffel
  first covariant derivative `∇_p e_q = ∑_m Γ^m{}_{pq} e^α_m` and expand each `R(e_m, e_r) e_s`
  by `riemannOp_chartBasisVec_alpha_eq`.

## Main results

* `nablaCurvSec_chartBasisVec_alpha_frame_expand` — the off-centre chart-`α` frame expansion
  of the differentiated base curvature on chart-frame triples, with the chart `∇R` coefficient
  `nablaChartRiemannCoeff`.
* `nablaChartRiemannCoeff_contDiffOn_interior` — the chart `∇R` coefficient is `C^∞` on the
  chart-target interior.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The chart-`α` differentiated-Riemann coefficient.** For chart indices `p` (derivation),
`q, r` (antisymmetric), `s` (acted), `l` (frame), this is the coefficient of `e^α_l` in the
chart-`α` frame expansion of `(∇_{e^α_p} R)(e^α_q, e^α_r)(e^α_s)`. It is the fixed polynomial in
the chart Christoffel symbols, the chart Riemann coefficients, and the first partial derivative
of the chart Riemann coefficients given by the four-term Leibniz expansion of `nablaCurvSec`:
```
nablaChartRiemannCoeff g α p q r s l
  = ∂_p R^l{}_{sqr}
    + ∑_m R^m{}_{sqr} Γ^l{}_{pm}
    − ∑_m Γ^m{}_{pq} R^l{}_{smr}
    − ∑_m Γ^m{}_{pr} R^l{}_{sqm}
    − ∑_m Γ^m{}_{ps} R^l{}_{mqr},
```
with `R^l{}_{ijk} := chartRiemannTensor g α i j k l` and `Γ^k{}_{ij} := chartChristoffel g α i j k`,
all evaluated at the Euclidean chart point `y`. -/
def nablaChartRiemannCoeff (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s l : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l) y
      + (∑ m : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) g α s q r m y *
            chartChristoffel (I := I) g α p m l y)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p q m y *
            chartRiemannTensor (I := I) g α s m r l y)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p r m y *
            chartRiemannTensor (I := I) g α s q m l y)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p s m y *
            chartRiemannTensor (I := I) g α m q r l y)

set_option linter.unusedSectionVars false in
/-- The first model-basis partial derivative of a function `C^∞` on the chart-target interior is
again `C^∞` there. -/
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

set_option linter.unusedSectionVars false in
/-- The chart-`α` Riemann coefficient `chartRiemannTensor g α i j k l` is `C^∞` on the interior
of the chart target. It is the polynomial `∂Γ − ∂Γ + ΓΓ` in the chart Christoffel symbols, each
of which is `C^∞` there (`chartChristoffel_contDiffOn_interior`). -/
private lemma chartRiemannTensor_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      (interior ((extChartAt I α).target : Set E)) := by
  classical
  set U : Set E := interior ((extChartAt I α).target : Set E) with hU_def
  have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b c) U :=
    fun a b c => chartChristoffel_contDiffOn_interior (I := I) g α a b c
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

set_option linter.unusedSectionVars false in
/-- **The chart-`α` differentiated-Riemann coefficient is `C^∞` on the chart-target interior.**
It is a polynomial in the chart Christoffel symbols, the chart Riemann coefficients, and the
first partials of the chart Riemann coefficients, each `C^∞` on the chart-target interior
(`chartChristoffel_contDiffOn_interior`, `chartRiemannTensor_contDiffOn_interior`,
`partialDeriv_contDiffOn_interior_of_contDiffOn`). -/
theorem nablaChartRiemannCoeff_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (nablaChartRiemannCoeff (I := I) g α p q r s l)
      (interior ((extChartAt I α).target : Set E)) := by
  classical
  set U : Set E := interior ((extChartAt I α).target : Set E) with hU_def
  have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b c) U :=
    fun a b c => chartChristoffel_contDiffOn_interior (I := I) g α a b c
  have hR : ∀ a b c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α a b c d) U :=
    fun a b c d => chartRiemannTensor_contDiffOn_interior (I := I) g α a b c d
  have hdR : ContDiffOn ℝ ∞
      (partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hR s q r l) p
  have hsum1 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α s q r m y *
          chartChristoffel (I := I) g α p m l y) U :=
    ContDiffOn.sum (fun m _ => (hR s q r m).mul (hΓ p m l))
  have hsum2 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p q m y *
          chartRiemannTensor (I := I) g α s m r l y) U :=
    ContDiffOn.sum (fun m _ => (hΓ p q m).mul (hR s m r l))
  have hsum3 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p r m y *
          chartRiemannTensor (I := I) g α s q m l y) U :=
    ContDiffOn.sum (fun m _ => (hΓ p r m).mul (hR s q m l))
  have hsum4 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p s m y *
          chartRiemannTensor (I := I) g α m q r l y) U :=
    ContDiffOn.sum (fun m _ => (hΓ p s m).mul (hR m q r l))
  have hrw : (nablaChartRiemannCoeff (I := I) g α p q r s l) =
      fun y : E =>
        partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l) y
          + (∑ m : Fin (Module.finrank ℝ E),
              chartRiemannTensor (I := I) g α s q r m y *
                chartChristoffel (I := I) g α p m l y)
          - (∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α p q m y *
                chartRiemannTensor (I := I) g α s m r l y)
          - (∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α p r m y *
                chartRiemannTensor (I := I) g α s q m l y)
          - (∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α p s m y *
                chartRiemannTensor (I := I) g α m q r l y) := rfl
  rw [hrw]
  exact ((((hdR.add hsum1).sub hsum2).sub hsum3).sub hsum4)

/-! ### The four Leibniz terms of `nablaCurvSec` on chart-`α` frame vectors -/

/-- **Leading term: covariant derivative of the chart-`α` curvature section.** For globally-smooth
fields `Xp, Xq, Xr, Xs` agreeing with the chart-`α` frame fields `e^α_p, e^α_q, e^α_r, e^α_s` on
an open neighbourhood `U ∋ x` inside `chartLeviCivitaGoodSet α`, the covariant derivative of the
curvature section `b ↦ R(Xq, Xr) Xs (b)` along `Xp` at `x` equals
`∑_l (∂_p R^l{}_{sqr} + ∑_m R^m{}_{sqr} Γ^l{}_{pm}) • e^α_l x`, by the chart-`α` frame expansion of
the curvature section (`riemannOp_chartBasisVec_alpha_eq` pointwise) and the Leibniz rule. -/
private lemma nablaCurvSec_chartBasisVec_alpha_leadingTerm
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (_hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    (LeviCivita (I := I) g).toFun
        (fun b => riemannSec (LeviCivita (I := I) g) Xq Xr Xs b) x (Xp x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l) (extChartAt I α x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartRiemannTensor (I := I) g α s q r m (extChartAt I α x) *
              chartChristoffel (I := I) g α p m l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hXp_x : Xp x = chartBasisVecFiber (I := I) α p x := hXp_eq x hxU
  set S : Π y : M, TangentSpace I y := fun b => riemannSec cov Xq Xr Xs b with hS_def
  have hS_diff : MDiffAt (T% S) x :=
    (riemannSec_contMDiff (cov := cov) hXq hXr hXs x).mdifferentiableAt (by simp)

  set Rc : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m y => chartRiemannTensor (I := I) g α s q r m (extChartAt I α y) with hRc_def
  set term : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun m y => Rc m y • chartBasisVecFiber (I := I) α m y with hterm_def
  have hS_eq_sum_on_U : ∀ y ∈ U, S y = ∑ m : Fin (Module.finrank ℝ E), term m y := by
    intro y hy
    have hy_good : y ∈ chartLeviCivitaGoodSet (I := I) α := hU_good hy
    have hSval : S y = riemannSec cov Xq Xr Xs y := rfl
    rw [hSval]

    rw [← riemannOp_apply_smooth (cov := cov) hXq hXr hXs]
    rw [hXq_eq y hy, hXr_eq y hy, hXs_eq y hy]
    rw [riemannOp_chartBasisVec_alpha_eq (I := I) g α s q r hy_good]
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hRc_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (Rc m) x := by
    intro m
    have hR_cda : ContDiffAt ℝ ∞ (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
      have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
        chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
      exact (chartRiemannTensor_contDiffOn_interior (I := I) g α s q r m).contDiffAt
        (isOpen_interior.mem_nhds hxint)
    have hR_d : DifferentiableAt ℝ (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) :=
      hR_cda.differentiableAt (by simp)
    have hR_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hR_d
    have hphi_mdiff : MDiffAt (extChartAt I α) x :=
      mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
    exact hR_mdiff.comp x hphi_mdiff
  have hframe_diff : ∀ m : Fin (Module.finrank ℝ E),
      MDiffAt (T% (fun y : M => chartBasisVecFiber (I := I) α m y)) x :=
    fun m => chartBasisVec_alpha_mdifferentiableAt (I := I) α m hx
  have hterm_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (T% (term m)) x :=
    fun m => MDifferentiableAt.smul_section (hRc_diff m) (hframe_diff m)
  have hsum_diff :
      MDiffAt (T% fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    MDifferentiableAt.sum_section (s := Finset.univ) (t := term) hterm_diff
  have hS_ev_sum :
      (fun y : M => S y) =ᶠ[𝓝 x]
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) := by
    filter_upwards [hU_open.mem_nhds hxU] with y hy using hS_eq_sum_on_U y hy
  have hcov_S_eq :
      cov.toFun S x =
        cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hS_diff hsum_diff
      Filter.univ_mem hS_ev_sum
  rw [hS_def] at hcov_S_eq ⊢
  rw [hcov_S_eq, hXp_x]
  have hsum_apply :
      (cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x)
          (chartBasisVecFiber (I := I) α p x) =
        ∑ m : Fin (Module.finrank ℝ E),
          (cov.toFun (term m) x) (chartBasisVecFiber (I := I) α p x) := by
    have hfun :
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) =
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum term := by
      funext y; simp
    rw [hfun]
    exact leviCivita_finset_sum_apply (I := I) g
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) term
      (chartBasisVecFiber (I := I) α p x) hterm_diff
  rw [hsum_apply]
  have hleib : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (term m) x) (chartBasisVecFiber (I := I) α p x) =
        extDerivFun (I := I) (Rc m) x (chartBasisVecFiber (I := I) α p x) •
            chartBasisVecFiber (I := I) α m x +
          Rc m x •
            (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α m y) x)
              (chartBasisVecFiber (I := I) α p x) := by
    intro m
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y : M => chartBasisVecFiber (I := I) α m y) (g := Rc m) (x := x)
      (hframe_diff m) (hRc_diff m)
    have hterm_eq : term m = (Rc m) • (fun y : M => chartBasisVecFiber (I := I) α m y) := by
      funext y; rfl
    rw [hterm_eq]
    have happ := congr($(hleibniz) (chartBasisVecFiber (I := I) α p x))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] at happ
    rw [happ, add_comm]
  rw [Finset.sum_congr rfl (fun m _ => hleib m)]
  have hder : ∀ m : Fin (Module.finrank ℝ E),
      extDerivFun (I := I) (Rc m) x (chartBasisVecFiber (I := I) α p x) =
        partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
    intro m
    have hR_cda : ContDiffAt ℝ ∞ (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
      have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
        chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
      exact (chartRiemannTensor_contDiffOn_interior (I := I) g α s q r m).contDiffAt
        (isOpen_interior.mem_nhds hxint)
    exact extDerivFun_comp_extChartAt_apply_basis_alpha (I := I) α hx hR_cda p
  have hRc_x : ∀ m : Fin (Module.finrank ℝ E),
      Rc m x = chartRiemannTensor (I := I) g α s q r m (extChartAt I α x) := fun m => rfl
  have hinner : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α m y) x)
          (chartBasisVecFiber (I := I) α p x) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p m l (extChartAt I α x) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α p m hx]
  rw [Finset.sum_congr rfl (fun m _ => by rw [hder m, hRc_x m, hinner m])]

  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun l => chartBasisVecFiber (I := I) α l x with he_def
  set D : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x)
    with hD_def
  set Rr : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => chartRiemannTensor (I := I) g α s q r m (extChartAt I α x) with hRr_def
  set Γq : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m l => chartChristoffel (I := I) g α p m l (extChartAt I α x) with hΓq_def
  calc
    (∑ m : Fin (Module.finrank ℝ E),
        (D m • e m + Rr m • ∑ l : Fin (Module.finrank ℝ E), Γq m l • e l))
        = (∑ m : Fin (Module.finrank ℝ E), D m • e m) +
            (∑ m : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E), (Rr m * Γq m l) • e l) := by
          rw [Finset.sum_add_distrib]
          refine congrArg (fun t => (∑ m : Fin (Module.finrank ℝ E), D m • e m) + t) ?_
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul]
      _ = (∑ l : Fin (Module.finrank ℝ E), D l • e l) +
            (∑ l : Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E), (Rr m * Γq m l) • e l) := by
          rw [Finset.sum_comm]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (D l + ∑ m : Fin (Module.finrank ℝ E), Rr m * Γq m l) • e l := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← Finset.sum_smul, ← add_smul]

/-- **Bundled-`riemannOp` expansion of a chart-Christoffel-contracted antisymmetric slot.** For
`x ∈ chartLeviCivitaGoodSet α` and chart indices `m', r, s`, the bundled Riemann operator on the
frame triple `(e^α_{m'} x, e^α_r x, e^α_s x)` expands as `∑_l R^l{}_{s m' r} • e^α_l x`. This
restates `riemannOp_chartBasisVec_alpha_eq` (acted index `s`, first/second antisymmetric `m', r`)
in the bundled-`riemannOp` form. -/
private lemma riemannOp_chartFrame_triple
    (g : SmoothRiemannianMetric I M) (α : M)
    (m' r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    riemannOp (cov := LeviCivita (I := I) g) x
        (chartBasisVecFiber (I := I) α m' x) (chartBasisVecFiber (I := I) α r x)
        (chartBasisVecFiber (I := I) α s x) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α s m' r l (extChartAt I α x) •
          chartBasisVecFiber (I := I) α l x :=
  riemannOp_chartBasisVec_alpha_eq (I := I) g α s m' r hx

/-- **Chart-`α` frame value of a first covariant derivative.** For globally-smooth fields `Xp, Xq`
agreeing with the chart-`α` frame fields `e^α_p, e^α_q` on an open neighbourhood `U ∋ x` inside
`chartLeviCivitaGoodSet α`, the first covariant derivative value `(∇_{Xp} Xq)(x)` equals
`∑_m Γ^m{}_{pq}(ϕ_α x) • e^α_m x`, by germ-locality of `cov.toFun` in `Xq` and value-locality in
`Xp x`, reduced to `LeviCivita_chartBasisVec_alpha_basis_apply`. -/
private lemma covApply_chartFrame_value
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq : Π b : M, TangentSpace I b} {U : Set M}
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y) :
    covApply (LeviCivita (I := I) g) Xp Xq x =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p q m (extChartAt I α x) •
          chartBasisVecFiber (I := I) α m x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  rw [covApply_apply]
  have hXq_diff : MDiffAt (T% Xq) x := (hXq x).mdifferentiableAt (by simp)
  have hchart_q_diff : MDiffAt (T% (fun z : M => chartBasisVecFiber (I := I) α q z)) x :=
    chartBasisVec_alpha_mdifferentiableAt (I := I) α q hx
  have hXq_ev : (fun z : M => Xq z) =ᶠ[𝓝 x]
      (fun z : M => chartBasisVecFiber (I := I) α q z) := by
    filter_upwards [hU_open.mem_nhds hxU] with z hz using hXq_eq z hz
  have hcov_congr :
      cov.toFun Xq x = cov.toFun (fun z : M => chartBasisVecFiber (I := I) α q z) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hXq_diff hchart_q_diff
      Filter.univ_mem hXq_ev
  rw [hcov_congr, hXp_eq x hxU]
  rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α p q hx]

/-- **First correction term: `R(∇_p e_q, e_r) e_s` on chart-`α` frame vectors.** For
`x ∈ chartLeviCivitaGoodSet α`, the curvature with the chart-Christoffel first covariant
derivative `∇_{e^α_p} e^α_q = ∑_m Γ^m{}_{pq} e^α_m` inserted into the first antisymmetric slot
expands as `∑_l (∑_m Γ^m{}_{pq} R^l{}_{smr}) • e^α_l x`. -/
private lemma nablaCurvSec_chartBasisVec_alpha_corr_firstAntisym
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (_hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    riemannSec (LeviCivita (I := I) g) (covApply (LeviCivita (I := I) g) Xp Xq) Xr Xs x =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p q m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s m r l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hcXpXq := covApply_contMDiff (cov := cov) hXp hXq

  rw [← riemannOp_apply_smooth (cov := cov) hcXpXq hXr hXs]
  rw [covApply_chartFrame_value (I := I) g α p q hx hXq hU_open hxU hXp_eq hXq_eq,
    hXr_eq x hxU, hXs_eq x hxU]

  set er : TangentSpace I x := chartBasisVecFiber (I := I) α r x with her_def
  set es : TangentSpace I x := chartBasisVecFiber (I := I) α s x with hes_def
  have hexpand :
      riemannOp (cov := cov) x
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α p q m (extChartAt I α x) •
              chartBasisVecFiber (I := I) α m x) er es =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p q m (extChartAt I α x) •
            riemannOp (cov := cov) x (chartBasisVecFiber (I := I) α m x) er es := by
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply]
  rw [hexpand]
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α p q m (extChartAt I α x) •
          riemannOp (cov := cov) x (chartBasisVecFiber (I := I) α m x) er es =
        ∑ l : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α p q m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s m r l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [her_def, hes_def, riemannOp_chartFrame_triple (I := I) g α m r s hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun m _ => hper m), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_smul]

/-- **Second correction term: `R(e_q, ∇_p e_r) e_s` on chart-`α` frame vectors.** The chart
expansion with `∇_{e^α_p} e^α_r = ∑_m Γ^m{}_{pr} e^α_m` inserted into the second antisymmetric
slot, giving `∑_l (∑_m Γ^m{}_{pr} R^l{}_{sqm}) • e^α_l x`. -/
private lemma nablaCurvSec_chartBasisVec_alpha_corr_secondAntisym
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (_hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    riemannSec (LeviCivita (I := I) g) Xq (covApply (LeviCivita (I := I) g) Xp Xr) Xs x =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p r m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s q m l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hcXpXr := covApply_contMDiff (cov := cov) hXp hXr
  rw [← riemannOp_apply_smooth (cov := cov) hXq hcXpXr hXs]
  rw [hXq_eq x hxU,
    covApply_chartFrame_value (I := I) g α p r hx hXr hU_open hxU hXp_eq hXr_eq,
    hXs_eq x hxU]
  set eq' : TangentSpace I x := chartBasisVecFiber (I := I) α q x with heq'_def
  set es : TangentSpace I x := chartBasisVecFiber (I := I) α s x with hes_def
  have hexpand :
      riemannOp (cov := cov) x eq'
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α p r m (extChartAt I α x) •
              chartBasisVecFiber (I := I) α m x) es =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p r m (extChartAt I α x) •
            riemannOp (cov := cov) x eq' (chartBasisVecFiber (I := I) α m x) es := by
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply]
  rw [hexpand]
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α p r m (extChartAt I α x) •
          riemannOp (cov := cov) x eq' (chartBasisVecFiber (I := I) α m x) es =
        ∑ l : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α p r m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s q m l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [heq'_def, hes_def, riemannOp_chartFrame_triple (I := I) g α q m s hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun m _ => hper m), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_smul]

/-- **Third correction term: `R(e_q, e_r)(∇_p e_s)` on chart-`α` frame vectors.** The chart
expansion with `∇_{e^α_p} e^α_s = ∑_m Γ^m{}_{ps} e^α_m` inserted into the acted slot, giving
`∑_l (∑_m Γ^m{}_{ps} R^l{}_{mqr}) • e^α_l x`. -/
private lemma nablaCurvSec_chartBasisVec_alpha_corr_acted
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (_hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    riemannSec (LeviCivita (I := I) g) Xq Xr (covApply (LeviCivita (I := I) g) Xp Xs) x =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p s m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α m q r l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hcXpXs := covApply_contMDiff (cov := cov) hXp hXs
  rw [← riemannOp_apply_smooth (cov := cov) hXq hXr hcXpXs]
  rw [hXq_eq x hxU, hXr_eq x hxU,
    covApply_chartFrame_value (I := I) g α p s hx hXs hU_open hxU hXp_eq hXs_eq]
  set eq' : TangentSpace I x := chartBasisVecFiber (I := I) α q x with heq'_def
  set er : TangentSpace I x := chartBasisVecFiber (I := I) α r x with her_def
  have hexpand :
      riemannOp (cov := cov) x eq' er
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α p s m (extChartAt I α x) •
              chartBasisVecFiber (I := I) α m x) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p s m (extChartAt I α x) •
            riemannOp (cov := cov) x eq' er (chartBasisVecFiber (I := I) α m x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul]
  rw [hexpand]
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α p s m (extChartAt I α x) •
          riemannOp (cov := cov) x eq' er (chartBasisVecFiber (I := I) α m x) =
        ∑ l : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α p s m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α m q r l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [heq'_def, her_def, riemannOp_chartFrame_triple (I := I) g α q r m hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun m _ => hper m), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_smul]

/-- **Off-centre chart-`α` frame expansion of the differentiated base curvature `∇R`.** For
`x ∈ chartLeviCivitaGoodSet α` and globally-smooth tangent fields `Xp, Xq, Xr, Xs` agreeing with
the chart-`α` frame fields `e^α_p, e^α_q, e^α_r, e^α_s` on an open neighbourhood `U ∋ x` inside
the chart-`α` good set, the differentiated base curvature
`(∇_{Xp} R)(Xq, Xr) Xs (x) = nablaCurvSec (LeviCivita g) Xp Xq Xr Xs x` expands in the chart-`α`
frame with the chart `∇R` coefficient `nablaChartRiemannCoeff`:
```
nablaCurvSec (LeviCivita g) Xp Xq Xr Xs x
  = ∑ l, nablaChartRiemannCoeff g α p q r s l (ϕ_α x) • e^α_l x.
```
This is the off-centre chart-`α` analogue of `riemannOp_chartBasisVec_alpha_eq`, one
covariant-derivative order higher: it assembles the four Leibniz terms of `nablaCurvSec_def` from
the leading-term covariant derivative of the curvature section
(`nablaCurvSec_chartBasisVec_alpha_leadingTerm`) and the three chart-Christoffel-corrected
curvature terms (`..._corr_firstAntisym`, `..._corr_secondAntisym`, `..._corr_acted`). -/
theorem nablaCurvSec_chartBasisVec_alpha_frame_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    nablaCurvSec (LeviCivita (I := I) g) Xp Xq Xr Xs x =
      ∑ l : Fin (Module.finrank ℝ E),
        nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  rw [nablaCurvSec_def]
  rw [nablaCurvSec_chartBasisVec_alpha_leadingTerm (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq,
    nablaCurvSec_chartBasisVec_alpha_corr_firstAntisym (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq,
    nablaCurvSec_chartBasisVec_alpha_corr_secondAntisym (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq,
    nablaCurvSec_chartBasisVec_alpha_corr_acted (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq]

  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← sub_smul, ← sub_smul, ← sub_smul]
  rfl


end Connection
end Integral
end DifferentialGeometry

end
