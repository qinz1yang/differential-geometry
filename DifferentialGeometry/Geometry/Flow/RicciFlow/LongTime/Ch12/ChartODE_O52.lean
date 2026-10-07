import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartConnection_O52
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# CH12-O52 G2a: the chart map solves a first-order system

`w = (Ψ, DΨ)` satisfies `Dw = chartODE_O52 P ((G̃, DG̃), w)` (`secondDeriv_eq_O52`), and
`chartODE_O52 P` is smooth on `{A invertible} × univ × T × univ` (`[FROZEN] CH12-O52 G2`).
-/

set_option autoImplicit false

open Set
open scoped ContDiff
open DifferentialGeometry.CheegerGromovCompactness

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The right-hand side of the first-order system for `(Ψ, DΨ)`. -/
noncomputable def chartODE_O52 (P : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q : ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E))) :
    E →L[ℝ] (E × (E →L[ℝ] E)) :=
  q.2.2.prod ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (q.2.2.comp q.1.1.inverse)).comp
    ((1 / 2 : ℝ) • (koszul_O52 q.1.2 -
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)
          ((ContinuousLinearMap.compL ℝ E E ℝ).flip q.2.2)).comp
        (((ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)).flip q.2.2).comp
          ((koszul_O52 (fderiv ℝ P q.2.1)).comp q.2.2)))))

theorem chartODE_O52_apply_fst (P : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q : ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E))) (a : E) :
    (chartODE_O52 P q a).1 = q.2.2 a := rfl

theorem chartODE_O52_apply_snd (P : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q : ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E))) (a b : E) :
    (chartODE_O52 P q a).2 b = q.2.2 (q.1.1.inverse ((1 / 2 : ℝ) • (koszul_O52 q.1.2 a b -
      (koszul_O52 (fderiv ℝ P q.2.1) (q.2.2 a) (q.2.2 b)).comp q.2.2))) := by
  simp [chartODE_O52]

theorem contDiff_koszul_O52 : ContDiff ℝ ∞ (koszul_O52 (E := E)) := by
  let fl := (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have h : (koszul_O52 (E := E)) = fun T => T + fl T - L.comp (fl T) := rfl
  rw [h]
  exact (contDiff_id.add fl.contDiff).sub (contDiff_const.clm_comp fl.contDiff)

/-- `chartODE_O52 P` is smooth on `{A invertible} × univ × T × univ`. -/
theorem contDiffOn_chartODE_O52 [FiniteDimensional ℝ E] {P : E → E →L[ℝ] E →L[ℝ] ℝ} {T : Set E}
    (hT : IsOpen T) (hP : ContDiffOn ℝ ∞ P T) :
    ContDiffOn ℝ ∞ (chartODE_O52 P)
      (({A | A.IsInvertible} ×ˢ univ) ×ˢ (T ×ˢ univ)) := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨⟨hA, -⟩, hz, -⟩ := hq
  have hN : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) => q.2.2) q :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hA' : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) =>
        q.1.1.inverse) q :=
    (hA.contDiffAt_map_inverse).comp q (contDiff_fst.comp contDiff_fst).contDiffAt
  have hA'' : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) => q.1.2) q :=
    (contDiff_snd.comp contDiff_fst).contDiffAt
  have hDP : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) =>
        fderiv ℝ P q.2.1) q := by
    have h1 : ContDiffOn ℝ ∞ (fun z => fderiv ℝ P z) T :=
      hP.fderiv_of_isOpen hT (by exact_mod_cast le_top)
    exact (h1.contDiffAt (hT.mem_nhds hz)).comp q (contDiff_fst.comp contDiff_snd).contDiffAt
  have hK1 := contDiff_koszul_O52.contDiffAt.comp q hA''
  have hK2 := contDiff_koszul_O52.contDiffAt.comp q hDP
  have hpre : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) =>
        ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)
          ((ContinuousLinearMap.compL ℝ E E ℝ).flip q.2.2)) q :=
    contDiffAt_const.clm_apply (contDiffAt_const.clm_apply hN)
  have hfl : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) =>
        (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)).flip q.2.2) q :=
    contDiffAt_const.clm_apply hN
  have hY := hpre.clm_comp (hfl.clm_comp (hK2.clm_comp hN))
  have hX := (contDiffAt_const (c := (1 / 2 : ℝ))).smul (hK1.sub hY)
  have hpost : ContDiffAt ℝ ∞ (fun q :
      ((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) × (E × (E →L[ℝ] E)) =>
        ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (q.2.2.comp q.1.1.inverse)) q :=
    contDiffAt_const.clm_apply (hN.clm_comp hA')
  have hS := hpost.clm_comp hX
  have hprod := (contDiffAt_const (c := (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := E) (F := E)
    (G := E →L[ℝ] E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).clm_apply
      (hN.prodMk hS)
  exact hprod

/-- **The system** `D(Ψ, DΨ) = chartODE_O52 P ((G̃, DG̃), (Ψ, DΨ))` at a point. -/
theorem fderiv_chartPair_eq_O52 [FiniteDimensional ℝ E] {P : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Ψ : E → E} {y : E} (hP : DifferentiableAt ℝ P (Ψ y)) (hΨ : ContDiffAt ℝ ∞ Ψ y)
    (hsym : ∀ v w, P (Ψ y) v w = P (Ψ y) w v)
    (hA : (pullbackForm (P (Ψ y), fderiv ℝ Ψ y)).IsInvertible) :
    fderiv ℝ (fun x => (Ψ x, fderiv ℝ Ψ x)) y =
      chartODE_O52 P ((pullbackForm (P (Ψ y), fderiv ℝ Ψ y),
        fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y), (Ψ y, fderiv ℝ Ψ y)) := by
  have hΨ2 : ContDiffAt ℝ 2 Ψ y := hΨ.of_le (by simp)
  have hΨd : DifferentiableAt ℝ Ψ y := hΨ2.differentiableAt (by norm_num)
  have hMd : DifferentiableAt ℝ (fderiv ℝ Ψ) y :=
    (hΨ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [DifferentiableAt.fderiv_prodMk hΨd hMd]
  ext a : 1
  refine Prod.ext rfl ?_
  ext b : 1
  rw [chartODE_O52_apply_snd]
  exact secondDeriv_eq_O52 hP hΨ2 hsym hA a b

end GC.LongTime.Ch12
