import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contDiffAt_prodChart_of_isInteriorPoint
    {n : WithTop ℕ∞} {F : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hx : I.IsInteriorPoint x)
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n F (t, x)) :
    ContDiffAt ℝ n
      (fun p : ℝ × E => F (p.1, (extChartAt I x).symm p.2))
      (t, extChartAt I x x) := by
  have hsrc := (contMDiffAt_iff_source
    (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ)) (f := F) (x := (t, x))).mp hF
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hsrc
  have hn : Set.range (𝓘(ℝ, ℝ).prod I) ∈
      𝓝 (extChartAt (𝓘(ℝ, ℝ).prod I) (t, x) (t, x)) := by
    rw [ModelWithCorners.range_prod, extChartAt_prod, extChartAt_model_space_eq_id]
    exact prod_mem_nhds (by simp) (range_mem_nhds_isInteriorPoint hx)
  have hd := hsrc.contDiffAt hn
  simpa only [Function.comp_def, extChartAt_prod, PartialEquiv.prod_coe_symm,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    extChartAt_coe_symm, Function.id_def, PartialEquiv.prod_coe, Prod.map_apply] using hd

theorem mvfderiv_eq_fderiv_of_isInteriorPoint
    {f : M → ℝ} {x : M} (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (v : TangentSpace I x) :
    mvfderiv (I := I) f x v =
      fderiv ℝ (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) v := by
  have hm := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x))
    (congrArg (fun L => L v) hf.mfderiv)
  rw [fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)] at hm
  change mvfderiv (I := I) f x v =
    fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) (extChartAt I x x) v at hm
  simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp, Function.comp_def, id_eq] using hm

theorem hasDerivAt_mvfderiv_of_contMDiffAt
    {F : ℝ → M → ℝ} {Ft : M → ℝ} {t : ℝ} {x : M}
    (hx : I.IsInteriorPoint x)
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
      (fun p : ℝ × M => F p.1 p.2) (t, x))
    (hFdiff : ∀ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (F s) x)
    (hFtdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) Ft x)
    (htime : ∀ y, HasDerivAt (fun s => F s y) (Ft y) t)
    (v : TangentSpace I x) :
    HasDerivAt (fun s => mvfderiv (I := I) (F s) x v)
      (mvfderiv (I := I) Ft x v) t := by
  let Φ : ℝ → E → ℝ := fun s y => F s ((extChartAt I x).symm y)
  have hΦ : ContDiffAt ℝ 2 (fun p : ℝ × E => Φ p.1 p.2)
      (t, extChartAt I x x) := contDiffAt_prodChart_of_isInteriorPoint hx hF
  have hraw : (fun y : E => Ft ((extChartAt I x).symm y)) =ᶠ[𝓝 (extChartAt I x x)]
      fun y => (fderiv ℝ (fun p : ℝ × E => Φ p.1 p.2) (t, y)) (1, 0) := by
    apply eventuallyEq_timeFDeriv (Φ := Φ)
      (Ψ := fun _ y => Ft ((extChartAt I x).symm y))
      (timeSet := Set.univ) (t := t)
    · exact Filter.univ_mem
    · have hev := (hΦ.eventually (by norm_num)).mono fun p hp =>
        (hp.of_le (by norm_num)).differentiableAt_one
      have hev' : ∀ᶠ p in 𝓝 t ×ˢ 𝓝 (extChartAt I x x),
          DifferentiableAt ℝ (fun p : ℝ × E => Φ p.1 p.2) p := by
        simpa only [nhds_prod_eq] using hev
      exact (tendsto_const_nhds.prodMk (Filter.tendsto_id)).eventually hev'
    · exact Filter.Eventually.of_forall fun y => (htime _).hasDerivWithinAt
  have hd := fixedBaseFDerivTimeDerivativeAt_of_contDiffAt Φ (V := v) hΦ
  have hleft (s : ℝ) := mvfderiv_eq_fderiv_of_isInteriorPoint hx (hFdiff s) v
  have hright := mvfderiv_eq_fderiv_of_isInteriorPoint hx hFtdiff v
  rw [hraw.fderiv_eq] at hright
  simp_rw [hleft]
  exact hd.congr_deriv hright.symm

end DifferentialGeometry
