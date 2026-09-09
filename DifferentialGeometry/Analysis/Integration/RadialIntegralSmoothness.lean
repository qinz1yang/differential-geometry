import DifferentialGeometry.Analysis.Integration.RadialIntegral
import DifferentialGeometry.Analysis.Integration.Measure.FiniteParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

universe u v

noncomputable section

open MeasureTheory Set

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace DifferentialGeometry.Integral

local instance : IsFiniteMeasure (volume : Measure (Icc (0 : ℝ) 1)) where
  measure_univ_lt_top := by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top

private theorem radialIntegral_eq_integral_subtype
    {E F : Type*} [AddCommMonoid E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (f : E → F) (x : E) :
    radialIntegral k f x = ∫ s : Icc (0 : ℝ) 1, (s : ℝ) ^ k • f ((s : ℝ) • x) := by
  rw [integral_subtype measurableSet_Icc (fun s : ℝ => s ^ k • f (s • x)),
    integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.integral_of_le zero_le_one

section NormedDomain

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousOn_radialIntegral (k : ℕ) {f : E → F} {U : Set E}
    (hstar : StarConvex ℝ 0 U) (hf : ContinuousOn f U) :
    ContinuousOn (radialIntegral k f) U := by
  have hF : ContinuousOn
      (fun p : E × Icc (0 : ℝ) 1 => (p.2 : ℝ) ^ k • f ((p.2 : ℝ) • p.1))
      (U ×ˢ univ) := by
    apply (by fun_prop : ContinuousOn (fun p : E × Icc (0 : ℝ) 1 => (p.2 : ℝ) ^ k)
      (U ×ˢ univ)).smul
    exact hf.comp (by fun_prop) (fun p hp => hstar.smul_mem hp.1 p.2.property.1 p.2.property.2)
  simpa only [← radialIntegral_eq_integral_subtype] using
    (continuousOn_integral_of_compact_support (μ := (volume : Measure (Icc (0 : ℝ) 1)))
      (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) 1)))
      (f := fun v (s : Icc (0 : ℝ) 1) => (s : ℝ) ^ k • f ((s : ℝ) • v)) hF
      (fun p s _ hs => (hs (mem_univ s)).elim))

theorem hasFDerivAt_radialIntegral (k : ℕ) {f : E → F} {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hf : ContDiffOn ℝ 1 f U)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (radialIntegral k f) (radialIntegral (k + 1) (fderiv ℝ f) x) x := by
  let A := fun v : E => fun s : Icc (0 : ℝ) 1 => (s : ℝ) ^ k • f ((s : ℝ) • v)
  let A' := fun v : E => fun s : Icc (0 : ℝ) 1 =>
    (s : ℝ) ^ (k + 1) • fderiv ℝ f ((s : ℝ) • v)
  have hA : ContinuousOn (fun p : E × Icc (0 : ℝ) 1 => A p.1 p.2) (U ×ˢ univ) := by
    apply (by fun_prop : ContinuousOn (fun p : E × Icc (0 : ℝ) 1 => (p.2 : ℝ) ^ k)
      (U ×ˢ univ)).smul
    exact hf.continuousOn.comp (by fun_prop)
      (fun p hp => hstar.smul_mem hp.1 p.2.property.1 p.2.property.2)
  have hA' : ContinuousOn (fun p : E × Icc (0 : ℝ) 1 => A' p.1 p.2) (U ×ˢ univ) := by
    apply (by fun_prop : ContinuousOn (fun p : E × Icc (0 : ℝ) 1 => (p.2 : ℝ) ^ (k + 1))
      (U ×ˢ univ)).smul
    exact (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp (by fun_prop)
      (fun p hp => hstar.smul_mem hp.1 p.2.property.1 p.2.property.2)
  have hdiff (v : E) (hv : v ∈ U) (s : Icc (0 : ℝ) 1) :
      HasFDerivAt (fun z => A z s) (A' v s) v := by
    have hfv := ((hf.differentiableOn one_ne_zero) _
      (hstar.smul_mem hv s.property.1 s.property.2)).differentiableAt
        (hU.mem_nhds (hstar.smul_mem hv s.property.1 s.property.2))
    have hd := (hfv.hasFDerivAt.comp v ((hasFDerivAt_id v).const_smul (s : ℝ))).const_smul
      ((s : ℝ) ^ k)
    change HasFDerivAt (fun z => (s : ℝ) ^ k • f ((s : ℝ) • z))
      ((s : ℝ) ^ k • (fderiv ℝ f ((s : ℝ) • v)).comp
        ((s : ℝ) • ContinuousLinearMap.id ℝ E)) v at hd
    convert hd using 1
    ext w
    simp only [A', smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul, pow_succ]
  have h := Measure.hasFDerivAt_integral_compactOn volume hU A A' hA hA' hdiff x hx
  simpa only [A, A', ← radialIntegral_eq_integral_subtype] using h

theorem fderiv_radialIntegral (k : ℕ) {f : E → F} {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hf : ContDiffOn ℝ 1 f U)
    {x : E} (hx : x ∈ U) :
    fderiv ℝ (radialIntegral k f) x = radialIntegral (k + 1) (fderiv ℝ f) x :=
  (hasFDerivAt_radialIntegral k hU hstar hf hx).fderiv

end NormedDomain

theorem contDiffOn_radialIntegral_joint
    {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞) (k : ℕ) {S : Set P} {U : Set E} (hS : IsOpen S) (hU : IsOpen U)
    (hstar : StarConvex ℝ 0 U) {f : P → E → F}
    (hf : ContDiffOn ℝ n (Function.uncurry f) (S ×ˢ U)) :
    ContDiffOn ℝ n (fun p : P × E => radialIntegral k (f p.1) p.2) (S ×ˢ U) := by
  let A : (P × E) × ℝ → P × E := fun z => (z.1.1, z.2 • z.1.2)
  let Ω := A ⁻¹' (S ×ˢ U)
  have hA : ContDiff ℝ n A := by fun_prop
  have hΩ : IsOpen Ω := (hS.prod hU).preimage hA.continuous
  have hsub : (S ×ˢ U) ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := by
    intro z hz
    exact ⟨hz.1.1, hstar.smul_mem hz.1.2 hz.2.1 hz.2.2⟩
  have hint : ContDiffOn ℝ n
      (fun z : (P × E) × ℝ => z.2 ^ k • f z.1.1 (z.2 • z.1.2)) Ω := by
    exact (contDiffOn_snd.pow k).smul (hf.comp hA.contDiffOn (fun _ hz => hz))
  apply (DifferentialGeometry.Integral.Measure.contDiffOn_integral_subtype_of_isCompact n isCompact_Icc volume
    (hS.prod hU) hΩ hsub hint).congr
  intro z _
  rw [radialIntegral, integral_subtype measurableSet_Icc
    (fun s : ℝ => s ^ k • f z.1 (s • z.2)), integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.integral_of_le zero_le_one

theorem contDiffOn_radialIntegral
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞) (k : ℕ) {f : E → F} {U : Set E} (hU : IsOpen U)
    (hstar : StarConvex ℝ 0 U) (hf : ContDiffOn ℝ n f U) :
    ContDiffOn ℝ n (radialIntegral k f) U := by
  have hF : ContDiffOn ℝ n (Function.uncurry (fun (_ : ℝ) => f)) (univ ×ˢ U) :=
    hf.comp contDiffOn_snd (fun _ hp => hp.2)
  exact (contDiffOn_radialIntegral_joint n k isOpen_univ hU hstar hF).comp
    (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => ⟨mem_univ (0 : ℝ), hx⟩)

end DifferentialGeometry.Integral
