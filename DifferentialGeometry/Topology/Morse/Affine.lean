import DifferentialGeometry.Topology.Morse.RelativePerturbationMorse
import DifferentialGeometry.Topology.Manifold.MFDeriv.Affine

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


private theorem fderiv_fderiv_const_sub (f : E → ℝ) (b : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => b - f y)) x = -fderiv ℝ (fderiv ℝ f) x := by
  have heq : fderiv ℝ (fun y => b - f y) = -fderiv ℝ f := funext fun y => fderiv_const_sub b
  rw [heq,fderiv_neg]

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}


theorem isCriticalPointAt_const_sub_iff {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (b : ℝ) :
    IsCriticalPointAt I (fun y => b - f y) x ↔ IsCriticalPointAt I f x := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => b - f y) x) = 0 ↔
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) = 0
  rw [DifferentialGeometry.Manifold.mfderiv_const_sub_real hf b,neg_eq_zero]

variable [IsManifold I ∞ M]


theorem isNondegenerateCriticalPointAt_const_sub_iff {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hx : I.IsInteriorPoint x) (b : ℝ) :
    IsNondegenerateCriticalPointAt I (fun y => b - f y) x ↔ IsNondegenerateCriticalPointAt I f x := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  let g : E → ℝ := fun z => f (c.symm z)
  have hxc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hg : ContDiffAt ℝ 2 g (c x) :=
    (((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
      (c.open_target.mem_nhds (c.map_source hxc))).contDiffAt).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hbg : ContDiffAt ℝ 2 (fun z => b - g z) (c x) := contDiffAt_const.sub hg
  change (IsCriticalPointAt I (fun y => b - f y) x ∧
      (QuadraticMap.associated (R := ℝ) (chartHessianAt (fun z => b - g z) (c x))).SeparatingLeft) ↔
    (IsCriticalPointAt I f x ∧ (QuadraticMap.associated (R := ℝ) (chartHessianAt g (c x))).SeparatingLeft)
  rw [isCriticalPointAt_const_sub_iff (hf.mdifferentiableAt (by simp)) b,
    separatingLeft_chartHessianAt_iff hbg,separatingLeft_chartHessianAt_iff hg,fderiv_fderiv_const_sub]
  constructor
  · rintro ⟨hc,h⟩
    refine ⟨hc,fun v w hvw => ?_⟩
    exact h (congrArg Neg.neg hvw)
  · rintro ⟨hc,h⟩
    refine ⟨hc,fun v w hvw => ?_⟩
    exact h (neg_injective hvw)

end DifferentialGeometry.Morse
