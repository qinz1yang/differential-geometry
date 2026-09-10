import DifferentialGeometry.Topology.Morse.RelativePerturbationPositive
import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace Poincare.Morse
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem associated_chartHessianAt_eq {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    QuadraticMap.associated (R := ℝ) (chartHessianAt g x) = chartHessianBilinAt g x := by
  apply QuadraticMap.associated_left_inverse
  intro v w
  exact hg.isSymmSndFDerivAt (by norm_num) v w


theorem separatingLeft_chartHessianAt_iff {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    (QuadraticMap.associated (R := ℝ) (chartHessianAt g x)).SeparatingLeft ↔
      Injective (fderiv ℝ (fderiv ℝ g) x) := by
  rw [associated_chartHessianAt_eq hg]
  constructor
  · intro h v w hvw
    apply sub_eq_zero.mp
    apply h
    intro z
    change (fderiv ℝ (fderiv ℝ g) x) (v - w) z = 0
    rw [map_sub, hvw, sub_self, zero_apply]
  · intro h v hv
    apply h
    apply ContinuousLinearMap.ext
    intro w
    have hw : (fderiv ℝ (fderiv ℝ g) x) v w = 0 := hv w
    simpa only [map_zero, zero_apply] using hw

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


theorem isNondegenerateCriticalPointAt_of_bijective_hessian {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hx : I.IsInteriorPoint x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0)
    (hess : Bijective (fderiv ℝ (fderiv ℝ (fun z => f ((extChartAt I x).symm z)))
      (extChartAt I x x))) : IsNondegenerateCriticalPointAt I f x := by
  refine ⟨hcrit,?_⟩
  apply (separatingLeft_chartHessianAt_iff _).mpr hess.1
  let c := Poincare.Manifold.interiorChart I ∞ x
  have hc : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  exact (((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
    (c.open_target.mem_nhds (c.map_source hc))).contDiffAt).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

variable [FiniteDimensional ℝ E] [T2Space M]


theorem exists_positive_relative_morse_on_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U S : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hUS : U ⊆ S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ S, 0 < g x) ∧ ∀ x ∈ K, IsCriticalPointAt I g x →
        IsNondegenerateCriticalPointAt I g x := by
  obtain ⟨g,hg,hfix,hpositive,hreg⟩ :=
    exists_positive_relative_nondegenerate_perturbation hf hK hU hKU hKI hUS hpos
  exact ⟨g,hg,hfix,hpositive,fun x hx hc =>
    isNondegenerateCriticalPointAt_of_bijective_hessian hg (hKI x hx) hc (hreg x hx hc)⟩

end Poincare.Morse
