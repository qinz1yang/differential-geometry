import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lExpGram_det_pos_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    0 < (lExpGram S T x Z tau).det := by
  let z : E := Z
  let L : E →ₗ[ℝ] TangentSpace I (lExp S T x Z tau) :=
    { toFun := fun V ↦ lExpField S T x Z V tau
      map_add' := by
        intro V W
        exact (mfderiv 𝓘(ℝ, E) I
          (fun U : E ↦ lExp S T x U tau) z).map_add V W
      map_smul' := by
        intro c V
        exact (mfderiv 𝓘(ℝ, E) I
          (fun U : E ↦ lExp S T x U tau) z).map_smul c V }
  have hinj : Function.Injective L := by
    intro V W hVW
    exact lExpDeriv_inj (I := I) S T x Z tau hdom hnconj hVW
  have hLI : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) ↦
        lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau) := by
    change LinearIndependent ℝ (L ∘ (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E))
    exact (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).linearIndependent.map' L
      (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [lExpGram] using
    lGram_det_pos (I := I) S T (fun q ↦ lExp S T x Z q)
      (fun i q ↦ lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) q)
      tau hLI

theorem lExpDensity_pos_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    0 < lExpDensity S T x Z tau := by
  exact Real.sqrt_pos.mpr
    (lExpGram_det_pos_of_nonconj S T x Z tau hdom hnconj)

theorem lExpJac_pos_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    0 < lExpJacobian S T x Z tau := by
  exact div_pos
    (lExpDensity_pos_of_nonconj S T x Z tau hdom hnconj)
    (lSourceDensity_pos S T x)

theorem lExpDensity_hasDeriv_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    HasDerivAt (lExpDensity S T x Z)
      ((1 / 2) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) *
        lExpDensity S T x Z tau) tau := by
  have htau : 0 < tau :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).1
  have ht : T - tau ∈ D.regular := by
    have hclock := lExpPosDom_regularity S T x Z hdom
      (show Real.sqrt tau ∈ Icc (0 : ℝ) (Real.sqrt tau) from
        ⟨Real.sqrt_nonneg tau, le_rfl⟩)
    simpa only [Real.sq_sqrt htau.le] using hclock
  let gamma : ℝ → M := fun q ↦ lExp S T x Z q
  let Y : Fin (Module.finrank ℝ E) →
      ∀ q, TangentSpace I (gamma q) :=
    fun i q ↦ lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) q
  let z : E := Z
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun r : ℝ ↦ (z, r)) tau :=
    (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma tau := by
    have hExp :=
      (lExp_smoothOn S hS T x).contMDiffAt
        ((lExpPosDom_open S hS T x).mem_nhds hdom)
    have hcomp := hExp.comp tau hpair
    exact hcomp.mdifferentiableAt (by simp)
  have hJac (i : Fin (Module.finrank ℝ E)) :
      HasLJacobiAt S T gamma (Y i) tau := by
    simpa only [gamma, Y, lExpField] using
      hasLJacobiAt_lExp S hS T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau hdom
  have hY : ∀ i, DifferentiableAt ℝ
      (chartRepAt (I := I) gamma (Y i) tau) tau :=
    fun i ↦ (hJac i).2.1
  have hpos : 0 < (lGram S T gamma Y tau).det := by
    simpa only [lExpGram, gamma, Y] using
      lExpGram_det_pos_of_nonconj S T x Z tau hdom hnconj
  have hout :=
    lJacobianDen_hasDeriv S hS T gamma Y tau ht hgamma hY hpos
  exact hout

theorem lExpJac_hasDeriv_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    HasDerivAt (lExpJacobian S T x Z)
      ((1 / 2) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) *
        lExpJacobian S T x Z tau) tau := by
  have hout :=
    (lExpDensity_hasDeriv_of_nonconj
      S hS T x Z tau hdom hnconj).div_const (lSourceDensity S T x)
  change HasDerivAt (fun r ↦ lExpDensity S T x Z r / lSourceDensity S T x) _ tau
  apply hout.congr_deriv
  exact mul_div_assoc _ _ _

theorem lExpDensity_log_hasDeriv_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    HasDerivAt (fun q ↦ Real.log (lExpDensity S T x Z q))
      ((1 / 2) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau)) tau := by
  have hpos :=
    lExpDensity_pos_of_nonconj S T x Z tau hdom hnconj
  have hout :=
    (lExpDensity_hasDeriv_of_nonconj
      S hS T x Z tau hdom hnconj).log hpos.ne'
  simpa only [mul_div_assoc, div_self hpos.ne', mul_one] using hout

theorem lExpJac_log_hasDeriv_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    HasDerivAt (fun q ↦ Real.log (lExpJacobian S T x Z q))
      ((1 / 2) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau)) tau := by
  have hpos :=
    lExpJac_pos_of_nonconj S T x Z tau hdom hnconj
  have hout :=
    (lExpJac_hasDeriv_of_nonconj
      S hS T x Z tau hdom hnconj).log hpos.ne'
  simpa only [mul_div_assoc, div_self hpos.ne', mul_one] using hout

theorem lExpJac_log_deriv_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    deriv (fun q ↦ Real.log (lExpJacobian S T x Z q)) tau =
      (1 / 2) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) :=
  (lExpJac_log_hasDeriv_of_nonconj S hS T x Z tau hdom hnconj).deriv

end DifferentialGeometry.PDE.RicciFlow
