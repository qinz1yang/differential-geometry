import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockInterface
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.CurvatureBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MEvolution

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff Matrix BigOperators

private theorem normalizedWedge_fin_two :
    normalizedWedge
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 2 => Real) 0)
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 2 => Real) 1)
        ![![1, 0], ![0, 1]] = (1 / 2 : Real) := by
  rw [normalizedWedge_apply]
  change (1 / 2 : Real) * (1 * 1 - 0 * 0) = 1 / 2
  ring

private theorem normalizedWedge_fin_three :
    normalizedWedge
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 3 => Real) 0)
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 3 => Real) 2)
        ![![1, 0, 0], ![0, 0, 1]] = (1 / 2 : Real) := by
  rw [normalizedWedge_apply]
  change (1 / 2 : Real) * (1 * 1 - 0 * 0) = 1 / 2
  ring

private def rankOneGramY (_ : Fin 1) (a b : Fin 2) : Real :=
  ![![0, 1], ![-1, 0]] a b

private def rankOneGramX (_ : Fin 1) (a : Fin 2) : Real :=
  ![2, 3] a

private def rankOneGramU (a b : Fin 2) : Real :=
  ![![0, 1], ![-1, 0]] a b

private def rankOneGramW (a : Fin 2) : Real :=
  ![5, 7] a

private theorem rank_one_gram_regression :
    hamiltonGramQuadratic rankOneGramY rankOneGramX
        rankOneGramU rankOneGramW = 1089 ∧
      hamiltonGramReaction rankOneGramY rankOneGramX
        rankOneGramU rankOneGramW = 0 ∧
      hamiltonReactionPolynomial
        (hamiltonGramK rankOneGramY)
        (hamiltonGramP rankOneGramY rankOneGramX)
        (hamiltonGramM rankOneGramX)
        rankOneGramU rankOneGramW = 0 := by
  norm_num [hamiltonGramQuadratic, hamiltonGramLinearTerm,
    hamiltonGramReaction, hamiltonReactionPolynomial, hamiltonGramK,
    hamiltonGramP, hamiltonGramM, rankOneGramY, rankOneGramX,
    rankOneGramU, rankOneGramW, Fin.sum_univ_two]

private def rankDeficientGramY (r a b : Fin 2) : Real :=
  ![![![0, 1], ![-1, 0]], ![![0, 2], ![-2, 0]]] r a b

private def rankDeficientGramX (r a : Fin 2) : Real :=
  ![![1, 0], ![0, 1]] r a

private def rankDeficientGramU (a b : Fin 2) : Real :=
  ![![0, 1], ![-1, 0]] a b

private def rankDeficientGramW (a : Fin 2) : Real :=
  ![3, 5] a

private theorem rank_deficient_gram_regression :
    hamiltonGramQuadratic rankDeficientGramY rankDeficientGramX
        rankDeficientGramU rankDeficientGramW = 106 ∧
      hamiltonGramReaction rankDeficientGramY rankDeficientGramX
        rankDeficientGramU rankDeficientGramW = 338 ∧
      hamiltonReactionPolynomial
        (hamiltonGramK rankDeficientGramY)
        (hamiltonGramP rankDeficientGramY rankDeficientGramX)
        (hamiltonGramM rankDeficientGramX)
        rankDeficientGramU rankDeficientGramW = 338 := by
  norm_num [hamiltonGramQuadratic, hamiltonGramLinearTerm,
    hamiltonGramReaction, hamiltonReactionPolynomial, hamiltonGramK,
    hamiltonGramP, hamiltonGramM, rankDeficientGramY, rankDeficientGramX,
    rankDeficientGramU, rankDeficientGramW, Fin.sum_univ_two]

private def kronecker {n : Nat} (a b : Fin n) : Real :=
  if a = b then 1 else 0

private def roundTwoCurvature (k : Real) (a b c d : Fin 2) : Real :=
  k * (kronecker a d * kronecker b c - kronecker a c * kronecker b d)

private def roundTwoRicci (k : Real) (a b : Fin 2) : Real :=
  k * kronecker a b

private def cylinderProjection (a b : Fin 3) : Real :=
  if a = b ∧ a.val < 2 then 1 else 0

private def cylinderCurvature (k : Real) (a b c d : Fin 3) : Real :=
  k * (cylinderProjection a d * cylinderProjection b c -
    cylinderProjection a c * cylinderProjection b d)

private def cylinderRicci (k : Real) (a b : Fin 3) : Real :=
  k * cylinderProjection a b

private theorem flat_hamilton_evolution_regression
    (clock : HarnackClock) (a b c : Fin 2) :
    hamiltonPEvolutionReactionComponent
        (fun _ _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ _ _ => 0)
        (fun _ _ _ => 0) a b c = 0 ∧
      hamiltonMComponent clock (fun _ _ _ _ => 0) (fun _ _ => 0)
        (fun _ _ => 0) a b = 0 ∧
      hamiltonMEvolutionReactionComponent clock
        (fun _ _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ _ _ => 0) (fun _ _ => 0) a b = 0 := by
  simp [hamiltonPEvolutionReactionComponent, hamiltonPComponent,
    hamiltonMComponent, hamiltonCurvatureRicciComponent,
    hamiltonMEvolutionReactionComponent]

private theorem roundTwo_hamiltonP_evolution_regression
    (k : Real) (a b c : Fin 2) :
    hamiltonPEvolutionReactionComponent
      (roundTwoCurvature k) (roundTwoRicci k) (fun _ _ _ _ _ => 0)
      (fun _ _ _ => 0) a b c = 0 := by
  simp [hamiltonPEvolutionReactionComponent, hamiltonPComponent]

private theorem roundTwo_hamiltonM_component_regression
    (clock : HarnackClock) (k : Real) (a b : Fin 2) :
    hamiltonMComponent clock (roundTwoCurvature k) (roundTwoRicci k)
        (fun _ _ => 0) a b =
      (k ^ 2 + k / (2 * clock.elapsed)) * kronecker a b := by
  fin_cases a <;> fin_cases b <;>
    simp [hamiltonMComponent, hamiltonCurvatureRicciComponent,
      roundTwoCurvature, roundTwoRicci, kronecker, Fin.sum_univ_two] <;>
    ring

private theorem roundTwo_hamiltonM_evolution_regression
    (clock : HarnackClock) (k : Real) (a b : Fin 2) :
    hamiltonMEvolutionReactionComponent clock
        (roundTwoCurvature k) (roundTwoRicci k) (fun _ _ _ => 0)
        (fun _ _ _ _ => 0) (fun _ _ => 0) a b =
      (4 * k ^ 3 + k ^ 2 / clock.elapsed -
        k / (2 * clock.elapsed ^ 2)) * kronecker a b := by
  fin_cases a <;> fin_cases b <;>
    simp [hamiltonMEvolutionReactionComponent, hamiltonMComponent,
      hamiltonCurvatureRicciComponent, hamiltonPComponent,
      roundTwoCurvature, roundTwoRicci, kronecker, Fin.sum_univ_two] <;>
    ring

private theorem cylinder_hamiltonP_evolution_regression
    (k : Real) (a b c : Fin 3) :
    hamiltonPEvolutionReactionComponent
      (cylinderCurvature k) (cylinderRicci k) (fun _ _ _ _ _ => 0)
      (fun _ _ _ => 0) a b c = 0 := by
  simp [hamiltonPEvolutionReactionComponent, hamiltonPComponent]

private theorem cylinder_hamiltonM_component_regression
    (clock : HarnackClock) (k : Real) (a b : Fin 3) :
    hamiltonMComponent clock (cylinderCurvature k) (cylinderRicci k)
        (fun _ _ => 0) a b =
      (k ^ 2 + k / (2 * clock.elapsed)) * cylinderProjection a b := by
  fin_cases a <;> fin_cases b <;>
    simp [hamiltonMComponent, hamiltonCurvatureRicciComponent,
      cylinderCurvature, cylinderRicci, cylinderProjection,
      Fin.sum_univ_three] <;>
    ring

private theorem cylinder_hamiltonM_evolution_regression
    (clock : HarnackClock) (k : Real) (a b : Fin 3) :
    hamiltonMEvolutionReactionComponent clock
        (cylinderCurvature k) (cylinderRicci k) (fun _ _ _ => 0)
        (fun _ _ _ _ => 0) (fun _ _ => 0) a b =
      (4 * k ^ 3 + k ^ 2 / clock.elapsed -
        k / (2 * clock.elapsed ^ 2)) * cylinderProjection a b := by
  fin_cases a <;> fin_cases b <;>
    simp [hamiltonMEvolutionReactionComponent, hamiltonMComponent,
      hamiltonCurvatureRicciComponent, hamiltonPComponent,
      cylinderCurvature, cylinderRicci, cylinderProjection,
      Fin.sum_univ_three] <;>
    ring

private def formalExpanderP
    (R : Fin 2 -> Fin 2 -> Fin 2 -> Fin 2 -> Real)
    (F : Fin 2 -> Real) (a b c : Fin 2) : Real :=
  ∑ d, R a b c d * F d

private def formalExpanderM
    (R : Fin 2 -> Fin 2 -> Fin 2 -> Fin 2 -> Real)
    (F : Fin 2 -> Real) (a c : Fin 2) : Real :=
  -(∑ b, ∑ d, R a b c d * F b * F d)

private def formalExpanderU
    (F W : Fin 2 -> Real) (a b : Fin 2) : Real :=
  (1 / 2 : Real) * (W a * F b - W b * F a)

private theorem roundTwo_formalExpander_regression
    (k : Real) (F W : Fin 2 -> Real) :
    hamiltonQuadraticForm
        (fun a b c d => roundTwoCurvature k a b d c)
        (formalExpanderP (roundTwoCurvature k) F)
        (formalExpanderM (roundTwoCurvature k) F)
        (formalExpanderU F W) W = 0 ∧
      forall a b,
        hamiltonBlockSigma
          (fun i j l m => roundTwoCurvature k i j m l)
          (formalExpanderP (roundTwoCurvature k) F)
          (formalExpanderU F W) W a b = 0 := by
  constructor
  · simp [hamiltonQuadraticForm, roundTwoCurvature, kronecker,
      formalExpanderP, formalExpanderM, formalExpanderU, Fin.sum_univ_two]
    ring
  · intro a b
    fin_cases a <;> fin_cases b <;>
      simp [hamiltonBlockSigma, roundTwoCurvature, kronecker,
        formalExpanderP, formalExpanderU, Fin.sum_univ_two] <;>
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

omit [FiniteDimensional Real E] in
private theorem roundMetric_curvature_pos_of_orthonormal
    (x : Metric.sphere (0 : E) 1)
    (X Y : TangentSpace (𝓡 n) x)
    (hXX : (roundMetric (E := E) (n := n)).inner x X X = 1)
    (hYY : (roundMetric (E := E) (n := n)).inner x Y Y = 1)
    (hXY : (roundMetric (E := E) (n := n)).inner x X Y = 0) :
    0 < Geometry.Curvature.metricRm04StandardAt
      (roundMetric (E := E) (n := n)) x X Y Y X := by
  rw [roundMetric_sec_value, hXX, hYY, hXY]
  norm_num

end DifferentialGeometry.PDE.RicciFlow
