import DifferentialGeometry.Geometry.Surface.TensorTraceFree
import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Hodge.OneFormHarmonic
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization
import DifferentialGeometry.Geometry.Hodge.Codifferential
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HeatProbeEnergy
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OneFormRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.NormSqPositivity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open MeasureTheory
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Forms
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open Tensor0SNabla
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


private theorem inner0S_symm'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A := by
  unfold inner0S MetricFiberData.inner
  exact (tensor0SMetricData (I := I) g x s).symm A B

private theorem inner0S_add_left'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A + B) C =
      inner0S (I := I) g x s A C + inner0S (I := I) g x s B C := by
  let D := tensor0SMetricData (I := I) g x s
  change D.flat (A + B) C = D.flat A C + D.flat B C
  rw [D.flat.map_add]
  rfl

private theorem inner0S_add_right'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A (B + C) =
      inner0S (I := I) g x s A B + inner0S (I := I) g x s A C := by
  let D := tensor0SMetricData (I := I) g x s
  change D.flat A (B + C) = D.flat A B + D.flat A C
  exact map_add (D.flat A) B C

private theorem inner0S_sub_right'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A (B - C) =
      inner0S (I := I) g x s A B - inner0S (I := I) g x s A C := by
  let D := tensor0SMetricData (I := I) g x s
  change D.flat A (B - C) = D.flat A B - D.flat A C
  exact map_sub (D.flat A) B C

private theorem inner0S_neg_right'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A (-B) = - inner0S (I := I) g x s A B := by
  let D := tensor0SMetricData (I := I) g x s
  change D.flat A (-B) = - D.flat A B
  exact map_neg (D.flat A) B

private theorem swapSlots0S_apply {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : Fin 2 → TangentSpace I x) :
    swapSlots0S (I := I) A v = A (fun i => v (Equiv.swap (0 : Fin 2) 1 i)) := by
  change A (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i)) = A (fun i => v (Equiv.swap (0 : Fin 2) 1 i))
  rw [Equiv.symm_swap]

private theorem swapSlots0S_apply_basis {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (p q : TangentSpace I x) :
    swapSlots0S (I := I) A (fun a : Fin 2 => if a = 0 then p else q) =
      A (fun a : Fin 2 => if a = 0 then q else p) := by
  rw [swapSlots0S_apply]
  congr 1
  funext a
  fin_cases a <;> simp

private theorem inner0S_swapSlots_left {x : M}
    (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    inner0S (I := I) g x 2 (swapSlots0S (I := I) A) B =
      inner0S (I := I) g x 2 A (swapSlots0S (I := I) B) := by
  classical
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x with hb
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x k l (extChartAt I x x) with hgInv
  have hinv := DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  rw [inner0S_two_eq_coord (I := I) g x basis gInv hinv,
      inner0S_two_eq_coord (I := I) g x basis gInv hinv]
  simp only [swapSlots0S_apply_basis]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

private theorem inner0S_sub_left'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B C : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (A - B) C =
      inner0S (I := I) g x s A C - inner0S (I := I) g x s B C := by
  let D := tensor0SMetricData (I := I) g x s
  change D.flat (A - B) C = D.flat A C - D.flat B C
  rw [map_sub]
  rfl

private theorem swapSlots0S_swapSlots {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    swapSlots0S (I := I) (swapSlots0S (I := I) T) = T := by
  ext v
  rw [swapSlots0S_apply, swapSlots0S_apply]
  congr 1
  funext i
  rw [Equiv.swap_apply_self]

private theorem swapSlots0S_metricTensor0S {x : M} (g : SmoothRiemannianMetric I M) :
    swapSlots0S (I := I) (metricTensor0S (I := I) g x) = metricTensor0S (I := I) g x := by
  ext v
  rw [swapSlots0S_apply, metricTensor0S_apply, metricTensor0S_apply]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact g.symm x (v 1) (v 0)

private theorem inner0S_add_smul_self
    (g : SmoothRiemannianMetric I M) (x : M)
    (D W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (a : Real) :
    inner0S (I := I) g x 2 (D + a • W) (D + a • W) =
      inner0S (I := I) g x 2 D D + 2 * a * inner0S (I := I) g x 2 D W
        + a ^ 2 * inner0S (I := I) g x 2 W W := by
  rw [inner0S_add_left', inner0S_add_right', inner0S_add_right']
  simp only [inner0S_smul_left, inner0S_smul_right]
  rw [show inner0S (I := I) g x 2 W D = inner0S (I := I) g x 2 D W from inner0S_symm' (I := I) g x 2 W D]
  ring


def oneFormReaction2D (g : SmoothRiemannianMetric I M) {x : M}
    (hx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  let gradK : TangentSpace I x := gradFun (I := I) g (gaussCurvature (I := I) g) x
  let dKcov : TangentSpace I x →L[Real] Real := g.inner x gradK
  let hcov : TangentSpace I x →L[Real] Real := g.inner x (cotangentSharp (I := I) g x hx)
  covectorTensorProd0S (I := I) dKcov hcov
    + covectorTensorProd0S (I := I) hcov dKcov
    - (hcov gradK) • metricTensor0S (I := I) g x


private theorem covectorTensorProd0S_apply {x : M}
    (a b : TangentSpace I x →L[Real] Real)
    (v : Fin 2 → TangentSpace I x) :
    covectorTensorProd0S (I := I) a b v = a (v 0) * b (v 1) := by
  unfold covectorTensorProd0S
  change ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      ((a.smulRight b) (v 0))) (fun i : Fin 1 => v i.succ) = a (v 0) * b (v 1)
  have htail : (fun i : Fin 1 => v i.succ) = fun _ : Fin 1 => v 1 := by
    funext i; fin_cases i; rfl
  rw [htail]
  change (a.smulRight b) (v 0) (v 1) = a (v 0) * b (v 1)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem oneFormReaction2D_apply (g : SmoothRiemannianMetric I M) {x : M}
    (hx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    oneFormReaction2D (I := I) g hx (vec2 (I := I) X Y) =
      g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x) X
          * g.inner x (cotangentSharp (I := I) g x hx) Y
        + g.inner x (cotangentSharp (I := I) g x hx) X
          * g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x) Y
        - g.inner x (cotangentSharp (I := I) g x hx)
            (gradFun (I := I) g (gaussCurvature (I := I) g) x)
          * g.inner x X Y := by
  have hpush : oneFormReaction2D (I := I) g hx (vec2 (I := I) X Y) =
      covectorTensorProd0S (I := I) (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
          (g.inner x (cotangentSharp (I := I) g x hx)) (vec2 (I := I) X Y)
        + covectorTensorProd0S (I := I) (g.inner x (cotangentSharp (I := I) g x hx))
          (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x)) (vec2 (I := I) X Y)
        - (g.inner x (cotangentSharp (I := I) g x hx)
            (gradFun (I := I) g (gaussCurvature (I := I) g) x))
          • (metricTensor0S (I := I) g x (vec2 (I := I) X Y)) := rfl
  rw [hpush, covectorTensorProd0S_apply, covectorTensorProd0S_apply, metricTensor0S_apply,
    show vec2 (I := I) X Y 0 = X from rfl, show vec2 (I := I) X Y 1 = Y from rfl, smul_eq_mul]

private theorem curry_eval' {n : ℕ} {z : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n + 1) z)
    (v0 : TangentSpace I z) (vs : Fin n → TangentSpace I z) :
    (tensor0S_curry (𝕜 := Real) (I := I) n z T v0) vs = T (Fin.cons v0 vs) :=
  TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) T v0 vs

private theorem ricReact_eval' (g : SmoothRiemannianMetric I M) (x : M)
    (nR : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    DifferentialGeometry.PDE.RicciFlow.Evolution.HeatProbeEnergy.ricciVariationOneFormReaction
        (I := I) g x nR α (vec2 (I := I) X Y) =
      nR (vec3 (I := I) X Y (cotangentSharp (I := I) g x α)) +
        nR (vec3 (I := I) Y X (cotangentSharp (I := I) g x α)) -
        nR (vec3 (I := I) (cotangentSharp (I := I) g x α) X Y) := by
  classical
  set Hs : TangentSpace I x := cotangentSharp (I := I) g x α with hHs
  have hswap : (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) = vec2 (I := I) Y X := by
    funext i
    fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hexpand :
      DifferentialGeometry.PDE.RicciFlow.Evolution.HeatProbeEnergy.ricciVariationOneFormReaction
          (I := I) g x nR α (vec2 (I := I) X Y) =
        (tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs
            (vec2 (I := I) X Y) +
          ((tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs).domDomCongr
              (Equiv.swap (0 : Fin 2) 1) (vec2 (I := I) X Y) -
          (tensor0S_curry (𝕜 := Real) (I := I) 2 x nR) Hs (vec2 (I := I) X Y) := rfl
  have hterm1 : (tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs
      (vec2 (I := I) X Y) = nR (vec3 (I := I) X Y Hs) := by
    rw [curry_eval' (nR.domDomCongr (finRotate 3)) Hs (vec2 (I := I) X Y)]
    show nR (fun i => (Fin.cons Hs (vec2 (I := I) X Y) : Fin 3 → TangentSpace I x) (finRotate 3 i))
      = nR (vec3 (I := I) X Y Hs)
    congr 1
    funext i
    fin_cases i <;> rfl
  have hterm2 : ((tensor0S_curry (𝕜 := Real) (I := I) 2 x
        (nR.domDomCongr (finRotate 3))) Hs).domDomCongr
      (Equiv.swap (0 : Fin 2) 1) (vec2 (I := I) X Y) = nR (vec3 (I := I) Y X Hs) := by
    show (tensor0S_curry (𝕜 := Real) (I := I) 2 x (nR.domDomCongr (finRotate 3))) Hs
        (fun i => (vec2 (I := I) X Y) (Equiv.swap (0 : Fin 2) 1 i)) = nR (vec3 (I := I) Y X Hs)
    rw [hswap, curry_eval' (nR.domDomCongr (finRotate 3)) Hs (vec2 (I := I) Y X)]
    show nR (fun i => (Fin.cons Hs (vec2 (I := I) Y X) : Fin 3 → TangentSpace I x) (finRotate 3 i))
      = nR (vec3 (I := I) Y X Hs)
    congr 1
    funext i
    fin_cases i <;> rfl
  have hterm3 : (tensor0S_curry (𝕜 := Real) (I := I) 2 x nR) Hs (vec2 (I := I) X Y) =
      nR (vec3 (I := I) Hs X Y) := by
    rw [curry_eval' nR Hs (vec2 (I := I) X Y)]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hexpand, hterm1, hterm2, hterm3]


set_option linter.unusedVariables false in
theorem oneFormReaction2D_eq_ricciVariation
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (hx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaRic : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRic : ∀ Y V W : TangentSpace I x,
      nablaRic (vec3 (I := I) Y V W) =
        extDerivFun (I := I) (gaussCurvature (I := I) g) x Y * g.inner x V W) :
    oneFormReaction2D (I := I) g hx =
      DifferentialGeometry.PDE.RicciFlow.Evolution.HeatProbeEnergy.ricciVariationOneFormReaction
        (I := I) g x nablaRic hx := by
  have hdK : ∀ w : TangentSpace I x,
      extDerivFun (I := I) (gaussCurvature (I := I) g) x w
        = g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x) w := by
    intro w
    rw [show extDerivFun (I := I) (gaussCurvature (I := I) g) x w
          = mfderiv I 𝓘(Real, Real) (gaussCurvature (I := I) g) x w from rfl,
      inner_gradFun]
  ext v
  rw [show v = vec2 (I := I) (v 0) (v 1) from by funext i; fin_cases i <;> rfl]
  rw [ricReact_eval' (I := I) g x nablaRic hx (v 0) (v 1), oneFormReaction2D_apply]
  simp only [hRic, hdK]
  rw [g.symm x (v 1) (cotangentSharp (I := I) g x hx),
      g.symm x (v 0) (cotangentSharp (I := I) g x hx),
      g.symm x (gradFun (I := I) g (gaussCurvature (I := I) g) x)
        (cotangentSharp (I := I) g x hx)]
  ring


theorem gradNormSq_decomposition_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    normSq0S (I := I) g x 2 T =
      normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g T)
        + normSq0S (I := I) g x 2 (antisymmetricPart0S (I := I) T)
        + (2 : Real)⁻¹ * metricTracePair0SAt (I := I) g T ^ 2 := by
  classical
  have hA : normSq0S (I := I) g x 2 T
      = normSq0S (I := I) g x 2 (symmetricPart0S (I := I) T)
        + normSq0S (I := I) g x 2 (antisymmetricPart0S (I := I) T) := by
    set p := symmetricPart0S (I := I) T with hp
    set q := antisymmetricPart0S (I := I) T with hq
    have hTSA : T = p + q := by
      rw [hp, hq]; unfold symmetricPart0S antisymmetricPart0S; module
    have hpq : inner0S (I := I) g x 2 p q = 0 := by
      rw [hp, hq]
      unfold symmetricPart0S antisymmetricPart0S
      rw [inner0S_smul_left, inner0S_smul_right]
      have h0 : inner0S (I := I) g x 2 (T + swapSlots0S (I := I) T)
          (T - swapSlots0S (I := I) T) = 0 := by
        rw [inner0S_add_left', inner0S_sub_right', inner0S_sub_right']
        have e1 : inner0S (I := I) g x 2 (swapSlots0S (I := I) T) T
            = inner0S (I := I) g x 2 T (swapSlots0S (I := I) T) := by
          rw [inner0S_swapSlots_left]
        have e2 : inner0S (I := I) g x 2 (swapSlots0S (I := I) T) (swapSlots0S (I := I) T)
            = inner0S (I := I) g x 2 T T := by
          rw [inner0S_swapSlots_left, swapSlots0S_swapSlots]
        rw [e1, e2]; ring
      rw [h0]; ring
    have hqp : inner0S (I := I) g x 2 q p = 0 := by rw [inner0S_symm' (I := I) g x 2]; exact hpq
    rw [normSq0S_eq_inner, normSq0S_eq_inner, normSq0S_eq_inner, hTSA,
        inner0S_add_left', inner0S_add_right', inner0S_add_right', hpq, hqp]
    ring
  have hF6 : metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T)
      = metricTracePair0SAt (I := I) g T := by
    unfold symmetricPart0S metricTracePair0SAt
    rw [inner0S_smul_right, inner0S_add_right']
    have hsw : inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) (swapSlots0S (I := I) T)
        = inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) T := by
      rw [← inner0S_swapSlots_left, swapSlots0S_metricTensor0S]
    rw [hsw]; ring
  have hcard : normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) = 2 := by
    rw [normSq0S_metricTensor0S_eq_card (I := I) g
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
      (fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x))
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)]
    have hc2 : Fintype.card (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) = 2 := by
      rw [← Module.finrank_eq_card_basis
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)]
      exact hdim
    rw [hc2]; norm_num
  have hB : normSq0S (I := I) g x 2 (symmetricPart0S (I := I) T)
      = normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g T)
        + (2 : Real)⁻¹ * metricTracePair0SAt (I := I) g T ^ 2 := by
    set p := symmetricPart0S (I := I) T with hp
    set gm := metricTensor0S (I := I) g x with hgm
    set tp := metricTracePair0SAt (I := I) g T with htp
    have hc : (Module.finrank Real E : Real)⁻¹ * metricTracePair0SAt (I := I) g p
        = (2 : Real)⁻¹ * tp := by
      rw [hF6, hdim]; norm_num
    have hDeq : ahlforsOperator (I := I) g T = p - ((2 : Real)⁻¹ * tp) • gm := by
      have hun : ahlforsOperator (I := I) g T
          = symmetricPart0S (I := I) T
            - ((Module.finrank Real E : Real)⁻¹
                * metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T))
              • metricTensor0S (I := I) g x := rfl
      rw [hun, ← hp, ← hgm, hc]
    have hSD : p = ahlforsOperator (I := I) g T + ((2 : Real)⁻¹ * tp) • gm := by
      rw [hDeq]; abel
    have hF4 : inner0S (I := I) g x 2 (ahlforsOperator (I := I) g T) gm = 0 := by
      rw [hDeq, inner0S_sub_left', inner0S_smul_left]
      have hpg : inner0S (I := I) g x 2 p gm = tp := by
        rw [inner0S_symm' (I := I) g x 2]
        show metricTracePair0SAt (I := I) g p = tp
        exact hF6
      rw [hpg, show inner0S (I := I) g x 2 gm gm = 2 from by
        rw [← normSq0S_eq_inner]; exact hcard]
      ring
    rw [normSq0S_eq_inner, hSD, inner0S_add_smul_self, hF4,
        show inner0S (I := I) g x 2 gm gm = 2 from by
          rw [← normSq0S_eq_inner]; exact hcard,
        ← normSq0S_eq_inner]
    ring
  rw [hA, hB]; ring


private theorem trace_symmetricPart0S
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T)
      = metricTracePair0SAt (I := I) g T := by
  unfold symmetricPart0S metricTracePair0SAt
  rw [inner0S_smul_right, inner0S_add_right']
  have hsw : inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) (swapSlots0S (I := I) T)
      = inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) T := by
    rw [← inner0S_swapSlots_left, swapSlots0S_metricTensor0S]
  rw [hsw]; ring

private theorem metricTensorField_eq_metricTensor0S
    (g : SmoothRiemannianMetric I M) (y : M) :
    metricTensorField (I := I) g y = metricTensor0S (I := I) g y := by
  ext v
  rw [metricTensorField_apply, metricTensor0S_apply]

private noncomputable def ahlforsTraceFun
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) : M → Real :=
  fun y => metricTracePair0SAt (I := I) g (nablaH y)

private theorem ahlforsTraceFun_smooth
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (ahlforsTraceFun (I := I) g nablaH) :=
  trace02_smooth (I := I) (M := M) g nablaH

private noncomputable def ahlforsHalfTraceFun
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) : M → Real :=
  fun y => (2 : Real)⁻¹ * ahlforsTraceFun (I := I) g nablaH y

private theorem ahlforsHalfTraceFun_smooth
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (ahlforsHalfTraceFun (I := I) g nablaH) :=
  contMDiff_const.mul (ahlforsTraceFun_smooth (I := I) g nablaH)

private noncomputable def ahlforsSwapSection
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    TwoTensorSection (I := I) (M := M) :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
    (∞ : WithTop ℕ∞) (Equiv.swap (0 : Fin 2) 1) nablaH

private theorem ahlforsSwapSection_apply
    (nablaH : TwoTensorSection (I := I) (M := M)) (y : M) :
    ahlforsSwapSection (I := I) nablaH y = swapSlots0S (I := I) (nablaH y) := by
  have h1 : ahlforsSwapSection (I := I) nablaH y
      = ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) (nablaH y) := rfl
  rw [h1]
  ext v
  rw [swapSlots0S_apply]
  rfl

private noncomputable def ahlforsMetricPart
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    TwoTensorSection (I := I) (M := M) :=
  tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s := 2)
    (ahlforsHalfTraceFun (I := I) g nablaH) (ahlforsHalfTraceFun_smooth (I := I) g nablaH)
    (metricTensorField (I := I) g)

private noncomputable def ahlforsSection
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    TwoTensorSection (I := I) (M := M) :=
  (2 : Real)⁻¹ • (nablaH + ahlforsSwapSection (I := I) nablaH)
    - ahlforsMetricPart (I := I) g nablaH

private theorem ahlforsSection_add_metricPart
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) :
    ahlforsSection (I := I) g nablaH + ahlforsMetricPart (I := I) g nablaH
      = (2 : Real)⁻¹ • (nablaH + ahlforsSwapSection (I := I) nablaH) := by
  rw [ahlforsSection]
  exact sub_add_cancel _ _

private theorem ahlforsSection_apply
    [T2Space M] [SigmaCompactSpace M]
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) (y : M) :
    ahlforsSection (I := I) g nablaH y = ahlforsOperator (I := I) g (nablaH y) := by
  have hLHS : ahlforsSection (I := I) g nablaH y
      = (2 : Real)⁻¹ • (nablaH y + swapSlots0S (I := I) (nablaH y))
        - ahlforsHalfTraceFun (I := I) g nablaH y • metricTensor0S (I := I) g y := by
    rw [ahlforsSection]
    rw [show ((2 : Real)⁻¹ • (nablaH + ahlforsSwapSection (I := I) nablaH)
          - ahlforsMetricPart (I := I) g nablaH) y
        = (2 : Real)⁻¹ • ((nablaH + ahlforsSwapSection (I := I) nablaH) y)
          - ahlforsMetricPart (I := I) g nablaH y from rfl]
    rw [show (nablaH + ahlforsSwapSection (I := I) nablaH) y
        = nablaH y + ahlforsSwapSection (I := I) nablaH y from rfl]
    rw [ahlforsSwapSection_apply]
    rw [show ahlforsMetricPart (I := I) g nablaH y
        = ahlforsHalfTraceFun (I := I) g nablaH y • metricTensorField (I := I) g y from rfl]
    rw [metricTensorField_eq_metricTensor0S]
  rw [hLHS]
  have hRHS : ahlforsOperator (I := I) g (nablaH y)
      = symmetricPart0S (I := I) (nablaH y)
        - ((Module.finrank Real E : Real)⁻¹
            * metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) (nablaH y)))
          • metricTensor0S (I := I) g y := rfl
  rw [hRHS, trace_symmetricPart0S, hdim]
  rw [show symmetricPart0S (I := I) (nablaH y)
      = (2 : Real)⁻¹ • (nablaH y + swapSlots0S (I := I) (nablaH y)) from rfl]
  rw [show ahlforsHalfTraceFun (I := I) g nablaH y
      = (2 : Real)⁻¹ * metricTracePair0SAt (I := I) g (nablaH y) from rfl]
  norm_num

private theorem invMetric_contract_oneform
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (omg : TangentSpace I x →L[Real] Real) (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx, gInv i j * (omg (basis i) * g.inner x (basis j) X)) = omg X := by
  classical
  have hXrepr : X = ∑ k : Idx, basis.repr X k • basis k := (basis.sum_repr X).symm
  have hinner : ∀ j : Idx, g.inner x (basis j) X
      = ∑ k : Idx, basis.repr X k * g.inner x (basis j) (basis k) := by
    intro j
    conv_lhs => rw [hXrepr]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
  calc
    (∑ i : Idx, ∑ j : Idx, gInv i j * (omg (basis i) * g.inner x (basis j) X))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
            gInv i j * (omg (basis i) * (basis.repr X k * g.inner x (basis j) (basis k))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hinner j, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
            gInv i j * (omg (basis i) * (basis.repr X k * g.inner x (basis j) (basis k))) := by
          rw [show (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
              gInv i j * (omg (basis i) * (basis.repr X k * g.inner x (basis j) (basis k))))
            = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx,
              gInv i j * (omg (basis i) * (basis.repr X k * g.inner x (basis j) (basis k)))
            from Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
          exact Finset.sum_comm
    _ = ∑ k : Idx, basis.repr X k *
            ∑ i : Idx, omg (basis i) * ∑ j : Idx, gInv i j * g.inner x (basis j) (basis k) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
    _ = ∑ k : Idx, basis.repr X k * omg (basis k) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          congr 1
          rw [Finset.sum_eq_single k]
          · rw [show (∑ j : Idx, gInv k j * g.inner x (basis j) (basis k)) = 1 from by
              rw [show (1 : Real) = if k = k then (1 : Real) else 0 from by simp]
              exact (hinv k k).1]
            ring
          · intro i _ hik
            rw [show (∑ j : Idx, gInv i j * g.inner x (basis j) (basis k))
                = if i = k then (1 : Real) else 0 from (hinv i k).1]
            simp [hik]
          · intro hk
            exact absurd (Finset.mem_univ k) hk
    _ = omg X := by
          conv_rhs => rw [hXrepr]
          rw [map_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul, smul_eq_mul]

private theorem roughLap_apply_eq_sum'
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X : TangentSpace I x) :
    roughLap0STensor (I := I) g (s := 1) T (fun _ : Fin 1 => X) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * T (vec3 (I := I) (basis i) (basis j) X) := by
  rw [roughLap0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv T (fun _ : Fin 1 => X)]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [metricTraceInput_one_eq_vec3]

set_option backward.isDefEq.respectTransparency false in
private theorem nabla0SFun_ahlfors_eval
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (Xf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (Y Z : TangentSpace I x) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
        (metricCov (I := I) (M := M) g) Xf (ahlforsSection (I := I) g nablaH) x
        (vec2 (I := I) Y Z)
      = (2 : Real)⁻¹ * (nabla2H x (vec3 (I := I) (Xf x) Y Z)
            + nabla2H x (vec3 (I := I) (Xf x) Z Y))
        - (2 : Real)⁻¹ * extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (Xf x)
          * g.inner x Y Z := by
  classical
  have hmc : IsMetricCompatible_gen (I := I) (metricCov (I := I) (M := M) g) g :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hsec := ahlforsSection_add_metricPart (I := I) g nablaH
  have hadd := congrArg
    (fun A : TwoTensorSection (I := I) (M := M) =>
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
        (metricCov (I := I) (M := M) g) Xf A x) hsec
  simp only at hadd
  rw [nabla0SFun_add (I := I) (metricCov (I := I) (M := M) g) Xf
      (ahlforsSection (I := I) g nablaH) (ahlforsMetricPart (I := I) g nablaH) x,
    nabla0SFun_smul (I := I) (metricCov (I := I) (M := M) g) Xf (2 : Real)⁻¹
      (nablaH + ahlforsSwapSection (I := I) nablaH) x,
    nabla0SFun_add (I := I) (metricCov (I := I) (M := M) g) Xf
      nablaH (ahlforsSwapSection (I := I) nablaH) x] at hadd
  have happ := congrArg
    (fun T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x =>
      T (vec2 (I := I) Y Z)) hadd
  simp only at happ
  have hexpand :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) Xf (ahlforsSection (I := I) g nablaH) x
          (vec2 (I := I) Y Z)
        + nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) Xf (ahlforsMetricPart (I := I) g nablaH) x
          (vec2 (I := I) Y Z)
      = (2 : Real)⁻¹ *
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (metricCov (I := I) (M := M) g) Xf nablaH x (vec2 (I := I) Y Z)
            + nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (metricCov (I := I) (M := M) g) Xf (ahlforsSwapSection (I := I) nablaH) x
              (vec2 (I := I) Y Z)) := happ
  have hP : nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (metricCov (I := I) (M := M) g) Xf nablaH x (vec2 (I := I) Y Z)
      = nabla2H x (vec3 (I := I) (Xf x) Y Z) := ((hRealizes2 x).2 Xf Y Z).symm
  have hswapcomp : (vec2 (I := I) Y Z) ∘ (Equiv.swap (0 : Fin 2) 1) = vec2 (I := I) Z Y := by
    funext k
    fin_cases k <;>
      simp [Function.comp, vec2, DifferentialGeometry.Integral.Connection.vec2,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hQ : nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (metricCov (I := I) (M := M) g) Xf (ahlforsSwapSection (I := I) nablaH) x
      (vec2 (I := I) Y Z)
      = nabla2H x (vec3 (I := I) (Xf x) Z Y) := by
    rw [ahlforsSwapSection,
      nabla0SFun_domDomCongr (I := I) (metricCov (I := I) (M := M) g) Xf
        (Equiv.swap (0 : Fin 2) 1) nablaH x (vec2 (I := I) Y Z),
      hswapcomp]
    exact ((hRealizes2 x).2 Xf Z Y).symm
  have hdu : ∀ (y : M) (v : TangentSpace I y),
      duSec (I := I) (ahlforsHalfTraceFun (I := I) g nablaH)
          (ahlforsHalfTraceFun_smooth (I := I) g nablaH) y (fun _ : Fin 1 => v)
        = extDerivFun (I := I) (ahlforsHalfTraceFun (I := I) g nablaH) y v := by
    intro y v
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_extDerivFun (I := I)
      (ahlforsHalfTraceFun (I := I) g nablaH) y v
  have hRreal := nabla_smul_metric (I := I) (M := M)
    (metricCov (I := I) (M := M) g) g hmc
    (ahlforsHalfTraceFun (I := I) g nablaH) (ahlforsHalfTraceFun_smooth (I := I) g nablaH)
    (duSec (I := I) (ahlforsHalfTraceFun (I := I) g nablaH)
      (ahlforsHalfTraceFun_smooth (I := I) g nablaH)) hdu
  have hR : nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (metricCov (I := I) (M := M) g) Xf (ahlforsMetricPart (I := I) g nablaH) x
      (vec2 (I := I) Y Z)
      = extDerivFun (I := I) (ahlforsHalfTraceFun (I := I) g nablaH) x (Xf x)
        * g.inner x Y Z := by
    have hreal_app := (hRreal Xf x (vec2 (I := I) Y Z)).symm
    rw [show ahlforsMetricPart (I := I) g nablaH
        = tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) (s := 2)
            (ahlforsHalfTraceFun (I := I) g nablaH)
            (ahlforsHalfTraceFun_smooth (I := I) g nablaH)
            (metricTensorField (I := I) g) from rfl,
      hreal_app]
    change (Bundle.continuousMultilinearMap.product_fun
        (duSec (I := I) (ahlforsHalfTraceFun (I := I) g nablaH)
          (ahlforsHalfTraceFun_smooth (I := I) g nablaH) x)
        (metricTensorField (I := I) g x)) (Fin.cons (Xf x) (vec2 (I := I) Y Z)) = _
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    have hleft : Fin.cons (Xf x) (vec2 (I := I) Y Z) ∘ Fin.castAdd 2
        = fun _ : Fin 1 => Xf x := by
      funext a
      fin_cases a
      rfl
    have hright : Fin.cons (Xf x) (vec2 (I := I) Y Z) ∘ Fin.natAdd 1
        = vec2 (I := I) Y Z := by
      funext a
      fin_cases a <;> rfl
    rw [hleft, hright, hdu x (Xf x), metricTensorField_apply,
      show vec2 (I := I) Y Z 0 = Y from rfl, show vec2 (I := I) Y Z 1 = Z from rfl]
  have hhalf : extDerivFun (I := I) (ahlforsHalfTraceFun (I := I) g nablaH) x (Xf x)
      = (2 : Real)⁻¹ * extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (Xf x) := by
    have htau_md : MDifferentiableAt I 𝓘(Real, Real) (ahlforsTraceFun (I := I) g nablaH) x :=
      (ahlforsTraceFun_smooth (I := I) g nablaH).contMDiffAt.mdifferentiableAt (by simp)
    have hconst := DifferentialGeometry.extDerivFun_const_mul (I := I)
      (c := (2 : Real)⁻¹) (f := ahlforsTraceFun (I := I) g nablaH) (x := x) htau_md
    have hv := DFunLike.congr_fun hconst (Xf x)
    simpa [ahlforsHalfTraceFun, Pi.smul_apply, smul_eq_mul] using hv
  rw [hP, hQ, hR, hhalf] at hexpand
  linarith [hexpand]

set_option backward.isDefEq.respectTransparency false in
private theorem ahlfors_divergence_sum
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Bsec : Idx → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hBsec : ∀ i, Bsec i x = basis i)
    (X : TangentSpace I x) :
    (2 : Real) * (∑ i, ∑ j, gInv i j *
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) x
          (vec2 (I := I) (basis j) X))
      = roughLap0STensor (I := I) g (s := 1) (nabla2H x) (fun _ : Fin 1 => X)
        + metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) := by
  classical
  haveI : IsManifold I 3 M :=
    IsManifold.of_le (by decide : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hmc : IsMetricCompatible_gen (I := I) (metricCov (I := I) (M := M) g) g :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hentry : ∀ i j,
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) x
          (vec2 (I := I) (basis j) X)
      = (2 : Real)⁻¹ * (nabla2H x (vec3 (I := I) (basis i) (basis j) X)
            + nabla2H x (vec3 (I := I) (basis i) X (basis j)))
        - (2 : Real)⁻¹ * extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
          * g.inner x (basis j) X := by
    intro i j
    rw [nabla0SFun_ahlfors_eval (I := I) g h nablaH nabla2H hRealizes2 (Bsec i) x
      (basis j) X, hBsec i]
  have hRL : roughLap0STensor (I := I) g (s := 1) (nabla2H x) (fun _ : Fin 1 => X)
      = ∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) (basis j) X) :=
    roughLap_apply_eq_sum' (I := I) g basis gInv hinv (nabla2H x) X
  have hR2' : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) h nablaH x (nabla2H x) :=
    hRealizes2 x
  have hcomm : OneFormThirdCovDerivCommAt (I := I)
      (metricRm13 (I := I) (M := M) g) (h x) (nabla2H x) :=
    oneFormThirdCovDerivCommAt_of_leviCivita (I := I) g
      (metricRm13 (I := I) (M := M) g) h nablaH (h x) (nabla2H x)
      (metricCurvData (I := I) (M := M) g).h_rm13 rfl hR2'
  have hSkew : Rm13MetricSkewAt (I := I) g x (metricRm13 (I := I) (M := M) g x) :=
    rm13MetricSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm13 (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g)
      (metricCurvData (I := I) (M := M) g).h_rm13
      (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have hAlpha : h x =
      dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x)
          (cotangentSharp (I := I) g x (h x))) := by
    ext v
    have hv : (fun _ : Fin 1 => v 0) = v := by
      funext i
      fin_cases i
      rfl
    rw [← hv]
    rw [dualToCotangent_apply_gen, tangentFlatLinear_apply_gen]
    rw [cotangentSharp_inner, cotangentToDual_apply]
  have hcurvV : CurvatureTraceOneFormEqRicVectorAt (I := I)
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (h x) basis gInv (cotangentSharp (I := I) g x (h x)) :=
    curvatureTraceOneFormEqRicVectorAt_of_metric_dual (I := I) g
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (h x) basis gInv (cotangentSharp (I := I) g x (h x)) hinv
      (metricCurvData (I := I) (M := M) g).h_ricci13 hSkew hAlpha
  have hswapRic : ∀ U V : TangentSpace I x,
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) U V) =
        metricRicciAt (I := I) (M := M) g x (vec2 (I := I) V U) := by
    intro U V
    have hcomp : ∀ i j : Idx,
        metricRicciAt (I := I) (M := M) g x
            (fun q : Fin 2 => if q = 0 then basis i else basis j) =
          metricRicciAt (I := I) (M := M) g x
            (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
      intro i j
      exact metricRicciSymm (I := I) (M := M) g basis gInv hinv i j
    exact DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
      (I := I) basis (metricRicciAt (I := I) (M := M) g x) hcomp U V
  have hRic :
      (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j))) -
          (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j))) =
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) := by
    have key : ∀ i j : Idx,
        gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)) -
            gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)) =
          -(gInv i j * metricRm13 (I := I) (M := M) g x (h x)
            (vec3 (I := I) (basis i) X (basis j))) := by
      intro i j
      rw [← mul_sub, hcomm (basis i) X (basis j), mul_neg]
    calc
      (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j))) -
            (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)))
          = ∑ i, ∑ j,
              (gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)) -
                gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j))) := by
            simp only [Finset.sum_sub_distrib]
        _ = ∑ i, ∑ j,
              -(gInv i j * metricRm13 (I := I) (M := M) g x (h x)
                (vec3 (I := I) (basis i) X (basis j))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
        _ = -∑ i, ∑ j, gInv i j * metricRm13 (I := I) (M := M) g x (h x)
              (vec3 (I := I) (basis i) X (basis j)) := by
            simp only [Finset.sum_neg_distrib]
        _ = metricRicci (I := I) (M := M) g x
              (vec2 (I := I) X (cotangentSharp (I := I) g x (h x))) := hcurvV X
        _ = metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) X (cotangentSharp (I := I) g x (h x))) := by
            rw [metricRicci_apply]
        _ = metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) :=
            hswapRic X (cotangentSharp (I := I) g x (h x))
  obtain ⟨Ws, hWs⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hterm : ∀ i j, nabla2H x (vec3 (I := I) X (basis i) (basis j))
      = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) Ws nablaH x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    rw [← hWs]
    exact (hRealizes2 x).2 Ws (basis i) (basis j)
  have hdtau0 : (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)))
      = extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x X := by
    have hd : differential1FormFun (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (nablaH y)) x (fun _ : Fin 1 => Ws x)
        = metricTracePair0SAt (I := I) g
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (metricCov (I := I) (M := M) g) Ws nablaH x) :=
      dTrace02_eq (I := I) (M := M) (metricCov (I := I) (M := M) g) g hmc nablaH Ws x
    calc
      (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)))
          = ∑ i, ∑ j, gInv i j *
              (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
                (metricCov (I := I) (M := M) g) Ws nablaH x)
                (vec2 (I := I) (basis i) (basis j)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hterm i j]
        _ = metricTracePair0SAt (I := I) g
              (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
                (metricCov (I := I) (M := M) g) Ws nablaH x) :=
            (metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv _).symm
        _ = differential1FormFun (I := I)
              (fun y : M => metricTracePair0SAt (I := I) g (nablaH y)) x
              (fun _ : Fin 1 => Ws x) := hd.symm
        _ = extDerivFun (I := I)
              (fun y : M => metricTracePair0SAt (I := I) g (nablaH y)) x (Ws x) :=
            differential1FormFun_apply_eq_extDerivFun (I := I) _ x (Ws x)
        _ = extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x X := by
            rw [hWs]
            rfl
  have hcontract : (∑ i, ∑ j, gInv i j *
        (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
          * g.inner x (basis j) X))
      = extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x X :=
    invMetric_contract_oneform (I := I) g basis gInv hinv
      (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x) X
  have hsum : (∑ i, ∑ j, gInv i j *
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) x
          (vec2 (I := I) (basis j) X))
      = (2 : Real)⁻¹ *
            (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) (basis j) X))
        + (2 : Real)⁻¹ *
            (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)))
        - (2 : Real)⁻¹ *
            (∑ i, ∑ j, gInv i j *
              (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
                * g.inner x (basis j) X)) := by
    calc
      (∑ i, ∑ j, gInv i j *
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) x
            (vec2 (I := I) (basis j) X))
          = ∑ i, ∑ j,
              ((2 : Real)⁻¹ * (gInv i j * nabla2H x (vec3 (I := I) (basis i) (basis j) X))
                + (2 : Real)⁻¹ * (gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)))
                - (2 : Real)⁻¹ * (gInv i j *
                    (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
                      * g.inner x (basis j) X))) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hentry i j]
            ring
        _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hRL, hsum]
  linarith [hRic, hdtau0, hcontract]

set_option linter.unusedVariables false in
private theorem ahlforsDivergence_weitzenbock
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Dh : Tensor0SSection (I := I) (M := M) 2)
    (nablaDh : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hDh : ∀ y : M, Dh y = ahlforsOperator (I := I) g (nablaH y))
    (hnablaDh : ∀ x : M,
      Nabla0SRealizesAt (I := I) 2 (metricCov (I := I) (M := M) g) Dh nablaDh x)
    (x : M) (X : TangentSpace I x) :
    (2 : Real) * metricTraceFirstTwo0STensor (I := I) g (s := 1) (nablaDh x) (fun _ : Fin 1 => X)
      = roughLap0STensor (I := I) g (s := 1) (nabla2H x) (fun _ : Fin 1 => X)
        + metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) := by
  classical
  haveI : IsManifold I 3 M :=
    IsManifold.of_le (by decide : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hmc : IsMetricCompatible_gen (I := I) (metricCov (I := I) (M := M) g) g :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hDhSec : Dh = ahlforsSection (I := I) g nablaH := by
    refine DFunLike.ext _ _ (fun y => ?_)
    rw [hDh y, ahlforsSection_apply (I := I) hdim g nablaH y]
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
    with hbasis_def
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x x) with hgInv_def
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
    simpa [hbasis_def, hgInv_def] using
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
  let B : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun i => (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose
  have hB : ∀ i, B i x = basis i := fun i =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose_spec
  have hentry : ∀ i j, nablaDh x (vec3 (I := I) (basis i) (basis j) X)
      = (2 : Real)⁻¹ * (nabla2H x (vec3 (I := I) (basis i) (basis j) X)
            + nabla2H x (vec3 (I := I) (basis i) X (basis j)))
        - (2 : Real)⁻¹ * extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
          * g.inner x (basis j) X := by
    intro i j
    have hcons : vec3 (I := I) (basis i) (basis j) X
        = Fin.cons (B i x) (vec2 (I := I) (basis j) X) := by
      rw [hB i]
      funext k
      fin_cases k <;> rfl
    calc
      nablaDh x (vec3 (I := I) (basis i) (basis j) X)
          = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (metricCov (I := I) (M := M) g) (B i) Dh x (vec2 (I := I) (basis j) X) := by
            rw [hcons]
            exact hnablaDh x (B i) (vec2 (I := I) (basis j) X)
        _ = (2 : Real)⁻¹ * (nabla2H x (vec3 (I := I) (basis i) (basis j) X)
                + nabla2H x (vec3 (I := I) (basis i) X (basis j)))
            - (2 : Real)⁻¹
              * extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
              * g.inner x (basis j) X := by
            rw [hDhSec,
              nabla0SFun_ahlfors_eval (I := I) g h nablaH nabla2H hRealizes2 (B i) x
                (basis j) X, hB i]
  have hLHS : metricTraceFirstTwo0STensor (I := I) g (s := 1) (nablaDh x) (fun _ : Fin 1 => X)
      = ∑ i, ∑ j, gInv i j * nablaDh x (vec3 (I := I) (basis i) (basis j) X) := by
    rw [metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv (nablaDh x)
        (fun _ : Fin 1 => X)]
    unfold metricTrace0S2InBasis
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [metricTraceInput_one_eq_vec3]
  have hRL : roughLap0STensor (I := I) g (s := 1) (nabla2H x) (fun _ : Fin 1 => X)
      = ∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) (basis j) X) :=
    roughLap_apply_eq_sum' (I := I) g basis gInv hinv (nabla2H x) X
  have hR2' : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) h nablaH x (nabla2H x) :=
    hRealizes2 x
  have hcomm : OneFormThirdCovDerivCommAt (I := I)
      (metricRm13 (I := I) (M := M) g) (h x) (nabla2H x) :=
    oneFormThirdCovDerivCommAt_of_leviCivita (I := I) g
      (metricRm13 (I := I) (M := M) g) h nablaH (h x) (nabla2H x)
      (metricCurvData (I := I) (M := M) g).h_rm13 rfl hR2'
  have hSkew : Rm13MetricSkewAt (I := I) g x (metricRm13 (I := I) (M := M) g x) :=
    rm13MetricSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm13 (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g)
      (metricCurvData (I := I) (M := M) g).h_rm13
      (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have hAlpha : h x =
      dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x)
          (cotangentSharp (I := I) g x (h x))) := by
    ext v
    have hv : (fun _ : Fin 1 => v 0) = v := by
      funext i
      fin_cases i
      rfl
    rw [← hv]
    rw [dualToCotangent_apply_gen, tangentFlatLinear_apply_gen]
    rw [cotangentSharp_inner, cotangentToDual_apply]
  have hcurvV : CurvatureTraceOneFormEqRicVectorAt (I := I)
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (h x) basis gInv (cotangentSharp (I := I) g x (h x)) :=
    curvatureTraceOneFormEqRicVectorAt_of_metric_dual (I := I) g
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (h x) basis gInv (cotangentSharp (I := I) g x (h x)) hinv
      (metricCurvData (I := I) (M := M) g).h_ricci13 hSkew hAlpha
  have hswapRic : ∀ U V : TangentSpace I x,
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) U V) =
        metricRicciAt (I := I) (M := M) g x (vec2 (I := I) V U) := by
    intro U V
    have hcomp : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        metricRicciAt (I := I) (M := M) g x
            (fun q : Fin 2 => if q = 0 then basis i else basis j) =
          metricRicciAt (I := I) (M := M) g x
            (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
      intro i j
      exact metricRicciSymm (I := I) (M := M) g basis gInv hinv i j
    exact DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
      (I := I) basis (metricRicciAt (I := I) (M := M) g x) hcomp U V
  have hRic :
      (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j))) -
          (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j))) =
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) := by
    have key : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)) -
            gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)) =
          -(gInv i j * metricRm13 (I := I) (M := M) g x (h x)
            (vec3 (I := I) (basis i) X (basis j))) := by
      intro i j
      rw [← mul_sub, hcomm (basis i) X (basis j), mul_neg]
    calc
      (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j))) -
            (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)))
          = ∑ i, ∑ j,
              (gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)) -
                gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j))) := by
            simp only [Finset.sum_sub_distrib]
        _ = ∑ i, ∑ j,
              -(gInv i j * metricRm13 (I := I) (M := M) g x (h x)
                (vec3 (I := I) (basis i) X (basis j))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
        _ = -∑ i, ∑ j, gInv i j * metricRm13 (I := I) (M := M) g x (h x)
              (vec3 (I := I) (basis i) X (basis j)) := by
            simp only [Finset.sum_neg_distrib]
        _ = metricRicci (I := I) (M := M) g x
              (vec2 (I := I) X (cotangentSharp (I := I) g x (h x))) := hcurvV X
        _ = metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) X (cotangentSharp (I := I) g x (h x))) := by
            rw [metricRicci_apply]
        _ = metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) :=
            hswapRic X (cotangentSharp (I := I) g x (h x))
  obtain ⟨Ws, hWs⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hterm : ∀ i j, nabla2H x (vec3 (I := I) X (basis i) (basis j))
      = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) Ws nablaH x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    rw [← hWs]
    exact (hRealizes2 x).2 Ws (basis i) (basis j)
  have hdtau0 : (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)))
      = extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x X := by
    have hd : differential1FormFun (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (nablaH y)) x (fun _ : Fin 1 => Ws x)
        = metricTracePair0SAt (I := I) g
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (metricCov (I := I) (M := M) g) Ws nablaH x) :=
      dTrace02_eq (I := I) (M := M) (metricCov (I := I) (M := M) g) g hmc nablaH Ws x
    calc
      (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) X (basis i) (basis j)))
          = ∑ i, ∑ j, gInv i j *
              (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
                (metricCov (I := I) (M := M) g) Ws nablaH x)
                (vec2 (I := I) (basis i) (basis j)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hterm i j]
        _ = metricTracePair0SAt (I := I) g
              (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
                (metricCov (I := I) (M := M) g) Ws nablaH x) :=
            (metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv _).symm
        _ = differential1FormFun (I := I)
              (fun y : M => metricTracePair0SAt (I := I) g (nablaH y)) x
              (fun _ : Fin 1 => Ws x) := hd.symm
        _ = extDerivFun (I := I)
              (fun y : M => metricTracePair0SAt (I := I) g (nablaH y)) x (Ws x) :=
            differential1FormFun_apply_eq_extDerivFun (I := I) _ x (Ws x)
        _ = extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x X := by
            rw [hWs]
            rfl
  have hcontract : (∑ i, ∑ j, gInv i j *
        (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
          * g.inner x (basis j) X))
      = extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x X :=
    invMetric_contract_oneform (I := I) g basis gInv hinv
      (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x) X
  have hsum : (∑ i, ∑ j, gInv i j * nablaDh x (vec3 (I := I) (basis i) (basis j) X))
      = (2 : Real)⁻¹ *
            (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) (basis j) X))
        + (2 : Real)⁻¹ *
            (∑ i, ∑ j, gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)))
        - (2 : Real)⁻¹ *
            (∑ i, ∑ j, gInv i j *
              (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
                * g.inner x (basis j) X)) := by
    calc
      (∑ i, ∑ j, gInv i j * nablaDh x (vec3 (I := I) (basis i) (basis j) X))
          = ∑ i, ∑ j,
              ((2 : Real)⁻¹ * (gInv i j * nabla2H x (vec3 (I := I) (basis i) (basis j) X))
                + (2 : Real)⁻¹ * (gInv i j * nabla2H x (vec3 (I := I) (basis i) X (basis j)))
                - (2 : Real)⁻¹ * (gInv i j *
                    (extDerivFun (I := I) (ahlforsTraceFun (I := I) g nablaH) x (basis i)
                      * g.inner x (basis j) X))) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hentry i j]
            ring
        _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hLHS, hRL, hsum]
  linarith [hRic, hdtau0, hcontract]

theorem ahlfors_identity_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Dh : Tensor0SSection (I := I) (M := M) 2)
    (nablaDh : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hDh : ∀ y : M, Dh y = ahlforsOperator (I := I) g (nablaH y))
    (hnablaDh : ∀ x : M,
      Nabla0SRealizesAt (I := I) 2 (metricCov (I := I) (M := M) g) Dh nablaDh x)
    (x : M) :
    (2 : Real) • metricTraceFirstTwo0STensor (I := I) g (s := 1) (nablaDh x) =
      roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • (h x) := by
  ext v
  have hLHS : ((2 : Real) • metricTraceFirstTwo0STensor (I := I) g (s := 1) (nablaDh x)) v
      = (2 : Real) * metricTraceFirstTwo0STensor (I := I) g (s := 1) (nablaDh x) v := rfl
  have hRHS : (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • (h x)) v
      = roughLap0STensor (I := I) g (s := 1) (nabla2H x) v
        + gaussCurvature (I := I) g x * (h x) v := rfl
  rw [hLHS, hRHS]
  set X := v 0 with hX
  have hv : v = (fun _ : Fin 1 => X) := by funext i; fin_cases i; rfl
  rw [hv, ahlforsDivergence_weitzenbock hdim g h nablaH nabla2H Dh nablaDh
      hRealizes1 hRealizes2 hDh hnablaDh x X,
    ricci_eq_gaussCurvature_smul_metric_twoDim hdim g x
      (cotangentSharp (I := I) g x (h x)) X,
    cotangentSharp_inner, cotangentToDual_apply]


private theorem inner0S_add_smul_self_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (D W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (a : Real) :
    inner0S (I := I) g x 1 (D + a • W) (D + a • W) =
      inner0S (I := I) g x 1 D D + 2 * a * inner0S (I := I) g x 1 D W
        + a ^ 2 * inner0S (I := I) g x 1 W W := by
  rw [inner0S_add_left', inner0S_add_right', inner0S_add_right']
  simp only [inner0S_smul_left, inner0S_smul_right]
  rw [show inner0S (I := I) g x 1 W D = inner0S (I := I) g x 1 D W from
    inner0S_symm' (I := I) g x 1 W D]
  ring

private theorem oneFormWrap_bridge
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (W : SmoothCcTensor g 0 1)
    (hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h y))
    (x : M) :
    (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH x))
      ∧ (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x))) :=
  DifferentialGeometry.Analysis.Spectral.OneFormRealization.wrapped_covGrad_rawConnLap_realizes
    (I := I) (M := M) g h nablaH nabla2H W hW x (hRealizes2 x)

set_option backward.isDefEq.respectTransparency false in
private theorem inner0S_eq_tensorInnerScalar
    (g : SmoothRiemannianMetric I M) {s : ℕ} (x : M)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (SA SB : Cₛ^∞⟮I; TensorRSModel 0 s Real E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (hSA : TensorRSSpace.toModel (SA x) = TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
    (hSB : TensorRSSpace.toModel (SB x) = TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) :
    inner0S (I := I) g x s A B = tensorInnerScalar (I := I) (M := M) g 0 s SA SB x := by
  rw [tensorInnerScalar_apply, hSA, hSB, inner_toRS0,
    ← inner0S_eq_covariantTensorInnerPointwise]

set_option linter.unusedVariables false in
private theorem roughLapPlusK_normSq_expand
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x)) :
    (∫ x, normSq0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
            + gaussCurvature (I := I) g x • (h x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = (∫ x, normSq0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        + (2 : Real) * (∫ x, gaussCurvature (I := I) g x *
              inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        + (∫ x, gaussCurvature (I := I) g x ^ 2 * normSq0S (I := I) g x 1 (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  set W : SmoothCcTensor g 0 1 :=
    { toSection := h.toTensorRSField (∞ : WithTop ℕ∞)
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h y) := fun y =>
    Tensor0SField.toRS0_eq (I := I) (M := M) (∞ : WithTop ℕ∞) h y
  set L : SmoothCcTensor g 0 1 := rawTensorConnLapSmooth (I := I) g 0 1 W with hL_def
  have hB2 : ∀ x : M, TensorRSSpace.toModel (L.toSection x) =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0 (roughLap0STensor (I := I) g (s := 1) (nabla2H x))) :=
    fun x => (oneFormWrap_bridge (I := I) g h nablaH nabla2H hRealizes2 W hW x).2
  have hWx : ∀ x : M, TensorRSSpace.toModel (W.toSection x) =
      TensorRSSpace.toModel (Tensor0SSpace.toRS0 (h x)) :=
    fun x => congrArg TensorRSSpace.toModel (hW x)
  have hf1 : ∀ x : M, normSq0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
      = tensorInnerScalar (I := I) (M := M) g 0 1 L.toSection L.toSection x := by
    intro x
    rw [normSq0S_eq_inner]
    exact inner0S_eq_tensorInnerScalar (I := I) g x _ _ L.toSection L.toSection (hB2 x) (hB2 x)
  have hf2 : ∀ x : M, inner0S (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
      = tensorInnerScalar (I := I) (M := M) g 0 1 L.toSection W.toSection x := fun x =>
    inner0S_eq_tensorInnerScalar (I := I) g x _ _ L.toSection W.toSection (hB2 x) (hWx x)
  have hf3 : ∀ x : M, normSq0S (I := I) g x 1 (h x)
      = tensorInnerScalar (I := I) (M := M) g 0 1 W.toSection W.toSection x := by
    intro x
    rw [normSq0S_eq_inner]
    exact inner0S_eq_tensorInnerScalar (I := I) g x _ _ W.toSection W.toSection (hWx x) (hWx x)
  have hcont1 : Continuous
      (fun x : M => normSq0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x))) :=
    ((tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
      L.toSection L.toSection).continuous).congr (fun x => (hf1 x).symm)
  have hcont2 : Continuous (fun x : M => gaussCurvature (I := I) g x *
      inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)) :=
    (hK.continuous.mul (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
      L.toSection W.toSection).continuous).congr
      (fun x => by rw [Pi.mul_apply, hf2 x])
  have hcont3 : Continuous (fun x : M => gaussCurvature (I := I) g x ^ 2 *
      normSq0S (I := I) g x 1 (h x)) :=
    ((hK.continuous.pow 2).mul (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
      W.toSection W.toSection).continuous).congr
      (fun x => by rw [Pi.mul_apply, hf3 x])
  have hint1 := integrable_of_continuous_compactSpace (I := I) (M := M) g hcont1
  have hint2 := integrable_of_continuous_compactSpace (I := I) (M := M) g hcont2
  have hint3 := integrable_of_continuous_compactSpace (I := I) (M := M) g hcont3
  have hpt : ∀ x : M, normSq0S (I := I) g x 1
      (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • (h x))
      = normSq0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
        + ((2 : Real) * (gaussCurvature (I := I) g x *
            inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x))
          + gaussCurvature (I := I) g x ^ 2 * normSq0S (I := I) g x 1 (h x)) := by
    intro x
    rw [normSq0S_eq_inner, inner0S_add_smul_self_one (I := I) g x _ _ _,
      ← normSq0S_eq_inner, ← normSq0S_eq_inner]
    ring
  have hint2' : Integrable (fun x : M => (2 : Real) * (gaussCurvature (I := I) g x *
      inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := hint2.const_mul 2
  have hint23 : Integrable (fun x : M => (2 : Real) * (gaussCurvature (I := I) g x *
      inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x))
      + gaussCurvature (I := I) g x ^ 2 * normSq0S (I := I) g x 1 (h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := hint2'.add hint3
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_add hint1 hint23,
    MeasureTheory.integral_add hint2' hint3,
    MeasureTheory.integral_const_mul]
  ring

private theorem toModel_apply0S {s : ℕ} {z : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z)
    (m : Fin s → TangentSpace I z) :
    Tensor0SSpace.toModel T m = T m := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem toRS0_sum {s : ℕ} {z : M} {ι : Type*} [Fintype ι]
    (f : ι → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toRS0 (∑ i : ι, f i) = ∑ i : ι, Tensor0SSpace.toRS0 (f i) := by
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SSpace.toRS0_apply, ContinuousLinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Tensor0SSpace.toRS0_apply]

private theorem tensor0S_sum_apply' {ι : Type*} [Fintype ι] {z : M} {s : ℕ}
    (T : ι → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z)
    (v : Fin s → TangentSpace I z) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      change (0 : ContinuousMultilinearMap Real (fun _ : Fin s => TangentSpace I z) Real) v = 0
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change T a v + (∑ i ∈ S, T i) v = T a v + ∑ i ∈ S, T i v
      rw [ih]

set_option backward.isDefEq.respectTransparency false in
private theorem nabla0SFun_two_koszul'
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (A : TwoTensorSection (I := I) (M := M)) (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X A x
        (vec2 (I := I) (Y x) (Z x)) =
      extDerivFun (I := I) (fun p : M => A p (vec2 (I := I) (Y p) (Z p))) x (X x) -
        A x (vec2 (I := I) ((cov (fun p => Y p) x) (X x)) (Z x)) -
        A x (vec2 (I := I) (Y x) ((cov (fun p => Z p) x) (X x))) := by
  classical
  have h := nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 2) cov X ![Y, Z] A x
  have hslots : (fun a : Fin 2 => (![Y, Z] a) x) = vec2 (I := I) (Y x) (Z x) := by
    funext a; fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hp : (fun p : M => A p (fun a : Fin 2 => (![Y, Z] a) p)) =
      (fun p : M => A p (vec2 (I := I) (Y p) (Z p))) := by
    funext p; congr 1; funext a; fin_cases a <;>
      simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hslots, hp, Fin.sum_univ_two] at h
  have hu0 : (Function.update (vec2 (I := I) (Y x) (Z x)) 0
        ((cov (fun p => (![Y, Z] 0) p) x) (X x))) =
      vec2 (I := I) ((cov (fun p => Y p) x) (X x)) (Z x) := by
    funext a; fin_cases a <;>
      simp [Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hu1 : (Function.update (vec2 (I := I) (Y x) (Z x)) 1
        ((cov (fun p => (![Y, Z] 1) p) x) (X x))) =
      vec2 (I := I) (Y x) ((cov (fun p => Z p) x) (X x)) := by
    funext a; fin_cases a <;>
      simp [Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hu0, hu1] at h
  rw [h]; ring

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SCovDeriv_two_eval
    (g : SmoothRiemannianMetric I M)
    (A : TwoTensorSection (I := I) (M := M))
    (Xf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (b : M) (w₁ w₂ : TangentSpace I b) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
          (fun y : M => A y) b (Xf b))
        (vec2 (I := I) w₁ w₂)
      = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) Xf A b (vec2 (I := I) w₁ w₂) := by
  classical
  set Z₁ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ⟨smoothExtensionTangent (I := I) b w₁,
      smoothExtensionTangent_contMDiff (I := I) b w₁⟩ with hZ₁def
  set Z₂ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ⟨smoothExtensionTangent (I := I) b w₂,
      smoothExtensionTangent_contMDiff (I := I) b w₂⟩ with hZ₂def
  have hZ₁ : Z₁ b = w₁ := smoothExtensionTangent_eq (I := I) b w₁
  have hZ₂ : Z₂ b = w₂ := smoothExtensionTangent_eq (I := I) b w₂
  rw [show vec2 (I := I) w₁ w₂ = vec2 (I := I) (Z₁ b) (Z₂ b) from by rw [hZ₁, hZ₂]]
  have hA2 : TensorSectionMDiffAt (I := I) 2 (fun y : M => A y) b :=
    A.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 1
    (fun y : M => A y) hA2 Z₁ (Xf b) (fun _ : Fin 1 => (Z₂ b : TangentSpace I b))
  set W1 : (y : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y :=
    fun y : M => curriedSection I M (fun z : M => A z) y (Z₁ y) with hW1def
  have hcurroMD := (mdifferentiableAt_curriedSection_iff_section (I := I) (M := M)
    (fun z : M => A z) (x := b)).mp hA2
  have hZ₁MD : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (fun y : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) y (Z₁ y)) b :=
    Z₁.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hW1 : TensorSectionMDiffAt (I := I) 1 W1 b :=
    MDifferentiableAt.clm_bundle_apply (b := id) hcurroMD hZ₁MD
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 0
    W1 hW1 Z₂ (Xf b) (fun i : Fin 0 => i.elim0)
  set W0 : (y : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 y :=
    fun y : M => curriedSection I M W1 y (Z₂ y) with hW0def
  have hd0 : Tensor0SSpace.toModel
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W0 b (Xf b))
      (fun i : Fin 0 => i.elim0)
      = extDerivFun (I := I) (scalarFn I M W0) b (Xf b) := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g W0 b (Xf b)]
    rfl
  have hsc : scalarFn I M W0 = fun p : M => A p (vec2 (I := I) (Z₁ p) (Z₂ p)) := by
    funext p
    rw [scalarFn_eq_apply_zero]
    have h1 : W0 p (0 : Fin 0 → TangentSpace I p) = W1 p (Fin.cons (Z₂ p) 0) := by
      rw [hW0def]
      exact curry_eval' (I := I) (W1 p) (Z₂ p) 0
    have h2 : W1 p (Fin.cons (Z₂ p) (0 : Fin 0 → TangentSpace I p))
        = A p (Fin.cons (Z₁ p) (Fin.cons (Z₂ p) 0)) := by
      rw [hW1def]
      exact curry_eval' (I := I) (A p) (Z₁ p) (Fin.cons (Z₂ p) 0)
    have h3 : (Fin.cons (Z₁ p) (Fin.cons (Z₂ p) (0 : Fin 0 → TangentSpace I p))
        : Fin 2 → TangentSpace I p) = vec2 (I := I) (Z₁ p) (Z₂ p) := by
      funext a
      fin_cases a <;> rfl
    rw [h1, h2, h3]
  have hcons2 : (Fin.cons (Z₂ b) (fun i : Fin 0 => i.elim0)
      : Fin 1 → TangentSpace I b) = fun _ : Fin 1 => (Z₂ b : TangentSpace I b) := by
    funext i
    fin_cases i
    rfl
  have hLC1 : (LeviCivita (I := I) g).toFun (fun y : M => Z₁ y) b (Xf b)
      = (metricCov (I := I) (M := M) g) (fun p : M => Z₁ p) b (Xf b) := rfl
  have hLC2 : (LeviCivita (I := I) g).toFun (fun y : M => Z₂ y) b (Xf b)
      = (metricCov (I := I) (M := M) g) (fun p : M => Z₂ p) b (Xf b) := rfl
  have hT2 : Tensor0SSpace.toModel
      (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M => A y) b (Xf b)) (vec2 (I := I) (Z₁ b) (Z₂ b))
      = Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
            (fun y : M => A y) b (Xf b))
          (Fin.cons (Z₁ b) (fun _ : Fin 1 => (Z₂ b : TangentSpace I b))) := by
    congr 1
    funext a
    fin_cases a <;> rfl
  rw [hT2, hpeel1]
  rw [show (fun _ : Fin 1 => (Z₂ b : TangentSpace I b))
      = (Fin.cons (Z₂ b) (fun i : Fin 0 => i.elim0) : Fin 1 → TangentSpace I b) from
    hcons2.symm]
  rw [hpeel2, hd0]
  rw [nabla0SFun_two_koszul' (I := I) (metricCov (I := I) (M := M) g) Xf Z₁ Z₂ A b]
  rw [hsc]
  have hterm2 : Tensor0SSpace.toModel (A b)
      (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Z₁ y) b (Xf b))
        (Fin.cons (Z₂ b) (fun i : Fin 0 => i.elim0)))
      = A b (vec2 (I := I) ((metricCov (I := I) (M := M) g) (fun p => Z₁ p) b (Xf b)) (Z₂ b)) := by
    rw [toModel_apply0S]
    congr 1
    funext a
    fin_cases a
    · exact hLC1
    · rfl
  have hterm3 : Tensor0SSpace.toModel (W1 b)
      (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Z₂ y) b (Xf b))
        (fun i : Fin 0 => i.elim0))
      = A b (vec2 (I := I) (Z₁ b) ((metricCov (I := I) (M := M) g) (fun p => Z₂ p) b (Xf b))) := by
    rw [toModel_apply0S, hW1def]
    rw [show curriedSection I M (fun z : M => A z) b (Z₁ b)
          (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Z₂ y) b (Xf b))
            (fun i : Fin 0 => i.elim0))
        = A b (Fin.cons (Z₁ b)
            (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Z₂ y) b (Xf b))
              (fun i : Fin 0 => i.elim0))) from
      curry_eval' (I := I) (A b) (Z₁ b) _]
    congr 1
    funext a
    fin_cases a
    · rfl
    · exact hLC2
  rw [hterm2, hterm3]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem toModel_contract_eval (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[Real] Tensor0SSpace s I b from
          contract_covariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[Real] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons ((v : TangentSpace I b) : E) m) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem contract_covariant_toRS0 {b : M} (v : TangentSpace I b)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 b) :
    contract_covariant (𝕜 := Real) 0 1 b v (Tensor0SSpace.toRS0 T)
      = Tensor0SSpace.toRS0 (tensor0S_curry (𝕜 := Real) (I := I) 1 b T v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  rw [toModel_contract_eval (I := I) 1 b v (Tensor0SSpace.toRS0 T) D m]
  rw [show (show Tensor0SSpace 0 I b →L[Real] Tensor0SSpace 2 I b from
      Tensor0SSpace.toRS0 T) D = tensor0SSpace_evalScalar b D • T from rfl]
  rw [show (Tensor0SSpace.toRS0 (tensor0S_curry (𝕜 := Real) (I := I) 1 b T v)) D
      = tensor0SSpace_evalScalar b D • tensor0S_curry (𝕜 := Real) (I := I) 1 b T v from rfl]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  congr 1

private theorem tensor2_add_left {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (a b w : TangentSpace I x) :
    A (vec2 (I := I) (a + b) w) = A (vec2 (I := I) a w) + A (vec2 (I := I) b w) := by
  have h := Tensor0SSpace.map_update_add (I := I) A (vec2 (I := I) a w) 0 a b
  have e0 : Function.update (vec2 (I := I) a w) 0 (a + b) = vec2 (I := I) (a + b) w := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  have e1 : Function.update (vec2 (I := I) a w) 0 a = vec2 (I := I) a w := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  have e2 : Function.update (vec2 (I := I) a w) 0 b = vec2 (I := I) b w := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  rw [e0, e1, e2] at h
  exact h

private theorem tensor2_smul_left {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (a w : TangentSpace I x) :
    A (vec2 (I := I) (c • a) w) = c * A (vec2 (I := I) a w) := by
  have h := Tensor0SSpace.map_update_smul (I := I) A (vec2 (I := I) a w) 0 c a
  have e0 : Function.update (vec2 (I := I) a w) 0 (c • a) = vec2 (I := I) (c • a) w := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  have e1 : Function.update (vec2 (I := I) a w) 0 a = vec2 (I := I) a w := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  rw [e0, e1] at h
  rw [h, smul_eq_mul]

private theorem tensor2_add_right {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (w a b : TangentSpace I x) :
    A (vec2 (I := I) w (a + b)) = A (vec2 (I := I) w a) + A (vec2 (I := I) w b) := by
  have h := Tensor0SSpace.map_update_add (I := I) A (vec2 (I := I) w a) 1 a b
  have e0 : Function.update (vec2 (I := I) w a) 1 (a + b) = vec2 (I := I) w (a + b) := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  have e1 : Function.update (vec2 (I := I) w a) 1 a = vec2 (I := I) w a := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  have e2 : Function.update (vec2 (I := I) w a) 1 b = vec2 (I := I) w b := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  rw [e0, e1, e2] at h
  exact h

private theorem tensor2_smul_right {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (w a : TangentSpace I x) :
    A (vec2 (I := I) w (c • a)) = c * A (vec2 (I := I) w a) := by
  have h := Tensor0SSpace.map_update_smul (I := I) A (vec2 (I := I) w a) 1 c a
  have e0 : Function.update (vec2 (I := I) w a) 1 (c • a) = vec2 (I := I) w (c • a) := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  have e1 : Function.update (vec2 (I := I) w a) 1 a = vec2 (I := I) w a := by
    funext q; fin_cases q <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
      Function.update]
  rw [e0, e1] at h
  rw [h, smul_eq_mul]

private theorem tensor2_sum_left {ι : Type*} [Fintype ι] {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (r : ι → Real) (b : ι → TangentSpace I x) (w : TangentSpace I x) :
    A (vec2 (I := I) (∑ k : ι, r k • b k) w) = ∑ k : ι, r k * A (vec2 (I := I) (b k) w) := by
  classical
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun t => A (vec2 (I := I) t w)
      map_add' := fun a b' => tensor2_add_left (I := I) A a b' w
      map_smul' := fun c a => by
        rw [tensor2_smul_left (I := I) A c a w]; rfl }
  change L (∑ k : ι, r k • b k) = ∑ k : ι, r k * A (vec2 (I := I) (b k) w)
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

private theorem tensor2_sum_right {ι : Type*} [Fintype ι] {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (r : ι → Real) (b : ι → TangentSpace I x) (w : TangentSpace I x) :
    A (vec2 (I := I) w (∑ k : ι, r k • b k)) = ∑ k : ι, r k * A (vec2 (I := I) w (b k)) := by
  classical
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun t => A (vec2 (I := I) w t)
      map_add' := fun a b' => tensor2_add_right (I := I) A w a b'
      map_smul' := fun c a => by
        rw [tensor2_smul_right (I := I) A c w a]; rfl }
  change L (∑ k : ι, r k • b k) = ∑ k : ι, r k * A (vec2 (I := I) w (b k))
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

set_option maxHeartbeats 1600000 in
private theorem inner0S_covectorProd_eval
    (g : SmoothRiemannianMetric I M) {x : M}
    (u v : TangentSpace I x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    inner0S (I := I) g x 2
        (covectorTensorProd0S (I := I) (g.inner x u) (g.inner x v)) T
      = T (vec2 (I := I) u v) := by
  classical
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
    with hbasis_def
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x k l (extChartAt I x x) with hgInv_def
  have hinv := DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
    (I := I) g x
  have hcoef : ∀ (w : TangentSpace I x) k,
      (∑ i, gInv i k * g.inner x w (basis i)) = basis.repr w k := by
    intro w k
    have hw : w = ∑ m, basis.repr w m • basis m := (basis.sum_repr w).symm
    calc
      (∑ i, gInv i k * g.inner x w (basis i))
          = ∑ i, gInv i k * ∑ m, basis.repr w m * g.inner x (basis m) (basis i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            congr 1
            rw [g.symm x w (basis i)]
            conv_lhs => rw [hw]
            rw [map_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [map_smul, smul_eq_mul, g.symm x (basis i) (basis m)]
      _ = ∑ m, basis.repr w m * ∑ i, g.inner x (basis m) (basis i) * gInv i k := by
            rw [show (∑ i, gInv i k * ∑ m, basis.repr w m * g.inner x (basis m) (basis i))
                = ∑ i, ∑ m, basis.repr w m * (g.inner x (basis m) (basis i) * gInv i k) from by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun m _ => ?_
              ring]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ m, basis.repr w m * (if m = k then 1 else 0) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [(hinv m k).2]
      _ = basis.repr w k := by
            rw [Finset.sum_eq_single k]
            · simp
            · intro m _ hm
              simp [hm]
            · intro hk
              exact absurd (Finset.mem_univ k) hk
  have hswap4 : ∀ (F : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real),
      (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
    intro F
    calc
      (∑ i, ∑ j, ∑ k, ∑ l, F i j k l)
          = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact Finset.sum_comm
        _ = ∑ k, ∑ i, ∑ j, ∑ l, F i j k l := Finset.sum_comm
        _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun i _ => ?_
            exact Finset.sum_comm
        _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact Finset.sum_comm
  rw [inner0S_two_eq_coord (I := I) g x basis gInv hinv]
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, gInv i k * gInv j l *
        covectorTensorProd0S (I := I) (g.inner x u) (g.inner x v)
          (fun a : Fin 2 => if a = 0 then basis i else basis j) *
        T (fun a : Fin 2 => if a = 0 then basis k else basis l))
        = ∑ i, ∑ j, ∑ k, ∑ l, gInv i k * gInv j l *
            (g.inner x u (basis i) * g.inner x v (basis j)) *
            T (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [covectorTensorProd0S_apply]
          simp
    _ = ∑ k, ∑ l, ∑ i, ∑ j, gInv i k * gInv j l *
            (g.inner x u (basis i) * g.inner x v (basis j)) *
            T (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          exact hswap4 _
    _ = ∑ k, ∑ l, basis.repr u k * basis.repr v l *
            T (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← hcoef u k, ← hcoef v l]
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = T (vec2 (I := I) u v) := by
          have hif : ∀ k l, (fun a : Fin 2 => if a = 0 then basis k else basis l)
              = vec2 (I := I) (basis k) (basis l) := by
            intro k l
            funext a
            fin_cases a <;> rfl
          conv_rhs => rw [show u = ∑ m, basis.repr u m • basis m from (basis.sum_repr u).symm]
          rw [tensor2_sum_left (I := I) T (fun m => basis.repr u m) (fun m => basis m) v]
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_rhs => rw [show v = ∑ m, basis.repr v m • basis m from (basis.sum_repr v).symm]
          rw [tensor2_sum_right (I := I) T (fun m => basis.repr v m) (fun m => basis m)
            (basis k), Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hif k l]
          ring

private theorem cotangentSharp_gen_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    cotangentSharp_gen (I := I) g x β = cotangentSharp (I := I) g x β := by
  apply tangentFlatLinear_injective_gen (I := I) g x
  apply LinearMap.ext
  intro w
  rw [tangentFlatLinear_apply_gen, tangentFlatLinear_apply_gen]
  rw [cotangentSharp_inner_gen, cotangentToDual_apply_gen,
    cotangentSharp_inner, cotangentToDual_apply]

private theorem swap_covectorProd {x : M}
    (a b : TangentSpace I x →L[Real] Real) :
    swapSlots0S (I := I) (covectorTensorProd0S (I := I) (M := M) a b)
      = covectorTensorProd0S (I := I) b a := by
  ext v
  rw [swapSlots0S_apply, covectorTensorProd0S_apply, covectorTensorProd0S_apply]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

private theorem swap_smul_tensor {x : M} (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    swapSlots0S (I := I) (c • A) = c • swapSlots0S (I := I) A := by
  ext v
  rw [swapSlots0S_apply]
  rw [show (c • A) (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
      = c * A (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) from rfl]
  rw [show (c • swapSlots0S (I := I) A) v = c * swapSlots0S (I := I) A v from rfl,
    swapSlots0S_apply]

private theorem swap_add_tensor {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    swapSlots0S (I := I) (A + B) = swapSlots0S (I := I) A + swapSlots0S (I := I) B := by
  ext v
  rw [swapSlots0S_apply]
  rw [show (A + B) (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
      = A (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
        + B (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) from rfl]
  rw [show (swapSlots0S (I := I) A + swapSlots0S (I := I) B) v
      = swapSlots0S (I := I) A v + swapSlots0S (I := I) B v from rfl,
    swapSlots0S_apply, swapSlots0S_apply]

private theorem swap_sub_tensor {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    swapSlots0S (I := I) (A - B) = swapSlots0S (I := I) A - swapSlots0S (I := I) B := by
  ext v
  rw [swapSlots0S_apply]
  rw [show (A - B) (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
      = A (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
        - B (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) from rfl]
  rw [show (swapSlots0S (I := I) A - swapSlots0S (I := I) B) v
      = swapSlots0S (I := I) A v - swapSlots0S (I := I) B v from rfl,
    swapSlots0S_apply, swapSlots0S_apply]

private theorem swap_ahlfors (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    swapSlots0S (I := I) (ahlforsOperator (I := I) g T) = ahlforsOperator (I := I) g T := by
  rw [show ahlforsOperator (I := I) g T
      = symmetricPart0S (I := I) T
        - ((Module.finrank Real E : Real)⁻¹
            * metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T))
          • metricTensor0S (I := I) g x from rfl]
  rw [swap_sub_tensor, swap_smul_tensor, swapSlots0S_metricTensor0S]
  congr 1
  rw [show symmetricPart0S (I := I) T = (2 : Real)⁻¹ • (T + swapSlots0S (I := I) T) from rfl]
  rw [swap_smul_tensor, swap_add_tensor, swapSlots0S_swapSlots]
  congr 1
  abel

private theorem normSq_metric_two
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) = 2 := by
  rw [normSq0S_metricTensor0S_eq_card (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) g x k l (extChartAt I x x))
    (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)]
  have hc2 : Fintype.card (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) = 2 := by
    rw [← Module.finrank_eq_card_basis
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)]
    exact hdim
  rw [hc2]
  norm_num

private theorem ahlfors_inner_metric
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    inner0S (I := I) g x 2 (ahlforsOperator (I := I) g T) (metricTensor0S (I := I) g x)
      = 0 := by
  have hDeq : ahlforsOperator (I := I) g T
      = symmetricPart0S (I := I) T
        - ((2 : Real)⁻¹ * metricTracePair0SAt (I := I) g T) • metricTensor0S (I := I) g x := by
    rw [show ahlforsOperator (I := I) g T
        = symmetricPart0S (I := I) T
          - ((Module.finrank Real E : Real)⁻¹
              * metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T))
            • metricTensor0S (I := I) g x from rfl,
      trace_symmetricPart0S, hdim]
    norm_num
  rw [hDeq, inner0S_sub_left', inner0S_smul_left]
  have hpg : inner0S (I := I) g x 2 (symmetricPart0S (I := I) T) (metricTensor0S (I := I) g x)
      = metricTracePair0SAt (I := I) g T := by
    rw [inner0S_symm' (I := I) g x 2]
    exact trace_symmetricPart0S (I := I) g T
  rw [hpg, show inner0S (I := I) g x 2 (metricTensor0S (I := I) g x)
        (metricTensor0S (I := I) g x) = 2 from by
      rw [← normSq0S_eq_inner]
      exact normSq_metric_two (I := I) hdim g x]
  ring

private theorem inner_ahlfors_self
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    inner0S (I := I) g x 2 (T) (ahlforsOperator (I := I) g T)
      = normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g T) := by
  rw [normSq0S_eq_inner]
  have hsplit : inner0S (I := I) g x 2 T (ahlforsOperator (I := I) g T)
      - inner0S (I := I) g x 2 (ahlforsOperator (I := I) g T) (ahlforsOperator (I := I) g T)
      = inner0S (I := I) g x 2 (T - ahlforsOperator (I := I) g T)
          (ahlforsOperator (I := I) g T) := by
    rw [inner0S_sub_left']
  have hTsub : T - ahlforsOperator (I := I) g T
      = (2 : Real)⁻¹ • (T - swapSlots0S (I := I) T)
        + ((2 : Real)⁻¹ * metricTracePair0SAt (I := I) g T) • metricTensor0S (I := I) g x := by
    rw [show ahlforsOperator (I := I) g T
        = symmetricPart0S (I := I) T
          - ((Module.finrank Real E : Real)⁻¹
              * metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T))
            • metricTensor0S (I := I) g x from rfl,
      trace_symmetricPart0S, hdim,
      show symmetricPart0S (I := I) T = (2 : Real)⁻¹ • (T + swapSlots0S (I := I) T) from rfl]
    rw [show (((2 : ℕ) : Real))⁻¹ = (2 : Real)⁻¹ from by norm_num]
    module
  have hanti : inner0S (I := I) g x 2 (T - swapSlots0S (I := I) T)
      (ahlforsOperator (I := I) g T) = 0 := by
    rw [inner0S_sub_left']
    have hswap : inner0S (I := I) g x 2 (swapSlots0S (I := I) T) (ahlforsOperator (I := I) g T)
        = inner0S (I := I) g x 2 T (ahlforsOperator (I := I) g T) := by
      rw [inner0S_swapSlots_left, swap_ahlfors]
    rw [hswap]
    ring
  have hmet : inner0S (I := I) g x 2 (metricTensor0S (I := I) g x)
      (ahlforsOperator (I := I) g T) = 0 := by
    rw [inner0S_symm' (I := I) g x 2]
    exact ahlfors_inner_metric (I := I) hdim g T
  have hzero : inner0S (I := I) g x 2 (T - ahlforsOperator (I := I) g T)
      (ahlforsOperator (I := I) g T) = 0 := by
    rw [hTsub, inner0S_add_left', inner0S_smul_left, inner0S_smul_left, hanti, hmet]
    ring
  linarith [hsplit, hzero]

private theorem reaction_pairing_eq
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (hx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g hx) T
      = 2 * inner0S (I := I) g x 2
          (covectorTensorProd0S (I := I)
            (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
            (g.inner x (cotangentSharp (I := I) g x hx)))
          (ahlforsOperator (I := I) g T) := by
  set a : TangentSpace I x →L[Real] Real :=
    g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x) with ha_def
  set bb : TangentSpace I x →L[Real] Real :=
    g.inner x (cotangentSharp (I := I) g x hx) with hb_def
  set P : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    covectorTensorProd0S (I := I) a bb with hP_def
  have hreac : oneFormReaction2D (I := I) g hx
      = P + covectorTensorProd0S (I := I) bb a
        - (bb (gradFun (I := I) g (gaussCurvature (I := I) g) x))
          • metricTensor0S (I := I) g x := rfl
  have hDeq : ahlforsOperator (I := I) g T
      = (2 : Real)⁻¹ • (T + swapSlots0S (I := I) T)
        - ((2 : Real)⁻¹ * metricTracePair0SAt (I := I) g T) • metricTensor0S (I := I) g x := by
    rw [show ahlforsOperator (I := I) g T
        = symmetricPart0S (I := I) T
          - ((Module.finrank Real E : Real)⁻¹
              * metricTracePair0SAt (I := I) g (symmetricPart0S (I := I) T))
            • metricTensor0S (I := I) g x from rfl,
      trace_symmetricPart0S, hdim,
      show symmetricPart0S (I := I) T = (2 : Real)⁻¹ • (T + swapSlots0S (I := I) T) from rfl]
    norm_num
  have hPg : inner0S (I := I) g x 2 P (metricTensor0S (I := I) g x)
      = g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x)
          (cotangentSharp (I := I) g x hx) := by
    rw [hP_def, ha_def, hb_def,
      inner0S_covectorProd_eval (I := I) g
        (gradFun (I := I) g (gaussCurvature (I := I) g) x)
        (cotangentSharp (I := I) g x hx) (metricTensor0S (I := I) g x),
      metricTensor0S_apply]
    rfl
  have hPswapT : inner0S (I := I) g x 2 P (swapSlots0S (I := I) T)
      = inner0S (I := I) g x 2 (covectorTensorProd0S (I := I) bb a) T := by
    rw [← inner0S_swapSlots_left, hP_def, swap_covectorProd]
  have hRHS : 2 * inner0S (I := I) g x 2 P (ahlforsOperator (I := I) g T)
      = inner0S (I := I) g x 2 P T
        + inner0S (I := I) g x 2 (covectorTensorProd0S (I := I) bb a) T
        - metricTracePair0SAt (I := I) g T *
            g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x)
              (cotangentSharp (I := I) g x hx) := by
    rw [hDeq, inner0S_sub_right', inner0S_smul_right, inner0S_smul_right,
      inner0S_add_right', hPswapT, hPg]
    ring
  have hLHS : inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g hx) T
      = inner0S (I := I) g x 2 P T
        + inner0S (I := I) g x 2 (covectorTensorProd0S (I := I) bb a) T
        - bb (gradFun (I := I) g (gaussCurvature (I := I) g) x)
            * metricTracePair0SAt (I := I) g T := by
    rw [hreac, inner0S_sub_left', inner0S_add_left', inner0S_smul_left]
    rw [show inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) T
        = metricTracePair0SAt (I := I) g T from rfl]
  rw [hLHS, hRHS, hb_def]
  rw [show g.inner x (cotangentSharp (I := I) g x hx)
        (gradFun (I := I) g (gaussCurvature (I := I) g) x)
      = g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x)
          (cotangentSharp (I := I) g x hx) from
    g.symm x (cotangentSharp (I := I) g x hx)
      (gradFun (I := I) g (gaussCurvature (I := I) g) x)]
  ring

private noncomputable def ahlforsCc
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) : SmoothCcTensor g 0 2 :=
  { toSection := (ahlforsSection (I := I) g nablaH).toTensorRSField (∞ : WithTop ℕ∞)
    hasCompactSupport := HasCompactSupport.of_compactSpace _ }

private theorem ahlforsCc_toSection
    (g : SmoothRiemannianMetric I M)
    (nablaH : TwoTensorSection (I := I) (M := M)) (y : M) :
    (ahlforsCc (I := I) g nablaH).toSection y
      = Tensor0SSpace.toRS0 (ahlforsSection (I := I) g nablaH y) :=
  Tensor0SField.toRS0_eq (I := I) (M := M) (∞ : WithTop ℕ∞)
    (ahlforsSection (I := I) g nablaH) y

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem covDivergence_ahlforsCc
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (b : M) :
    (covDivergence (I := I) (M := M) g 1 (ahlforsCc (I := I) g nablaH)).toSection b
      = Tensor0SSpace.toRS0 ((2 : Real)⁻¹ •
          (roughLap0STensor (I := I) g (s := 1) (nabla2H b)
            + gaussCurvature (I := I) g b • h b)) := by
  classical
  have hfr : ∀ i j : Fin (Module.finrank Real E),
      g.inner b (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b)
        = if i = j then 1 else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hli : LinearIndependent Real (fun i : Fin (Module.finrank Real E) =>
      smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro s c hsum j hj
    have happ := congrArg (fun v : TangentSpace I b =>
      g.inner b (smoothOrthoFrame (I := I) g b j b) v) hsum
    simp only at happ
    rw [map_sum] at happ
    rw [show (∑ i ∈ s, g.inner b (smoothOrthoFrame (I := I) g b j b)
          (c i • smoothOrthoFrame (I := I) g b i b))
        = ∑ i ∈ s, c i * (if j = i then (1 : Real) else 0) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hfr j i]] at happ
    rw [Finset.sum_eq_single j] at happ
    · simpa using happ
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hjs
      exact absurd hj hjs
  let gInvON : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i j => if i = j then 1 else 0
  let bas : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I b) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)
  have hbas : ∀ i, bas i = smoothOrthoFrame (I := I) g b i b := fun i => by
    simp [bas, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hinvON : MetricInverseInBasis_gen (I := I) g b bas gInvON := by
    intro i j
    constructor
    · rw [Finset.sum_eq_single i]
      · rw [hbas i, hbas j, hfr i j]
        simp [gInvON]
      · intro k _ hk
        rw [show gInvON i k = 0 from by simp [gInvON, Ne.symm hk]]
        ring
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [Finset.sum_eq_single j]
      · rw [hbas i, hbas j, hfr i j]
        simp [gInvON]
      · intro k _ hk
        rw [show gInvON k j = 0 from by simp [gInvON, hk]]
        ring
      · intro hj
        exact absurd (Finset.mem_univ j) hj
  set Bsec : Fin (Module.finrank Real E) →
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun i => smoothOrthoFrameSection (I := I) (M := M) g b i with hBsecdef
  have hBsec : ∀ i, Bsec i b = bas i := by
    intro i
    rw [hbas i]
    rfl
  have hdiv : ∀ w : TangentSpace I b,
      (2 : Real) * (∑ i, ∑ j, gInvON i j *
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) b
            (vec2 (I := I) (bas j) w))
        = roughLap0STensor (I := I) g (s := 1) (nabla2H b) (fun _ : Fin 1 => w)
          + metricRicciAt (I := I) (M := M) g b
              (vec2 (I := I) (cotangentSharp (I := I) g b (h b)) w) :=
    fun w => ahlfors_divergence_sum (I := I) g h nablaH nabla2H hRealizes2
      bas gInvON hinvON Bsec hBsec w
  have hdiag : ∀ w : TangentSpace I b,
      (∑ i, ∑ j, gInvON i j *
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) b
            (vec2 (I := I) (bas j) w))
        = ∑ i, nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) b
            (vec2 (I := I) (bas i) w) := by
    intro w
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [gInvON]
    · intro k _ hk
      rw [show gInvON i k = 0 from by simp [gInvON, Ne.symm hk]]
      ring
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [covDivergence_toSection_apply (I := I) (M := M) g 1 (ahlforsCc (I := I) g nablaH) b]
  rw [show covDivergenceRaw (I := I) (M := M) g 1 (ahlforsCc (I := I) g nablaH) b
      = ∑ i : Fin (Module.finrank Real E),
          covDivergenceBilinear (I := I) (M := M) g 1 (ahlforsCc (I := I) g nablaH) b
            (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b) from rfl]
  have hsummand : ∀ i : Fin (Module.finrank Real E),
      covDivergenceBilinear (I := I) (M := M) g 1 (ahlforsCc (I := I) g nablaH) b
          (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)
        = Tensor0SSpace.toRS0 (tensor0S_curry (𝕜 := Real) (I := I) 1 b
            (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
              (fun y : M => ahlforsSection (I := I) g nablaH y) b
              (smoothOrthoFrame (I := I) g b i b))
            (smoothOrthoFrame (I := I) g b i b)) := by
    intro i
    have hMD : MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
          (smoothOrthoFrame (I := I) g b i z)) b :=
      (smoothOrthoFrame_smooth (I := I) g b i).contMDiffAt.mdifferentiableAt (by simp)
    rw [codiffPsi_apply (I := I) (M := M) g 1 (ahlforsCc (I := I) g nablaH) b hMD hMD]
    have hRS : (TensorRSNabla.tensorRSCovariantDerivative I M 0 2
          (LeviCivita (I := I) g)).toFun
          (fun z : M => (ahlforsCc (I := I) g nablaH).toSection z) b
          (smoothOrthoFrame (I := I) g b i b)
        = Tensor0SSpace.toRS0
            (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
              (fun y : M => ahlforsSection (I := I) g nablaH y) b
              (smoothOrthoFrame (I := I) g b i b)) := by
      exact nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) g)
        (ahlforsSection (I := I) g nablaH) b (smoothOrthoFrame (I := I) g b i b)
    rw [hRS, contract_covariant_toRS0 (I := I) (smoothOrthoFrame (I := I) g b i b) _]
  rw [Finset.sum_congr rfl (fun i _ => hsummand i), ← toRS0_sum]
  congr 1
  ext v
  rw [tensor0S_sum_apply']
  have hstep : ∀ i : Fin (Module.finrank Real E),
      (tensor0S_curry (𝕜 := Real) (I := I) 1 b
          (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
            (fun y : M => ahlforsSection (I := I) g nablaH y) b
            (smoothOrthoFrame (I := I) g b i b))
          (smoothOrthoFrame (I := I) g b i b)) v
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (metricCov (I := I) (M := M) g) (Bsec i) (ahlforsSection (I := I) g nablaH) b
            (vec2 (I := I) (bas i) (v 0)) := by
    intro i
    rw [curry_eval' (I := I)
      (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M => ahlforsSection (I := I) g nablaH y) b
        (smoothOrthoFrame (I := I) g b i b))
      (smoothOrthoFrame (I := I) g b i b) v]
    have hcv : (Fin.cons (smoothOrthoFrame (I := I) g b i b) v : Fin 2 → TangentSpace I b)
        = vec2 (I := I) (smoothOrthoFrame (I := I) g b i b) (v 0) := by
      funext a
      fin_cases a
      · rfl
      · show v 0 = v 0
        rfl
    rw [hcv]
    rw [show (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
          (fun y : M => ahlforsSection (I := I) g nablaH y) b
          (smoothOrthoFrame (I := I) g b i b))
          (vec2 (I := I) (smoothOrthoFrame (I := I) g b i b) (v 0))
        = Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
              (fun y : M => ahlforsSection (I := I) g nablaH y) b
              (smoothOrthoFrame (I := I) g b i b))
            (vec2 (I := I) (smoothOrthoFrame (I := I) g b i b) (v 0)) from rfl]
    rw [show smoothOrthoFrame (I := I) g b i b = Bsec i b from rfl]
    rw [tensor0SCovDeriv_two_eval (I := I) g (ahlforsSection (I := I) g nablaH)
      (Bsec i) b (Bsec i b) (v 0)]
    rw [show Bsec i b = bas i from hBsec i]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  have hfin := hdiv (v 0)
  rw [hdiag (v 0)] at hfin
  have hRic : metricRicciAt (I := I) (M := M) g b
      (vec2 (I := I) (cotangentSharp (I := I) g b (h b)) (v 0))
      = gaussCurvature (I := I) g b * h b v := by
    rw [ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim g b
      (cotangentSharp (I := I) g b (h b)) (v 0),
      cotangentSharp_inner, cotangentToDual_apply]
    congr 1
    congr 1
    funext a
    fin_cases a
    rfl
  have hRHS : (((2 : Real)⁻¹ •
      (roughLap0STensor (I := I) g (s := 1) (nabla2H b)
        + gaussCurvature (I := I) g b • h b)) : Tensor0SSpace (𝕜 := Real) (E := E)
        (H := H) (I := I) (M := M) 1 b) v
      = (2 : Real)⁻¹ * (roughLap0STensor (I := I) g (s := 1) (nabla2H b) v
          + gaussCurvature (I := I) g b * h b v) := rfl
  rw [hRHS]
  have hv0 : (fun _ : Fin 1 => v 0) = v := by
    funext a
    fin_cases a
    rfl
  rw [hv0] at hfin
  linarith [hfin, hRic]

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SCovDeriv_one_eval
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (hreal : NablaOneFormSectionRealizes (I := I) (metricCov (I := I) (M := M) g) h nablaH)
    (Vf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (w : TangentSpace I x) :
    (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
        (fun y : M => h y) x (Vf x)) (fun _ : Fin 1 => w)
      = nablaH x (vec2 (I := I) (Vf x) w) := by
  classical
  set Zf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ⟨smoothExtensionTangent (I := I) x w,
      smoothExtensionTangent_contMDiff (I := I) x w⟩ with hZfdef
  have hZf : Zf x = w := smoothExtensionTangent_eq (I := I) x w
  have hh1 : TensorSectionMDiffAt (I := I) 1 (fun y : M => h y) x :=
    h.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 0
    (fun y : M => h y) hh1 Zf (Vf x) (fun i : Fin 0 => i.elim0)
  have hd0 : Tensor0SSpace.toModel
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => curriedSection I M (fun z : M => h z) y (Zf y)) x (Vf x))
      (fun i : Fin 0 => i.elim0)
      = extDerivFun (I := I)
          (scalarFn I M (fun y : M => curriedSection I M (fun z : M => h z) y (Zf y)))
          x (Vf x) := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g
      (fun y : M => curriedSection I M (fun z : M => h z) y (Zf y)) x (Vf x)]
    rfl
  have hsc : scalarFn I M (fun y : M => curriedSection I M (fun z : M => h z) y (Zf y))
      = fun p : M => h p (fun _ : Fin 1 => Zf p) := by
    funext p
    rw [scalarFn_eq_apply_zero]
    have h1 : curriedSection I M (fun z : M => h z) p (Zf p) (0 : Fin 0 → TangentSpace I p)
        = h p (Fin.cons (Zf p) 0) := curry_eval' (I := I) (h p) (Zf p) 0
    rw [h1]
    congr 1
    funext a
    fin_cases a
    rfl
  have hkosz := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_one_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (metricCov (I := I) (M := M) g) Vf Zf h x
  have hreal_x := hreal x Vf (Zf x)
  have hcons : (Fin.cons (Zf x) (fun i : Fin 0 => i.elim0) : Fin 1 → TangentSpace I x)
      = fun _ : Fin 1 => Zf x := by
    funext i
    fin_cases i
    rfl
  have hLHS : (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
        (fun y : M => h y) x (Vf x)) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
            (fun y : M => h y) x (Vf x)) (Fin.cons (Zf x) (fun i : Fin 0 => i.elim0)) := by
    rw [toModel_apply0S, hcons, hZf]
  rw [hLHS, hpeel, hd0, hsc]
  have hterm2 : Tensor0SSpace.toModel (h x)
      (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Zf y) x (Vf x))
        (fun i : Fin 0 => i.elim0))
      = h x (fun _ : Fin 1 =>
          (metricCov (I := I) (M := M) g) (fun y : M => Zf y) x (Vf x)) := by
    rw [toModel_apply0S]
    congr 1
    funext a
    fin_cases a
    rfl
  rw [hterm2]
  rw [show nablaH x (vec2 (I := I) (Vf x) w)
      = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
          (metricCov (I := I) (M := M) g) Vf h x (fun _ : Fin 1 => Zf x) from by
    rw [show (fun _ : Fin 1 => Zf x) = (fun _ : Fin 1 => w) from by rw [hZf]]
    rw [show vec2 (I := I) (Vf x) w = vec2 (I := I) (Vf x) ((fun _ : Fin 1 => w) 0) from rfl]
    exact hreal x Vf w]
  rw [hkosz]

set_option backward.isDefEq.respectTransparency false in
private theorem lifted_oneForm_eq
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) (y : M) :
    liftedTensorSection (I := I) (M := M) g 0 1
        ((h : OneFormSection (I := I) (M := M)).toTensorRSField (∞ : WithTop ℕ∞)) y
      = h y := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  show Tensor0SSpace.toModel
      (liftedTensorSection (I := I) (M := M) g 0 1
        (h.toTensorRSField (∞ : WithTop ℕ∞)) y) m
    = Tensor0SSpace.toModel (h y) m
  rw [toModel_liftedTensorSection]
  rw [show TensorRSSpace.toModel
      ((h.toTensorRSField (∞ : WithTop ℕ∞)) y)
      = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (h y)) from
    congrArg TensorRSSpace.toModel (Tensor0SField.toRS0_eq (I := I) (M := M) _ h y)]
  rw [lower_toRS0 (I := I) (M := M) g 1 y (h y)]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [toModel_apply0S, toModel_apply0S]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem prepend_toSection_eq
    (g : SmoothRiemannianMetric I M)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (h : OneFormSection (I := I) (M := M))
    (W : SmoothCcTensor g 0 1)
    (hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h y))
    (x : M) :
    (TensorSpectral.prependCovGradSlot (I := I) (M := M) g 0 1
        ⟨gaussCurvature (I := I) g, hK⟩ W).toSection x
      = Tensor0SSpace.toRS0
          (covectorTensorProd0S (I := I)
            (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
            (g.inner x (cotangentSharp (I := I) g x (h x)))) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from
        (TensorSpectral.prependCovGradSlot (I := I) (M := M) g 0 1
          ⟨gaussCurvature (I := I) g, hK⟩ W).toSection x) D) m
      = Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from
            (extDerivFun (I := I)
                ((⟨gaussCurvature (I := I) g, hK⟩ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x (m 0))
              • W.toSection x) D)
          (Matrix.vecTail m) from
    TensorSpectral.prependCovGradSlot_toSection_apply_eval (I := I) (M := M) g 0 1
      ⟨gaussCurvature (I := I) g, hK⟩ W x D m]
  rw [show ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from
      (extDerivFun (I := I)
          ((⟨gaussCurvature (I := I) g, hK⟩ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x (m 0))
        • W.toSection x) D)
      = (extDerivFun (I := I) (gaussCurvature (I := I) g) x (m 0))
          • ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from W.toSection x) D)
      from rfl]
  rw [show (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from W.toSection x) D
      = (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from
          Tensor0SSpace.toRS0 (h x)) D from by rw [hW x]]
  rw [show (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from
      Tensor0SSpace.toRS0 (h x)) D = tensor0SSpace_evalScalar x D • h x from rfl]
  rw [show (Tensor0SSpace.toRS0
      (covectorTensorProd0S (I := I)
        (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
        (g.inner x (cotangentSharp (I := I) g x (h x))))) D
      = tensor0SSpace_evalScalar x D •
          covectorTensorProd0S (I := I)
            (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
            (g.inner x (cotangentSharp (I := I) g x (h x))) from rfl]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [toModel_apply0S, toModel_apply0S, covectorTensorProd0S_apply]
  rw [show g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x) (m 0)
      = extDerivFun (I := I) (gaussCurvature (I := I) g) x (m 0) from by
    rw [show extDerivFun (I := I) (gaussCurvature (I := I) g) x (m 0)
        = mfderiv I 𝓘(Real, Real) (gaussCurvature (I := I) g) x (m 0) from rfl,
      inner_gradFun]]
  rw [show g.inner x (cotangentSharp (I := I) g x (h x)) (m 1)
      = h x (fun _ : Fin 1 => m 1) from by
    rw [cotangentSharp_inner, cotangentToDual_apply]]
  rw [show (Matrix.vecTail m : Fin 1 → TangentSpace I x) = fun _ : Fin 1 => m 1 from by
    funext i
    fin_cases i
    rfl]
  simp only [smul_eq_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
private theorem curvatureEnergy_masterIBP
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x)) :
    (2 : Real) * (∫ x, gaussCurvature (I := I) g x *
            inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, gaussCurvature (I := I) g x ^ 2 * normSq0S (I := I) g x 1 (h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (2 : Real) * (∫ x, gaussCurvature (I := I) g x *
            normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
            normSq0S (I := I) g x 1 (h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = 0 := by
  classical
  set W : SmoothCcTensor g 0 1 :=
    { toSection := h.toTensorRSField (∞ : WithTop ℕ∞)
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h y) := fun y =>
    Tensor0SField.toRS0_eq (I := I) (M := M) (∞ : WithTop ℕ∞) h y
  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨gaussCurvature (I := I) g, hK⟩ with hζ_def
  set GW : SmoothCcTensor g 0 (1 + 1) := TensorSpectral.covGrad (I := I) (M := M) g 0 1 W
    with hGW_def
  set LW : SmoothCcTensor g 0 1 := rawTensorConnLapSmooth (I := I) g 0 1 W with hLW_def
  set KW : SmoothCcTensor g 0 1 := TensorSpectral.scalarSmul (I := I) (M := M) g 0 1 ζ W
    with hKW_def
  set SGW : SmoothCcTensor g 0 (1 + 1) :=
    TensorSpectral.scalarSmul (I := I) (M := M) g 0 (1 + 1) ζ GW with hSGW_def
  set PP : SmoothCcTensor g 0 (1 + 1) :=
    TensorSpectral.prependCovGradSlot (I := I) (M := M) g 0 1 ζ W with hPP_def
  set DW : SmoothCcTensor g 0 2 := ahlforsCc (I := I) g nablaH with hDW_def
  set dKT : (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    fun x => covectorTensorProd0S (I := I)
      (g.inner x (gradFun (I := I) g (gaussCurvature (I := I) g) x))
      (g.inner x (cotangentSharp (I := I) g x (h x))) with hdKT_def
  have hB1 : ∀ x : M, GW.toFun x = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH x)) :=
    fun x => (oneFormWrap_bridge (I := I) g h nablaH nabla2H hRealizes2 W hW x).1
  have hB2 : ∀ x : M, LW.toFun x =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0 (roughLap0STensor (I := I) g (s := 1) (nabla2H x))) :=
    fun x => (oneFormWrap_bridge (I := I) g h nablaH nabla2H hRealizes2 W hW x).2
  have hDWs : ∀ y : M, DW.toSection y
      = Tensor0SSpace.toRS0 (ahlforsSection (I := I) g nablaH y) :=
    ahlforsCc_toSection (I := I) g nablaH
  have hDhval : ∀ y : M, ahlforsSection (I := I) g nablaH y
      = ahlforsOperator (I := I) g (nablaH y) :=
    fun y => ahlforsSection_apply (I := I) hdim g nablaH y
  have hPPs : ∀ x : M, PP.toSection x = Tensor0SSpace.toRS0 (dKT x) :=
    prepend_toSection_eq (I := I) g hK h W hW
  have hDIVs : ∀ b : M,
      (covDivergence (I := I) (M := M) g 1 DW).toSection b
        = Tensor0SSpace.toRS0 ((2 : Real)⁻¹ •
            (roughLap0STensor (I := I) g (s := 1) (nabla2H b)
              + gaussCurvature (I := I) g b • h b)) :=
    covDivergence_ahlforsCc (I := I) hdim g h nablaH nabla2H hRealizes2
  have hKWs : ∀ x : M, TensorRSSpace.toModel (KW.toSection x)
      = gaussCurvature (I := I) g x • TensorRSSpace.toModel (Tensor0SSpace.toRS0 (h x)) := by
    intro x
    rw [hKW_def, TensorSpectral.scalarSmul_toSection_apply, TensorRSSpace.toModel_smul, hW x]
    rfl
  have hSGWs : ∀ x : M, TensorRSSpace.toModel (SGW.toSection x)
      = gaussCurvature (I := I) g x • GW.toFun x := by
    intro x
    rw [hSGW_def, TensorSpectral.scalarSmul_toSection_apply, TensorRSSpace.toModel_smul]
    rfl
  have hcovKW : ∀ x : M, (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun x
      = SGW.toFun x + PP.toFun x := by
    intro x
    have h0 := TensorSpectral.prependCovGradSlot_toSection (I := I) (M := M) g 0 1 ζ W
    have h1 : PP.toSection x
        = (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toSection x
          - SGW.toSection x := by
      rw [hPP_def]
      rw [show (TensorSpectral.prependCovGradSlot (I := I) (M := M) g 0 1 ζ W).toSection
          = (TensorSpectral.covGrad (I := I) (M := M) g 0 1
              (TensorSpectral.scalarSmul (I := I) (M := M) g 0 1 ζ W)).toSection
            - (TensorSpectral.scalarSmul (I := I) (M := M) g 0 (1 + 1) ζ
              (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W)).toSection from h0]
      rfl
    have h2 : (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toSection x
        = SGW.toSection x + PP.toSection x := by
      rw [h1]
      abel
    rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
      h2, TensorRSSpace.toModel_add]
  have hf1 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (SGW.toFun x)
      = gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x) := by
    intro x
    rw [show SGW.toFun x = TensorRSSpace.toModel (SGW.toSection x) from rfl, hSGWs x,
      tensorInnerPointwise_smul_right]
    congr 1
    rw [hB1 x, ← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hf2 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (PP.toFun x)
      = inner0S (I := I) g x 2 (nablaH x) (dKT x) := by
    intro x
    rw [hB1 x, show PP.toFun x = TensorRSSpace.toModel (PP.toSection x) from rfl, hPPs x,
      inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
  have hf3 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 1 x
        (LW.toFun x) (KW.toFun x)
      = gaussCurvature (I := I) g x *
          inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x) := by
    intro x
    rw [show KW.toFun x = TensorRSSpace.toModel (KW.toSection x) from rfl, hKWs x,
      tensorInnerPointwise_smul_right]
    congr 1
    rw [hB2 x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
  have hf4 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (SGW.toFun x) (DW.toFun x)
      = gaussCurvature (I := I) g x *
          normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x)) := by
    intro x
    rw [show SGW.toFun x = TensorRSSpace.toModel (SGW.toSection x) from rfl, hSGWs x,
      tensorInnerPointwise_smul_left]
    congr 1
    rw [hB1 x, show DW.toFun x = TensorRSSpace.toModel (DW.toSection x) from rfl, hDWs x,
      hDhval x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
    exact inner_ahlfors_self (I := I) hdim g (nablaH x)
  have hf5 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (PP.toFun x) (DW.toFun x)
      = inner0S (I := I) g x 2 (dKT x) (ahlforsOperator (I := I) g (nablaH x)) := by
    intro x
    rw [show PP.toFun x = TensorRSSpace.toModel (PP.toSection x) from rfl, hPPs x,
      show DW.toFun x = TensorRSSpace.toModel (DW.toSection x) from rfl, hDWs x,
      hDhval x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
  have hf6 : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 1 x
        (KW.toFun x) ((covDivergence (I := I) (M := M) g 1 DW).toFun x)
      = (2 : Real)⁻¹ * (gaussCurvature (I := I) g x *
            inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
          + gaussCurvature (I := I) g x ^ 2 * normSq0S (I := I) g x 1 (h x)) := by
    intro x
    rw [show KW.toFun x = TensorRSSpace.toModel (KW.toSection x) from rfl, hKWs x,
      show (covDivergence (I := I) (M := M) g 1 DW).toFun x
        = TensorRSSpace.toModel ((covDivergence (I := I) (M := M) g 1 DW).toSection x)
        from rfl, hDIVs x,
      tensorInnerPointwise_smul_left, inner_toRS0,
      ← inner0S_eq_covariantTensorInnerPointwise]
    rw [show inner0S (I := I) g x 1 (h x)
          ((2 : Real)⁻¹ • (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
            + gaussCurvature (I := I) g x • h x))
        = (2 : Real)⁻¹ * (inner0S (I := I) g x 1 (h x)
              (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
            + gaussCurvature (I := I) g x * inner0S (I := I) g x 1 (h x) (h x)) from by
      rw [inner0S_smul_right, inner0S_add_right', inner0S_smul_right]]
    rw [show inner0S (I := I) g x 1 (h x) (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
        = inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x) from
      inner0S_symm' (I := I) g x 1 _ _]
    rw [show inner0S (I := I) g x 1 (h x) (h x) = normSq0S (I := I) g x 1 (h x) from
      (normSq0S_eq_inner (I := I) g x 1 (h x)).symm]
    ring
  have int_f1 : Integrable (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
      (GW.toFun x) (SGW.toFun x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GW SGW
  have int_f2 : Integrable (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
      (GW.toFun x) (PP.toFun x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GW PP
  have int_f4 : Integrable (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
      (SGW.toFun x) (DW.toFun x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) SGW DW
  have int_f5 : Integrable (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
      (PP.toFun x) (DW.toFun x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) PP DW
  have hI1 : (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (SGW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (GW.toFun x) (PP.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = - ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
          (LW.toFun x) (KW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hGreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g 1 W KW
    have hLHS : tensorL2Inner (I := I) (M := M) g 0 (1 + 1)
        (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun
        (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun
        = (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            (GW.toFun x) (SGW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            (GW.toFun x) (PP.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      show (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x)
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = _
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        rw [show (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x
            = GW.toFun x from rfl, hcovKW x, tensorInnerPointwise_add_right]))]
      exact MeasureTheory.integral_add int_f1 int_f2
    have hRHS : tensorL2Inner (I := I) (M := M) g 0 1
        (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun KW.toFun
        = ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
            (LW.toFun x) (KW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl
    rw [← hLHS, ← hRHS]
    exact hGreen
  have hI2 : (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (SGW.toFun x) (DW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        (PP.toFun x) (DW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = - ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
          (KW.toFun x) ((covDivergence (I := I) (M := M) g 1 DW).toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hIBP := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g 1 KW DW
    have hLHS : tensorL2Inner (I := I) (M := M) g 0 (1 + 1)
        (TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun DW.toFun
        = (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            (SGW.toFun x) (DW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            (PP.toFun x) (DW.toFun x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      show (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
          ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 KW).toFun x) (DW.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = _
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        rw [hcovKW x, tensorInnerPointwise_add_left]))]
      exact MeasureTheory.integral_add int_f4 int_f5
    have hRHS : tensorL2Inner (I := I) (M := M) g 0 1
        KW.toFun (covDivergence (I := I) (M := M) g 1 DW).toFun
        = ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
            (KW.toFun x) ((covDivergence (I := I) (M := M) g 1 DW).toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl
    rw [← hLHS, ← hRHS]
    exact hIBP
  set VK : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hK with hVK_def
  have hWS := tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
    (h.toTensorRSField (∞ : WithTop ℕ∞)) (h.toTensorRSField (∞ : WithTop ℕ∞))
  have hT1eval : ∀ x : M,
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
      = inner0S (I := I) g x 2 (nablaH x) (dKT x) := by
    intro x
    have hlift : liftedTensorSection (I := I) (M := M) g 0 1
        (h.toTensorRSField (∞ : WithTop ℕ∞)) x = h x := lifted_oneForm_eq (I := I) g h x
    have hlow : loweredCovDerivAt (I := I) (M := M) g 0 1
        (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)
        = tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
            (fun y : M => h y) x (VK x) := by
      rw [loweredCovDerivAt_def]
      rw [show (liftedTensorSection (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)))
          = (fun y : M => h y) from funext (fun y => lifted_oneForm_eq (I := I) g h y)]
    rw [hlift, hlow]
    rw [show covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
          (fun y : M => h y) x (VK x)))
        (Tensor0SSpace.toModel (h x))
        = inner0S (I := I) g x 1
            (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
              (fun y : M => h y) x (VK x)) (h x) from
      (inner0S_eq_covariantTensorInnerPointwise (I := I) g x 1 _ _).symm]
    rw [inner0S_one_eq_eval_sharp_right (I := I) g x _ (h x), cotangentToDual_apply_gen,
      cotangentSharp_gen_eq (I := I) g x (h x)]
    rw [tensor0SCovDeriv_one_eval (I := I) g h nablaH hRealizes1 VK x
      (cotangentSharp (I := I) g x (h x))]
    rw [show VK x = gradFun (I := I) g (gaussCurvature (I := I) g) x from rfl]
    rw [show inner0S (I := I) g x 2 (nablaH x) (dKT x)
        = inner0S (I := I) g x 2 (dKT x) (nablaH x) from
      inner0S_symm' (I := I) g x 2 _ _]
    rw [hdKT_def]
    rw [inner0S_covectorProd_eval (I := I) g
      (gradFun (I := I) g (gaussCurvature (I := I) g) x)
      (cotangentSharp (I := I) g x (h x)) (nablaH x)]
  have hT2eval : ∀ x : M,
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
      = inner0S (I := I) g x 2 (nablaH x) (dKT x) := by
    intro x
    rw [show covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
        = inner0S (I := I) g x 1
            (liftedTensorSection (I := I) (M := M) g 0 1
              (h.toTensorRSField (∞ : WithTop ℕ∞)) x)
            (loweredCovDerivAt (I := I) (M := M) g 0 1
              (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)) from
      (inner0S_eq_covariantTensorInnerPointwise (I := I) g x 1 _ _).symm]
    rw [inner0S_symm' (I := I) g x 1 _ _]
    rw [show inner0S (I := I) g x 1
        (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x))
        (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x)
        = covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
            (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
              (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
            (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
              (h.toTensorRSField (∞ : WithTop ℕ∞)) x)) from
      inner0S_eq_covariantTensorInnerPointwise (I := I) g x 1 _ _]
    exact hT1eval x
  have hABcont : Continuous (fun x : M =>
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
      + covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))) :=
    ((tangentSectionAction_contMDiff (I := I) VK hWS).continuous).congr
      (fun x => tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 1
        (h.toTensorRSField (∞ : WithTop ℕ∞)) (h.toTensorRSField (∞ : WithTop ℕ∞)) VK x)
  have hAcont : Continuous (fun x : M =>
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))) := by
    refine (hABcont.const_mul (2 : Real)⁻¹).congr (fun x => ?_)
    rw [hT1eval x, hT2eval x]
    ring
  have hBcont : Continuous (fun x : M =>
      covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
        (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))) := by
    refine hAcont.congr (fun x => ?_)
    rw [hT1eval x, hT2eval x]
  have hAint := integrable_of_continuous_compactSpace (I := I) (M := M) g hAcont
  have hBint := integrable_of_continuous_compactSpace (I := I) (M := M) g hBcont
  have hIBP3 := integral_tensorInner_covDeriv_integrationByParts (I := I) (M := M) g 0 1
    (h.toTensorRSField (∞ : WithTop ℕ∞)) (h.toTensorRSField (∞ : WithTop ℕ∞)) VK
    hWS hAint hBint
  have hnsq : ∀ x : M, tensorInnerScalar (I := I) (M := M) g 0 1
      (h.toTensorRSField (∞ : WithTop ℕ∞)) (h.toTensorRSField (∞ : WithTop ℕ∞)) x
      = normSq0S (I := I) g x 1 (h x) := by
    intro x
    rw [tensorInnerScalar_apply]
    rw [show TensorRSSpace.toModel ((h.toTensorRSField (∞ : WithTop ℕ∞)) x)
        = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (h x)) from
      congrArg TensorRSSpace.toModel (Tensor0SField.toRS0_eq (I := I) (M := M) _ h x)]
    rw [← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hdivVK : ∀ x : M, divergence_g (I := I) g VK x
      = - formLaplacianScalar (I := I) g hK x := by
    intro x
    rw [show formLaplacianScalar (I := I) g hK x
        = - divergence_g (I := I) g (grad_g (I := I) g hK) x from rfl]
    ring
  have hR2 : (2 : Real) * (∫ x,
        covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
          (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
          (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, formLaplacianScalar (I := I) g hK x * normSq0S (I := I) g x 1 (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hBA : (∫ x,
        covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
          (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
          (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = ∫ x,
          covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
            (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
              (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
            (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
              (h.toTensorRSField (∞ : WithTop ℕ∞)) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        beta_reduce
        rw [hT2eval x, hT1eval x]))
    have hdivint : (∫ x, tensorInnerScalar (I := I) (M := M) g 0 1
          (h.toTensorRSField (∞ : WithTop ℕ∞)) (h.toTensorRSField (∞ : WithTop ℕ∞)) x
          * divergence_g (I := I) g VK x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = - ∫ x, formLaplacianScalar (I := I) g hK x * normSq0S (I := I) g x 1 (h x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← MeasureTheory.integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      rw [hnsq x, hdivVK x]
      ring
    rw [hBA, hdivint] at hIBP3
    linarith [hIBP3]
  have hf2A : ∀ x : M, inner0S (I := I) g x 2 (nablaH x) (dKT x)
      = covariantTensorInnerPointwise (I := I) (M := M) (0 + 1) g x
          (Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)) x (VK x)))
          (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g 0 1
            (h.toTensorRSField (∞ : WithTop ℕ∞)) x)) :=
    fun x => (hT1eval x).symm
  have hcontA1 : Continuous (fun x : M => gaussCurvature (I := I) g x *
      inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)) := by
    refine (hK.continuous.mul (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
      LW.toSection W.toSection).continuous).congr (fun x => ?_)
    rw [Pi.mul_apply]
    congr 1
    rw [tensorInnerScalar_apply]
    rw [show TensorRSSpace.toModel (LW.toSection x) = LW.toFun x from rfl, hB2 x]
    rw [show TensorRSSpace.toModel (W.toSection x)
        = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (h x)) from
      congrArg TensorRSSpace.toModel (hW x)]
    rw [inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
  have hcontA2 : Continuous (fun x : M => gaussCurvature (I := I) g x ^ 2 *
      normSq0S (I := I) g x 1 (h x)) := by
    refine ((hK.continuous.pow 2).mul (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
      (h.toTensorRSField (∞ : WithTop ℕ∞))
      (h.toTensorRSField (∞ : WithTop ℕ∞))).continuous).congr (fun x => ?_)
    rw [Pi.mul_apply, hnsq x]
  have intA1 := integrable_of_continuous_compactSpace (I := I) (M := M) g hcontA1
  have intA2 := integrable_of_continuous_compactSpace (I := I) (M := M) g hcontA2
  have hI1' : (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, inner0S (I := I) g x 2 (nablaH x) (dKT x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = - ∫ x, gaussCurvature (I := I) g x *
          inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have e1 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (Filter.Eventually.of_forall hf1)
    have e2 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (Filter.Eventually.of_forall hf2)
    have e3 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (Filter.Eventually.of_forall hf3)
    linarith [hI1, e1, e2, e3]
  have hI2' : (∫ x, gaussCurvature (I := I) g x *
        normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, inner0S (I := I) g x 2 (dKT x) (ahlforsOperator (I := I) g (nablaH x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = - ((2 : Real)⁻¹ * (∫ x, gaussCurvature (I := I) g x *
            inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (2 : Real)⁻¹ * (∫ x, gaussCurvature (I := I) g x ^ 2 *
            normSq0S (I := I) g x 1 (h x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))) := by
    have e4 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (Filter.Eventually.of_forall hf4)
    have e5 := integral_congr_ae (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (Filter.Eventually.of_forall hf5)
    have e6 : (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
          (KW.toFun x) ((covDivergence (I := I) (M := M) g 1 DW).toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = (2 : Real)⁻¹ * (∫ x, gaussCurvature (I := I) g x *
              inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (2 : Real)⁻¹ * (∫ x, gaussCurvature (I := I) g x ^ 2 *
              normSq0S (I := I) g x 1 (h x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hf6)]
      rw [show (fun x : M => (2 : Real)⁻¹ * (gaussCurvature (I := I) g x *
            inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x)
          + gaussCurvature (I := I) g x ^ 2 * normSq0S (I := I) g x 1 (h x)))
          = (fun x : M => (2 : Real)⁻¹ * (gaussCurvature (I := I) g x *
              inner0S (I := I) g x 1 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)) (h x))
            + (2 : Real)⁻¹ * (gaussCurvature (I := I) g x ^ 2 *
              normSq0S (I := I) g x 1 (h x))) from by
        funext x
        ring]
      rw [MeasureTheory.integral_add (intA1.const_mul (2 : Real)⁻¹)
        (intA2.const_mul (2 : Real)⁻¹),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    linarith [hI2, e4, e5, e6]
  have hA4 : (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = 2 * ∫ x, inner0S (I := I) g x 2 (dKT x) (ahlforsOperator (I := I) g (nablaH x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [reaction_pairing_eq (I := I) hdim g (h x) (nablaH x), hdKT_def]
  have hA6 : (∫ x, formLaplacianScalar (I := I) g hK x * normSq0S (I := I) g x 1 (h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = 2 * ∫ x, inner0S (I := I) g x 2 (nablaH x) (dKT x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← hR2]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hf2A x).symm))
  linarith [hI1', hI2', hA4, hA6]

theorem curvatureEnergyIdentity_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x)) :
    (∫ x, normSq0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      =
      (∫ x, normSq0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
              + gaussCurvature (I := I) g x • (h x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        + (2 : Real) * (∫ x, gaussCurvature (I := I) g x *
              normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        + (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
              normSq0S (I := I) g x 1 (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hexp := roughLapPlusK_normSq_expand hdim g h nablaH nabla2H hK hRealizes1 hRealizes2
  have hmaster := curvatureEnergy_masterIBP hdim g h nablaH nabla2H hK hRealizes1 hRealizes2
  linarith [hexp, hmaster]


theorem curvatureEnergyInequality_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hKpos : ∀ x : M, 0 ≤ gaussCurvature (I := I) g x) :
    (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
            normSq0S (I := I) g x 1 (h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      ≤
      (∫ x, normSq0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hid := curvatureEnergyIdentity_twoDim hdim g h nablaH nabla2H hK hRealizes1 hRealizes2
  have h1 : (0 : Real) ≤ ∫ x, normSq0S (I := I) g x 1
      (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • (h x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_nonneg (fun y => normSq0S_nonneg (I := I) g y 1 _)
  have h2 : (0 : Real) ≤ ∫ x, gaussCurvature (I := I) g x *
      normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_nonneg (fun y => mul_nonneg (hKpos y) (normSq0S_nonneg (I := I) g y 2 _))
  linarith [hid, h1, h2]


set_option backward.isDefEq.respectTransparency false in
private theorem toRS0_add {s : ℕ} {z : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toRS0 (A + B) = Tensor0SSpace.toRS0 A + Tensor0SSpace.toRS0 B := by
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SSpace.toRS0_apply, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toRS0_apply, Tensor0SSpace.toRS0_apply, smul_add]

set_option backward.isDefEq.respectTransparency false in
private theorem toRS0_smul {s : ℕ} {z : M} (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toRS0 (c • A) = c • Tensor0SSpace.toRS0 A := by
  apply ContinuousLinearMap.ext
  intro D
  rw [Tensor0SSpace.toRS0_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toRS0_apply, smul_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem toRS0_zero {s : ℕ} {z : M} :
    Tensor0SSpace.toRS0 (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z)
      = 0 := by
  apply ContinuousLinearMap.ext
  intro D
  rw [Tensor0SSpace.toRS0_apply, smul_zero]
  rfl

private theorem normSq0S_zero'
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    normSq0S (I := I) g x s
      (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) = 0 := by
  rw [normSq0S_eq_inner,
    show (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
      = (0 : Real) • (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
      from (zero_smul _ _).symm,
    inner0S_smul_left]
  ring

private theorem eq_zero_of_integral_zero_of_continuous_nonneg
    (g : SmoothRiemannianMetric I M) {f : M → Real}
    (hcont : Continuous f) (hnonneg : ∀ y : M, 0 ≤ f y)
    (hzero : (∫ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0)
    (x : M) : f x = 0 := by
  by_contra hne
  haveI : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hint : Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hcont
  have hpos : 0 < ∫ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [integral_pos_iff_support_of_nonneg hnonneg hint]
    refine (hcont.isOpen_support).measure_pos _ ⟨x, ?_⟩
    rw [Function.mem_support]
    exact hne
  linarith [hpos, hzero]

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
private theorem equalityEnergyZero_iff_ahlforsZero
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hKpos : ∀ x : M, 0 ≤ gaussCurvature (I := I) g x) :
    ((∫ x, normSq0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
              + gaussCurvature (I := I) g x • (h x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0
        ∧ (∫ x, gaussCurvature (I := I) g x *
              normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0)
      ↔ (∀ x : M, ahlforsOperator (I := I) g (nablaH x) = 0) := by
  classical
  set W : SmoothCcTensor g 0 1 :=
    { toSection := h.toTensorRSField (∞ : WithTop ℕ∞)
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW_def
  have hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (h y) := fun y =>
    Tensor0SField.toRS0_eq (I := I) (M := M) (∞ : WithTop ℕ∞) h y
  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨gaussCurvature (I := I) g, hK⟩ with hζ_def
  set LW : SmoothCcTensor g 0 1 := rawTensorConnLapSmooth (I := I) g 0 1 W with hLW_def
  set KW : SmoothCcTensor g 0 1 := TensorSpectral.scalarSmul (I := I) (M := M) g 0 1 ζ W
    with hKW_def
  set DW : SmoothCcTensor g 0 2 := ahlforsCc (I := I) g nablaH with hDW_def
  have hB1 : ∀ x : M,
      (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x
        = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaH x)) :=
    fun x => (oneFormWrap_bridge (I := I) g h nablaH nabla2H hRealizes2 W hW x).1
  have hB2 : ∀ x : M, LW.toFun x =
      TensorRSSpace.toModel
        (Tensor0SSpace.toRS0 (roughLap0STensor (I := I) g (s := 1) (nabla2H x))) :=
    fun x => (oneFormWrap_bridge (I := I) g h nablaH nabla2H hRealizes2 W hW x).2
  have hDWs : ∀ y : M, DW.toSection y
      = Tensor0SSpace.toRS0 (ahlforsSection (I := I) g nablaH y) :=
    ahlforsCc_toSection (I := I) g nablaH
  have hDhval : ∀ y : M, ahlforsSection (I := I) g nablaH y
      = ahlforsOperator (I := I) g (nablaH y) :=
    fun y => ahlforsSection_apply (I := I) hdim g nablaH y
  have hS1 : ∀ x : M, TensorRSSpace.toModel ((LW + KW).toSection x)
      = TensorRSSpace.toModel
          (Tensor0SSpace.toRS0 (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
            + gaussCurvature (I := I) g x • h x)) := by
    intro x
    rw [SmoothCcTensor.toSection_add,
      show (LW.toSection + KW.toSection) x = LW.toSection x + KW.toSection x from rfl,
      TensorRSSpace.toModel_add, toRS0_add, TensorRSSpace.toModel_add]
    congr 1
    · exact hB2 x
    · rw [hKW_def, TensorSpectral.scalarSmul_toSection_apply, TensorRSSpace.toModel_smul,
        hW x, toRS0_smul, TensorRSSpace.toModel_smul]
      rfl
  have hQ1cont : Continuous (fun x : M => normSq0S (I := I) g x 1
      (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • h x)) := by
    refine ((tensorInnerScalar_contMDiff (I := I) (M := M) g 0 1
      (LW + KW).toSection (LW + KW).toSection).continuous).congr (fun x => ?_)
    rw [tensorInnerScalar_apply, hS1 x, ← normSq0S_eq_tensorInnerPointwise_toRS0]
  have hDcont : Continuous (fun x : M => normSq0S (I := I) g x 2
      (ahlforsOperator (I := I) g (nablaH x))) := by
    refine ((tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2
      DW.toSection DW.toSection).continuous).congr (fun x => ?_)
    rw [tensorInnerScalar_apply, hDWs x, hDhval x, ← normSq0S_eq_tensorInnerPointwise_toRS0]
  constructor
  · rintro ⟨hQ1, _hQ2⟩
    have hzero1 : ∀ x : M, roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • h x = 0 := by
      intro x
      have h0 := eq_zero_of_integral_zero_of_continuous_nonneg (I := I) g hQ1cont
        (fun y => normSq0S_nonneg (I := I) g y 1 _) hQ1 x
      by_contra hne
      exact (normSq0S_pos_of_ne_zero (I := I) g x 1 _ hne).ne' h0
    have hdivzero : ∀ b : M,
        (covDivergence (I := I) (M := M) g 1 DW).toSection b = 0 := by
      intro b
      rw [covDivergence_ahlforsCc (I := I) hdim g h nablaH nabla2H hRealizes2 b,
        hzero1 b, smul_zero]
      exact toRS0_zero (I := I)
    have hIBP := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g 1 W DW
    have hRHS0 : tensorL2Inner (I := I) (M := M) g 0 1
        W.toFun (covDivergence (I := I) (M := M) g 1 DW).toFun = 0 := by
      show (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 1 x
          (W.toFun x) ((covDivergence (I := I) (M := M) g 1 DW).toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0
      rw [show (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 1 x
          (W.toFun x) ((covDivergence (I := I) (M := M) g 1 DW).toFun x))
          = fun _ : M => (0 : Real) from funext (fun x => by
        rw [show (covDivergence (I := I) (M := M) g 1 DW).toFun x
            = TensorRSSpace.toModel ((covDivergence (I := I) (M := M) g 1 DW).toSection x)
            from rfl, hdivzero x]
        rw [show TensorRSSpace.toModel
            (0 : TensorRSSpace 0 1 I x) = (0 : Real) •
              TensorRSSpace.toModel (0 : TensorRSSpace 0 1 I x) from by
          rw [zero_smul, TensorRSSpace.toModel_zero]]
        rw [tensorInnerPointwise_smul_right]
        simp)]
      simp
    have hpt : ∀ x : M, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
        ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x) (DW.toFun x)
        = normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x)) := by
      intro x
      rw [hB1 x, show DW.toFun x = TensorRSSpace.toModel (DW.toSection x) from rfl,
        hDWs x, hDhval x, inner_toRS0, ← inner0S_eq_covariantTensorInnerPointwise]
      exact inner_ahlfors_self (I := I) hdim g (nablaH x)
    have hDint0 : (∫ x, normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
      have hL : tensorL2Inner (I := I) (M := M) g 0 (1 + 1)
          (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun DW.toFun
          = ∫ x, normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        change (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (1 + 1) x
            ((TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x) (DW.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = _
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      rw [← hL, hIBP, hRHS0]
      ring
    intro x
    have h0 := eq_zero_of_integral_zero_of_continuous_nonneg (I := I) g hDcont
      (fun y => normSq0S_nonneg (I := I) g y 2 _) hDint0 x
    by_contra hne
    exact (normSq0S_pos_of_ne_zero (I := I) g x 2 _ hne).ne' h0
  · intro hz
    have hsecZero : ahlforsSection (I := I) g nablaH
        = (0 : TwoTensorSection (I := I) (M := M)) := by
      refine DFunLike.ext _ _ (fun y => ?_)
      rw [hDhval y, hz y]
      rfl
    have hzero1 : ∀ (x : M) (w : TangentSpace I x),
        roughLap0STensor (I := I) g (s := 1) (nabla2H x) (fun _ : Fin 1 => w)
          + metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) w) = 0 := by
      intro x w
      classical
      set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
        with hbasis_def
      set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
          DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
        fun i j =>
          DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
            (I := I) g x i j (extChartAt I x x) with hgInv_def
      have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
        simpa [hbasis_def, hgInv_def] using
          (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
            (I := I) g x)
      let B : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
        fun i => (ContMDiffSection.exists_eq_at_gen
          (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose
      have hB : ∀ i, B i x = basis i := fun i =>
        (ContMDiffSection.exists_eq_at_gen
          (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose_spec
      have hdiv := ahlfors_divergence_sum (I := I) g h nablaH nabla2H hRealizes2
        basis gInv hinv B hB w
      have hzsum : (∑ i, ∑ j, gInv i j *
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (metricCov (I := I) (M := M) g) (B i) (ahlforsSection (I := I) g nablaH) x
            (vec2 (I := I) (basis j) w)) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
        rw [hsecZero, nabla_zero (I := I) 2 (metricCov (I := I) (M := M) g) (B i) x]
        rw [show (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
            (vec2 (I := I) (basis j) w) = 0 from rfl]
        ring
      rw [hzsum] at hdiv
      linarith [hdiv]
    have hQ1tensor : ∀ x : M, roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • h x = 0 := by
      intro x
      ext v
      have hz1 := hzero1 x (v 0)
      have hRic : metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) (v 0))
          = gaussCurvature (I := I) g x * h x v := by
        rw [ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim g x
          (cotangentSharp (I := I) g x (h x)) (v 0),
          cotangentSharp_inner, cotangentToDual_apply]
        congr 1
        congr 1
        funext a
        fin_cases a
        rfl
      have hv0 : (fun _ : Fin 1 => v 0) = v := by
        funext a
        fin_cases a
        rfl
      rw [hv0] at hz1
      rw [show (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
            + gaussCurvature (I := I) g x • h x) v
          = roughLap0STensor (I := I) g (s := 1) (nabla2H x) v
            + gaussCurvature (I := I) g x * h x v from rfl,
        show (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) v
          = 0 from rfl]
      linarith [hz1, hRic]
    constructor
    · rw [show (fun x : M => normSq0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
            + gaussCurvature (I := I) g x • h x))
          = fun x : M => (0 : Real) from funext (fun x => by
        rw [hQ1tensor x]
        exact normSq0S_zero' (I := I) g x 1)]
      simp
    · rw [show (fun x : M => gaussCurvature (I := I) g x *
          normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x)))
          = fun x : M => (0 : Real) from funext (fun x => by
        rw [hz x]
        rw [normSq0S_zero' (I := I) g x 2]
        ring)]
      simp

theorem curvatureEnergyEquality_iff_ahlforsZero_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hKpos : ∀ x : M, 0 ≤ gaussCurvature (I := I) g x) :
    ((∫ x, normSq0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        - (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        - (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
              normSq0S (I := I) g x 1 (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)))
      ↔ (∀ x : M, ahlforsOperator (I := I) g (nablaH x) = 0) := by
  have hid := curvatureEnergyIdentity_twoDim hdim g h nablaH nabla2H hK hRealizes1 hRealizes2
  have hQ1nn : (0 : Real) ≤ ∫ x, normSq0S (I := I) g x 1
      (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • (h x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_nonneg (fun y => normSq0S_nonneg (I := I) g y 1 _)
  have hQ2nn : (0 : Real) ≤ ∫ x, gaussCurvature (I := I) g x *
      normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_nonneg (fun y => mul_nonneg (hKpos y) (normSq0S_nonneg (I := I) g y 2 _))
  refine Iff.trans ?_
    (equalityEnergyZero_iff_ahlforsZero hdim g h nablaH nabla2H hK hRealizes1 hRealizes2 hKpos)
  constructor
  · intro heq
    exact ⟨by linarith [hid, heq, hQ1nn, hQ2nn], by linarith [hid, heq, hQ1nn, hQ2nn]⟩
  · intro hz
    obtain ⟨hQ1z, hQ2z⟩ := hz
    linarith [hid, hQ1z, hQ2z]


end DifferentialGeometry.Integral.Connection
