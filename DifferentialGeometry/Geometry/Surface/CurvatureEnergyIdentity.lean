import DifferentialGeometry.Geometry.Surface.TensorTraceFree
import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Hodge.OneFormHarmonic
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization
import DifferentialGeometry.Geometry.Hodge.Codifferential
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HeatProbeEnergy

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
            (vec2 (I := I) (cotangentSharp (I := I) g x (h x)) X) :=
  sorry

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
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
  sorry

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
      = 0 :=
  sorry

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
      ↔ (∀ x : M, ahlforsOperator (I := I) g (nablaH x) = 0) :=
  sorry

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
