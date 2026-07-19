import DifferentialGeometry.Geometry.Hodge.OneFormHarmonic
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


private theorem ofModel_domDomCongr_toModel_eq {r : ℕ} {x : M}
    (σ : Equiv.Perm (Fin r))
    (d : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x) :
    (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel d)) :
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x) =
      ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap Real (fun _ : Fin r => TangentSpace I x) Real
          from d) := by
  have h : ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel d) =
      Tensor0SSpace.toModel
        (ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap Real (fun _ : Fin r => TangentSpace I x) Real
            from d)) := rfl
  rw [h, Tensor0SSpace.ofModel_toModel]


def oneFormExtDerivAt
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  nablaAlpha x -
    Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel (nablaAlpha x)))


private theorem oneFormExtDerivAt_apply
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    oneFormExtDerivAt (I := I) nablaAlpha x v =
      nablaAlpha x v -
        nablaAlpha x (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) := by
  have hkey :
      (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel (nablaAlpha x)))) v =
        nablaAlpha x (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) := by
    rw [ofModel_domDomCongr_toModel_eq (I := I) (Equiv.swap (0 : Fin 2) 1) (nablaAlpha x)]
    rfl
  calc
    oneFormExtDerivAt (I := I) nablaAlpha x v
        = nablaAlpha x v -
            (Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
                (Tensor0SSpace.toModel (nablaAlpha x)))) v :=
          Tensor0SSpace.sub_apply 2 x _ _ v
    _ = nablaAlpha x v - nablaAlpha x (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) := by
          rw [hkey]


theorem oneFormIsClosed_iff_extDerivAt_eq_zero
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) :
    OneFormIsClosed (I := I) α nablaAlpha ↔
      ∀ x : M,
        oneFormExtDerivAt (I := I) nablaAlpha x =
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) := by
  constructor
  · intro hclosed x
    refine tensor0SSpace_ext 2 x (fun v => ?_)
    rw [Tensor0SSpace.zero_apply, oneFormExtDerivAt_apply, sub_eq_zero]
    have h1 : v = vec2 (I := I) (v 0) (v 1) := by
      funext i; fin_cases i <;> rfl
    have h2 : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = vec2 (I := I) (v 1) (v 0) := by
      funext i
      fin_cases i <;>
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
          Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [h2]
    conv_lhs => rw [h1]
    exact hclosed x (v 0) (v 1)
  · intro h x X Y
    have hz := h x
    have happ := congrArg
      (fun T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x =>
        T (vec2 (I := I) X Y)) hz
    simp only [Tensor0SSpace.zero_apply] at happ
    rw [oneFormExtDerivAt_apply, sub_eq_zero] at happ
    have h2 : (fun i => (vec2 (I := I) X Y) ((Equiv.swap (0 : Fin 2) 1) i)) =
        vec2 (I := I) Y X := by
      funext i
      fin_cases i <;>
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2,
          Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [h2] at happ
    exact happ


def nablaOneFormExtDerivAt
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  nabla2Alpha x -
    Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (Tensor0SSpace.toModel (nabla2Alpha x)))


private theorem nablaOneFormExtDerivAt_apply
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (x : M) (v : Fin 3 → TangentSpace I x) :
    nablaOneFormExtDerivAt (I := I) nabla2Alpha x v =
      nabla2Alpha x v -
        nabla2Alpha x (fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) := by
  have hkey :
      (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
            (Tensor0SSpace.toModel (nabla2Alpha x)))) v =
        nabla2Alpha x (fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) := by
    rw [ofModel_domDomCongr_toModel_eq (I := I) (Equiv.swap (1 : Fin 3) 2) (nabla2Alpha x)]
    rfl
  calc
    nablaOneFormExtDerivAt (I := I) nabla2Alpha x v
        = nabla2Alpha x v -
            (Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
                (Tensor0SSpace.toModel (nabla2Alpha x)))) v :=
          Tensor0SSpace.sub_apply 3 x _ _ v
    _ = nabla2Alpha x v - nabla2Alpha x (fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) := by
          rw [hkey]


private theorem differential1FormFun_neg (u : M → Real) (x : M) :
    differential1FormFun (I := I) (fun y => -(u y)) x =
      -(differential1FormFun (I := I) u x) := by
  unfold differential1FormFun
  have h1 : mfderiv I 𝓘(Real, Real) (fun y : M => -(u y)) x =
      -(mfderiv I 𝓘(Real, Real) u x) := mfderiv_neg u x
  rw [h1]
  have h2 : (-(mfderiv I 𝓘(Real, Real) u x)).toLinearMap =
      -((mfderiv I 𝓘(Real, Real) u x).toLinearMap) := rfl
  rw [h2, ← dualToCotangentLinear_apply, ← dualToCotangentLinear_apply]
  exact map_neg _ _


private theorem roughLap_apply_eq_sum
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


def oneFormHodgeLaplacianAt
    (g : SmoothRiemannianMetric I M)
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  differential1FormFun (I := I)
      (fun y : M => oneFormCodifferentialAt (I := I) g nablaAlpha y) x -
    roughLap0STensor (I := I) g (s := 1)
      (nablaOneFormExtDerivAt (I := I) nabla2Alpha x)


theorem oneFormWeitzenbockIdentity
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x
          (fun _ : Fin 1 => X) =
        -roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) := by
  classical
  haveI : IsManifold I 3 M :=
    IsManifold.of_le (by decide : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  intro x X
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
  obtain ⟨W, hW⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hmc : IsMetricCompatible_gen (I := I) (metricCov (I := I) (M := M) g) g :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hR2' : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) α nablaAlpha x (nabla2Alpha x) :=
    hRealizes2 x
  have hcomm : OneFormThirdCovDerivCommAt (I := I)
      (metricRm13 (I := I) (M := M) g) (α x) (nabla2Alpha x) :=
    oneFormThirdCovDerivCommAt_of_leviCivita (I := I) g
      (metricRm13 (I := I) (M := M) g) α nablaAlpha (α x) (nabla2Alpha x)
      (metricCurvData (I := I) (M := M) g).h_rm13 rfl hR2'
  have hSkew : Rm13MetricSkewAt (I := I) g x (metricRm13 (I := I) (M := M) g x) :=
    rm13MetricSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm13 (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g)
      (metricCurvData (I := I) (M := M) g).h_rm13
      (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have hAlpha : α x =
      dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x)
          (cotangentSharp (I := I) g x (α x))) := by
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
      (α x) basis gInv (cotangentSharp (I := I) g x (α x)) :=
    curvatureTraceOneFormEqRicVectorAt_of_metric_dual (I := I) g
      (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
      (α x) basis gInv (cotangentSharp (I := I) g x (α x)) hinv
      (metricCurvData (I := I) (M := M) g).h_ricci13 hSkew hAlpha
  have hcurv : ∀ Y : TangentSpace I x,
      -∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          gInv i j * metricRm13 (I := I) (M := M) g x (α x)
            (vec3 (I := I) (basis i) Y (basis j)) =
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I) Y (cotangentSharp (I := I) g x (α x))) := by
    intro Y
    exact hcurvV Y
  have hswap : ∀ U V : TangentSpace I x,
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
  have hterm : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      nabla2Alpha x (vec3 (I := I) X (basis i) (basis j)) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g) W nablaAlpha x
          (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    rw [← hW]
    exact (hRealizes2 x).2 W (basis i) (basis j)
  have hswapin : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      (fun k : Fin 3 =>
          (vec3 (I := I) (basis i) (basis j) X) ((Equiv.swap (1 : Fin 3) 2) k)) =
        vec3 (I := I) (basis i) X (basis j) := by
    intro i j
    funext k
    fin_cases k <;>
      simp [Equiv.swap_apply_def, vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hLHS :
      oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x (fun _ : Fin 1 => X) =
        differential1FormFun (I := I)
            (fun y : M => oneFormCodifferentialAt (I := I) g nablaAlpha y) x
            (fun _ : Fin 1 => X) -
          roughLap0STensor (I := I) g (s := 1)
            (nablaOneFormExtDerivAt (I := I) nabla2Alpha x) (fun _ : Fin 1 => X) :=
    Tensor0SSpace.sub_apply 1 x _ _ (fun _ : Fin 1 => X)
  have hA :
      differential1FormFun (I := I)
          (fun y : M => oneFormCodifferentialAt (I := I) g nablaAlpha y) x
          (fun _ : Fin 1 => X) =
        -∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) X (basis i) (basis j)) := by
    have hcodiff :
        differential1FormFun (I := I)
            (fun y : M => oneFormCodifferentialAt (I := I) g nablaAlpha y) x =
          -(differential1FormFun (I := I)
            (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x) :=
      differential1FormFun_neg (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x
    have happ :
        differential1FormFun (I := I)
            (fun y : M => oneFormCodifferentialAt (I := I) g nablaAlpha y) x
            (fun _ : Fin 1 => X) =
          (-(differential1FormFun (I := I)
            (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x))
            (fun _ : Fin 1 => X) := by
      rw [hcodiff]
    have hnegapp :
        (-(differential1FormFun (I := I)
            (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x))
            (fun _ : Fin 1 => X) =
          -(differential1FormFun (I := I)
            (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x
            (fun _ : Fin 1 => X)) :=
      Tensor0SSpace.neg_apply 1 x _ (fun _ : Fin 1 => X)
    rw [happ, hnegapp]
    congr 1
    rw [show (fun _ : Fin 1 => X) = (fun _ : Fin 1 => W x) from by funext _; exact hW.symm]
    have hd :
        differential1FormFun (I := I)
            (fun y : M => metricTracePair0SAt (I := I) g (nablaAlpha y)) x
            (fun _ : Fin 1 => W x) =
          metricTracePair0SAt (I := I) g
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
              (metricCov (I := I) (M := M) g) W nablaAlpha x) :=
      dTrace02_eq (I := I) (M := M) (metricCov (I := I) (M := M) g) g hmc nablaAlpha W x
    rw [hd, metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
        (metricCov (I := I) (M := M) g) W nablaAlpha x)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hterm i j]
  have hB :
      roughLap0STensor (I := I) g (s := 1)
          (nablaOneFormExtDerivAt (I := I) nabla2Alpha x) (fun _ : Fin 1 => X) =
        (∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) (basis j) X)) -
          (∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) X (basis j))) := by
    rw [roughLap_apply_eq_sum (I := I) g basis gInv hinv
      (nablaOneFormExtDerivAt (I := I) nabla2Alpha x) X]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nablaOneFormExtDerivAt_apply, hswapin i j, mul_sub]
  have hRL :
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) =
        ∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) (basis j) X) :=
    roughLap_apply_eq_sum (I := I) g basis gInv hinv (nabla2Alpha x) X
  have hRic :
      (∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) X (basis j))) -
          (∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) X (basis i) (basis j))) =
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) := by
    have key : ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) X (basis j)) -
            gInv i j * nabla2Alpha x (vec3 (I := I) X (basis i) (basis j)) =
          -(gInv i j * metricRm13 (I := I) (M := M) g x (α x)
            (vec3 (I := I) (basis i) X (basis j))) := by
      intro i j
      rw [← mul_sub, hcomm (basis i) X (basis j), mul_neg]
    calc
      (∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) X (basis j))) -
            (∑ i, ∑ j, gInv i j * nabla2Alpha x (vec3 (I := I) X (basis i) (basis j)))
          = ∑ i, ∑ j,
              (gInv i j * nabla2Alpha x (vec3 (I := I) (basis i) X (basis j)) -
                gInv i j * nabla2Alpha x (vec3 (I := I) X (basis i) (basis j))) := by
            simp only [Finset.sum_sub_distrib]
        _ = ∑ i, ∑ j,
              -(gInv i j * metricRm13 (I := I) (M := M) g x (α x)
                (vec3 (I := I) (basis i) X (basis j))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
        _ = -∑ i, ∑ j, gInv i j * metricRm13 (I := I) (M := M) g x (α x)
              (vec3 (I := I) (basis i) X (basis j)) := by
            simp only [Finset.sum_neg_distrib]
        _ = metricRicci (I := I) (M := M) g x
              (vec2 (I := I) X (cotangentSharp (I := I) g x (α x))) := hcurv X
        _ = metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) X (cotangentSharp (I := I) g x (α x))) := by
            rw [metricRicci_apply]
        _ = metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) :=
            hswap X (cotangentSharp (I := I) g x (α x))
  rw [hLHS, hA, hB, hRL]
  linear_combination hRic


theorem isHarmonicOneForm_hodgeLaplacianAt_eq_zero
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hHarm : IsHarmonicOneForm (I := I) g α nablaAlpha)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x
          (fun _ : Fin 1 => X) = 0 := by
  intro x X
  rw [oneFormWeitzenbockIdentity (I := I) g α nablaAlpha nabla2Alpha hRealizes2 x X]
  rw [isHarmonicOneForm_roughLap_eq_ricciSharp (I := I) g α nablaAlpha nabla2Alpha
    hHarm hRealizes2 x X]
  ring


end DifferentialGeometry.Integral.Connection
