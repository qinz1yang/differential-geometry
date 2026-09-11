import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateIdentities
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.RicciTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.PIdentities

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def hamiltonDivPPerm : Equiv.Perm (Fin 4) where
  toFun q := if q = 0 then 0 else if q = 1 then 2 else if q = 2 then 3 else 1
  invFun q := if q = 0 then 0 else if q = 1 then 3 else if q = 2 then 1 else 2
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def hamiltonScalarHessianPerm : Equiv.Perm (Fin 4) where
  toFun q := if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else 1
  invFun q := if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else 1
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def hamiltonRicciSquarePerm : Equiv.Perm (Fin 4) where
  toFun q := if q = 0 then 2 else if q = 1 then 0 else if q = 2 then 1 else 3
  invFun q := if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 0 else 3
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def hamiltonCurvatureRicciPerm : Equiv.Perm (Fin 6) where
  toFun q :=
    if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 5 else if q = 4 then 1 else 3
  invFun q :=
    if q = 0 then 1 else if q = 1 then 4 else if q = 2 then 2 else
      if q = 3 then 5 else if q = 4 then 0 else 3
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private theorem sum_reorder_four
    {Idx : Type*} [Fintype Idx] {R : Type*} [AddCommMonoid R]
    (F : Idx -> Idx -> Idx -> Idx -> R) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      ∑ k : Idx, ∑ i : Idx, ∑ l : Idx, ∑ j : Idx, F i j k l := by
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
        ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
      rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ l : Idx, ∑ j : Idx, F i j k l := by
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]

variable [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem metricNabla2Ric_coordinateFrameAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (d a i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx
      (𝕜 := Real) E) :
    metricNabla2Ric (I := I) (M := M) (S.family.metric t) x
        (vec4
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x d x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) =
      coordNab2Ric (I := I) S x t x d a i j := by
  let cov := S.family.connection t
  let Ric := S.ricci t
  let nablaRic := metricNablaRic (I := I) (M := M) (S.family.metric t)
  let nabla2Ric := metricNabla2Ric (I := I) (M := M) (S.family.metric t)
  have hsecond :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov nablaRic nabla2Ric := by
    simpa [cov, Ric, nablaRic, nabla2Ric, metricNablaRic, metricNabla2Ric,
      SolutionFamily.connection, SolutionFamily.ricci, SolutionOn.ricci,
      SolutionOn.family, metricCov, metricRicci] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov nablaRic
        (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
          3 cov (by
            simpa [cov, SolutionFamily.connection, SolutionOn.family, metricCov] using
              metricCov_smooth (I := I) (M := M) (S.family.metric t)) nablaRic))
  have hnabla : ∀ y a i j,
      nablaRic y
          (vec3
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j y)) =
        nablaRicComp (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
          t y a i j := by
    intro y p q r
    simp [nablaRic, metricNablaRic, nablaRicComp,
      SolutionFamily.connection, SolutionFamily.ricci, SolutionOn.ricci,
      SolutionOn.family, metricCov, metricRicci]
  exact coordNab2Can (I := I) S t x nablaRic nabla2Ric hsecond hnabla d a i j

noncomputable def hamiltonDivPAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  roughLap0STensor (I := I) g (metricNabla2Ric (I := I) (M := M) g x) -
    metricTraceFirstTwo0STensor (I := I) g
      ((metricNabla2Ric (I := I) (M := M) g x).domDomCongr hamiltonDivPPerm)

noncomputable def hamiltonScalarHessianAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  metricTraceFirstTwo0STensor (I := I) g
    ((metricNabla2Ric (I := I) (M := M) g x).domDomCongr
      hamiltonScalarHessianPerm)

noncomputable def hamiltonRicciSquareAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  metricTraceFirstTwo0STensor (I := I) g
    ((Tensor0SSpace.product
      (metricRicci (I := I) (M := M) g x)
      (metricRicci (I := I) (M := M) g x)).domDomCongr hamiltonRicciSquarePerm)

noncomputable def hamiltonCurvatureRicciAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  metricTraceFirstTwo0STensor (I := I) g
    (metricTraceFirstTwo0STensor (I := I) g
      ((Tensor0SSpace.product
        (metricRm04 (I := I) (M := M) g x)
        (metricRicci (I := I) (M := M) g x)).domDomCongr
          hamiltonCurvatureRicciPerm))

noncomputable def hamiltonMbarAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  roughLap0STensor (I := I) g (metricNabla2Ric (I := I) (M := M) g x) -
      (1 / 2 : Real) • hamiltonScalarHessianAt (I := I) g x +
    2 • hamiltonCurvatureRicciAt (I := I) g x -
      hamiltonRicciSquareAt (I := I) g x

noncomputable def hamiltonMAt
    (clock : HarnackClock) (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  hamiltonMbarAt (I := I) g x +
    (1 / (2 * clock.elapsed) : Real) • metricRicci (I := I) (M := M) g x

omit [SigmaCompactSpace M] in
theorem hamiltonDivPAt_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonDivPAt (I := I) g x (vec2 A B) =
      (∑ i : Idx, ∑ j : Idx,
          gInv i j * metricNabla2Ric (I := I) (M := M) g x
            (vec4 (basis i) (basis j) A B)) -
        ∑ i : Idx, ∑ j : Idx,
          gInv i j * metricNabla2Ric (I := I) (M := M) g x
            (vec4 (basis i) A B (basis j)) := by
  classical
  rw [hamiltonDivPAt, Tensor0SSpace.sub_apply,
    roughLap0STensor_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine congrArg₂ (· - ·) ?_ ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have hslots :
        metricTraceInput (I := I) (basis i) (basis j) (vec2 A B) =
          vec4 (basis i) (basis j) A B := by
      funext q
      fin_cases q <;> rfl
    rw [hslots]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Tensor0SSpace.domDomCongr_apply]
    have hslots :
        (fun q => metricTraceInput (I := I) (basis i) (basis j) (vec2 A B)
          (hamiltonDivPPerm q)) = vec4 (basis i) A B (basis j) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots]

omit [SigmaCompactSpace M] in
theorem hamiltonScalarHessianAt_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonScalarHessianAt (I := I) g x (vec2 A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * metricNabla2Ric (I := I) (M := M) g x
          (vec4 A B (basis i) (basis j)) := by
  classical
  rw [hamiltonScalarHessianAt, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Tensor0SSpace.domDomCongr_apply]
  have hslots :
      (fun q => metricTraceInput (I := I) (basis i) (basis j) (vec2 A B)
        (hamiltonScalarHessianPerm q)) = vec4 A B (basis i) (basis j) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]

omit [SigmaCompactSpace M] in
theorem hamiltonRicciSquareAt_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonRicciSquareAt (I := I) g x (vec2 A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (metricRicci (I := I) (M := M) g x (vec2 A (basis i)) *
            metricRicci (I := I) (M := M) g x (vec2 (basis j) B)) := by
  classical
  rw [hamiltonRicciSquareAt, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply]
  have hleft :
      ((fun q => metricTraceInput (I := I) (basis i) (basis j) (vec2 A B)
        (hamiltonRicciSquarePerm q)) ∘ Fin.castAdd 2) =
        vec2 A (basis i) := by
    funext q
    fin_cases q <;> rfl
  have hright :
      ((fun q => metricTraceInput (I := I) (basis i) (basis j) (vec2 A B)
        (hamiltonRicciSquarePerm q)) ∘ Fin.natAdd 2) =
        vec2 (basis j) B := by
    funext q
    fin_cases q <;> rfl
  rw [hleft, hright]

omit [SigmaCompactSpace M] in
theorem hamiltonCurvatureRicciAt_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonCurvatureRicciAt (I := I) g x (vec2 A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              (metricRm04 (I := I) (M := M) g x
                  (vec4 A (basis k) (basis i) B) *
                metricRicci (I := I) (M := M) g x
                  (vec2 (basis l) (basis j)))) := by
  classical
  rw [hamiltonCurvatureRicciAt, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply]
  have hleft :
      ((fun q =>
        metricTraceInput (I := I) (basis k) (basis l)
          (metricTraceInput (I := I) (basis i) (basis j) (vec2 A B))
          (hamiltonCurvatureRicciPerm q)) ∘ Fin.castAdd 2) =
        vec4 A (basis k) (basis i) B := by
    funext q
    fin_cases q <;> rfl
  have hright :
      ((fun q =>
        metricTraceInput (I := I) (basis k) (basis l)
          (metricTraceInput (I := I) (basis i) (basis j) (vec2 A B))
          (hamiltonCurvatureRicciPerm q)) ∘ Fin.natAdd 4) =
        vec2 (basis l) (basis j) := by
    funext q
    fin_cases q <;> rfl
  rw [hleft, hright]

omit [SigmaCompactSpace M] in
theorem hamiltonCurvatureRicciAt_eq_raised_contraction
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonCurvatureRicciAt (I := I) g x (vec2 A B) =
      ∑ k : Idx, ∑ i : Idx,
        metricRm04 (I := I) (M := M) g x
            (vec4 A (basis k) (basis i) B) *
          raised02CompAt (I := I) basis gInv
            (metricRicci (I := I) (M := M) g x) k i := by
  rw [hamiltonCurvatureRicciAt_apply (I := I) g basis gInv hinv A B]
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              (metricRm04 (I := I) (M := M) g x
                  (vec4 A (basis k) (basis i) B) *
                metricRicci (I := I) (M := M) g x
                  (vec2 (basis l) (basis j))))) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j *
          (gInv k l *
            (metricRm04 (I := I) (M := M) g x
                (vec4 A (basis k) (basis i) B) *
              metricRicci (I := I) (M := M) g x
                (vec2 (basis l) (basis j)))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ l : Idx, ∑ j : Idx,
        gInv i j *
          (gInv k l *
            (metricRm04 (I := I) (M := M) g x
                (vec4 A (basis k) (basis i) B) *
              metricRicci (I := I) (M := M) g x
                (vec2 (basis l) (basis j)))) :=
      sum_reorder_four (fun i j k l =>
        gInv i j *
          (gInv k l *
            (metricRm04 (I := I) (M := M) g x
                (vec4 A (basis k) (basis i) B) *
              metricRicci (I := I) (M := M) g x
                (vec2 (basis l) (basis j)))))
    _ = ∑ k : Idx, ∑ i : Idx,
        metricRm04 (I := I) (M := M) g x
            (vec4 A (basis k) (basis i) B) *
          raised02CompAt (I := I) basis gInv
            (metricRicci (I := I) (M := M) g x) k i := by
      unfold raised02CompAt
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

omit [SigmaCompactSpace M] in
theorem hamiltonCurvatureRicciAt_eq_neg_rm04RicciContractionAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (a b : Idx) :
    hamiltonCurvatureRicciAt (I := I) g x (vec2 (basis a) (basis b)) =
      -rm04RicciContractionAt (I := I) basis
        (metricRm04 (I := I) (M := M) g x) gInv
        (metricRicci (I := I) (M := M) g x) a b := by
  let K := metricCurvatureSections (I := I) (M := M) g
  have hOutput : Rm04OutputSkewAt (I := I)
      (metricRm04 (I := I) (M := M) g x) := by
    simpa using
      (DifferentialGeometry.Geometry.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes
        (x := x))
  rw [hamiltonCurvatureRicciAt_eq_raised_contraction
    (I := I) g basis gInv hinv (basis a) (basis b)]
  unfold rm04RicciContractionAt
  calc
    (∑ k : Idx, ∑ i : Idx,
        metricRm04 (I := I) (M := M) g x
            (vec4 (basis a) (basis k) (basis i) (basis b)) *
          raised02CompAt (I := I) basis gInv
            (metricRicci (I := I) (M := M) g x) k i) =
      ∑ k : Idx, ∑ i : Idx,
        (-metricRm04 (I := I) (M := M) g x
            (vec4 (basis a) (basis k) (basis b) (basis i))) *
          raised02CompAt (I := I) basis gInv
            (metricRicci (I := I) (M := M) g x) k i := by
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hOutput (basis a) (basis k) (basis i) (basis b)]
    _ = -(∑ k : Idx, ∑ i : Idx,
        metricRm04 (I := I) (M := M) g x
            (vec4 (basis a) (basis k) (basis b) (basis i)) *
          raised02CompAt (I := I) basis gInv
            (metricRicci (I := I) (M := M) g x) k i) := by
      simp only [neg_mul, Finset.sum_neg_distrib]

omit [SigmaCompactSpace M] in
theorem hamiltonDivPAt_eq_rough_laplacian
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    hamiltonDivPAt (I := I) (S.family.metric (t : Real)) x =
      roughLap0STensor (I := I) (S.family.metric (t : Real))
          (metricNabla2Ric (I := I) (M := M) (S.family.metric (t : Real)) x) -
        (1 / 2 : Real) •
          hamiltonScalarHessianAt (I := I) (S.family.metric (t : Real)) x -
        hamiltonRicciSquareAt (I := I) (S.family.metric (t : Real)) x +
        hamiltonCurvatureRicciAt (I := I) (S.family.metric (t : Real)) x := by
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
    (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j => coordInv (I := I) S x (t : Real) x i j
  have hinv : MetricInverseInBasis (I := I) (M := M)
      (S.family.metric (t : Real)) x basis gInv := by
    simpa [basis, gInv] using coordInvReal (I := I) S x (t : Real)
  have hInv : ∀ i j, gInv i j = gInv j i :=
    MetricInverseInBasis.symmetric (I := I) (M := M) (S.family.metric (t : Real)) x
      basis gInv hinv
  apply ext0S_basis (I := I) basis
  intro slots
  let a := slots 0
  let b := slots 1
  have hslots : (fun q : Fin 2 => basis (slots q)) = vec2 (basis a) (basis b) := by
    funext q
    fin_cases q <;> rfl
  have hcomm := (coordCommAt (I := I) S hS x) t x (by simp) a b
  have hrough :
      roughLap0STensor (I := I) (S.family.metric (t : Real))
          (metricNabla2Ric (I := I) (M := M) (S.family.metric (t : Real)) x)
          (vec2 (basis a) (basis b)) =
        roughLapRicInFrame (M := M) (coordInv (I := I) S x)
          (coordNab2Ric (I := I) S x) (t : Real) x a b := by
    rw [roughLap0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I)
        (S.family.metric (t : Real)) basis gInv hinv]
    unfold metricTrace0S2InBasis roughLapRicInFrame
    simp only [gInv, basis,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have hinput :
        metricTraceInput (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)
            (vec2
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x)) =
          vec4
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput,
      metricNabla2Ric_coordinateFrameAt (I := I) S (t : Real) x]
  have hdiv :
      hamiltonDivPAt (I := I) (S.family.metric (t : Real)) x
          (vec2 (basis a) (basis b)) =
        roughLapRicInFrame (M := M) (coordInv (I := I) S x)
            (coordNab2Ric (I := I) S x) (t : Real) x a b -
          contractedNabla2RicLeftInFrame (M := M) (coordInv (I := I) S x)
            (coordNab2Ric (I := I) S x) (t : Real) x a b := by
    rw [hamiltonDivPAt_apply (I := I) (S.family.metric (t : Real))
      basis gInv hinv (basis a) (basis b)]
    unfold roughLapRicInFrame contractedNabla2RicLeftInFrame
    simp only [gInv, basis,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
    simp_rw [metricNabla2Ric_coordinateFrameAt (I := I) S (t : Real) x]
  have hhess :
      hamiltonScalarHessianAt (I := I) (S.family.metric (t : Real)) x
          (vec2 (basis a) (basis b)) =
        scalarHessianFromNabla2RicInFrame (M := M) (coordInv (I := I) S x)
          (coordNab2Ric (I := I) S x) (t : Real) x a b := by
    rw [hamiltonScalarHessianAt_apply (I := I) (S.family.metric (t : Real))
      basis gInv hinv (basis a) (basis b)]
    unfold scalarHessianFromNabla2RicInFrame
    simp only [gInv, basis,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [metricNabla2Ric_coordinateFrameAt (I := I) S (t : Real) x]
  have hsquare :
      hamiltonRicciSquareAt (I := I) (S.family.metric (t : Real)) x
          (vec2 (basis a) (basis b)) =
        ricciQuadraticCompInFrame (I := I) S (coordInv (I := I) S x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
          (t : Real) x a b := by
    rw [hamiltonRicciSquareAt_apply (I := I) (S.family.metric (t : Real))
      basis gInv hinv (basis a) (basis b)]
    simp only [ricciQuadraticCompInFrame, ricciOneUpCompInFrame,
      ricciCompInFrame, gInv, basis, Finset.sum_mul,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply,
      SolutionOn.ricciAt, SolutionFamily.ricciAt]
    calc
      (∑ i, ∑ j,
          coordInv (I := I) S x (t : Real) x i j *
            (metricRicciAt (I := I) (M := M) (S.base.metric (t : Real)) x
                (vec2
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)) *
              metricRicciAt (I := I) (M := M) (S.base.metric (t : Real)) x
                (vec2
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x)))) =
        ∑ j, ∑ i,
          coordInv (I := I) S x (t : Real) x i j *
            (metricRicciAt (I := I) (M := M) (S.base.metric (t : Real)) x
                (vec2
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)) *
              metricRicciAt (I := I) (M := M) (S.base.metric (t : Real)) x
                (vec2
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x))) := by
          rw [Finset.sum_comm]
      _ = ∑ i, ∑ j,
          coordInv (I := I) S x (t : Real) x i j *
              metricRicciAt (I := I) (M := M) (S.base.metric (t : Real)) x
                (vec2
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) *
            metricRicciAt (I := I) (M := M) (S.base.metric (t : Real)) x
              (vec2
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show coordInv (I := I) S x (t : Real) x j i =
              coordInv (I := I) S x (t : Real) x i j by
            simpa [gInv] using hInv j i]
          ring
  have hcurv :
      hamiltonCurvatureRicciAt (I := I) (S.family.metric (t : Real)) x
          (vec2 (basis a) (basis b)) =
        -rmRicciContractionCompInFrame (I := I) S S.base.rm04
          (coordInv (I := I) S x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
          (t : Real) x a b := by
    rw [hamiltonCurvatureRicciAt_eq_neg_rm04RicciContractionAt
      (I := I) (S.family.metric (t : Real)) basis gInv hinv a b]
    simp [rm04RicciContractionAt, rmRicciContractionCompInFrame,
      raised02CompAt, raisedRicciCompInFrame, gInv, basis,
      DifferentialGeometry.Geometry.Curvature.rm04Comp,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply,
      SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm04]
  simp only [component0S_apply, hslots, Tensor0SSpace.sub_apply,
    Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [hdiv, hrough, hhess, hsquare, hcurv, hcomm.1]
  ring

omit [SigmaCompactSpace M] in
theorem hamiltonMbarAt_eq_hamiltonDivPAt_add
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    hamiltonMbarAt (I := I) (S.family.metric (t : Real)) x =
      hamiltonDivPAt (I := I) (S.family.metric (t : Real)) x +
        hamiltonCurvatureRicciAt (I := I) (S.family.metric (t : Real)) x := by
  rw [hamiltonMbarAt, hamiltonDivPAt_eq_rough_laplacian (I := I) S hS t x]
  module

omit [SigmaCompactSpace M] in
theorem hamiltonMAt_eq_hamiltonDivPAt_add
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M) :
    hamiltonMAt (I := I) clock (S.family.metric clock.time) x =
      hamiltonDivPAt (I := I) (S.family.metric clock.time) x +
          hamiltonCurvatureRicciAt (I := I) (S.family.metric clock.time) x +
        (1 / (2 * clock.elapsed) : Real) •
          metricRicci (I := I) (M := M) (S.family.metric clock.time) x := by
  rw [hamiltonMAt,
    hamiltonMbarAt_eq_hamiltonDivPAt_add (I := I) S hS ⟨clock.time, ht⟩ x]

omit [SigmaCompactSpace M] in
theorem hamiltonMAt_apply
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (A B : TangentSpace I x) :
    hamiltonMAt (I := I) clock (S.family.metric clock.time) x (vec2 A B) =
      hamiltonDivPAt (I := I) (S.family.metric clock.time) x (vec2 A B) +
        hamiltonCurvatureRicciAt (I := I) (S.family.metric clock.time) x (vec2 A B) +
        (1 / (2 * clock.elapsed) : Real) *
          metricRicci (I := I) (M := M) (S.family.metric clock.time) x (vec2 A B) := by
  have h := hamiltonMAt_eq_hamiltonDivPAt_add (I := I) S hS clock ht x
  have hAB := congrArg (fun T => T (vec2 A B)) h
  simpa only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul] using hAB

omit [SigmaCompactSpace M] in
theorem hamiltonMAt_apply_basis
    {D : RealTimeInterval}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M)
      (S.family.metric clock.time) x basis gInv)
    (a b : Idx) :
    hamiltonMAt (I := I) clock (S.family.metric clock.time) x
        (vec2 (basis a) (basis b)) =
      (∑ i : Idx, ∑ j : Idx,
        gInv i j * metricNabla2Ric (I := I) (M := M)
          (S.family.metric clock.time) x
          (vec4 (basis i) (basis j) (basis a) (basis b))) -
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * metricNabla2Ric (I := I) (M := M)
          (S.family.metric clock.time) x
          (vec4 (basis i) (basis a) (basis b) (basis j)) +
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x
                  (vec4 (basis a) (basis k) (basis i) (basis b)) *
                metricRicci (I := I) (M := M) (S.family.metric clock.time) x
                  (vec2 (basis l) (basis j)))) +
      (1 / (2 * clock.elapsed) : Real) *
        metricRicci (I := I) (M := M) (S.family.metric clock.time) x
          (vec2 (basis a) (basis b)) := by
  rw [hamiltonMAt_apply (I := I) S hS clock ht x
      (basis a) (basis b),
    hamiltonDivPAt_apply (I := I) (S.family.metric clock.time)
      basis gInv hinv (basis a) (basis b),
    hamiltonCurvatureRicciAt_apply (I := I)
      (S.family.metric clock.time) basis gInv hinv (basis a) (basis b)]

omit [SigmaCompactSpace M] in
theorem hamiltonMAt_metricTrace_eq
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M) :
    metricTracePair0SAt (I := I) (S.family.metric clock.time)
        (hamiltonMAt (I := I) clock (S.family.metric clock.time) x) =
      (1 / 2 : Real) *
        (deriv (fun s : Real => S.scalar s x) clock.time +
          S.scalar clock.time x / clock.elapsed) := by
  classical
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => coordInv (I := I) S x clock.time x i j
  have hinv : MetricInverseInBasis (I := I) (M := M)
      (S.family.metric clock.time) x basis gInv := by
    simpa [basis, gInv] using coordInvReal (I := I) S x clock.time
  have hrough :
      metricTracePair0SAt (I := I) (S.family.metric clock.time)
          (roughLap0STensor (I := I) (S.family.metric clock.time)
            (metricNabla2Ric (I := I) (M := M) (S.family.metric clock.time) x)) =
        scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x)
          (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
          clock.time x := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I)
      (S.family.metric clock.time) basis gInv hinv]
    unfold scalarLaplacianTraceInFrame coordRoughRic
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [roughLap0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I)
        (S.family.metric clock.time) basis gInv hinv]
    unfold metricTrace0S2InBasis
    simp only [gInv, basis, coordinateFrameAt_toBasis_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hinput :
        metricTraceInput (I := I)
            (coordinateFrameAt (I := I) x i x)
            (coordinateFrameAt (I := I) x j x)
            (vec2
              (coordinateFrameAt (I := I) x a x)
              (coordinateFrameAt (I := I) x b x)) =
          vec4
            (coordinateFrameAt (I := I) x i x)
            (coordinateFrameAt (I := I) x j x)
            (coordinateFrameAt (I := I) x a x)
            (coordinateFrameAt (I := I) x b x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput, metricNabla2Ric_coordinateFrameAt (I := I) S clock.time x]
  have hhess :
      metricTracePair0SAt (I := I) (S.family.metric clock.time)
          (hamiltonScalarHessianAt (I := I) (S.family.metric clock.time) x) =
        scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x)
          (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
          clock.time x := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I)
      (S.family.metric clock.time) basis gInv hinv]
    calc
      (∑ a, ∑ b, gInv a b *
          hamiltonScalarHessianAt (I := I) (S.family.metric clock.time) x
            (vec2 (basis a) (basis b))) =
          ∑ a, ∑ b, coordInv (I := I) S x clock.time x a b *
            scalarHessianFromNabla2RicInFrame (M := M)
              (coordInv (I := I) S x) (coordNab2Ric (I := I) S x)
              clock.time x a b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hamiltonScalarHessianAt_apply (I := I)
          (S.family.metric clock.time) basis gInv hinv (basis a) (basis b)]
        unfold scalarHessianFromNabla2RicInFrame
        simp only [gInv, basis, coordinateFrameAt_toBasis_apply]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [metricNabla2Ric_coordinateFrameAt (I := I) S clock.time x]
      _ = scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x)
          (roughLapRicInFrame (M := M) (coordInv (I := I) S x)
            (coordNab2Ric (I := I) S x)) clock.time x :=
        scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace
          (M := M) (coordInv (I := I) S x) (coordNab2Ric (I := I) S x)
            clock.time x
      _ = scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x)
          (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
          clock.time x := by rfl
  have hnorm :
      ricciNormSqInFrame (I := I) S (coordInv (I := I) S x)
          (coordinateFrameAt (I := I) x) clock.time x =
        normSq0S (I := I) (S.family.metric clock.time) x 2
          (S.ricci clock.time x) := by
    exact ricciNormSq_basis (I := I) S (coordInv (I := I) S x)
      (coordinateFrameAt (I := I) x) basis hinv
      (by intro i; simp [basis, coordinateFrameAt_toBasis_apply])
  have hInvSym : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      coordInv (I := I) S x clock.time x i j =
        coordInv (I := I) S x clock.time x j i :=
    MetricInverseInBasis.symmetric (I := I) (M := M) (S.family.metric clock.time) x
      basis gInv hinv
  have hRicSym : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x)
          clock.time x i j =
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x)
          clock.time x j i := by
    intro i j
    have h := metricRicciSymm (I := I) (M := M)
      (S.family.metric clock.time) basis gInv hinv i j
    simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt,
      basis, coordinateFrameAt_toBasis_apply] using h
  have hsquareComp : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      hamiltonRicciSquareAt (I := I) (S.family.metric clock.time) x
          (vec2 (basis a) (basis b)) =
        ricciQuadraticCompInFrame (I := I) S (coordInv (I := I) S x)
          (coordinateFrameAt (I := I) x) clock.time x a b := by
    intro a b
    rw [hamiltonRicciSquareAt_apply (I := I) (S.family.metric clock.time)
      basis gInv hinv (basis a) (basis b)]
    simp only [ricciQuadraticCompInFrame, ricciOneUpCompInFrame,
      ricciCompInFrame, gInv, basis, Finset.sum_mul,
      coordinateFrameAt_toBasis_apply, SolutionOn.ricciAt, SolutionFamily.ricciAt]
    calc
      (∑ i, ∑ j,
          coordInv (I := I) S x clock.time x i j *
            (metricRicciAt (I := I) (M := M) (S.base.metric clock.time) x
                (vec2 (coordinateFrameAt (I := I) x a x)
                  (coordinateFrameAt (I := I) x i x)) *
              metricRicciAt (I := I) (M := M) (S.base.metric clock.time) x
                (vec2 (coordinateFrameAt (I := I) x j x)
                  (coordinateFrameAt (I := I) x b x)))) =
        ∑ j, ∑ i,
          coordInv (I := I) S x clock.time x i j *
            (metricRicciAt (I := I) (M := M) (S.base.metric clock.time) x
                (vec2 (coordinateFrameAt (I := I) x a x)
                  (coordinateFrameAt (I := I) x i x)) *
              metricRicciAt (I := I) (M := M) (S.base.metric clock.time) x
                (vec2 (coordinateFrameAt (I := I) x j x)
                  (coordinateFrameAt (I := I) x b x))) := by rw [Finset.sum_comm]
      _ = ∑ i, ∑ j,
          coordInv (I := I) S x clock.time x i j *
              metricRicciAt (I := I) (M := M) (S.base.metric clock.time) x
                (vec2 (coordinateFrameAt (I := I) x a x)
                  (coordinateFrameAt (I := I) x j x)) *
            metricRicciAt (I := I) (M := M) (S.base.metric clock.time) x
              (vec2 (coordinateFrameAt (I := I) x i x)
                (coordinateFrameAt (I := I) x b x)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hInvSym j i]
        ring
  have hsquare :
      metricTracePair0SAt (I := I) (S.family.metric clock.time)
          (hamiltonRicciSquareAt (I := I) (S.family.metric clock.time) x) =
        normSq0S (I := I) (S.family.metric clock.time) x 2
          (S.ricci clock.time x) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I)
      (S.family.metric clock.time) basis gInv hinv]
    simp_rw [hsquareComp]
    rw [scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_at
      (I := I) S (coordInv (I := I) S x) (coordinateFrameAt (I := I) x)
        clock.time x hInvSym hRicSym]
    exact hnorm
  have hcurv :
      metricTracePair0SAt (I := I) (S.family.metric clock.time)
          (hamiltonCurvatureRicciAt (I := I) (S.family.metric clock.time) x) =
        normSq0S (I := I) (S.family.metric clock.time) x 2
          (S.ricci clock.time x) := by
    let K := metricCurvatureSections (I := I) (M := M) (S.family.metric clock.time)
    have hLower : Rm04LowersRm13At (I := I) (S.family.metric clock.time) x
        (metricRm13 (I := I) (M := M) (S.family.metric clock.time) x)
        (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x) :=
      rm04LowersRm13At_of_realizes (I := I) (S.family.metric clock.time)
        (metricCov (I := I) (M := M) (S.family.metric clock.time))
        (metricRm13 (I := I) (M := M) (S.family.metric clock.time))
        (metricRm04 (I := I) (M := M) (S.family.metric clock.time))
        K.rm13Realizes K.rm04Realizes x
    have hTrace : RicciRealizesRm04FirstTraceAt (I := I)
        (metricRicci (I := I) (M := M) (S.family.metric clock.time) x)
        (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x)
        gInv basis := by
      exact ricciFirstTraceAt_of_rm13_section (I := I)
        (S.family.metric clock.time) basis gInv hinv
        (metricRicci (I := I) (M := M) (S.family.metric clock.time))
        (metricRm13 (I := I) (M := M) (S.family.metric clock.time))
        (metricRm04 (I := I) (M := M) (S.family.metric clock.time))
        K.ricciRealizes hLower
    have hOutput : Rm04OutputSkewAt (I := I)
        (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x) := by
      exact DifferentialGeometry.Geometry.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (S.family.metric clock.time)
        (metricRm04 (I := I) (M := M) (S.family.metric clock.time))
        K.rm04Realizes
    have hmain := metricTrace_rm04RicciContractionAt_eq_neg_inner
      (I := I) basis
      (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x)
      gInv (metricRicci (I := I) (M := M) (S.family.metric clock.time) x)
      hTrace hOutput
    have hmain' :
        (∑ a, ∑ b, gInv a b *
          rm04RicciContractionAt (I := I) basis
            (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x)
            gInv (metricRicci (I := I) (M := M) (S.family.metric clock.time) x)
            a b) =
          -ricciNormSqInFrame (I := I) S (coordInv (I := I) S x)
            (coordinateFrameAt (I := I) x) clock.time x := by
      simpa [gInv, basis, raised02CompAt, raisedRicciCompInFrame,
        DifferentialGeometry.Geometry.Curvature.raisedRicciComponentsInFrame,
        ricciNormSqInFrame, ricciCompInFrame, ricciTwoTensorField,
        SolutionOn.ricciAt, SolutionFamily.ricciAt,
        coordinateFrameAt_toBasis_apply] using hmain
    rw [metricTracePair0SAt_eq_sum_basis (I := I)
      (S.family.metric clock.time) basis gInv hinv]
    calc
      (∑ a, ∑ b, gInv a b *
          hamiltonCurvatureRicciAt (I := I) (S.family.metric clock.time) x
            (vec2 (basis a) (basis b))) =
        -(∑ a, ∑ b, gInv a b *
          rm04RicciContractionAt (I := I) basis
            (metricRm04 (I := I) (M := M) (S.family.metric clock.time) x)
            gInv (metricRicci (I := I) (M := M) (S.family.metric clock.time) x)
            a b) := by
          simp_rw [hamiltonCurvatureRicciAt_eq_neg_rm04RicciContractionAt
            (I := I) (S.family.metric clock.time) basis gInv hinv]
          simp only [mul_neg, Finset.sum_neg_distrib]
      _ = ricciNormSqInFrame (I := I) S (coordInv (I := I) S x)
          (coordinateFrameAt (I := I) x) clock.time x := by rw [hmain']; ring
      _ = normSq0S (I := I) (S.family.metric clock.time) x 2
          (S.ricci clock.time x) := hnorm
  have hlap := scalarLaplacianTraceInFrame_coord_eq_laplacianAt
    (I := I) S x (⟨clock.time, ht⟩)
  have hevolWithin := scalarEvolution_of_isSolution (I := I) S hS
    (flowG (I := I) S) (fun _ => rfl) (fun _ => rfl) ⟨clock.time, ht⟩ x
  have hevol := hevolWithin.hasDerivAt (D.regular_mem_nhds ht)
  have hderiv :
      deriv (fun s : Real => S.scalar s x) clock.time =
        laplacianAt (I := I) (flowG (I := I) S) clock.time
            (S.scalar clock.time) x +
          2 * normSq0S (I := I) (S.family.metric clock.time) x 2
            (S.ricci clock.time x) := hevol.deriv
  have hric :
      metricRicci (I := I) (M := M) (S.family.metric clock.time) x =
        S.ricciAt clock.time x := by
    rfl
  unfold hamiltonMAt hamiltonMbarAt
  simp only [two_smul, metricTracePair0SAt_add, metricTracePair0SAt_sub,
    metricTracePair0SAt_smul]
  rw [hrough, hhess, hcurv, hsquare, hlap, hderiv, hric,
    SolutionOn.scalar_eq_metricTrace]
  ring

omit [SigmaCompactSpace M] in
private theorem hamiltonRicciSquareAt_symm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (a b : Idx) :
    hamiltonRicciSquareAt (I := I) g x (vec2 (basis a) (basis b)) =
      hamiltonRicciSquareAt (I := I) g x (vec2 (basis b) (basis a)) := by
  classical
  have hInv : ∀ i j, gInv i j = gInv j i :=
    MetricInverseInBasis.symmetric (I := I) (M := M) g x basis gInv hinv
  have hRic : ∀ i j,
      metricRicci (I := I) (M := M) g x (vec2 (basis i) (basis j)) =
        metricRicci (I := I) (M := M) g x (vec2 (basis j) (basis i)) :=
    metricRicciSymm (I := I) (M := M) g basis gInv hinv
  rw [hamiltonRicciSquareAt_apply (I := I) g basis gInv hinv,
    hamiltonRicciSquareAt_apply (I := I) g basis gInv hinv]
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (metricRicci (I := I) (M := M) g x (vec2 (basis a) (basis i)) *
            metricRicci (I := I) (M := M) g x (vec2 (basis j) (basis b)))) =
      ∑ j : Idx, ∑ i : Idx,
        gInv i j *
          (metricRicci (I := I) (M := M) g x (vec2 (basis a) (basis i)) *
            metricRicci (I := I) (M := M) g x (vec2 (basis j) (basis b))) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (metricRicci (I := I) (M := M) g x (vec2 (basis b) (basis i)) *
            metricRicci (I := I) (M := M) g x (vec2 (basis j) (basis a))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hInv j i, hRic a j, hRic i b]
      ring

omit [SigmaCompactSpace M] in
private theorem hamiltonCurvatureRicciAt_symm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (a b : Idx) :
    hamiltonCurvatureRicciAt (I := I) g x (vec2 (basis a) (basis b)) =
      hamiltonCurvatureRicciAt (I := I) g x (vec2 (basis b) (basis a)) := by
  let K := metricCurvatureSections (I := I) (M := M) g
  have hPair : ∀ W X Y Z : TangentSpace I x,
      metricRm04 (I := I) (M := M) g x (vec4 W X Y Z) =
        metricRm04 (I := I) (M := M) g x (vec4 Y Z W X) := by
    simpa using
      (DifferentialGeometry.Geometry.Connection.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes (x := x))
  have hRic : ∀ i j,
      metricRicci (I := I) (M := M) g x (vec2 (basis i) (basis j)) =
        metricRicci (I := I) (M := M) g x (vec2 (basis j) (basis i)) :=
    metricRicciSymm (I := I) (M := M) g basis gInv hinv
  have hInv : ∀ i j, gInv i j = gInv j i :=
    MetricInverseInBasis.symmetric (I := I) (M := M) g x basis gInv hinv
  rw [hamiltonCurvatureRicciAt_eq_neg_rm04RicciContractionAt
      (I := I) g basis gInv hinv a b,
    hamiltonCurvatureRicciAt_eq_neg_rm04RicciContractionAt
      (I := I) g basis gInv hinv b a,
    rm04RicciContractionAt_symm (I := I) basis
      (metricRm04 (I := I) (M := M) g x) gInv
      (metricRicci (I := I) (M := M) g x) hPair hRic hInv a b]

omit [SigmaCompactSpace M] in
theorem hamiltonMbarAt_symm
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : TangentSpace I x) :
    hamiltonMbarAt (I := I) g x (vec2 A B) =
      hamiltonMbarAt (I := I) g x (vec2 B A) := by
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
    (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
        (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
  have hcomp : ∀ a b,
      hamiltonMbarAt (I := I) g x (vec2 (basis a) (basis b)) =
        hamiltonMbarAt (I := I) g x (vec2 (basis b) (basis a)) := by
    intro a b
    have hrough :
        roughLap0STensor (I := I) g (metricNabla2Ric (I := I) (M := M) g x)
            (vec2 (basis a) (basis b)) =
          roughLap0STensor (I := I) g (metricNabla2Ric (I := I) (M := M) g x)
            (vec2 (basis b) (basis a)) := by
      rw [roughLap0STensor_apply, roughLap0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
      unfold metricTrace0S2InBasis
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have hleft :
          metricTraceInput (I := I) (basis i) (basis j) (vec2 (basis a) (basis b)) =
            vec4 (basis i) (basis j) (basis a) (basis b) := by
        funext q
        fin_cases q <;> rfl
      have hright :
          metricTraceInput (I := I) (basis i) (basis j) (vec2 (basis b) (basis a)) =
            vec4 (basis i) (basis j) (basis b) (basis a) := by
        funext q
        fin_cases q <;> rfl
      rw [hleft, hright, metricNabla2Ric_last_two_symm (I := I) (M := M)]
    have hhess :
        hamiltonScalarHessianAt (I := I) g x (vec2 (basis a) (basis b)) =
          hamiltonScalarHessianAt (I := I) g x (vec2 (basis b) (basis a)) := by
      rw [hamiltonScalarHessianAt_apply (I := I) g basis gInv hinv,
        hamiltonScalarHessianAt_apply (I := I) g basis gInv hinv]
      simpa [metricNabla2Ric, metricNablaRic, metricCov, metricRicci] using
        (DifferentialGeometry.Geometry.Connection.scalar_curvature_hessian_trace_symmetric
          (I := I) (M := M) g basis gInv hinv a b)
    have hsquare := hamiltonRicciSquareAt_symm (I := I) g basis gInv hinv a b
    have hcurv := hamiltonCurvatureRicciAt_symm (I := I) g basis gInv hinv a b
    simp only [hamiltonMbarAt, two_smul, Tensor0SSpace.sub_apply,
      Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    rw [hrough, hhess, hcurv, hsquare]
  have hsymm :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
      (I := I) basis (hamiltonMbarAt (I := I) g x) hcomp A B
  have hleft : (fun q : Fin 2 => if q = 0 then A else B) = vec2 A B := by
    funext q
    fin_cases q <;> rfl
  have hright : (fun q : Fin 2 => if q = 0 then B else A) = vec2 B A := by
    funext q
    fin_cases q <;> rfl
  rw [hleft, hright] at hsymm
  exact hsymm

omit [SigmaCompactSpace M] in
theorem hamiltonMAt_symm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (A B : TangentSpace I x) :
    hamiltonMAt (I := I) clock (S.family.metric clock.time) x (vec2 A B) =
      hamiltonMAt (I := I) clock (S.family.metric clock.time) x (vec2 B A) := by
  let _ := ht
  have hRic :
      metricRicci (I := I) (M := M) (S.family.metric clock.time) x (vec2 A B) =
        metricRicci (I := I) (M := M) (S.family.metric clock.time) x (vec2 B A) := by
    simpa using
      metricRicciAt_symm (I := I) (M := M) (S.family.metric clock.time) x A B
  simp only [hamiltonMAt, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply]
  rw [hamiltonMbarAt_symm (I := I), hRic]

end DifferentialGeometry.PDE.RicciFlow
