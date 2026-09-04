import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Connection.TimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.Difference
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Frame

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Lowering

variable {x : M}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02_add_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
      Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then u₁ else Z with hm
  have hupd : ∀ u : TangentSpace I x,
      Function.update m 0 u = (fun a : Fin 2 => if a = 0 then u else Z) := by
    intro u
    funext a
    fin_cases a <;> simp [hm]
  rw [Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq]
  calc q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z)
      = q (Function.update m 0 (u₁ + u₂)) := by rw [hupd]
    _ = q (Function.update m 0 u₁) + q (Function.update m 0 u₂) := q.map_update_add m 0 u₁ u₂
    _ = q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
          q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by rw [hupd, hupd]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02_smul_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (u Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then c • u else Z) =
      c * Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then u else Z with hm
  have hupd : ∀ u' : TangentSpace I x,
      Function.update m 0 u' = (fun a : Fin 2 => if a = 0 then u' else Z) := by
    intro u'
    funext a
    fin_cases a <;> simp [hm]
  rw [Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq]
  calc q (fun a : Fin 2 => if a = 0 then c • u else Z)
      = q (Function.update m 0 (c • u)) := by rw [hupd]
    _ = c • q (Function.update m 0 u) := q.map_update_smul m 0 c u
    _ = c * q (fun a : Fin 2 => if a = 0 then u else Z) := by rw [hupd, smul_eq_mul]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem lowerBilin_add
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A B : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (A + B) =
      lowerBilin (I := I) q A + lowerBilin (I := I) q B := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (lowerBilin (I := I) q (A + B)) v =
    Tensor0SSpace.eval (lowerBilin (I := I) q A + lowerBilin (I := I) q B) v
  rw [Tensor0SSpace.eval_add, lowerBilin_apply, lowerBilin_apply, lowerBilin_apply]
  have hAB : ((A + B) (v 1)) (v 0) = (A (v 1)) (v 0) + (B (v 1)) (v 0) := rfl
  rw [hAB, tensor02_add_left]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem lowerBilin_smul
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (c • A) = c • lowerBilin (I := I) q A := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (lowerBilin (I := I) q (c • A)) v =
    Tensor0SSpace.eval (c • lowerBilin (I := I) q A) v
  rw [Tensor0SSpace.eval_smul, lowerBilin_apply, lowerBilin_apply]
  have hA : ((c • A) (v 1)) (v 0) = c • ((A (v 1)) (v 0)) := rfl
  rw [hA, tensor02_smul_left, smul_eq_mul]

private def lowerTriOut
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 3)
    (Ei := fun _ : Fin 4 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          (lowerBilin (I := I) q (A X) :
            ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real)
        map_add' := by
          intro X₁ X₂
          rw [map_add]
          exact lowerBilin_add (I := I) q (A X₁) (A X₂)
        map_smul' := by
          intro c X
          rw [map_smul]
          exact lowerBilin_smul (I := I) q c (A X) })

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem lowerTriOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (w : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerTriOut (I := I) q A) w =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then ((A (w 0)) (w 2)) (w 1) else w 3) := by
  have h : Tensor0SSpace.eval (lowerTriOut (I := I) q A) w =
      Tensor0SSpace.eval (lowerBilin (I := I) q (A (w 0))) (Fin.tail w) := by
    rfl
  rw [h, lowerBilin_apply]
  congr 1

def lowerTri
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 4) 2)
    (lowerTriOut (I := I) q A)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lowerTri_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (v : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerTri (I := I) q A) v =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then ((A (v 0)) (v 1)) (v 2) else v 3) := by
  have h : Tensor0SSpace.eval (lowerTri (I := I) q A) v =
      Tensor0SSpace.eval (lowerTriOut (I := I) q A)
        (fun i : Fin 4 => v (Equiv.swap (1 : Fin 4) 2 i)) := rfl
  rw [h, lowerTriOut_apply]
  congr 1

end Lowering
section RaisedDifference

variable {x : M}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02_sub_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ - u₂ else Z) =
      Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ else Z) -
        Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  have h := tensor02_add_left (I := I) q (u₁ - u₂) u₂ Z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem metricField_slot0 (g : SmoothRiemannianMetric I M) (x : M)
    (u Z : TangentSpace I x) :
    Tensor0SSpace.eval (metricTensorField (I := I) g x)
        (fun a : Fin 2 => if a = 0 then u else Z) =
      g.inner x u Z := by
  rw [Tensor0SSpace.eval_eq, metricTensorField_apply]
  simp

private instance instContMDiffMetricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ :=
  CovariantDerivative.contMDiffCovariantDerivativeOn_univ_iff.mp
    (metricCov_smooth (I := I) g isOpen_univ)

def rmDiffVec (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x :=
  DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₁) x -
    DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₂) x

omit [SigmaCompactSpace M] in
@[simp]
theorem rmDiffVec_self (g : SmoothRiemannianMetric I M) (x : M) :
    rmDiffVec (I := I) g g x = 0 := by
  rw [rmDiffVec]
  exact sub_self (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g) x)

omit [SigmaCompactSpace M] in
theorem rmDiffLowAt_eq_lowerTri (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    rmDiffLowAt (I := I) g₁ g₂ x =
      lowerTri (I := I) (metricTensorField (I := I) g₁ x) (rmDiffVec (I := I) g₁ g₂ x) := by
  classical
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (rmDiffLowAt (I := I) g₁ g₂ x) v =
    Tensor0SSpace.eval
      (lowerTri (I := I) (metricTensorField (I := I) g₁ x) (rmDiffVec (I := I) g₁ g₂ x)) v
  have hv : DifferentialGeometry.Geometry.Curvature.vec4 (I := I) (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> simp [DifferentialGeometry.Geometry.Curvature.vec4]
  have h₁ :
      Tensor0SSpace.eval
          (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
            (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x) v =
        g₁.inner x (v 3)
          (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₁) x
            (v 0) (v 1) (v 2)) := by
    have h :=
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const
        (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) (v 0) (v 1) (v 2) (v 3)
    rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (I := I) (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x (v 0) (v 1) (v 2),
      hv] at h
    change Tensor0SSpace.eval
      (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x) v = _ at h
    exact h
  have h₂ :
      Tensor0SSpace.eval
          (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
            (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x) v =
        g₁.inner x (v 3)
          (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₂) x
            (v 0) (v 1) (v 2)) := by
    have h :=
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) (v 0) (v 1) (v 2) (v 3)
    rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (I := I) (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x (v 0) (v 1) (v 2),
      hv] at h
    change Tensor0SSpace.eval
      (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x) v = _ at h
    exact h
  have hsub : Tensor0SSpace.eval (rmDiffLowAt (I := I) g₁ g₂ x) v =
      Tensor0SSpace.eval
          (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
            (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x) v -
        Tensor0SSpace.eval
          (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
            (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x) v := by
    rw [rmDiffLowAt, Tensor0SSpace.eval_sub]
  have hvec : ((rmDiffVec (I := I) g₁ g₂ x (v 0)) (v 1)) (v 2) =
      DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₁) x
          (v 0) (v 1) (v 2) -
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₂) x
          (v 0) (v 1) (v 2) := rfl
  have hlin : ∀ u₁ u₂ : TangentSpace I x,
      g₁.inner x (u₁ - u₂) (v 3) = g₁.inner x u₁ (v 3) - g₁.inner x u₂ (v 3) := by
    intro u₁ u₂
    rw [← metricField_slot0 (I := I) g₁ x u₁ (v 3), ← metricField_slot0 (I := I) g₁ x u₂ (v 3),
      ← metricField_slot0 (I := I) g₁ x (u₁ - u₂) (v 3), tensor02_sub_left]
  rw [hsub, h₁, h₂, lowerTri_apply, metricField_slot0, hvec, hlin,
    g₁.symm x (v 3)
      (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₁) x
        (v 0) (v 1) (v 2)),
    g₁.symm x (v 3)
      (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₂) x
        (v 0) (v 1) (v 2))]

end RaisedDifference

section Speed

def rmDiffDot (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x)
    (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  (-2 : Real) •
      lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (rmDiffVec (I := I) (g₁ t) (g₂ t) x) +
    lowerTri (I := I) (metricTensorField (I := I) (g₁ t) x) (Sdot x)

omit [SigmaCompactSpace M] in
theorem rmDiffDot_apply (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x)
    (t : Real) (x : M) (v : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (rmDiffDot (I := I) g₁ g₂ Sdot t x) v =
      (-2 : Real) * Tensor0SSpace.eval (metricRicciAt (I := I) (g₁ t) x)
          (fun a : Fin 2 => if a = 0 then
            ((rmDiffVec (I := I) (g₁ t) (g₂ t) x (v 0)) (v 1)) (v 2) else v 3) +
        (g₁ t).inner x (((Sdot x (v 0)) (v 1)) (v 2)) (v 3) := by
  have hadd :
      Tensor0SSpace.eval (rmDiffDot (I := I) g₁ g₂ Sdot t x) v =
        Tensor0SSpace.eval ((-2 : Real) •
            lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
              (rmDiffVec (I := I) (g₁ t) (g₂ t) x)) v +
          Tensor0SSpace.eval
            (lowerTri (I := I) (metricTensorField (I := I) (g₁ t) x) (Sdot x)) v := by
    rw [rmDiffDot, Tensor0SSpace.eval_add]
  have hsmul :
      Tensor0SSpace.eval ((-2 : Real) •
          lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
            (rmDiffVec (I := I) (g₁ t) (g₂ t) x)) v =
        (-2 : Real) •
          Tensor0SSpace.eval
            (lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
              (rmDiffVec (I := I) (g₁ t) (g₂ t) x)) v := by
    rw [Tensor0SSpace.eval_smul]
  rw [hadd, hsmul, lowerTri_apply, lowerTri_apply, smul_eq_mul, metricField_slot0]

end Speed

section

variable {x : M}

omit [SigmaCompactSpace M] in
theorem rmDiffLow_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x)
    {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hRm : ∀ X Y Z : TangentSpace I x,
      HasDerivAt
        (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
        (((Sdot x X) Y) Z) t)
    (v : Fin 4 -> TangentSpace I x) :
    HasDerivAt (fun r : Real =>
        Tensor0SSpace.eval (rmDiffLowAt (I := I) (g₁ r) (g₂ r) x) v)
      (Tensor0SSpace.eval (rmDiffDot (I := I) g₁ g₂ Sdot t x) v) t := by
  classical
  set b : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x) with hb
  set F : Real → TangentSpace I x := fun r =>
    ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (v 0)) (v 1)) (v 2) with hF
  set Fdot : TangentSpace I x := ((Sdot x (v 0)) (v 1)) (v 2) with hFdot
  have hFderiv : HasDerivAt F Fdot t := hRm (v 0) (v 1) (v 2)
  have hcomp : ∀ k, HasDerivAt (fun r : Real => b.repr (F r) k) (b.repr Fdot k) t := by
    intro k
    have hL : HasDerivAt (fun r : Real =>
        (LinearMap.toContinuousLinearMap (b.coord k)) (F r))
        ((LinearMap.toContinuousLinearMap (b.coord k)) Fdot) t :=
      (LinearMap.toContinuousLinearMap (b.coord k)).hasFDerivAt.comp_hasDerivAt t hFderiv
    simpa using hL
  have hmet : ∀ k, HasDerivAt
      (fun r : Real => (g₁ r).inner x (b k) (v 3))
      ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
        (fun a : Fin 2 => if a = 0 then b k else v 3)) t := fun k => hPDE₁ (b k) (v 3)
  have hsum : ∀ r : Real,
      Tensor0SSpace.eval (rmDiffLowAt (I := I) (g₁ r) (g₂ r) x) v =
        ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 3) := by
    intro r
    rw [rmDiffLowAt_eq_lowerTri, lowerTri_apply,
      show ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (v 0)) (v 1)) (v 2) = F r from rfl]
    have hexp := tensor02_expand (I := I)
      (metricTensorField (I := I) (g₁ r) x) b (F r) (v 3)
    change Tensor0SSpace.eval (metricTensorField (I := I) (g₁ r) x)
        (fun a : Fin 2 => if a = 0 then F r else v 3) = _ at hexp
    rw [hexp]
    exact Finset.sum_congr rfl fun k _ => by
      change b.repr (F r) k * Tensor0SSpace.eval (metricTensorField (I := I) (g₁ r) x)
        (fun a : Fin 2 => if a = 0 then b k else v 3) = _
      rw [metricField_slot0]
  have hderiv : HasDerivAt (fun r : Real => ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 3))
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 3) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 3)))) t :=
    HasDerivAt.fun_sum fun k _ => (hcomp k).mul (hmet k)
  have hval :
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 3) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 3)))) =
        Tensor0SSpace.eval (rmDiffDot (I := I) g₁ g₂ Sdot t x) v := by
    rw [Finset.sum_add_distrib, rmDiffDot_apply]
    have hg : (∑ k, b.repr Fdot k * (g₁ t).inner x (b k) (v 3)) =
        (g₁ t).inner x Fdot (v 3) := by
      rw [← metricField_slot0 (I := I) (g₁ t) x Fdot (v 3)]
      have hexp := tensor02_expand (I := I)
        (metricTensorField (I := I) (g₁ t) x) b Fdot (v 3)
      change Tensor0SSpace.eval (metricTensorField (I := I) (g₁ t) x)
          (fun a : Fin 2 => if a = 0 then Fdot else v 3) = _ at hexp
      rw [hexp]
      exact Finset.sum_congr rfl fun k _ => by
        change b.repr Fdot k * (g₁ t).inner x (b k) (v 3) =
          b.repr Fdot k * Tensor0SSpace.eval (metricTensorField (I := I) (g₁ t) x)
            (fun a : Fin 2 => if a = 0 then b k else v 3)
        rw [metricField_slot0]
    have hr : (∑ k, b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 3))) =
        (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then F t else v 3) := by
      rw [tensor02_expand (I := I) (metricRicciAt (I := I) (g₁ t) x) b (F t) (v 3),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hg, hr]
    rw [show F t = ((rmDiffVec (I := I) (g₁ t) (g₂ t) x (v 0)) (v 1)) (v 2) from rfl,
      show Fdot = ((Sdot x (v 0)) (v 1)) (v 2) from rfl]
    have hric : metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then
            ((rmDiffVec (I := I) (g₁ t) (g₂ t) x (v 0)) (v 1)) (v 2) else v 3) =
        Tensor0SSpace.eval (metricRicciAt (I := I) (g₁ t) x)
          (fun a : Fin 2 => if a = 0 then
            ((rmDiffVec (I := I) (g₁ t) (g₂ t) x (v 0)) (v 1)) (v 2) else v 3) := rfl
    rw [hric]
    ring
  have := hderiv.congr_deriv hval
  simpa only [hsum] using this

end

section DivergenceForm

variable {Idx : Type*} [Fintype Idx]

def frameVec4 (frame : Idx -> (y : M) -> TangentSpace I y) (x : M) (i j k l : Idx) :
    Fin 4 -> TangentSpace I x :=
  DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
    (frame i x) (frame j x) (frame k x) (frame l x)

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem driftDiff_split (Ric₁ Ric₂ : MatrixComp M Idx) (Rm₁ Rm₂ : FourComp M Idx)
    (t : Real) (x : M) (i j k l : Idx) :
    riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
        riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l =
      riemann04RicciDriftInFrame (fun s y a b => Ric₁ s y a b - Ric₂ s y a b) Rm₁ t x i j k l +
        riemann04RicciDriftInFrame Ric₂
          (fun s y a b c d => Rm₁ s y a b c d - Rm₂ s y a b c d) t x i j k l := by
  classical
  simp only [riemann04RicciDriftInFrame, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

def rmDotRem (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Rm₁ Rm₂ B₁ B₂ : FourComp M Idx) (Ric₁ Ric₂ : MatrixComp M Idx)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  lapDiffRem (I := I) g₁ g₂ T₂ x (frameVec4 (I := I) frame x i j k l) -
    2 * ((B₁ t x i j k l - B₂ t x i j k l) - (B₁ t x i j l k - B₂ t x i j l k) +
      (B₁ t x i k j l - B₂ t x i k j l) - (B₁ t x i l j k - B₂ t x i l j k)) -
    (riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
      riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l)

end DivergenceForm

section LaplacianAlgebra

variable {s : ℕ}

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem roughLap0SField_sub (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g (T - U) =
      roughLap0SField (I := I) g T - roughLap0SField (I := I) g U := by
  rw [roughLap0SField, roughLap0SField, roughLap0SField, metricNabla0S_sub,
    covDiv0SField_sub]

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem roughLapSub_apply (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (v : Fin s -> TangentSpace I x) :
    roughLap0SField (I := I) g (T - U) x v =
      roughLap0SField (I := I) g T x v - roughLap0SField (I := I) g U x v := by
  have hfield : roughLap0SField (I := I) g (T - U) x =
      roughLap0SField (I := I) g T x - roughLap0SField (I := I) g U x := by
    rw [roughLap0SField_sub]; rfl
  rw [hfield]
  exact Tensor0SSpace.sub_apply (I := I) s x _ _ v

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem lapDiffFlux_apply_vec (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (v : Fin s -> TangentSpace I x) :
    roughLap0SField (I := I) g₁ T x v - roughLap0SField (I := I) g₂ T x v =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x v +
        lapDiffRem (I := I) g₁ g₂ T x v := by
  have hf := lapDiff_eq_div_flux (I := I) g₁ g₂ T
  have hx₁ : (roughLap0SField (I := I) g₁ T - roughLap0SField (I := I) g₂ T) x =
      roughLap0SField (I := I) g₁ T x - roughLap0SField (I := I) g₂ T x := rfl
  have hx₂ : (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) +
      lapDiffRem (I := I) g₁ g₂ T) x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x +
        lapDiffRem (I := I) g₁ g₂ T x := rfl
  have h : roughLap0SField (I := I) g₁ T x - roughLap0SField (I := I) g₂ T x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x +
        lapDiffRem (I := I) g₁ g₂ T x := by
    rw [← hx₁, ← hx₂, hf]
  have hl : (roughLap0SField (I := I) g₁ T x -
      roughLap0SField (I := I) g₂ T x) v =
      roughLap0SField (I := I) g₁ T x v - roughLap0SField (I := I) g₂ T x v :=
    Tensor0SSpace.sub_apply (I := I) s x _ _ v
  have hr : (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x +
      lapDiffRem (I := I) g₁ g₂ T x) v =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x v +
        lapDiffRem (I := I) g₁ g₂ T x v :=
    Tensor0SSpace.add_apply (I := I) s x _ _ v
  rw [← hl, ← hr, h]

end LaplacianAlgebra

section Capstone

variable {Idx : Type*} [Fintype Idx]

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem rmDiffComp_deriv
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Rm₁ Rm₂ roughLapRm₁ roughLapRm₂ B₁ B₂ : FourComp M Idx)
    (Ric₁ Ric₂ : MatrixComp M Idx)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₁ roughLapRm₁ B₁ Ric₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₂ roughLapRm₂ B₂ Ric₂)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (i j k l : Idx)
    (hL₁ : roughLapRm₁ (t : Real) x i j k l =
      roughLap0SField (I := I) g₁ T₁ x (frameVec4 (I := I) frame x i j k l))
    (hL₂ : roughLapRm₂ (t : Real) x i j k l =
      roughLap0SField (I := I) g₂ T₂ x (frameVec4 (I := I) frame x i j k l)) :
    HasDerivWithinAt (fun r : Real => Rm₁ r x i j k l - Rm₂ r x i j k l)
      (roughLap0SField (I := I) g₁ (T₁ - T₂) x (frameVec4 (I := I) frame x i j k l) +
        covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T₂) x
          (frameVec4 (I := I) frame x i j k l) +
        rmDotRem (I := I) g₁ g₂ T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂ frame (t : Real) x i j k l)
      D.carrier (t : Real) := by
  have hsub := (hev₁ t x i j k l).sub (hev₂ t x i j k l)
  refine hsub.congr_deriv ?_
  have hlap :
      roughLapRm₁ (t : Real) x i j k l - roughLapRm₂ (t : Real) x i j k l =
        roughLap0SField (I := I) g₁ (T₁ - T₂) x (frameVec4 (I := I) frame x i j k l) +
          covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T₂) x
            (frameVec4 (I := I) frame x i j k l) +
          lapDiffRem (I := I) g₁ g₂ T₂ x (frameVec4 (I := I) frame x i j k l) := by
    rw [hL₁, hL₂]
    have hk := lapDiffFlux_apply_vec (I := I) g₁ g₂ T₂ x
      (frameVec4 (I := I) frame x i j k l)
    have hd := roughLapSub_apply (I := I) g₁ T₁ T₂ x (frameVec4 (I := I) frame x i j k l)
    linarith [hk, hd]
  rw [rmDotRem]
  linarith [hlap]

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem rmLowComp_deriv
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (T₁ T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Rm₁ Rm₂ roughLapRm₁ roughLapRm₂ B₁ B₂ : FourComp M Idx)
    (Ric₁ Ric₂ : MatrixComp M Idx)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₁ roughLapRm₁ B₁ Ric₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₂ roughLapRm₂ B₂ Ric₂)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (i j k l : Idx)
    (hL₁ : roughLapRm₁ (t : Real) x i j k l =
      roughLap0SField (I := I) (g₁ (t : Real)) T₁ x (frameVec4 (I := I) frame x i j k l))
    (hL₂ : roughLapRm₂ (t : Real) x i j k l =
      roughLap0SField (I := I) (g₂ (t : Real)) T₂ x (frameVec4 (I := I) frame x i j k l))
    (hreal : ∀ r : Real, Rm₁ r x i j k l - Rm₂ r x i j k l =
      rmDiffLowAt (I := I) (g₁ r) (g₂ r) x (frameVec4 (I := I) frame x i j k l)) :
    HasDerivWithinAt
      (fun r : Real =>
        rmDiffLowAt (I := I) (g₁ r) (g₂ r) x (frameVec4 (I := I) frame x i j k l))
      (roughLap0SField (I := I) (g₁ (t : Real)) (T₁ - T₂) x
          (frameVec4 (I := I) frame x i j k l) +
        covDiv0SField (I := I) (g₁ (t : Real))
          (lapDiffFlux (I := I) (g₁ (t : Real)) (g₂ (t : Real)) T₂) x
          (frameVec4 (I := I) frame x i j k l) +
        rmDotRem (I := I) (g₁ (t : Real)) (g₂ (t : Real)) T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂ frame
          (t : Real) x i j k l)
      D.carrier (t : Real) := by
  have h := rmDiffComp_deriv (I := I) (g₁ (t : Real)) (g₂ (t : Real)) T₁ T₂
    Rm₁ Rm₂ roughLapRm₁ roughLapRm₂ B₁ B₂ Ric₁ Ric₂ frame hev₁ hev₂ t x i j k l hL₁ hL₂
  have hfun : (fun r : Real => Rm₁ r x i j k l - Rm₂ r x i j k l) =
      (fun r : Real =>
        rmDiffLowAt (I := I) (g₁ r) (g₂ r) x (frameVec4 (I := I) frame x i j k l)) :=
    funext hreal
  rw [← hfun]
  exact h

end Capstone

end DifferentialGeometry.PDE.RicciFlow

end
