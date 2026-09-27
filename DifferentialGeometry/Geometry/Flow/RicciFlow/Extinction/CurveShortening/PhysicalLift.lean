import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback
import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CoverCovariantDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSliceSmoothness
import Mathlib.Tactic.Ring

noncomputable section

open Bundle Manifold
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace ProductCurve

def physicalLift {M : Type*} (c : ProductCurve M) (lambda x t : ℝ) : M × ℝ :=
  (c.projection.lift x t, lambda * c.y x t)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def physicalField (c : ProductCurve M) (lambda : ℝ) (V : c.Field (I := I))
    (x t : ℝ) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (c.physicalLift lambda x t) :=
  ((V x t).1, lambda * (V x t).2)

theorem physicalField_smul (c : ProductCurve M) (lambda : ℝ) (f : ℝ → ℝ → ℝ)
    (V : c.Field (I := I)) (x t : ℝ) :
    c.physicalField lambda (fun z s => f z s • V z s) x t =
      f x t • c.physicalField lambda V x t := by
  apply Prod.ext
  · rfl
  · change lambda * (f x t * (V x t).2) = f x t * (lambda * (V x t).2)
    ring

private theorem mfderiv_dilation (lambda : ℝ) (hlambda : lambda ≠ 0) (p : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda).toContinuousLinearEquiv.toDiffeomorph)
      p v = (v.1, lambda * v.2) := by
  let L := (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda).toContinuousLinearEquiv
  have hL : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) L.toDiffeomorph p.2 =
      L.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (L.toContinuousLinearMap : ℝ → ℝ) p.2 = _
    exact L.toContinuousLinearMap.fderiv
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
    (Prod.map (id : M → M) L.toDiffeomorph) p v = _
  rw [mfderiv_prodMap mdifferentiableAt_id
    (L.toDiffeomorph.mdifferentiable (by decide) p.2), mfderiv_id, hL]
  rfl

theorem physicalLift_eq_prodCongr (c : ProductCurve M) (lambda : ℝ) (hlambda : lambda ≠ 0)
    (x t : ℝ) :
    c.physicalLift lambda x t =
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda).toContinuousLinearEquiv.toDiffeomorph)
        (c.coverLift x t) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem physicalLift_spatial_derivative (c : ProductCurve M) (lambda : ℝ)
    (hlambda : lambda ≠ 0) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.physicalLift lambda z t) x 1 =
      c.physicalField lambda (c.X (I := I)) x t := by
  let Φ := (Diffeomorph.refl I M ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda).toContinuousLinearEquiv.toDiffeomorph
  have heq : (fun z => c.physicalLift lambda z t) = Φ ∘ (fun z => c.coverLift z t) := rfl
  rw [heq, mfderiv_comp x (Φ.mdifferentiable (by decide) _)
    (c.coverLift_space_mdifferentiableAt hc x t ht)]
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ (c.coverLift x t)
    (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.coverLift z t) x 1) = _
  rw [c.cover_spatial_derivative J hc x t ht, mfderiv_dilation]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem physicalLift_time_derivative (c : ProductCurve M) (lambda : ℝ)
    (hlambda : lambda ≠ 0) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t) :
    mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun s => c.physicalLift lambda x s) J t 1 =
      c.physicalField lambda (c.velocity (I := I) J) x t := by
  let Φ := (Diffeomorph.refl I M ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda).toContinuousLinearEquiv.toDiffeomorph
  have heq : (fun s => c.physicalLift lambda x s) = Φ ∘ (fun s => c.coverLift x s) := rfl
  rw [heq, mfderiv_comp_mfderivWithin t (Φ.mdifferentiable (by decide) _)
    (c.coverLift_time_mdifferentiableWithinAt hc x t ht) huniq]
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) Φ (c.coverLift x t)
    (mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun s => c.coverLift x s) J t 1) = _
  rw [c.cover_time_derivative hc x t ht huniq, mfderiv_dilation]
  rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
theorem physicalLift_inner (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) (v w : TangentSpace I (c.projection.lift x t) × ℝ) :
    (coverProductMetric (g t) 1 zero_lt_one).inner (c.physicalLift lambda x t)
      (v.1, lambda * v.2) (w.1, lambda * w.2) = c.inner g lambda x t v w := by
  rw [coverProductMetric_inner]
  change (g t).inner (c.projection.lift x t) v.1 w.1 +
    1 ^ 2 * (lambda * v.2) * (lambda * w.2) = _
  rw [ProductCurve.inner]
  ring

theorem physicalField_normSq (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (V : c.Field (I := I)) (x t : ℝ) :
    (coverProductMetric (g t) 1 zero_lt_one).inner (c.physicalLift lambda x t)
      (c.physicalField lambda V x t) (c.physicalField lambda V x t) =
        c.normSq g lambda V x t :=
  c.physicalLift_inner g lambda x t (V x t) (V x t)

theorem physicalLift_speed (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : lambda ≠ 0) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    let X := mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.physicalLift lambda z t) x 1
    Real.sqrt ((coverProductMetric (g t) 1 zero_lt_one).inner
      (c.physicalLift lambda x t) X X) = c.speed g lambda x t := by
  dsimp only
  rw [c.physicalLift_spatial_derivative lambda hlambda hc x t ht]
  exact congrArg Real.sqrt (c.physicalField_normSq g lambda (c.X (I := I)) x t)

end ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem coverProductMetric_eq_pullback_dilation (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    coverProductMetric g lambda hlambda =
      Diffeomorph.pullbackMetric (g.prod (euclideanMetric (E := ℝ)))
        ((Diffeomorph.refl I M ∞).prodCongr
          (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda.ne').toContinuousLinearEquiv.toDiffeomorph) :=
  (Diffeomorph.pullbackMetric_prod_euclidean_smul g lambda hlambda.ne').symm

namespace ProductCurve

set_option backward.isDefEq.respectTransparency false in
theorem physicalLift_covariantDerivative [I.Boundaryless] (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (t : ℝ) (V : c.Field (I := I))
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (x : ℝ) :
    covDerivAlong (coverProductMetric (g t) 1 zero_lt_one)
      (fun z => c.physicalLift lambda z t) (fun z => c.physicalField lambda V z t) x =
        c.physicalField lambda (c.Dx g V) x t := by
  let Φ := (Diffeomorph.refl I M ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda.ne').toContinuousLinearEquiv.toDiffeomorph
  have hmetric : Diffeomorph.pullbackMetric (coverProductMetric (g t) 1 zero_lt_one) Φ =
      coverProductMetric (g t) lambda hlambda := by
    have hunit : coverProductMetric (g t) 1 zero_lt_one =
        (g t).prod (euclideanMetric (E := ℝ)) := by
      apply SmoothRiemannianMetric.ext_inner
      intro p v w
      rw [coverProductMetric_inner, SmoothRiemannianMetric.prod_inner,
        euclideanMetric_inner, Real.inner_apply]
      ring
    rw [hunit]
    exact (coverProductMetric_eq_pullback_dilation (g t) lambda hlambda).symm
  have hfield := mdifferentiableAt_tangentField_iff.mp
    (hV.contMDiffAt.mdifferentiableAt (by simp) (x := x))
  have hnat := covAlong_natMDiff (coverProductMetric (g t) 1 zero_lt_one) Φ
    (fun z => c.coverLift z t) (fun z => V z t) x hfield.1 hfield.2
  rw [hmetric, c.cover_covariantDerivative_of_boundaryless g lambda hlambda t V hV x] at hnat
  simp only [Φ, mfderiv_dilation] at hnat
  convert hnat.symm using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem physicalLift_Ds [I.Boundaryless] (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J)
    (V : c.Field (I := I))
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (x : ℝ) :
    let X := mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.physicalLift lambda z t) x 1
    (Real.sqrt ((coverProductMetric (g t) 1 zero_lt_one).inner
      (c.physicalLift lambda x t) X X))⁻¹ •
      covDerivAlong (coverProductMetric (g t) 1 zero_lt_one)
        (fun z => c.physicalLift lambda z t) (fun z => c.physicalField lambda V z t) x =
          c.physicalField lambda (c.Ds g lambda V) x t := by
  dsimp only
  rw [c.physicalLift_speed g lambda hlambda.ne' hc x t ht,
    c.physicalLift_covariantDerivative g lambda hlambda t V hV x]
  exact (c.physicalField_smul lambda (fun z s => (c.speed g lambda z s)⁻¹)
    (c.Dx g V) x t).symm

theorem physicalLift_unitTangent (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : lambda ≠ 0)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    let X := mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.physicalLift lambda z t) x 1;
    (Real.sqrt ((coverProductMetric (g t) 1 zero_lt_one).inner
      (c.physicalLift lambda x t) X X))⁻¹ • X =
        c.physicalField lambda (c.unitTangent g lambda) x t := by
  dsimp only
  rw [c.physicalLift_speed g lambda hlambda hc x t ht,
    c.physicalLift_spatial_derivative lambda hlambda hc x t ht]
  exact (c.physicalField_smul lambda (fun z s => (c.speed g lambda z s)⁻¹)
    (c.X (I := I)) x t).symm

variable [I.Boundaryless]

theorem physicalLift_iteratedDs (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (V : c.Field (I := I))
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) (m : ℕ) :
    let γ := fun x => c.physicalLift lambda x t;
    let G := coverProductMetric (g t) 1 zero_lt_one;
    let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1;
    let Ds := fun (W : (x : ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x)) x =>
      (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • covDerivAlong G γ W x;
    Ds^[m] (fun x => c.physicalField lambda V x t) =
      fun x => c.physicalField lambda (c.iteratedDs g lambda m V) x t := by
  let γ := fun x => c.physicalLift lambda x t
  let G := coverProductMetric (g t) 1 zero_lt_one
  let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1
  let D := fun (W : (x : ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x)) x =>
    (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • covDerivAlong G γ W x
  change D^[m] (fun x => c.physicalField lambda V x t) = _
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    simpa only [iteratedDs, Function.iterate_succ_apply'] using
      c.physicalLift_Ds g lambda hlambda hc t ht (c.iteratedDs g lambda m V)
        (c.cover_iteratedDs_contMDiff g lambda hlambda hc hi V t ht hV m) x

theorem physicalLift_curvatureVector (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    let γ := fun x => c.physicalLift lambda x t;
    let G := coverProductMetric (g t) 1 zero_lt_one;
    let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1;
    let T := fun x => (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • X x;
    (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • covDerivAlong G γ T x =
      c.physicalField lambda (c.curvatureVector g lambda) x t := by
  dsimp only
  have hT := funext (c.physicalLift_unitTangent g lambda hlambda.ne' hc t ht)
  rw [hT]
  exact c.physicalLift_Ds g lambda hlambda hc t ht (c.unitTangent g lambda)
    (c.cover_unitTangent_contMDiff g lambda hlambda hc hi t ht) x

theorem physicalLift_solution_equation (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J) (t : ℝ) (ht : t ∈ J)
    (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t) (x : ℝ) :
    let γ := fun x => c.physicalLift lambda x t;
    let G := coverProductMetric (g t) 1 zero_lt_one;
    let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1;
    let T := fun x => (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • X x;
    mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
      (fun s => c.physicalLift lambda x s) J t 1 =
        (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • covDerivAlong G γ T x := by
  dsimp only
  rw [c.physicalLift_time_derivative lambda hlambda.ne' hc.smooth x t ht huniq,
    c.physicalLift_curvatureVector g lambda hlambda hc.smooth hc.immersed t ht x]
  exact congrArg (fun v => (v.1, lambda * v.2)) (hc.equation x t ht)

theorem physicalLift_iteratedDs_curvature_normSq (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (m : ℕ) (x : ℝ) :
    let γ := fun x => c.physicalLift lambda x t;
    let G := coverProductMetric (g t) 1 zero_lt_one;
    let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1;
    let T := fun x => (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • X x;
    let Ds := fun (W : (x : ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x)) x =>
      (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • covDerivAlong G γ W x;
    let W := Ds^[m] (Ds T);
    G.inner (γ x) (W x) (W x) =
      c.normSq g lambda (c.iteratedDs g lambda m (c.curvatureVector g lambda)) x t := by
  let γ := fun x => c.physicalLift lambda x t
  let G := coverProductMetric (g t) 1 zero_lt_one
  let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1
  let T := fun x => (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • X x
  let D := fun (W : (x : ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x)) x =>
    (Real.sqrt (G.inner (γ x) (X x) (X x)))⁻¹ • covDerivAlong G γ W x
  have hH : D T = fun x => c.physicalField lambda (c.curvatureVector g lambda) x t :=
    funext (c.physicalLift_curvatureVector g lambda hlambda hc hi t ht)
  have hiter := c.physicalLift_iteratedDs g lambda hlambda hc hi t ht
    (c.curvatureVector g lambda) (c.cover_curvatureVector_contMDiff g lambda hlambda hc hi t ht) m
  change G.inner (γ x) ((D^[m] (D T)) x) ((D^[m] (D T)) x) = _
  rw [hH, hiter]
  exact c.physicalField_normSq g lambda (c.iteratedDs g lambda m (c.curvatureVector g lambda)) x t

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
