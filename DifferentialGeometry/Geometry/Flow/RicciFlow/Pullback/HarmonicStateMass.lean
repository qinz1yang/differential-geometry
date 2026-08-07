import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicDensityJoint
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# The finite state-dependent harmonic-map mass

The exponential-section coordinate of a map is nonlinear.  Consequently the
time derivative of the represented map is not the raw coefficient velocity:
the velocity must first be pushed through the coefficient derivative of the
local addition.  This file records that derivative on a finite spectral trial
space and packages its target-metric pairing as the faithful finite mass
operator.

The definitions here deliberately differ from `hmfFinMass`.  That older form
is the zero-section mass and has no state argument.  It is the linearization of
the present operator at the identity map, not the nonlinear Galerkin mass.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure

/-! ## Stability of finite coercive forms -/

/-- A continuous bilinear family which has a quantitative coercivity bound at
the origin retains half that bound on a sufficiently small state ball. -/
theorem bilin_coer_near
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V → V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousAt B 0)
    (hB : ∀ v : V, c * ‖v‖ * ‖v‖ ≤ B 0 v v) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : V, ‖u‖ < R → ∀ v : V,
      (c / 2) * ‖v‖ * ‖v‖ ≤ B u v v := by
  have hc2 : 0 < c / 2 := half_pos hc
  have hev : {u : V | ‖B u - B 0‖ < c / 2} ∈ 𝓝 (0 : V) := by
    have hball := hcont.eventually (Metric.ball_mem_nhds (B 0) hc2)
    filter_upwards [hball] with u hu
    simpa only [Metric.mem_ball, dist_eq_norm] using hu
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨R, hR, ?_⟩
  intro u hu v
  have hu_ball : u ∈ Metric.ball (0 : V) R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hdiff : ‖B u - B 0‖ ≤ c / 2 := (hsub hu_ball).le
  let D : V →L[ℝ] V →L[ℝ] ℝ := B u - B 0
  have habs : |D v v| ≤ (c / 2) * ‖v‖ * ‖v‖ := by
    have h₁ : ‖D v‖ ≤ ‖D‖ * ‖v‖ := D.le_opNorm v
    have h₂ : ‖D v v‖ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
    calc
      |D v v| = ‖D v v‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖D v‖ * ‖v‖ := h₂
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right h₁ (norm_nonneg v)
      _ ≤ ((c / 2) * ‖v‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        simpa only [D] using hdiff
      _ = (c / 2) * ‖v‖ * ‖v‖ := rfl
  have hDlow : -((c / 2) * ‖v‖ * ‖v‖) ≤ D v v :=
    neg_le_of_abs_le habs
  have heval : B u v v = B 0 v v + D v v := by
    simp only [D, ContinuousLinearMap.sub_apply]
    ring
  rw [heval]
  calc
    (c / 2) * ‖v‖ * ‖v‖ =
        c * ‖v‖ * ‖v‖ - (c / 2) * ‖v‖ * ‖v‖ := by ring
    _ ≤ B 0 v v + D v v := add_le_add (hB v) hDlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M

private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Coefficient derivative of the local addition -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem mfderiv_affine_line_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → M) (u v : V)
    (hmd : MDifferentiableAt 𝓘(ℝ, V) I f u) :
    mfderiv 𝓘(ℝ) I (fun a : ℝ ↦ f (u + a • v)) 0 1 =
      mfderiv 𝓘(ℝ, V) I f u v := by
  let line : ℝ → V := fun a ↦ u + a • v
  have hline_md : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, V) line 0 := by
    have hline_cd : ContMDiff 𝓘(ℝ) 𝓘(ℝ, V) ∞ line :=
      contMDiff_const.add (contMDiff_id.smul contMDiff_const)
    exact hline_cd.contMDiffAt.mdifferentiableAt (by decide)
  have hline_zero : line 0 = u := by
    simp only [line, zero_smul, add_zero]
  have hline_deriv : mfderiv 𝓘(ℝ) 𝓘(ℝ, V) line 0 1 = v := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt line
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0 := by
      simpa only [line] using
        ((hasFDerivAt_id (0 : ℝ)).smul_const v).const_add u
    rw [h.fderiv]
    change (1 : ℝ) • v = v
    exact one_smul ℝ v
  have hcomp := mfderiv_comp_apply (f := line) (x := (0 : ℝ))
    (hline_zero ▸ hmd) hline_md (1 : ℝ)
  change mfderiv 𝓘(ℝ) I (f ∘ line) 0 1 =
    mfderiv 𝓘(ℝ, V) I f u v
  have hgoal :
      mfderiv 𝓘(ℝ, V) I f (line 0)
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, V) line 0 1) =
        mfderiv 𝓘(ℝ, V) I f u v := by
    rw [hline_zero]
    exact congrArg (mfderiv 𝓘(ℝ, V) I f u) hline_deriv
  exact hcomp.trans hgoal

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [BoundarylessManifold I M] [ConnectedSpace M] in
private theorem mfderiv_euclidean_affine_line_apply
    {J : Type*} [Fintype J]
    (f : EuclideanSpace ℝ J → M) (u v : EuclideanSpace ℝ J)
    (hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ J) I f u) :
    mfderiv 𝓘(ℝ) I (fun a : ℝ ↦ f (u + a • v)) 0 1 =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ J) I f u v :=
  mfderiv_affine_line_apply (E := E) (I := I) (M := M) f u v hmd

/-- The derivative, in the finite spectral coefficient, of the local-addition
map at a fixed spatial point.  Its value is a tangent vector at the represented
map value, exactly as required for the harmonic-map time velocity. -/
noncomputable irreducible_def hmfSpecVar
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) (x : M) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
      TangentSpace I (hmfSpecMap (I := I) (M := M) q S x u) :=
  mfderiv 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
    (hmfSpecMap (I := I) (M := M) q S x) u

omit [BoundarylessManifold I M] [ConnectedSpace M] in
/-- Applying `hmfSpecVar` to a direction is the derivative of the corresponding
one-dimensional coefficient line.  This is the chain-rule bridge between the
finite-dimensional Fréchet derivative and `hmfStateVar`. -/
theorem hmfSpecVar_line
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v : EuclideanSpace ℝ {i // i ∈ S}) (x : M)
    (hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
      (hmfSpecMap (I := I) (M := M) q S x) u) :
    mfderiv 𝓘(ℝ) I
        (fun a : ℝ =>
          hmfSpecMap (I := I) (M := M) q S x (u + a • v)) 0 1 =
      hmfSpecVar (I := I) (M := M) q S u x v := by
  rw [hmfSpecVar_def]
  exact mfderiv_euclidean_affine_line_apply (E := E) (I := I) (M := M)
    (hmfSpecMap (I := I) (M := M) q S x) u v hmd

omit [BoundarylessManifold I M] [ConnectedSpace M] in
/-- On a differentiability point, the finite coefficient derivative agrees
with the intrinsic one-dimensional state variation. -/
theorem hmfSpecVar_state
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v : EuclideanSpace ℝ {i // i ∈ S}) (x : M)
    (hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
      (fun z : EuclideanSpace ℝ {i // i ∈ S} =>
        hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S z) x) u) :
    hmfStateVar (I := I) (M := M) q
        (hmfSpecIncl (I := I) (M := M) q S u)
        (hmfSpecIncl (I := I) (M := M) q S v) x =
      hmfSpecVar (I := I) (M := M) q S u x v := by
  have hcurve :
      (fun a : ℝ =>
        hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u +
            a • hmfSpecIncl (I := I) (M := M) q S v) x) =
      (fun a : ℝ =>
        hmfSpecMap (I := I) (M := M) q S x (u + a • v)) := by
    funext a
    simp only [hmfSpecMap_def, map_add, map_smul]
  rw [hmfStateVar, hcurve]
  have hmdMap : MDifferentiableAt
      𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
      (hmfSpecMap (I := I) (M := M) q S x) u := by
    have hmap :
        hmfSpecMap (I := I) (M := M) q S x =
          fun z : EuclideanSpace ℝ {i // i ∈ S} =>
            hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S z) x := by
      funext z
      rw [hmfSpecMap_def]
    rw [hmap]
    exact hmd
  exact hmfSpecVar_line (I := I) (M := M) q S u v x hmdMap

/-! ## The faithful finite mass -/

/-- Pointwise target-metric mass after both coefficient directions have been
pushed through the state derivative of the local addition. -/
noncomputable def hmfSpecMassPt
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) (x : M) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
      EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  let L := hmfSpecVar (I := I) (M := M) q S u x
  (ContinuousLinearMap.precomp ℝ L).comp
    ((q.inner
      (hmfSpecMap (I := I) (M := M) q S x u)).comp L)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem hmfSpecMassPt_apply
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v w : EuclideanSpace ℝ {i // i ∈ S}) (x : M) :
    hmfSpecMassPt (I := I) (M := M) q S u x v w =
      q.inner
        (hmfSpecMap (I := I) (M := M) q S x u)
        (hmfSpecVar (I := I) (M := M) q S u x v)
        (hmfSpecVar (I := I) (M := M) q S u x w) := by
  rfl

/-- The faithful finite mass operator, integrated against the moving domain
volume.  Integrating the bilinear maps themselves preserves linearity without
introducing separate scalar-integral linearity obligations. -/
noncomputable def hmfSpecMassOp
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
      EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  ∫ x, hmfSpecMassPt (I := I) (M := M) q S u x
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
/-- Joint continuity of the pointwise faithful mass on a coefficient ball
implies operator-norm continuity of the integrated finite mass for a fixed
domain metric. -/
theorem hmfSpecMass_cont
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R : ℝ)
    (hmass : ContinuousOn
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
        hmfSpecMassPt (I := I) (M := M) q S p.1 p.2)
      (Metric.closedBall
        (0 : EuclideanSpace ℝ {i // i ∈ S}) R ×ˢ (Set.univ : Set M))) :
    ContinuousOn
      (hmfSpecMassOp (I := I) (M := M) q h S)
      (Metric.closedBall (0 : EuclideanSpace ℝ {i // i ∈ S}) R) := by
  letI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace h
  simpa only [hmfSpecMassOp] using
    (integral_contOn_cpt
      (riemannianVolumeMeasure (I := I) (M := M) h)
      (fun u x => hmfSpecMassPt (I := I) (M := M) q S u x)
      (isCompact_closedBall
        (0 : EuclideanSpace ℝ {i // i ∈ S}) R) hmass)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
/-- Evaluation of the integrated mass operator can be moved inside the
integral once the pointwise bilinear-map field is integrable. -/
theorem hmfSpecMass_apply
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v w : EuclideanSpace ℝ {i // i ∈ S})
    (hint : Integrable
      (fun x => hmfSpecMassPt (I := I) (M := M) q S u x)
      (riemannianVolumeMeasure (I := I) (M := M) h)) :
    hmfSpecMassOp (I := I) (M := M) q h S u v w =
      ∫ x, q.inner
          (hmfSpecMap (I := I) (M := M) q S x u)
          (hmfSpecVar (I := I) (M := M) q S u x v)
          (hmfSpecVar (I := I) (M := M) q S u x w)
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
  have hintv : Integrable
      (fun x => hmfSpecMassPt (I := I) (M := M) q S u x v)
      (riemannianVolumeMeasure (I := I) (M := M) h) :=
    (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) v).integrable_comp hint
  rw [hmfSpecMassOp, ContinuousLinearMap.integral_apply hint v,
    ContinuousLinearMap.integral_apply hintv w]
  simp only [hmfSpecMassPt_apply]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
/-- The finite operator is exactly the faithful state mass restricted to the
spectral trial space whenever the local-addition coefficient slice is
differentiable. -/
theorem hmfSpecMass_state
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v w : EuclideanSpace ℝ {i // i ∈ S})
    (hmd : ∀ x : M,
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
        (fun z : EuclideanSpace ℝ {i // i ∈ S} =>
          hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S z) x) u)
    (hint : Integrable
      (fun x => hmfSpecMassPt (I := I) (M := M) q S u x)
      (riemannianVolumeMeasure (I := I) (M := M) h)) :
    hmfSpecMassOp (I := I) (M := M) q h S u v w =
      hmfStateMass (I := I) (M := M) q h
        (hmfSpecIncl (I := I) (M := M) q S u)
        (hmfSpecIncl (I := I) (M := M) q S v)
        (hmfSpecIncl (I := I) (M := M) q S w) := by
  rw [hmfSpecMass_apply (I := I) (M := M) q h S u v w hint]
  unfold hmfStateMass
  apply integral_congr_ae
  filter_upwards with x
  rw [hmfSpecVar_state (I := I) (M := M) q S u v x (hmd x),
    hmfSpecVar_state (I := I) (M := M) q S u w x (hmd x),
    hmfSpecMap_apply]

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
