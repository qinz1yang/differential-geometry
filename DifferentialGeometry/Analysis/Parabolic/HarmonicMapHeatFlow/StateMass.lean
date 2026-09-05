import DifferentialGeometry.Analysis.Parabolic.HarmonicMapHeatFlow.CoefficientRegularity
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.CompactIntegral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure

private noncomputable local instance harmonicMapFlowRealDualNormedAddCommGroup
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance harmonicMapFlowRealDualNormedSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance harmonicMapFlowRealBilinearNormedAddCommGroup
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance harmonicMapFlowRealBilinearNormedSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem bilin_coer_near
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V → V →L[ℝ] V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousAt B 0)
    (hB : ∀ v : V, c * ‖v‖ * ‖v‖ ≤ B 0 v v) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : V, ‖u‖ < R → ∀ v : V,
      (c / 2) * ‖v‖ * ‖v‖ ≤ B u v v := by
  let : NormedAddCommGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
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
    simp only [D, sub_apply]
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
      have hderiv : HasDerivAt line v 0 := by
        simpa only [line, id_eq, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v).const_add u
      exact hderiv.hasFDerivAt
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
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ J) I f u
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, EuclideanSpace ℝ J))
          u).symm.toContinuousLinearMap v) := by
  with_unfolding_all
    exact mfderiv_affine_line_apply (E := E) (I := I) (M := M) f u v hmd

noncomputable irreducible_def harmonicMapFlowSpectralVariation
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) (x : M) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
      TangentSpace I (harmonicMapFlowSpectralMap (I := I) (M := M) q S x u) :=
  (mfderiv 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
    (harmonicMapFlowSpectralMap (I := I) (M := M) q S x) u).comp
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S})) u).symm.toContinuousLinearMap

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralVariation_line
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v : EuclideanSpace ℝ {i // i ∈ S}) (x : M)
    (hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
      (harmonicMapFlowSpectralMap (I := I) (M := M) q S x) u) :
    mfderiv 𝓘(ℝ) I
        (fun a : ℝ =>
          harmonicMapFlowSpectralMap (I := I) (M := M) q S x (u + a • v)) 0 1 =
      harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x v := by
  rw [harmonicMapFlowSpectralVariation_def, ContinuousLinearMap.comp_apply]
  exact mfderiv_euclidean_affine_line_apply (E := E) (I := I) (M := M)
    (harmonicMapFlowSpectralMap (I := I) (M := M) q S x) u v hmd

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralVariation_state
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v : EuclideanSpace ℝ {i // i ∈ S}) (x : M)
    (hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
      (fun z : EuclideanSpace ℝ {i // i ∈ S} =>
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S z) x) u) :
    harmonicMapFlowStateVariation (I := I) (M := M) q
        (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S u)
        (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S v) x =
      harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x v := by
  have hcurve :
      (fun a : ℝ =>
        harmonicMapFlowAdd (I := I) (M := M) q
          (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S u +
            a • harmonicMapFlowSpectralInclusion (I := I) (M := M) q S v) x) =
      (fun a : ℝ =>
        harmonicMapFlowSpectralMap (I := I) (M := M) q S x (u + a • v)) := by
    funext a
    simp only [harmonicMapFlowSpectralMap_def, map_add, map_smul]
  rw [harmonicMapFlowStateVariation, hcurve]
  have hmdMap : MDifferentiableAt
      𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
      (harmonicMapFlowSpectralMap (I := I) (M := M) q S x) u := by
    have hmap :
        harmonicMapFlowSpectralMap (I := I) (M := M) q S x =
          fun z : EuclideanSpace ℝ {i // i ∈ S} =>
            harmonicMapFlowAdd (I := I) (M := M) q
              (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S z) x := by
      funext z
      rw [harmonicMapFlowSpectralMap_def]
    rw [hmap]
    exact hmd
  exact harmonicMapFlowSpectralVariation_line (I := I) (M := M) q S u v x hmdMap

noncomputable def harmonicMapFlowSpectralMassPointwise
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) (x : M) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
      EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  let L := harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x
  (ContinuousLinearMap.precomp ℝ L).comp
    ((q.inner
      (harmonicMapFlowSpectralMap (I := I) (M := M) q S x u)).comp L)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
@[simp] theorem harmonicMapFlowSpectralMassPointwise_apply
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v w : EuclideanSpace ℝ {i // i ∈ S}) (x : M) :
    harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x v w =
      q.inner
        (harmonicMapFlowSpectralMap (I := I) (M := M) q S x u)
        (harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x v)
        (harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x w) := by
  rfl

noncomputable def harmonicMapFlowSpectralMassOperator
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
      EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  ∫ x, harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralMassOperator_continuousOn
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R : ℝ)
    (hmass : ContinuousOn
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
        harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S p.1 p.2)
      (Metric.closedBall
        (0 : EuclideanSpace ℝ {i // i ∈ S}) R ×ˢ (Set.univ : Set M))) :
    ContinuousOn
      (harmonicMapFlowSpectralMassOperator (I := I) (M := M) q h S)
      (Metric.closedBall (0 : EuclideanSpace ℝ {i // i ∈ S}) R) := by
  let : NormedAddCommGroup
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
        EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
        EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace h
  have hfun : harmonicMapFlowSpectralMassOperator (I := I) (M := M) q h S =
      fun u => ∫ x, harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
    funext u
    rfl
  rw [hfun]
  exact integral_contOn_compact
    (riemannianVolumeMeasure (I := I) (M := M) h)
    (fun u x => harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x)
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ {i // i ∈ S}) R) hmass

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralMass_apply
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v w : EuclideanSpace ℝ {i // i ∈ S})
    (hint : Integrable
      (fun x => harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x)
      (riemannianVolumeMeasure (I := I) (M := M) h)) :
    harmonicMapFlowSpectralMassOperator (I := I) (M := M) q h S u v w =
      ∫ x, q.inner
          (harmonicMapFlowSpectralMap (I := I) (M := M) q S x u)
          (harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x v)
          (harmonicMapFlowSpectralVariation (I := I) (M := M) q S u x w)
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
  let : NormedAddCommGroup
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
        EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
        EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  have hintv : Integrable
      (fun x => harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x v)
      (riemannianVolumeMeasure (I := I) (M := M) h) :=
    (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) v).integrable_comp hint
  rw [harmonicMapFlowSpectralMassOperator, ContinuousLinearMap.integral_apply hint v,
    ContinuousLinearMap.integral_apply hintv w]
  simp only [harmonicMapFlowSpectralMassPointwise_apply]

omit [BoundarylessManifold I M] [ConnectedSpace M] in
theorem harmonicMapFlowSpectralMass_state
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u v w : EuclideanSpace ℝ {i // i ∈ S})
    (hmd : ∀ x : M,
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
        (fun z : EuclideanSpace ℝ {i // i ∈ S} =>
          harmonicMapFlowAdd (I := I) (M := M) q
            (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S z) x) u)
    (hint : Integrable
      (fun x => harmonicMapFlowSpectralMassPointwise (I := I) (M := M) q S u x)
      (riemannianVolumeMeasure (I := I) (M := M) h)) :
    harmonicMapFlowSpectralMassOperator (I := I) (M := M) q h S u v w =
      harmonicMapFlowStateMass (I := I) (M := M) q h
        (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S u)
        (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S v)
        (harmonicMapFlowSpectralInclusion (I := I) (M := M) q S w) := by
  rw [harmonicMapFlowSpectralMass_apply (I := I) (M := M) q h S u v w hint]
  unfold harmonicMapFlowStateMass
  apply integral_congr_ae
  filter_upwards with x
  rw [harmonicMapFlowSpectralVariation_state (I := I) (M := M) q S u v x (hmd x),
    harmonicMapFlowSpectralVariation_state (I := I) (M := M) q S u w x (hmd x),
    harmonicMapFlowSpectralMap_apply]

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
