import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BackgroundBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Product


noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def coverVerticalUnit (lambda : ℝ) (p : M × ℝ) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p :=
  (0, lambda⁻¹)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem ProductCurve.verticalUnit_eq_coverVerticalUnit (c : ProductCurve M)
    (lambda x t : ℝ) :
    c.verticalUnit (I := I) lambda x t = coverVerticalUnit (I := I) lambda (c.coverLift x t) :=
  rfl


omit [CompleteSpace E] in
theorem coverVerticalUnit_unit [T2Space M] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (p : M × ℝ) :
    (coverProductMetric g lambda hlambda).inner p
      (coverVerticalUnit lambda p) (coverVerticalUnit lambda p) = 1 := by
  rw [coverProductMetric_inner]
  change (g.inner p.1) 0 0 + lambda ^ 2 * lambda⁻¹ * lambda⁻¹ = 1
  simp only [map_zero, zero_add]
  field_simp [ne_of_gt hlambda]

private def verticalOrbit (q : M × DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle)
    (s : ℝ) : M × DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle :=
  (q.1, q.2 + (s : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem coverVerticalUnit_eq_orbit_derivative (A : QuotientProductAtlas I M)
    (lambda : ℝ) (p : M × ℝ) :
    letI := A.charts
    letI := A.smoothManifold
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p
        (0, (lambda⁻¹ : ℝ)) =
      mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (verticalOrbit (productCoverProjection p)) 0
        (lambda⁻¹ : ℝ) := by
  let := A.charts
  let := A.smoothManifold
  let line : ℝ → M × ℝ := fun s => (p.1, p.2 + s)
  have hline0 : line 0 = p := by simp [line]
  have hadd : HasFDerivAt (fun s : ℝ => p.2 + s) (ContinuousLinearMap.id ℝ ℝ) 0 := by
    simpa using! (hasFDerivAt_const p.2 (0 : ℝ)).add (hasFDerivAt_id (0 : ℝ))
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) line 0
      ((0 : ℝ →L[ℝ] TangentSpace I p.1).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) p.1 (0 : ℝ)).prodMk hadd.hasMFDerivAt
  have hpi : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      productCoverProjection (line 0) :=
    A.cover_smooth.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (0 : ℝ) hpi hline.mdifferentiableAt
  have heq : productCoverProjection ∘ line = verticalOrbit (productCoverProjection p) := by
    funext s
    simp only [Function.comp_apply, productCoverProjection, ContinuousMap.coe_mk, line,
      verticalOrbit, AddCircle.coe_add]
  rw [heq, hline0, hline.mfderiv] at hchain
  have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace (I.prod 𝓘(ℝ, ℝ))
      (productCoverProjection p) => L (lambda⁻¹ : ℝ)) hchain
  change mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
      (verticalOrbit (productCoverProjection p)) 0 (lambda⁻¹ : ℝ) =
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p
      (((0 : ℝ →L[ℝ] TangentSpace I p.1) (lambda⁻¹ : ℝ)),
        (ContinuousLinearMap.id ℝ ℝ) (lambda⁻¹ : ℝ)) at hv
  simpa only [zero_apply, ContinuousLinearMap.id_apply] using! hv.symm

variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_eq_iterCov {D : RealTimeInterval}
    (F : SolutionOn (I := I) (M := M) D) (t : ℝ) (m : ℕ) :
    nablaKRm04Field F t m = iterCov (F.base.metric t) 4 (metricRm04 (F.base.metric t)) m := by
  simpa only [SolutionFamily.rm04] using nablaKRm_eq_iterCov F t m


theorem coverVerticalUnit_smooth_parallel (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p : M × ℝ =>
        (⟨p, coverVerticalUnit lambda p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) ∧
    ∀ (p : M × ℝ) (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      (metricCov (coverProductMetric g lambda hlambda)) (coverVerticalUnit lambda) p v = 0 := by
  sorry

section QuotientVertical
variable (A : QuotientProductAtlas I M)

theorem coverVerticalUnit_lift_independent (lambda : ℝ)
    (p p' : M × ℝ) (hpp' : productCoverProjection p = productCoverProjection p') :
    letI := A.charts
    letI := A.smoothManifold
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p
        (coverVerticalUnit lambda p) =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p'
        (coverVerticalUnit lambda p') := by
  let _ := (inferInstance : FiniteDimensional ℝ E)
  let _ := (inferInstance : CompleteSpace E)
  let _ := (inferInstance : SigmaCompactSpace M)
  let _ := (inferInstance : T2Space M)
  let := A.charts
  let := A.smoothManifold
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p
      (0, (lambda⁻¹ : ℝ)) =
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p'
      (0, (lambda⁻¹ : ℝ))
  rw [coverVerticalUnit_eq_orbit_derivative, coverVerticalUnit_eq_orbit_derivative, hpp']

theorem exists_quotientVerticalUnit (lambda : ℝ) :
    letI := A.charts
    letI := A.smoothManifold
    ∃ U : ∀ q : M × Surgery.Topology.Circle, TangentSpace (I.prod 𝓘(ℝ, ℝ)) q,
      ∀ p : M × ℝ,
        mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p
          (coverVerticalUnit lambda p) = U (productCoverProjection p) := by
  let _ := (inferInstance : FiniteDimensional ℝ E)
  let _ := (inferInstance : CompleteSpace E)
  let _ := (inferInstance : SigmaCompactSpace M)
  let _ := (inferInstance : T2Space M)
  let := A.charts
  let := A.smoothManifold
  refine ⟨fun q => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (verticalOrbit q) 0
    (lambda⁻¹ : ℝ), ?_⟩
  exact coverVerticalUnit_eq_orbit_derivative A lambda


def quotientVerticalUnit (lambda : ℝ) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ q : M × Surgery.Topology.Circle, TangentSpace (I.prod 𝓘(ℝ, ℝ)) q :=
  (exists_quotientVerticalUnit A lambda).choose

theorem quotientVerticalUnit_cover (lambda : ℝ) (p : M × ℝ) :
    letI := A.charts
    letI := A.smoothManifold
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p
      (coverVerticalUnit lambda p) = quotientVerticalUnit A lambda (productCoverProjection p) :=
  (exists_quotientVerticalUnit A lambda).choose_spec p

theorem quotientVerticalUnit_smooth_unit_parallel [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q : M × Surgery.Topology.Circle =>
        (⟨q, quotientVerticalUnit A lambda q⟩ :
          TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × Surgery.Topology.Circle))) ∧
    (∀ q, (quotientProductMetric A g lambda hlambda).inner q
      (quotientVerticalUnit A lambda q) (quotientVerticalUnit A lambda q) = 1) ∧
    ∀ q (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q),
      (metricCov (quotientProductMetric A g lambda hlambda))
        (quotientVerticalUnit A lambda) q v = 0 := by
  sorry
end QuotientVertical

private noncomputable def scaleEuclidean (lambda : ℝ) (hlambda : 0 < lambda) :
    SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ :=
  DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2) (pow_pos hlambda 2)
    (DifferentialGeometry.euclideanMetric (E := ℝ))

private lemma scaleEuclidean_flat (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ (y : ℝ) (w : Fin 4 → TangentSpace 𝓘(ℝ, ℝ) y),
      metricRm04At (scaleEuclidean lambda hlambda) y w = 0 := by
  intro y w
  rw [← metricRm04_apply (I := 𝓘(ℝ, ℝ)) (M := ℝ) (g := scaleEuclidean lambda hlambda) (x := y)]
  rw [scaleEuclidean,
    DifferentialGeometry.Geometry.Curvature.metricRm_scale (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (c := lambda ^ 2) (hc := pow_pos hlambda 2)
      (g := DifferentialGeometry.euclideanMetric (E := ℝ)) y]
  rw [metricRm04_apply (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (g := DifferentialGeometry.euclideanMetric (E := ℝ)) (x := y)]
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04At_eq_zero_of_finrank_le_one
    (I := 𝓘(ℝ, ℝ)) (M := ℝ) (g := DifferentialGeometry.euclideanMetric (E := ℝ))
    (hE := by simp) y]
  simp

private lemma scaleEuclidean_ricci_flat (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ (y : ℝ) (w : Fin 2 → TangentSpace 𝓘(ℝ, ℝ) y),
      metricRicciAt (scaleEuclidean lambda hlambda) y w = 0 := by
  intro y w
  have hw : w = (vec2 (I := 𝓘(ℝ, ℝ)) (x := y) (w 0) (w 1) :
      Fin 2 → TangentSpace 𝓘(ℝ, ℝ) y) := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hw]
  rw [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (g := scaleEuclidean lambda hlambda)
      y (w 0) (w 1),
    DifferentialGeometry.Geometry.Curvature.ricciTensor_apply_basisSum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [DifferentialGeometry.Geometry.Curvature.riemannOp_eq_zero_of_finrank_le_one
    (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (cov := DifferentialGeometry.Geometry.Connection.LeviCivita (I := 𝓘(ℝ, ℝ))
      (scaleEuclidean lambda hlambda))
    (by simp) y _ _ _]
  simp

omit [SigmaCompactSpace M] in
theorem coverProduct_iterCov_rm04_apply [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ)
    (v : Fin (4 + m) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    iterCov (coverProductMetric g lambda hlambda) 4
        (metricRm04 (coverProductMetric g lambda hlambda)) m p v =
      iterCov g 4 (metricRm04 g) m p.1 (fun i => (v i).1) :=
  CheegerGromovCompactness.iterCov_prod_flat_apply (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)
    (g := g) (h := scaleEuclidean lambda hlambda)
    (scaleEuclidean_flat lambda hlambda) m p v

omit [SigmaCompactSpace M] in
theorem coverProduct_iterCov_ricci_apply [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ)
    (v : Fin (2 + m) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    iterCov (coverProductMetric g lambda hlambda) 2
        (metricRicci (coverProductMetric g lambda hlambda)) m p v =
      iterCov g 2 (metricRicci g) m p.1 (fun i => (v i).1) :=
  CheegerGromovCompactness.iterCov_ricci_prod_flat_apply (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)
    (g := g) (h := scaleEuclidean lambda hlambda)
    (scaleEuclidean_ricci_flat lambda hlambda) m p v


omit [SigmaCompactSpace M] in
theorem coverProduct_iterCov_rm04_mixed [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ)
    (v : Fin (4 + m) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p)
    (i : Fin (4 + m)) (hi : (v i).1 = 0) :
    iterCov (coverProductMetric g lambda hlambda) 4
      (metricRm04 (coverProductMetric g lambda hlambda)) m p v = 0 := by
  rw [coverProduct_iterCov_rm04_apply]
  exact (iterCov g 4 (metricRm04 g) m p.1).map_coord_zero i hi


omit [SigmaCompactSpace M] in
theorem coverProduct_iterCov_ricci_mixed [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ)
    (v : Fin (2 + m) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p)
    (i : Fin (2 + m)) (hi : (v i).1 = 0) :
    iterCov (coverProductMetric g lambda hlambda) 2
      (metricRicci (coverProductMetric g lambda hlambda)) m p v = 0 := by
  rw [coverProduct_iterCov_ricci_apply]
  exact (iterCov g 2 (metricRicci g) m p.1).map_coord_zero i hi

omit [SigmaCompactSpace M] in
theorem coverProduct_iterCov_normSq [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ) :
    normSq0S (coverProductMetric g lambda hlambda) p (4 + m)
        (iterCov (coverProductMetric g lambda hlambda) 4
          (metricRm04 (coverProductMetric g lambda hlambda)) m p) =
      normSq0S g p.1 (4 + m) (iterCov g 4 (metricRm04 g) m p.1) ∧
    normSq0S (coverProductMetric g lambda hlambda) p (2 + m)
        (iterCov (coverProductMetric g lambda hlambda) 2
          (metricRicci (coverProductMetric g lambda hlambda)) m p) =
      normSq0S g p.1 (2 + m) (iterCov g 2 (metricRicci g) m p.1) := by
  refine ⟨?_, ?_⟩
  · exact CheegerGromovCompactness.normSq0S_prod_of_forall_fst (I := I) (J := 𝓘(ℝ, ℝ))
      (M := M) (N := ℝ) g (scaleEuclidean lambda hlambda) p (4 + m) _ _
      (fun slots => coverProduct_iterCov_rm04_apply g lambda hlambda m p slots)
  · exact CheegerGromovCompactness.normSq0S_prod_of_forall_fst (I := I) (J := 𝓘(ℝ, ℝ))
      (M := M) (N := ℝ) g (scaleEuclidean lambda hlambda) p (2 + m) _ _
      (fun slots => coverProduct_iterCov_ricci_apply g lambda hlambda m p slots)

section QuotientCurvature
variable (A : QuotientProductAtlas I M)

theorem quotientProduct_iterCov_rm04_apply [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ)
    (v : Fin (4 + m) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    letI := A.charts
    letI := A.smoothManifold
    iterCov (quotientProductMetric A g lambda hlambda) 4
        (metricRm04 (quotientProductMetric A g lambda hlambda)) m (productCoverProjection p)
        (fun i => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
          productCoverProjection p (v i)) =
      iterCov g 4 (metricRm04 g) m p.1 (fun i => (v i).1) := by
  sorry

theorem quotientProduct_iterCov_ricci_apply [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (p : M × ℝ)
    (v : Fin (2 + m) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    letI := A.charts
    letI := A.smoothManifold
    iterCov (quotientProductMetric A g lambda hlambda) 2
        (metricRicci (quotientProductMetric A g lambda hlambda)) m (productCoverProjection p)
        (fun i => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
          productCoverProjection p (v i)) =
      iterCov g 2 (metricRicci g) m p.1 (fun i => (v i).1) := by
  sorry

theorem quotientProduct_iterCov_normSq [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (m : ℕ) (q : M × Surgery.Topology.Circle) :
    letI := A.charts
    letI := A.smoothManifold
    normSq0S (quotientProductMetric A g lambda hlambda) q (4 + m)
        (iterCov (quotientProductMetric A g lambda hlambda) 4
          (metricRm04 (quotientProductMetric A g lambda hlambda)) m q) =
      normSq0S g q.1 (4 + m) (iterCov g 4 (metricRm04 g) m q.1) ∧
    normSq0S (quotientProductMetric A g lambda hlambda) q (2 + m)
        (iterCov (quotientProductMetric A g lambda hlambda) 2
          (metricRicci (quotientProductMetric A g lambda hlambda)) m q) =
      normSq0S g q.1 (2 + m) (iterCov g 2 (metricRicci g) m q.1) := by
  sorry

theorem quotientProduct_ricciBackground_C [I.Boundaryless] {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∃ Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D a b,
      Bhat.family = quotientProductFamily A B.family lambda hlambda ∧
      Bhat.B₀ = B.B₀ ∧ Bhat.B₁ = B.B₁ ∧ Bhat.B₂ = B.B₂ ∧ Bhat.C = B.C := by
  let := A.charts
  let := A.smoothManifold
  obtain ⟨Bhat, hf, h0, h1, h2⟩ := quotientProduct_ricciBackground A B lambda hlambda
  exact ⟨Bhat, hf, h0, h1, h2, by simp only [RicciBackground.C, h0, h1, h2]⟩

theorem rfs_csf_ramp_geometry [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (F : SolutionOn (I := I) (M := M) D)
    (hF : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F)
    (hab : a < b) (hreg : Icc a b ⊆ D.regular) :
    ∃ B : RicciBackground (I := I) (M := M) D a b, B.family = F.base ∧
      ∀ lambda : ℝ, ∀ hlambda : 0 < lambda,
        letI := A.charts
        letI := A.smoothManifold
        ∃ Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D a b,
          Bhat.family = quotientProductFamily A F.base lambda hlambda ∧
          Bhat.B₀ = B.B₀ ∧ Bhat.B₁ = B.B₁ ∧ Bhat.B₂ = B.B₂ ∧ Bhat.C = B.C := by
  obtain ⟨B, hB, _⟩ := rfs_csf_background F hF hab hreg
  refine ⟨B, hB, ?_⟩
  intro lambda hlambda
  simpa only [hB] using quotientProduct_ricciBackground_C A B lambda hlambda
end QuotientCurvature

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
