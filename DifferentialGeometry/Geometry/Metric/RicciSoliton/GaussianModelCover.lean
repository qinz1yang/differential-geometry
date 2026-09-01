import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverGaussian

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private noncomputable def identityTrivialization (X : Type*) [TopologicalSpace X] :
    Trivialization Unit (id : X → X) :=
  { toOpenPartialHomeomorph := (Homeomorph.prodUnique X Unit).symm.toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    proj_toFun := by intro p hp; rfl }

private theorem identity_isCoveringMap (X : Type*) [TopologicalSpace X] :
    IsCoveringMap (id : X → X) := by
  refine IsCoveringMap.mk (f := (id : X → X)) (fun _ : X => Unit)
    (fun _ => identityTrivialization X) ?_
  intro x
  exact Set.mem_univ x

omit [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem diffeomorph_isCoveringMap
  (Φ : E ≃ₘ⟮modelWithCornersSelf Real E, I⟯ M) :
    IsCoveringMap (Φ : E → M) := by
  have hcomp := (identity_isCoveringMap E).homeomorph_comp Φ.toHomeomorph
  change IsCoveringMap (Φ : E → M) at hcomp
  exact hcomp

theorem exists_solitonModelCovering_of_isGaussianGradientRicciSoliton
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hGaussian : isGaussianGradientRicciSoliton (I := I) (E := E) g f 1) :
    ∃ cover : E → M,
      solitonModelCovering (euclideanMetric (E := E))
        (gaussianPotential (E := E)) g f cover := by
  rcases hGaussian with ⟨_hσ, Ψ, b, hmetric, hpotential⟩
  let fShift : C^∞⟮I, M; Real⟯ :=
    f + ContMDiffMap.const (I := I)
      (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) b
  have hmetric' : Diffeomorph.pullbackMetricCross euclideanMetric Ψ = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hxy := Diffeomorph.pullbackMetricCross_inner euclideanMetric Ψ x v w
    rw [hmetric] at hxy
    rw [Diffeomorph.pullbackMetricCross_inner]
    simpa only [scaleMetric_inner, one_mul] using hxy.symm
  have hpull : localPullMetric g Ψ.symm Ψ.symm.isLocalDiffeomorph =
      euclideanMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner]
    have hxy := Diffeomorph.pullbackMetricCross_inner g Ψ.symm x v w
    rw [Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hmetric'] at hxy
    exact hxy.symm
  have hshift : normalizedGradientRicciSoliton (I := I) g fShift := by
    apply normalizedGradientRicciSoliton_of_surjective_localPullMetric
      (I := modelWithCornersSelf Real E) (J := I)
      (h := euclideanMetric (E := E))
      (Fpot := gaussianPotential (E := E))
      (g := g) (f := fShift) (Phi := Ψ.symm)
      normalizedGradientRicciSoliton_gaussian h.1
      Ψ.symm.isLocalDiffeomorph Ψ.symm.surjective
    · exact hpull
    · intro x
      have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q (Ψ.symm x)) hpotential
      change f (Ψ.symm x) + b = gaussianPotential (Ψ (Ψ.symm x)) at hx
      rw [Ψ.apply_symm_apply] at hx
      exact hx.symm
  let nonemptyM : Nonempty M := ⟨Ψ.symm 0⟩
  have hb : b = 0 :=
    @normalizedGradientRicciSoliton_add_const_unique E _ _ _ H _ I _ M _ _ _ _ _
      nonemptyM g f b h hshift
  let cover : E → M := Ψ.symm
  refine ⟨cover, ?_⟩
  refine ⟨normalizedGradientRicciSoliton_gaussian, h,
    Ψ.symm.isLocalDiffeomorph, Ψ.symm.surjective,
    diffeomorph_isCoveringMap Ψ.symm, ?_, ?_⟩
  · intro x v w
    have hxy := Diffeomorph.pullbackMetricCross_inner g Ψ.symm x v w
    rw [Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hmetric'] at hxy
    simpa only [cover] using hxy
  · intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q (Ψ.symm x)) hpotential
    change f (Ψ.symm x) + b = gaussianPotential (Ψ (Ψ.symm x)) at hx
    rw [Ψ.apply_symm_apply, hb, add_zero] at hx
    exact hx.symm

end DifferentialGeometry.Geometry
