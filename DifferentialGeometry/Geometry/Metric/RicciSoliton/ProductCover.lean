import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderProduct
import DifferentialGeometry.Geometry.Metric.RicciSoliton.UniversalCover
import DifferentialGeometry.Geometry.Metric.Product.Completeness

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [Riemannian.Topology.SemilocallySimplyConnectedSpace M] [Inhabited M]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace Real E₂]
  [FiniteDimensional Real E₂]
variable {H₂ : Type*} [TopologicalSpace H₂]
variable {J : ModelWithCorners Real E₂ H₂} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N] [SimplyConnectedSpace N]

theorem exists_roundThreeCylinder_solitonModelCovering_of_product_diffeomorph
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {k : SmoothRiemannianMetric J N}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hk : RiemannianMetricComplete (I := J) k)
    (Phi : (N × Real) ≃ₘ⟮J.prod 𝓘(Real, Real), I⟯
      Riemannian.Topology.UniversalCover M)
    (hpull : Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g) Phi =
      k.prod (euclideanMetric (E := Real)))
    (hdim : Module.finrank Real E₂ = 2)
    (hpositive : ∃ x : N, 0 < metricScalarAt (I := J) k x) :
    ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential g f cover := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let flift : C^∞⟮I, Riemannian.Topology.UniversalCover M; Real⟯ :=
    f.comp ⟨proj, proj_contMDiff (I := I)⟩
  have hlift : normalizedGradientRicciSoliton (I := I)
      (liftedMetric (I := I) g) flift := normalizedGradientRicciSoliton_liftedMetric h
  let u := flift.comp Phi.toContMDiffMap
  have hpullSymm : localPullMetric (k.prod (euclideanMetric (E := Real)))
      Phi.symm Phi.symm.isLocalDiffeomorph = liftedMetric (I := I) g := by
    rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    exact Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr hpull
  have hkprod : RiemannianMetricComplete (I := J.prod 𝓘(Real, Real))
      (k.prod (euclideanMetric (E := Real))) :=
    RiemannianMetricComplete.prod hk euclideanMetric_complete
  have hprod : normalizedGradientRicciSoliton
      (I := J.prod 𝓘(Real, Real)) (k.prod (euclideanMetric (E := Real))) u := by
    apply normalizedGradientRicciSoliton_of_surjective_localPullMetric
      hlift hkprod Phi.symm.isLocalDiffeomorph Phi.symm.surjective hpullSymm
    intro x
    change flift x = flift (Phi (Phi.symm x))
    rw [Phi.apply_symm_apply]
  obtain ⟨Psi, hPsi⟩ :=
    exists_roundThreeCylinder_solitonModelCovering_of_prod_real_line_of_finrank_eq_two_of_scalar_pos
      (E := E₂) (I := J) (M := N) (g := k) (u := u) hprod hdim hpositive
  have hPhi : solitonModelCovering (k.prod (euclideanMetric (E := Real))) u
      (liftedMetric (I := I) g) flift Phi := by
    refine ⟨hprod, hlift, Phi.isLocalDiffeomorph, Phi.surjective, ?_, ?_, ?_⟩
    · exact (solitonModelCovering_isCoveringMap
        (solitonModelCovering_refl hlift)).comp_homeomorph Phi.toHomeomorph
    · intro x v w
      rw [← hpull, Diffeomorph.pullbackMetricCross_inner]
    · intro x
      rfl
  have hprojSurj : Function.Surjective
      (proj : Riemannian.Topology.UniversalCover M → M) := by
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath default x)⟩, rfl⟩
  have hproj : solitonModelCovering (liftedMetric (I := I) g) flift g f
      (proj : Riemannian.Topology.UniversalCover M → M) := by
    refine ⟨hlift, h, proj_localDiffeo (I := I), hprojSurj, proj_isCoveringMap, ?_, ?_⟩
    · intro x v w
      rw [liftedMetric_eq_localPullMetric, localPullMetric_inner]
    · intro x
      rfl
  refine ⟨proj ∘ Phi ∘ Psi, ?_⟩
  exact solitonModelCovering_comp_diffeomorph Psi hPsi
    (solitonModelCovering_comp_diffeomorph Phi hPhi hproj)

end DifferentialGeometry.Geometry
