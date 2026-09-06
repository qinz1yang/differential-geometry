import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

theorem solitonModelCovering_cylinderAntipodalQuotient :
    solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential cylinderAntipodalQuotientMetric
      cylinderAntipodalQuotientPotential cylinderAntipodalQuotientMap := by
  refine ⟨normalizedGradientRicciSoliton_roundThreeCylinder,
    normalizedGradientRicciSoliton_cylinderAntipodalQuotient,
    cylinderAntipodalQuotientMap_isLocalDiffeomorph,
    cylinderAntipodalQuotientMap_surjective,
    cylinderAntipodalQuotientMap_isCoveringMap, ?_, ?_⟩
  · intro x v w
    rw [← localPullMetric_cylinderAntipodalQuotientMetric,
      localPullMetric_inner]
  · intro x
    exact (cylinderAntipodalQuotientPotential_apply x).symm

theorem solitonModelCovering_cylinderDiagonalQuotient :
    solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential cylinderDiagonalQuotientMetric
      cylinderDiagonalQuotientPotential cylinderDiagonalQuotientMap := by
  refine ⟨normalizedGradientRicciSoliton_roundThreeCylinder,
    normalizedGradientRicciSoliton_cylinderDiagonalQuotient,
    cylinderDiagonalQuotientMap_isLocalDiffeomorph,
    cylinderDiagonalQuotientMap_surjective,
    cylinderDiagonalQuotientMap_isCoveringMap, ?_, ?_⟩
  · intro x v w
    rw [← localPullMetric_cylinderDiagonalQuotientMetric,
      localPullMetric_inner]
  · intro x
    exact (cylinderDiagonalQuotientPotential_apply x).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real E G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]

theorem noncompactSpace_of_solitonModelCovering_roundThreeCylinder
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → N}
    (hpi : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cover) :
    NoncompactSpace N := by
  refine not_compactSpace_iff.mp ?_
  intro hcompact
  let _ : CompactSpace N := hcompact
  obtain ⟨C, hC⟩ := (isCompact_range f.contMDiff.continuous).bddAbove
  let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
  have hle : f (cover (y, 2 * (|C| + 1))) ≤ C := hC ⟨_, rfl⟩
  rw [← solitonModelCovering_potential hpi,
    roundThreeCylinderShrinkerPotential_apply] at hle
  nlinarith [abs_nonneg C, le_abs_self C]

theorem solitonModelCovering_roundThreeCylinder_deckGroup_eq_trichotomy
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → N}
    (hpi : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cover) :
    (coveringDeckGroup cover = ⊥ ∧
      coveringDeckGroup cover ≠ cylinderAntipodalGroup ∧
      coveringDeckGroup cover ≠ cylinderDiagonalGroup) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      coveringDeckGroup cover ≠ ⊥ ∧
      coveringDeckGroup cover ≠ cylinderDiagonalGroup) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      coveringDeckGroup cover ≠ ⊥ ∧
      coveringDeckGroup cover ≠ cylinderAntipodalGroup) := by
  have hrank :
      1 < Module.rank Real (EuclideanSpace Real (Fin 3)) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    norm_num
  let : PreconnectedSpace
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere hrank 0 1)
  apply roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy
  · intro gamma
    let Phi := coveringDeckGroupDiffeomorph
      (solitonModelCovering_isLocalDiffeomorph hpi) gamma
    have hpreserves := solitonModelCovering_deckGroup_preserves hpi gamma
    refine ⟨Phi, rfl, ?_, ?_⟩
    · rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
      exact hpreserves.1
    · intro x
      change roundThreeCylinderShrinkerPotential (gamma.1 x) =
        roundThreeCylinderShrinkerPotential x
      exact congrArg
        (fun Fpot : C^∞⟮(𝓡 2).prod 𝓘(Real, Real),
          Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real; Real⟯ => Fpot x)
        hpreserves.2
  · intro gamma x hfix
    exact coveringDeckGroup_eq_one_of_apply_eq
      (solitonModelCovering_isCoveringMap hpi) gamma x hfix

theorem solitonModelCovering_roundThreeCylinder_target_homeomorph_trichotomy_of_isQuotientCoveringMap
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → N}
    (hπ : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f cover)
    (hquotient : IsQuotientCoveringMap cover (coveringDeckGroup cover)) :
    (coveringDeckGroup cover = ⊥ ∧
      ∃ e : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real ≃ₜ N,
        ∀ x, e x = cover x) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : RealProjectivePlane × Real ≃ₜ N,
        ∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₜ N,
        ∀ x, e (cylinderDiagonalQuotientHomeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) := by
  rcases solitonModelCovering_roundThreeCylinder_deckGroup_eq_trichotomy hπ with
    htrivial | hantipodal | hdiagonal
  · left
    have hinjective : Function.Injective cover := by
      intro x y hxy
      obtain ⟨gamma, hgamma⟩ := hquotient.apply_eq_iff_mem_orbit.mp hxy
      have hmem : gamma.1 ∈ (⊥ : Subgroup
          (Equiv.Perm
            (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
        rw [← htrivial.1]
        exact gamma.property
      have hone : gamma.1 = 1 := by
        simpa only [Subgroup.mem_bot] using hmem
      change gamma.1 y = x at hgamma
      rw [hone] at hgamma
      exact hgamma.symm
    let e : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real ≃ₜ N :=
      ((solitonModelCovering_isLocalDiffeomorph hπ).diffeomorphOfBijective
        ⟨hinjective, solitonModelCovering_surjective hπ⟩).toHomeomorph
    exact ⟨htrivial.1, e, fun _ => rfl⟩
  · right
    left
    have hquotient' : IsQuotientCoveringMap cover cylinderAntipodalGroup :=
      (IsQuotientCoveringMap.subgroup_congr
        cover (Equiv.Perm
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))
        (coveringDeckGroup cover) cylinderAntipodalGroup
        hantipodal.1).mp hquotient
    let e : RealProjectivePlane × Real ≃ₜ N :=
      cylinderAntipodalQuotientHomeomorph.symm.trans
        hquotient'.orbitRelQuotientHomeomorph
    refine ⟨hantipodal.1, e, fun x => ?_⟩
    change hquotient'.orbitRelQuotientHomeomorph
      (cylinderAntipodalQuotientHomeomorph.symm
        (realProjectivePlaneQuotientMap x.1, x.2)) = cover x
    rw [cylinderAntipodalQuotientHomeomorph_symm_apply]
    exact hquotient'.orbitRelQuotientHomeomorph_apply x
  · right
    right
    have hquotient' : IsQuotientCoveringMap cover cylinderDiagonalGroup :=
      (IsQuotientCoveringMap.subgroup_congr
        cover (Equiv.Perm
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))
        (coveringDeckGroup cover) cylinderDiagonalGroup
        hdiagonal.1).mp hquotient
    let e : PuncturedRealProjectiveThreeSpace ≃ₜ N :=
      cylinderDiagonalQuotientHomeomorph.symm.trans
        hquotient'.orbitRelQuotientHomeomorph
    refine ⟨hdiagonal.1, e, fun x => ?_⟩
    change hquotient'.orbitRelQuotientHomeomorph
      (cylinderDiagonalQuotientHomeomorph.symm
        (cylinderDiagonalQuotientHomeomorph
          (cylinderDiagonalQuotientMap x))) = cover x
    rw [Homeomorph.symm_apply_apply]
    exact hquotient'.orbitRelQuotientHomeomorph_apply x

end DifferentialGeometry.Geometry
