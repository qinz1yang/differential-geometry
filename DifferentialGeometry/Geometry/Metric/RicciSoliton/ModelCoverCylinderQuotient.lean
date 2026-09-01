import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

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

end DifferentialGeometry.Geometry
