import DifferentialGeometry.Topology.ProjectiveSpace.CylinderProjectiveSlice
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.CompactEmbedding
import DifferentialGeometry.Topology.ProjectiveSpace.SmoothNonembedding
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold

local notation "CylinderI" => ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ)

section

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''} [I.Boundaryless] [K.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold K n P] {f : M → N}

private theorem isSmoothEmbedding_diffeomorph_comp
    (hf : IsSmoothEmbedding I J n f) (d : Diffeomorph J K N P n) (hn : n ≠ 0) :
    IsSmoothEmbedding I K n (d ∘ f) := by
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    hn (d.contMDiff.comp hf.contMDiff) ?_, d.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩
  intro x
  rw [mfderiv_comp x (d.contMDiff.mdifferentiableAt hn) (hf.contMDiff.mdifferentiableAt hn)]
  exact ((d.isLocalDiffeomorph (f x)).mfderivToContinuousLinearEquiv hn).injective.comp
    ((hf.isImmersion.isImmersionAt x).mfderiv_injective hn)


end

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth

include Phi

theorem pointedLimit_not_projectiveSmoothEmbedding
    (hEuclidean : ∀ k : ℕ, (X.obj k).M ≃ₘ⟮I, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)) :
    ∀ e : SphereAntipodalQuotient → L.M, ¬ IsSmoothEmbedding (𝓡 2) I ∞ e := by
  intro e he
  obtain ⟨k0, hk0⟩ := pointedMaps_eventually_compactSmoothEmbedding Phi e he
  obtain ⟨f, hf, _, hfeq⟩ := hk0 k0 le_rfl
  let d := hEuclidean (subseq k0)
  have hcomp : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (d ∘ f) :=
    isSmoothEmbedding_diffeomorph_comp hf d (by decide)
  apply SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree
    (fun x => d (Phi.map k0 (e x)))
  have hmaps : (fun x => d (Phi.map k0 (e x))) = d ∘ f := by
    funext x
    exact congrArg d (hfeq x).symm
  exact hmaps ▸ hcomp

theorem pointedLimit_not_nontrivialCylinderQuotient_diffeomorph
    [FiniteDimensional ℝ E] [I.Boundaryless]
    (hEuclidean : ∀ k : ℕ, (X.obj k).M ≃ₘ⟮I, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)) :
    ¬ Nonempty ((SphereAntipodalQuotient × ℝ) ≃ₘ⟮CylinderI, I⟯ L.M) ∧
      ¬ Nonempty (CylinderDiagonalQuotient ≃ₘ⟮CylinderI, I⟯ L.M) := by
  have hlimit := pointedLimit_not_projectiveSmoothEmbedding Phi hEuclidean
  constructor
  · rintro ⟨d⟩
    apply hlimit (d ∘ SphereAntipodalQuotient.zeroSlice)
    exact isSmoothEmbedding_diffeomorph_comp
      SphereAntipodalQuotient.isSmoothEmbedding_zeroSlice d (by decide)
  · rintro ⟨d⟩
    apply hlimit (d ∘ CylinderDiagonalQuotient.projectiveSlice)
    exact isSmoothEmbedding_diffeomorph_comp
      CylinderDiagonalQuotient.isSmoothEmbedding_projectiveSlice d (by decide)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
