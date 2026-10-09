import DifferentialGeometry.Topology.Manifold.ActualNormalRelationClosed
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The literal projection of the same actual bounded normal disc is proper. -/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]

def actualNormalDiscProjection (k : ℕ) (Z : Set H) [ChartedSpace (Fin k → ℝ) Z]
    (V : Set Z) (ρ : ℝ) : actualNormalDisc k Z V ρ → V :=
  fun yn => ⟨yn.val.1, yn.property.1⟩

def actualNormalDiscCompactCoordinates (V : Set Z) (ρ : ℝ) :
    actualNormalDisc k Z V ρ ≃ₜ
      {yn : V × closedBall (0 : H) ρ |
        (yn.2 : H) ∈ (actualZeroSetTangentSpace k Z (yn.1 : Z))ᗮ} where
  toFun yn := ⟨(⟨yn.val.1, yn.property.1⟩,
    ⟨yn.val.2, by simpa only [mem_closedBall, dist_zero_right] using yn.property.2.2⟩),
      yn.property.2.1⟩
  invFun yn := ⟨((yn.val.1 : Z), (yn.val.2 : H)), yn.val.1.property, yn.property,
    by simpa only [mem_closedBall, dist_zero_right] using yn.val.2.property⟩
  left_inv yn := by rfl
  right_inv yn := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isProperMap_actualNormalDiscProjection [FiniteDimensional ℝ H]
    [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z]
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (V : Set Z) (ρ : ℝ) : IsProperMap (actualNormalDiscProjection k Z V ρ) := by
  have hc : IsClosed {yn : V × closedBall (0 : H) ρ |
      (yn.2 : H) ∈ (actualZeroSetTangentSpace k Z (yn.1 : Z))ᗮ} :=
    (isClosed_actualNormalRelation hemb).preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hp := (isProperMap_fst_of_compactSpace (X := V) (Y := closedBall (0 : H) ρ)).comp
    hc.isProperMap_subtypeVal
  exact hp.comp (actualNormalDiscCompactCoordinates V ρ).isProperMap

theorem actualNormalDiscProjection_surjective (V : Set Z) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Function.Surjective (actualNormalDiscProjection k Z V ρ) := by
  intro y
  exact ⟨⟨((y : Z), 0), y.property, Submodule.zero_mem _, by simpa only [norm_zero] using hρ⟩, rfl⟩

def nearestDiscProjection (Ω : TopologicalSpace.Opens H) (p : Ω → Z)
    (V : Set Z) (ρ : ℝ) : nearestDiscDomain Ω Z p V ρ → V :=
  fun z => ⟨p z.val, z.property.1⟩

theorem isProperMap_nearestDiscProjection [FiniteDimensional ℝ H]
    [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z]
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (Ω : TopologicalSpace.Opens H) (p : Ω → Z) (V : Set Z) (ρ : ℝ)
    (e : nearestDiscDomain Ω Z p V ρ ≃ₜ actualNormalDisc k Z V ρ)
    (he : ∀ z, (e z : Z × H) = nearestResidualCoordinates Ω Z p z) :
    IsProperMap (nearestDiscProjection Ω p V ρ) := by
  have heq : actualNormalDiscProjection k Z V ρ ∘ e = nearestDiscProjection Ω p V ρ := by
    funext z
    apply Subtype.ext
    exact congrArg Prod.fst (he z)
  rw [← heq]
  exact (isProperMap_actualNormalDiscProjection hemb V ρ).comp e.isProperMap

theorem nearestDiscProjection_surjective
    (Ω : TopologicalSpace.Opens H) (p : Ω → Z) (V : Set Z) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (e : nearestDiscDomain Ω Z p V ρ ≃ₜ actualNormalDisc k Z V ρ)
    (he : ∀ z, (e z : Z × H) = nearestResidualCoordinates Ω Z p z) :
    Function.Surjective (nearestDiscProjection Ω p V ρ) := by
  intro y
  obtain ⟨yn, hyn⟩ := actualNormalDiscProjection_surjective (k := k) V ρ hρ y
  refine ⟨e.symm yn, ?_⟩
  apply Subtype.ext
  have hh := congrArg Prod.fst (he (e.symm yn))
  rw [e.apply_symm_apply] at hh
  exact hh.symm.trans (congrArg Subtype.val hyn)

end GC.MetricGeometry
