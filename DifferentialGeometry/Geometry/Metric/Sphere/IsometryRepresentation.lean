import DifferentialGeometry.Geometry.Metric.LocalIsometryRigidity
import DifferentialGeometry.Geometry.Metric.Sphere.IsometryExtension
import DifferentialGeometry.Geometry.Topology.FiberBundleT2
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Orthogonal representations of round-sphere actions

A group action by round-metric-preserving diffeomorphisms of a positive-dimensional
unit sphere is induced by a representation into the ambient orthogonal group.
-/

noncomputable section

open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

private theorem sphereDiffeo_one :
    sphereDiffeo (E := E) (n := n) (1 : E ≃ₗᵢ[ℝ] E) =
      Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞ := by
  apply Diffeomorph.ext
  intro x
  apply Subtype.ext
  rfl

private theorem sphereDiffeo_mul (e f : E ≃ₗᵢ[ℝ] E) :
    sphereDiffeo (n := n) (e * f) =
      (sphereDiffeo (n := n) f).trans (sphereDiffeo (n := n) e) := by
  apply Diffeomorph.ext
  intro x
  apply Subtype.ext
  rfl

/-- A group-indexed family of round-metric-preserving sphere diffeomorphisms
which obeys the action laws is induced by a representation into the ambient
orthogonal group. -/
theorem orth_rep_of_iso
    {Γ : Type*} [Monoid Γ]
    (p : sphere (0 : E) 1)
    (φ : Γ → sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1)
    (hn : 0 < n)
    (hone : ∀ x, φ 1 x = x)
    (hmul : ∀ γ δ x, φ (γ * δ) x = φ γ (φ δ x))
    (hiso : ∀ γ x (v w : TangentSpace (𝓡 n) x),
      (roundMetric (E := E) (n := n)).inner x v w =
        (roundMetric (E := E) (n := n)).inner (φ γ x)
          (mfderiv (𝓡 n) (𝓡 n) (φ γ) x v)
          (mfderiv (𝓡 n) (𝓡 n) (φ γ) x w)) :
    ∃ ρ : Γ →* (E ≃ₗᵢ[ℝ] E),
      ∀ γ, sphereDiffeo (n := n) (ρ γ) = φ γ := by
  classical
  have hfr : 1 < finrank ℝ E := by
    rw [show finrank ℝ E = n + 1 from Fact.out]
    exact Nat.succ_lt_succ hn
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  letI : PreconnectedSpace (sphere (0 : E) 1) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank hfr) (0 : E) 1)
  have hex (γ : Γ) :
      ∃ e : E ≃ₗᵢ[ℝ] E, sphereDiffeo (n := n) e = φ γ := by
    let L : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) (φ γ p) :=
      (φ γ).mfderivToContinuousLinearEquiv (by decide) p
    have hL : ∀ v w,
        (roundMetric (E := E) (n := n)).inner (φ γ p) (L v) (L w) =
          (roundMetric (E := E) (n := n)).inner p v w := by
      intro v w
      exact (hiso γ p v w).symm
    obtain ⟨e, hep, hde⟩ :=
      ambient_iso_of_tan (E := E) (n := n) p (φ γ p) L hL
    refine ⟨e, ?_⟩
    have hfun :
        (fun x : sphere (0 : E) 1 => sphereDiffeo (n := n) e x) =
          fun x => φ γ x := by
      apply Riemannian.localIso_rigid
        (roundMetric (E := E) (n := n))
        (roundMetric (E := E) (n := n))
        (sphereDiffeo (n := n) e).isLocalDiffeomorph
        (φ γ).isLocalDiffeomorph
        (fun x v w => (roundInner_sphereDiffeo e x v w).symm)
        (hiso γ)
        p
      · apply Subtype.ext
        simpa only [sphereDiffeo_coe] using hep
      · ext v
        simpa only [L, Diffeomorph.mfderivToContinuousLinearEquiv_coe] using hde v
    apply Diffeomorph.ext
    exact congrFun hfun
  choose e he using hex
  let ρ : Γ →* (E ≃ₗᵢ[ℝ] E) :=
    { toFun := e
      map_one' := by
        apply sphereDiffeo_inj (E := E) (n := n)
        rw [he]
        apply Diffeomorph.ext
        intro x
        rw [hone]
        exact DFunLike.congr_fun sphereDiffeo_one x
      map_mul' γ δ := by
        apply sphereDiffeo_inj (E := E) (n := n)
        rw [sphereDiffeo_mul, he, he, he]
        apply Diffeomorph.ext
        exact hmul γ δ }
  exact ⟨ρ, he⟩

end Geometry
end DifferentialGeometry
