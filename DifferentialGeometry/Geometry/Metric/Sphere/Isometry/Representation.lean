import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Rigidity
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Extension
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Analysis.Normed.Module.Connected

open DifferentialGeometry.Geometry.Curvature


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

theorem exists_linearIsometryEquiv_of_localPullMetric_roundMetric_eq
    (hn : 0 < n)
    {f : sphere (0 : E) 1 → sphere (0 : E) 1}
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hmetric : localPullMetric (roundMetric (E := E) (n := n)) f hf = roundMetric) :
    ∃ e : E ≃ₗᵢ[ℝ] E,
      (sphereDiffeo (n := n) e : sphere (0 : E) 1 → sphere (0 : E) 1) = f := by
  classical
  have hfr : 1 < finrank ℝ E := by
    rw [show finrank ℝ E = n + 1 from Fact.out]
    exact Nat.succ_lt_succ hn
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (lt_trans Nat.zero_lt_one hfr)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  let : PreconnectedSpace (sphere (0 : E) 1) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank hfr) (0 : E) 1)
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).2 zero_le_one
  let p : sphere (0 : E) 1 := ⟨x, hx⟩
  have hpres (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
      (roundMetric (E := E) (n := n)).inner x v w =
        (roundMetric (E := E) (n := n)).inner (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) := by
    have h := congrArg (fun g : SmoothRiemannianMetric (𝓡 n) (sphere (0 : E) 1) =>
      g.inner x v w) hmetric
    rw [localPullMetric_inner] at h
    exact h.symm
  let L : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) (f p) :=
    hf.mfderivToContinuousLinearEquiv (by decide) p
  have hL : ∀ v w,
      (roundMetric (E := E) (n := n)).inner (f p) (L v) (L w) =
        (roundMetric (E := E) (n := n)).inner p v w := by
    intro v w
    exact (hpres p v w).symm
  obtain ⟨e, hep, hde⟩ := ambient_iso_of_tan (E := E) (n := n) p (f p) L hL
  refine ⟨e, ?_⟩
  apply Riemannian.localIso_rigid
    (roundMetric (E := E) (n := n)) (roundMetric (E := E) (n := n))
    (sphereDiffeo (n := n) e).isLocalDiffeomorph hf
    (fun x v w => (roundInner_sphereDiffeo e x v w).symm) hpres p
  · apply Subtype.ext
    simpa only [sphereDiffeo_coe] using hep
  · ext v
    with_unfolding_all exact hde v

theorem orth_rep_of_iso
    {Γ : Type*} [Monoid Γ]
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
  have hex (γ : Γ) :
      ∃ e : E ≃ₗᵢ[ℝ] E, sphereDiffeo (n := n) e = φ γ := by
    obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_localPullMetric_roundMetric_eq
      hn (φ γ).isLocalDiffeomorph (by
        apply SmoothRiemannianMetric.ext_inner
        intro x v w
        rw [localPullMetric_inner]
        exact (hiso γ x v w).symm)
    exact ⟨e, Diffeomorph.ext fun x => congrFun he x⟩
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
