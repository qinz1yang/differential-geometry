import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Mathlib.LinearAlgebra.Eigenspace.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

omit [BoundarylessManifold I M] in
private theorem restrict_inner (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpen U).inner x v w = g.inner (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  rw [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

theorem least_ricci_eigenpair_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (μ : ℝ) (w : TangentSpace I x)
    (hunit : (g.restrictOpen U).inner x w w = 1)
    (heigen : ricciSharp (g.restrictOpen U) x w = μ • w)
    (hmin : ∀ z, (g.restrictOpen U).inner x z z = 1 →
      μ ≤ ricciTensor (g.restrictOpen U) x z z)
    (hsimple : Module.End.eigenspace
      (ricciSharp (g.restrictOpen U) x).toLinearMap μ =
        Submodule.span ℝ {w}) :
    let u := mfderiv I I (Subtype.val : U → M) x w
    g.inner (x : M) u u = 1 ∧ ricciSharp g (x : M) u = μ • u ∧
      (∀ z, g.inner (x : M) z z = 1 → μ ≤ ricciTensor g (x : M) z z) ∧
      Module.End.eigenspace (ricciSharp g (x : M)).toLinearMap μ = Submodule.span ℝ {u} := by
  let e : TangentSpace I x ≃L[ℝ] TangentSpace I (x : M) := ContinuousLinearEquiv.refl ℝ E
  have he (z : TangentSpace I x) : e z = mfderiv I I (Subtype.val : U → M) x z := by
    rw [mfderiv_subtype_val]
    rfl
  have hi (z : TangentSpace I x) :
      e (ricciSharp (g.restrictOpen U) x z) = ricciSharp g (x : M) (e z) := by
    simpa only [he] using ricciSharp_restrictOpen g U x z
  have heu : ricciSharp g (x : M) (e w) = μ • e w := by rw [← hi, heigen, map_smul]
  change g.inner (x : M) (mfderiv I I (Subtype.val : U → M) x w) (mfderiv I I (Subtype.val : U → M) x w) = 1 ∧ _
  refine ⟨by rwa [← restrict_inner], ?_, ?_, ?_⟩
  · simpa only [he] using heu
  · intro z hz
    obtain ⟨v, rfl⟩ := e.surjective z
    have hv : (g.restrictOpen U).inner x v v = 1 := by
      rwa [restrict_inner, ← he]
    simpa only [ricciTensor_restrictOpen, ← he] using hmin v hv
  · apply le_antisymm
    · intro z hz
      obtain ⟨v, rfl⟩ := e.surjective z
      have hv : v ∈ Module.End.eigenspace
          (ricciSharp (g.restrictOpen U) x).toLinearMap μ := by
        apply Module.End.mem_eigenspace_iff.mpr
        change ricciSharp (g.restrictOpen U) x v = μ • v
        apply e.injective
        rw [hi, map_smul]
        exact Module.End.mem_eigenspace_iff.mp hz
      rw [hsimple] at hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
      apply Submodule.mem_span_singleton.mpr
      exact ⟨c, by simpa only [map_smul, he] using congrArg e hc⟩
    · apply Submodule.span_le.mpr
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      apply Module.End.mem_eigenspace_iff.mpr
      change ricciSharp g (x : M) (mfderiv I I (Subtype.val : U → M) x w) = μ • mfderiv I I (Subtype.val : U → M) x w
      simpa only [he] using heu

end DifferentialGeometry.Geometry.Curvature
