import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionGap
import DifferentialGeometry.Topology.Manifold.Submersion
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-! Geometric normal projectors of the unchanged embedded nearest-point target. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Manifold
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def actualZeroSetTangentSpace (k : ℕ) (Z : Set H)
    [ChartedSpace (Fin k → ℝ) Z] (z : Z) : Submodule ℝ H :=
  LinearMap.range (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) z).toLinearMap

def actualZeroSetNormalProjector [FiniteDimensional ℝ H] (k : ℕ) (Z : Set H)
    [ChartedSpace (Fin k → ℝ) Z] (z : Z) : H →L[ℝ] H :=
  (actualZeroSetTangentSpace k Z z)ᗮ.starProjection

theorem norm_actualZeroSetNormalProjector_sub_le [FiniteDimensional ℝ H]
    {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]
    [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z] (Ω : TopologicalSpace.Opens H)
    (p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯)
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H))
    (hp : _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p)
    (L : Submodule ℝ H) (hdim : Module.finrank ℝ L = k)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (z : Ω)
    (hclose :
      let D : H →L[ℝ] H :=
        mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H)) z
      ‖D - L.starProjection‖ ≤ ε) :
    ‖actualZeroSetNormalProjector k Z (p z) - Lᗮ.starProjection‖ ≤ 3 * ε := by
  let A : (Fin k → ℝ) →L[ℝ] H :=
    mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) (p z)
  let B : H →L[ℝ] (Fin k → ℝ) := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) p z
  let D : H →L[ℝ] H := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H)) z
  let R : Submodule ℝ H := actualZeroSetTangentSpace k Z (p z)
  have hchain : D = A.comp B := by
    exact mfderiv_comp z (hemb.contMDiff.mdifferentiableAt (by simp))
      (p.contMDiff.mdifferentiableAt (by simp))
  have hBsurj : Function.Surjective B :=
    (DifferentialGeometry.Topology.Manifold.isSubmersionAt_iff_surjective_mfderiv
      p p.contMDiff z).mp (hp.isSubmersionAt z)
  have hrange : LinearMap.range D.toLinearMap = R := by
    rw [hchain]
    change LinearMap.range (A.toLinearMap.comp B.toLinearMap) = LinearMap.range A.toLinearMap
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hBsurj)
  have hRdim : Module.finrank ℝ R = k := by
    change Module.finrank ℝ (LinearMap.range A.toLinearMap) = k
    have hAinj : Function.Injective A :=
      hemb.isImmersion.mfderiv_injective (by simp) (p z)
    calc
      _ = Module.finrank ℝ (Fin k → ℝ) := LinearMap.finrank_range_of_inj hAinj
      _ = k := by simp
  have hbound (u : H) (hu : u ∈ L) : ‖u - R.starProjection u‖ ≤ ε * ‖u‖ := by
    have hDu : D u ∈ R := by rw [← hrange]; exact ⟨u, rfl⟩
    calc
      _ = Metric.infDist u (R : Set H) := by
        simpa only [dist_eq_norm] using R.dist_starProjection_eq_infDist u
      _ ≤ dist u (D u) := Metric.infDist_le_dist_of_mem hDu
      _ = ‖(D - L.starProjection) u‖ := by
        rw [dist_eq_norm, sub_apply, L.starProjection_eq_self_iff.mpr hu, norm_sub_rev]
      _ ≤ ‖D - L.starProjection‖ * ‖u‖ := (D - L.starProjection).le_opNorm u
      _ ≤ ε * ‖u‖ := mul_le_mul_of_nonneg_right hclose (norm_nonneg u)
  have hgap := Submodule.norm_starProjection_sub_le_three_mul_of_one_sided_bound
    L R (hdim.trans hRdim.symm) hε0 hεhalf hbound
  change ‖Rᗮ.starProjection - Lᗮ.starProjection‖ ≤ 3 * ε
  rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
  have heq : (ContinuousLinearMap.id ℝ H - R.starProjection) -
      (ContinuousLinearMap.id ℝ H - L.starProjection) = L.starProjection - R.starProjection := by
    abel
  rwa [heq]

end GC.MetricGeometry
