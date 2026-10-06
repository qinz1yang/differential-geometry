import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem immersion_neighborhood_of_smoothDiskExtension
    {u : C(closedDisk, M)} {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U)
    (himm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∃ N : TopologicalSpace.Opens ℂ, Metric.closedBall (0 : ℂ) 1 ⊆ N ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun z : N => U z) ∧
      ∀ z : N, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : N => U w) z) := by
  obtain ⟨s, hs, hDs, hUs⟩ := hU.2
  let S : TopologicalSpace.Opens ℂ := ⟨s, hs⟩
  let F : S → M := fun z => U z
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hUs.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  let A : Set S := {z | _root_.Manifold.IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z}
  have hA : IsOpen A := IsOpen.isImmersionAt
  let N : TopologicalSpace.Opens ℂ :=
    ⟨Subtype.val '' A, S.isOpenEmbedding'.isOpenMap A hA⟩
  have hNs : (N : Set ℂ) ⊆ s := by
    rintro z ⟨w, _, rfl⟩
    exact w.property
  have hDN : Metric.closedBall (0 : ℂ) 1 ⊆ N := by
    intro z hz
    refine ⟨⟨z, hDs hz⟩, ?_, rfl⟩
    apply DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
      (by simp) hF
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y : S => U y) ⟨z, hDs hz⟩ : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact himm z hz
  have hNU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun z : N => U z) :=
    (hUs.mono hNs).comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  refine ⟨N, hDN, hNU, ?_⟩
  intro z
  obtain ⟨w, hw, heq⟩ := z.property
  have hwImm : _root_.Manifold.IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F w := hw
  have hinj := hwImm.mfderiv_injective (by simp)
  change Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y : S => U y) w : ℂ →L[ℝ] E) at hinj
  change Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y : N => U y) z : ℂ →L[ℝ] E)
  rw [DifferentialGeometry.mfderiv_restrict_open] at hinj ⊢
  rw [heq] at hinj
  exact hinj

/-- An immersed smooth disk extension induces an actual pullback metric on an
open neighborhood of the same closed disk. -/
theorem SmoothDiskExtension.exists_pullback_metric_neighborhood
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U)
    (himm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∃ (N : TopologicalSpace.Opens ℂ)
      (hsm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun z : N => U z))
      (hinj : ∀ z : N, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : N => U w) z)),
      Metric.closedBall (0 : ℂ) 1 ⊆ N ∧
      ∀ (z : N) (v w : TangentSpace 𝓘(ℝ, ℂ) z),
        (g.pullback (fun q : N => U q) hsm hinj).inner z v w =
          g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) := by
  obtain ⟨N, hDN, hsm, hinj⟩ :=
    immersion_neighborhood_of_smoothDiskExtension hU himm
  refine ⟨N, hsm, hinj, hDN, ?_⟩
  intro z v w
  simp only [SmoothRiemannianMetric.pullback_inner,
    DifferentialGeometry.mfderiv_restrict_open]
  rfl

end DifferentialGeometry.Geometry
