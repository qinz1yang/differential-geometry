import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def velocityLift (γ : 𝕜 → M) (t : 𝕜) : TangentBundle I M :=
  tangentMap 𝓘(𝕜, 𝕜) I γ ⟨t, (1 : 𝕜)⟩

@[simp] theorem velocityLift_proj (γ : 𝕜 → M) (t : 𝕜) :
    (velocityLift (I := I) γ t).proj = γ t := rfl

@[simp] theorem velocityLift_snd (γ : 𝕜 → M) (t : 𝕜) :
    (velocityLift (I := I) γ t).snd = mfderiv 𝓘(𝕜, 𝕜) I γ t (1 : 𝕜) := rfl

theorem velocityLift_eq_tangentMap (γ : 𝕜 → M) (t : 𝕜) :
    velocityLift (I := I) γ t = tangentMap 𝓘(𝕜, 𝕜) I γ ⟨t, (1 : 𝕜)⟩ := rfl

variable [IsManifold I 1 M] {m n : ℕ∞ω}

theorem _root_.ContMDiffAt.velocityLift {γ : 𝕜 → M} {t : 𝕜}
    (hγ : ContMDiffAt 𝓘(𝕜, 𝕜) I n γ t) (hmn : m + 1 ≤ n) :
    ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent m (velocityLift (I := I) γ) t := by
  have hv : ContMDiffAt 𝓘(𝕜, 𝕜) (𝓘(𝕜, 𝕜)).tangent m
      (fun s : 𝕜 => (⟨s, (1 : 𝕜)⟩ : TangentBundle 𝓘(𝕜, 𝕜) 𝕜)) t := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa using (contMDiffAt_const (I := 𝓘(𝕜, 𝕜)) (I' := 𝓘(𝕜, 𝕜))
      (n := m) (c := (1 : 𝕜)) (x := t))
  exact (hγ.mfderiv_const hmn).clm_apply_of_inCoordinates hv
    (hγ.of_le (le_self_add.trans hmn))

end DifferentialGeometry
