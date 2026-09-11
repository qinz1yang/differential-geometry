import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem stereographicInverse_isLocalDiffeomorph (v : S3) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (stereographic' 3 v).symm := by
  have he : chartAt E3 (-v) = stereographic' 3 v := by
    change stereographic' 3 (-(-v)) = stereographic' 3 v
    rw [neg_neg]
  let D : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 E3 ∞ :=
    { toPartialEquiv := (chartAt E3 (-v)).toPartialEquiv
      open_source := (chartAt E3 (-v)).open_source
      open_target := (chartAt E3 (-v)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  intro x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ D.symm
    (show x ∈ D.target from by change x ∈ (chartAt E3 (-v)).target; rw [he]; simp)
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (chartAt E3 (-v)).symm x at h
  simpa only [he] using h

def stereographicImage (north : S3) : Opens S3 :=
  (stereographicInverse_isLocalDiffeomorph north).image

theorem stereographicImage_eq (north : S3) : (stereographicImage north : Set S3) = {north}ᶜ := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [stereographic'_source] using
      (stereographic' 3 north).map_target (show x ∈ (stereographic' 3 north).target by simp)
  · intro hp
    exact ⟨stereographic' 3 north p, (stereographic' 3 north).left_inv (by simpa only [stereographic'_source] using hp)⟩

def stereographicDiffeomorph (north : S3) : E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ stereographicImage north :=
  diffeomorphOntoImage (stereographic' 3 north).symm
    (stereographicInverse_isLocalDiffeomorph north)
    ((stereographic' 3 north).symm.isOpenEmbedding (by simp)).injective

theorem stereographicDiffeomorph_apply (north : S3) (x : E3) :
    (stereographicDiffeomorph north x : S3) = (stereographic' 3 north).symm x := rfl

theorem stereographicDiffeomorph_coordinates (north : S3) (x : E3) :
    stereographic' 3 north (stereographicDiffeomorph north x : S3) = x :=
  (stereographic' 3 north).right_inv (by simp)

theorem stereographicDiffeomorph_symm_apply (north : S3) (p : stereographicImage north) :
    (stereographicDiffeomorph north).symm p = stereographic' 3 north p.val := by
  have h := stereographicDiffeomorph_coordinates north ((stereographicDiffeomorph north).symm p)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm
end DifferentialGeometry.Topology.Manifold
