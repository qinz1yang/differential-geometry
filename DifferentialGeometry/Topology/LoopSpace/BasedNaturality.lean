import DifferentialGeometry.Topology.LoopSpace.BasedCircle



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]


def basedCirclePostcompose (f : C(P, Q)) (p : P) : C(basedCircleLoop p, basedCircleLoop (f p)) :=
  ⟨fun γ => ⟨f.comp γ.val, congrArg f γ.property⟩,
    ((continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩


theorem pathToCircle_natural (f : C(P, Q)) (p : P) (γ : Path p p) :
    pathToCircle (γ.map f.continuous) = f.comp (pathToCircle γ) := by
  ext θ
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  simp only [ContinuousMap.comp_apply, pathToCircle_coe]
  rfl


theorem basedPathCircleHomeomorph_natural (f : C(P, Q)) (p : P) (γ : Path p p) :
    basedPathCircleHomeomorph (f p) (γ.map f.continuous) =
      basedCirclePostcompose f p (basedPathCircleHomeomorph p γ) := by
  apply Subtype.ext
  exact pathToCircle_natural f p γ


theorem basedPathCircleHomeomorph_refl (p : P) :
    (basedPathCircleHomeomorph p (Path.refl p)).val = FreeLoop.constants p := by
  ext θ
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  exact pathToCircle_coe (Path.refl p) t

end DifferentialGeometry.Topology
