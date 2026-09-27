import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations



noncomputable section

open Set Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M]



def affineChart (c : OpenPartialHomeomorph E M) (a : E) (L : V ≃L[ℝ] E) :
    OpenPartialHomeomorph V M :=
  (L.toHomeomorph.trans (Homeomorph.addLeft a)).toOpenPartialHomeomorph.trans c

@[simp] theorem affineChart_apply (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) (x : V) : affineChart c a L x = c (a + L x) := rfl

@[simp] theorem affineChart_source (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) : (affineChart c a L).source = (fun x => a + L x) ⁻¹' c.source := by
  simp [affineChart, Function.comp_def]

@[simp] theorem affineChart_target (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) : (affineChart c a L).target = c.target := by
  simp [affineChart]

@[simp] theorem affineChart_symm_apply (c : OpenPartialHomeomorph E M) (a : E)
    (L : V ≃L[ℝ] E) (x : M) : (affineChart c a L).symm x = L.symm (-a + c.symm x) := rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ChartedSpace F M]


theorem contMDiffOn_affineChart {c : OpenPartialHomeomorph E M}
    (hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ c.symm c.target)
    (a : E) (L : V ≃L[ℝ] E) :
    ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ (affineChart c a L) (affineChart c a L).source ∧
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, V) ∞ (affineChart c a L).symm (affineChart c a L).target := by
  constructor
  · rw [affineChart_source]
    exact hc.comp (contDiff_const.add L.contDiff).contMDiff.contMDiffOn (fun _ hx => hx)
  · rw [affineChart_target]
    exact (L.symm.contDiff.comp (contDiff_const.add contDiff_id)).contMDiff.comp_contMDiffOn hi



theorem affineChart_mfderiv {c : OpenPartialHomeomorph E M} (a : E) (L : V ≃L[ℝ] E)
    {x : V} (hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) c (a + L x)) (v : V) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (affineChart c a L) x v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) c (a + L x) (L v) := by
  have hA : HasFDerivAt (fun y : V => a + L y) (L : V →L[ℝ] E) x :=
    L.hasFDerivAt.const_add a
  have hd := mfderiv_comp x hc hA.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hA.fderiv] at hd
  exact congrArg (fun A => A v) hd

end DifferentialGeometry.Topology
