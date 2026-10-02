import DifferentialGeometry.Topology.ThreeManifold.Model
import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

abbrev tangentChartEquiv (p x : M)
    (hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    TangentSpace ThreeModel x ≃ₗ[ℝ] ThreeSpace :=
  DifferentialGeometry.tangentChartEquiv ThreeModel M p x hx

abbrev TangentOrientationSection :=
  DifferentialGeometry.ManifoldOrientation ThreeModel M 3

variable {M}


variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]

def PreservesTangentOrientationAt (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : M → N) (x : M)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x)) : Prop :=
  Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f x).toLinearMap hf)
      (oM.orientation x) = oN.orientation (f x)

def PreservesTangentOrientation (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : M → N) : Prop :=
  ContMDiff ThreeModel ThreeModel ∞ f ∧
    ∀ x : M, ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x),
      PreservesTangentOrientationAt oM oN f x hf

end

section

set_option autoImplicit false

universe u

theorem mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective
    {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (x : M)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x)) :
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f x).toLinearMap hf := by
  ext v
  rw [LinearEquiv.ofBijective_apply]
  change (f.mfderivToContinuousLinearEquiv (by simp) x :
    TangentSpace ThreeModel x → TangentSpace ThreeModel (f x)) v =
    mfderiv ThreeModel ThreeModel f x v
  rfl

theorem preservesOrientation_of_preservesTangentOrientation
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (oM : TangentOrientationSection M)
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (oN : TangentOrientationSection N)
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N)
    (h : PreservesTangentOrientation oM oN f) :
    f.preservesOrientation oM oN := by
  intro x
  obtain ⟨hf, hfx⟩ := h.2 x
  rw [mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective f x hf]
  exact hfx

end

section

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

theorem preservesTangentOrientation_refl (o : TangentOrientationSection M) :
    PreservesTangentOrientation o o (Diffeomorph.refl ThreeModel M ∞) := by
  constructor
  · exact contMDiff_id
  · intro x
    have hd : mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x
        = ContinuousLinearMap.id ℝ (TangentSpace ThreeModel x) := mfderiv_id
    have hbij : Function.Bijective
        (mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x) :=
      hd ▸ Function.bijective_id
    refine ⟨hbij, ?_⟩
    unfold PreservesTangentOrientationAt
    have he : LinearEquiv.ofBijective
        (mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x).toLinearMap hbij
        = LinearEquiv.refl ℝ (TangentSpace ThreeModel x) := by
      ext v
      change mfderiv ThreeModel ThreeModel (⇑(Diffeomorph.refl ThreeModel M ∞)) x v = v
      rw [hd]
      rfl
    have hm := congrArg (fun e : TangentSpace ThreeModel x ≃ₗ[ℝ] TangentSpace ThreeModel x =>
      Orientation.map (Fin 3) e (o.orientation x)) he
    have hr := congrArg (fun e : Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) ≃
      Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) => e (o.orientation x))
      (Orientation.map_refl (R := ℝ) (M := TangentSpace ThreeModel x) (Fin 3))
    exact hm.trans hr

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
