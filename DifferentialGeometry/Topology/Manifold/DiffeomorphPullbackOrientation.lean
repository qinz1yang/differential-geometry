import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {ι ι' ι'' : Type*}

private theorem orientation_reindex_trans (e : ι ≃ ι') (e' : ι' ≃ ι'')
    (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ E e' (Orientation.reindex ℝ E e o) =
      Orientation.reindex ℝ E (e.trans e') o := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

private theorem orientation_map_reindex (e : ι ≃ ι') (L : E ≃ₗ[ℝ] F)
    (o : Orientation ℝ E ι) :
    Orientation.reindex ℝ F e (Orientation.map ι L o) =
      Orientation.map ι' L (Orientation.reindex ℝ E e o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

variable {n : ℕ}

theorem tangentOrientationEquiv_reindex_eq_iff (L : E ≃ₗ[ℝ] F)
    (hE : Module.finrank ℝ E = n) (hF : Module.finrank ℝ F = n)
    (oE : Orientation ℝ E (Fin n)) (oF : Orientation ℝ F (Fin n)) :
    tangentOrientationEquiv L (Orientation.reindex ℝ E (finCongr hE.symm) oE) =
        Orientation.reindex ℝ F (finCongr hF.symm) oF ↔
      Orientation.map (Fin n) L oE = oF := by
  have hkey : (finCongr hE.symm).trans (finCongr L.finrank_eq) = finCongr hF.symm := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl
  have hmain : tangentOrientationEquiv L (Orientation.reindex ℝ E (finCongr hE.symm) oE) =
      Orientation.reindex ℝ F (finCongr hF.symm) (Orientation.map (Fin n) L oE) := by
    rw [tangentOrientationEquiv, Equiv.trans_apply]
    rw [(orientation_map_reindex (finCongr hE.symm) L oE).symm]
    rw [orientation_reindex_trans, hkey]
  rw [hmain]
  exact (Orientation.reindex ℝ F (finCongr hF.symm)).injective.eq_iff

theorem tangentOrientationEquiv_symm_reindex_map (L : E ≃ₗ[ℝ] F)
    (hE : Module.finrank ℝ E = n) (hF : Module.finrank ℝ F = n)
    (oF : Orientation ℝ F (Fin n)) :
    Orientation.map (Fin n) L
      (Orientation.reindex ℝ E (finCongr hE)
        (tangentOrientationEquiv L.symm
          (Orientation.reindex ℝ F (finCongr hF.symm) oF))) = oF := by
  have hcomp : (finCongr hE).trans (finCongr hE.symm) =
      Equiv.refl (Fin (Module.finrank ℝ E)) := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl
  have hinv : tangentOrientationEquiv L
      (tangentOrientationEquiv L.symm
        (Orientation.reindex ℝ F (finCongr hF.symm) oF)) =
      Orientation.reindex ℝ F (finCongr hF.symm) oF := by
    have h := tangentOrientationEquiv_symm L.symm
      (Orientation.reindex ℝ F (finCongr hF.symm) oF)
    simpa only [LinearEquiv.symm_symm] using h
  have hfix : Orientation.reindex ℝ E (finCongr hE.symm)
      (Orientation.reindex ℝ E (finCongr hE)
        (tangentOrientationEquiv L.symm
          (Orientation.reindex ℝ F (finCongr hF.symm) oF))) =
      tangentOrientationEquiv L.symm
        (Orientation.reindex ℝ F (finCongr hF.symm) oF) := by
    rw [orientation_reindex_trans, hcomp, Orientation.reindex_refl]
    rfl
  refine (tangentOrientationEquiv_reindex_eq_iff L hE hF
    (Orientation.reindex ℝ E (finCongr hE)
      (tangentOrientationEquiv L.symm
        (Orientation.reindex ℝ F (finCongr hF.symm) oF))) oF).mp ?_
  rw [hfix]
  exact hinv

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H K M N : Type*}
variable [TopologicalSpace H] [TopologicalSpace K]
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
variable {n : ℕ}

omit [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
set_option backward.isDefEq.respectTransparency false in
theorem Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm
    (f : M ≃ₘ⟮I, J⟯ N)
    (hbij : ∀ x : M, Function.Bijective (mfderiv I J (f : M → N) x)) (x : M)
    (Y : Orientation ℝ F (Fin (Module.finrank ℝ F))) :
    tangentOrientationEquiv
        (differentialEquivOfBijective I J (f : M → N) hbij x).symm.toLinearEquiv Y =
      tangentOrientationEquiv
        (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.symm Y := rfl

theorem Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv
    (f : M ≃ₘ⟮I, J⟯ N)
    (hbij : ∀ x : M, Function.Bijective (mfderiv I J (f : M → N) x))
    (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n)
    (h : ∀ x : M, oM.orientation x = Orientation.reindex ℝ E (finCongr oM.dimension_eq)
      (tangentOrientationEquiv
        (differentialEquivOfBijective I J (f : M → N) hbij x).symm.toLinearEquiv
        (Orientation.reindex ℝ F (finCongr oN.dimension_eq.symm) (oN.orientation (f x))))) :
    f.preservesOrientation oM oN := by
  intro x
  have hbridge := Diffeomorph.tangentOrientationEquiv_differentialEquivOfBijective_symm
    f hbij x
    (Orientation.reindex ℝ F (finCongr oN.dimension_eq.symm) (oN.orientation (f x)))
  rw [h x, hbridge]
  exact tangentOrientationEquiv_symm_reindex_map
    (E := TangentSpace I x) (F := TangentSpace J (f x))
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    oM.dimension_eq oN.dimension_eq (oN.orientation (f x))

theorem Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation
    (f : M ≃ₘ⟮I, J⟯ N) (hf : ContMDiff I J ∞ (f : M → N))
    (hbij : ∀ x : M, Function.Bijective (mfderiv I J (f : M → N) x))
    (o : SmoothOrientation J N) (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation J N n)
    (hN : ∀ y : N, o.val y =
      Orientation.reindex ℝ F (finCongr oN.dimension_eq.symm) (oN.orientation y))
    (hM : ∀ x : M, oM.orientation x = Orientation.reindex ℝ E (finCongr oM.dimension_eq)
      ((pullbackSmoothOrientation I J (f : M → N) hf hbij o).val x)) :
    f.preservesOrientation oM oN := by
  refine Diffeomorph.preservesOrientation_of_orientation_eq_tangentOrientationEquiv
    f hbij oM oN fun x => ?_
  rw [hM x, pullbackSmoothOrientation_apply, hN (f x)]

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem orientation_map_reindex_of_tangentOrientationEquiv
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {n : ℕ} (L : E ≃ₗ[ℝ] F) (hE : Module.finrank ℝ E = n) (hF : Module.finrank ℝ F = n)
    (oE : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (oF : Orientation ℝ F (Fin (Module.finrank ℝ F)))
    (h : tangentOrientationEquiv L oE = oF) :
    Orientation.map (Fin n) L (Orientation.reindex ℝ E (finCongr hE) oE) =
      Orientation.reindex ℝ F (finCongr hF) oF := by
  rw [← h]
  induction oE using Module.Ray.ind with
  | h vol hvol => rfl

end DifferentialGeometry.Topology.Manifold
