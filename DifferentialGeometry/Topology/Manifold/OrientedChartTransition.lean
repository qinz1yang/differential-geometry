import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Bundle.Orientation.Map
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.Manifold

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

private theorem mem_source_of_mem_trans_symm_source {Φ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞}
    {u : E} (hu : u ∈ (Φ.trans Ψ.symm).source) : u ∈ Φ.source ∧ Φ u ∈ Ψ.target := by
  have h : u ∈ (Φ.toPartialEquiv.trans Ψ.symm.toPartialEquiv).source := hu
  rw [PartialEquiv.trans_source] at h
  exact ⟨h.1, h.2⟩

theorem differentiableAt_symm_comp {Φ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞} {u : E}
    (hu : u ∈ (Φ.trans Ψ.symm).source) : DifferentiableAt ℝ (fun x => Ψ.symm (Φ x)) u := by
  obtain ⟨hus, hut⟩ := mem_source_of_mem_trans_symm_source hu
  have hm := (PartialDiffeomorph.mdifferentiableAt Ψ.symm (n := ∞) (by simp) hut).comp u
    (PartialDiffeomorph.mdifferentiableAt Φ (n := ∞) (by simp) hus)
  exact mdifferentiableAt_iff_differentiableAt.mp hm

theorem mfderiv_symm_mfderiv_apply_of_mem_target {Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞}
    {y : M} (hy : y ∈ Ψ.target) (w : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ.symm : M → E) y
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ : E → M) (Ψ.symm y) w) = w := by
  have hxs : Ψ.symm y ∈ Ψ.source := Ψ.toPartialEquiv.map_target hy
  have hpx : Ψ (Ψ.symm y) = y := Ψ.toPartialEquiv.right_inv hy
  have hmΨs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ.symm : M → E) (Ψ (Ψ.symm y)) := by
    rw [hpx]
    exact PartialDiffeomorph.mdifferentiableAt Ψ.symm (n := ∞) (by simp) hy
  have hmΨ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ : E → M) (Ψ.symm y) :=
    PartialDiffeomorph.mdifferentiableAt Ψ (n := ∞) (by simp) hxs
  have hcomp := mfderiv_comp (Ψ.symm y) hmΨs hmΨ
  have hev : ((Ψ.symm : M → E) ∘ (Ψ : E → M)) =ᶠ[𝓝 (Ψ.symm y)] id := by
    filter_upwards [Ψ.open_source.mem_nhds hxs] with x hx
    exact Ψ.toPartialEquiv.left_inv hx
  rw [hev.mfderiv_eq, mfderiv_id, hpx] at hcomp
  exact (DFunLike.congr_fun hcomp w).symm

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem det_fderiv_symm_comp_pos {n : ℕ} (o : ManifoldOrientation 𝓘(ℝ, E) M n)
    (oE : Orientation ℝ E (Fin n)) {Φ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞}
    (hΦ : ∀ x (hx : x ∈ Φ.source), Orientation.map (Fin n)
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hx).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv oE = o.orientation (Φ x))
    (hΨ : ∀ x (hx : x ∈ Ψ.source), Orientation.map (Fin n)
      ((Ψ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hx).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv oE = o.orientation (Ψ x))
    {u : E} (hu : u ∈ (Φ.trans Ψ.symm).source) :
    0 < (fderiv ℝ (fun x => Ψ.symm (Φ x)) u).det := by
  obtain ⟨hus, hut⟩ := mem_source_of_mem_trans_symm_source hu
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E :=
    (Fintype.card_fin n).trans o.dimension_eq.symm
  have hxs : Ψ.symm (Φ u) ∈ Ψ.source := Ψ.toPartialEquiv.map_target hut
  have hpx : Ψ (Ψ.symm (Φ u)) = Φ u := Ψ.toPartialEquiv.right_inv hut
  let A : E ≃ₗ[ℝ] E :=
    ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hus).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv
  let B : E ≃ₗ[ℝ] E :=
    ((Ψ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hxs).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv
  let C : E ≃ₗ[ℝ] E :=
    ((Ψ.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hut).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv
  have hA : Orientation.map (Fin n) A oE = o.orientation (Φ u) := hΦ u hus
  have hB : Orientation.map (Fin n) B oE = o.orientation (Φ u) := by
    rw [← hpx]
    exact hΨ (Ψ.symm (Φ u)) hxs
  have hBC : B.trans C = LinearEquiv.refl ℝ E :=
    LinearEquiv.ext fun w => mfderiv_symm_mfderiv_apply_of_mem_target hut w
  have hmap : Orientation.map (Fin n) (A.trans C) oE = oE := by
    rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between A C oE, hA, ← hB,
      DifferentialGeometry.VectorBundle.map_orientation_trans_between B C oE, hBC,
      Orientation.map_refl]
    rfl
  have hdet : 0 < LinearMap.det ((A.trans C : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) :=
    (Orientation.map_eq_iff_det_pos oE (A.trans C) hcard).mp hmap
  have hAc : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ.symm : M → E) (Φ u)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ : E → M) u) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x => Ψ.symm (Φ x)) u :=
    (mfderiv_comp u (PartialDiffeomorph.mdifferentiableAt Ψ.symm (n := ∞) (by simp) hut)
      (PartialDiffeomorph.mdifferentiableAt Φ (n := ∞) (by simp) hus)).symm
  have hlin : ((A.trans C : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) =
      ((fderiv ℝ (fun x => Ψ.symm (Φ x)) u : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    apply LinearMap.ext
    intro v
    change ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Ψ.symm : M → E) (Φ u)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ : E → M) u)) v = (fderiv ℝ (fun x => Ψ.symm (Φ x)) u) v
    rw [hAc, mfderiv_eq_fderiv]
    rfl
  rw [hlin] at hdet
  exact hdet

end

end DifferentialGeometry.Topology.Manifold
