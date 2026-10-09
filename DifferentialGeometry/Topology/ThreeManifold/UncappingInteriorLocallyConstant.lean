import DifferentialGeometry.Topology.ThreeManifold.UncappingInteriorCover
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
private local instance constantCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance constantCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem eq_of_uncappingInterior_core {Y : Type*} (f : C.uncappingInterior → Y)
    (hf : IsLocallyConstant f) (v : Y)
    (hcore : letI := C.coreCharts
      ∀ x : T.core, (𝓡∂ 3).IsInteriorPoint x →
        f ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩ = v) :
    ∀ y, f y = v := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  let g : T.core → C.uncappingInterior :=
    fun x => ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩
  have hg : Continuous g := C.coreInclusion.continuous.subtype_mk _
  have hall : ∀ x : T.core, f (g x) = v := by
    have hc := (hf.comp_continuous hg).isClosed_fiber v
    have hi : (𝓡∂ 3).interior T.core ⊆ {x | (f ∘ g) x = v} := hcore
    exact fun x => (closure_minimal hi hc) (ModelWithCorners.dense_interior (𝓡∂ 3) x)
  intro y
  let z₀ : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  let B : T.Boundary → ClosedCell 3 ≃ₘ⟮𝓡∂ 3,𝓡∂ 3⟯ ClosedCell 3 :=
    fun _ => Diffeomorph.refl _ _ ∞
  rcases C.uncappingInterior_cover B (by intros; rfl) (by intros; rfl) z₀ y with
    ⟨x,_,hy⟩ | ⟨b,z,hy⟩ | ⟨b,q,hq,hy⟩
  · have heq : y = g x := Subtype.ext hy
    rw [heq]
    exact hall x
  · have heq : y = g (T.coreBoundarySphere b (C.attaching b z)) :=
      Subtype.ext (hy.trans (C.boundary_eq b z))
    rw [heq]
    exact hall _
  · let R := Icc q.2 (1 : ℝ)
    let radial : R → ClosedCell 3 := fun r => ⟨r.val • q.1.val, by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [r.property.1,hq.1]),
        norm_eq_of_mem_sphere,mul_one]
      exact r.property.2⟩
    have hnorm (r : R) : ‖(radial r).val‖ = r.val := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [r.property.1,hq.1]),
        norm_eq_of_mem_sphere,mul_one]
    let γ : R → C.uncappingInterior := fun r => ⟨C.cap b (radial r),by
      apply C.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall b (Homeomorph.refl _) (by intros; rfl)
      rw [hnorm]
      exact hq.1.trans_le r.property.1⟩
    have hγ : Continuous γ := by
      apply Continuous.subtype_mk
      apply (C.cap b).continuous.comp
      apply Continuous.subtype_mk
      exact continuous_subtype_val.smul continuous_const
    let _ : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have heq := (hf.comp_continuous hγ).apply_eq_of_preconnectedSpace
      (⟨q.2,le_rfl,hq.2.le⟩ : R) (⟨1,hq.2.le,le_rfl⟩ : R)
    have hfirst : γ ⟨q.2,le_rfl,hq.2.le⟩ = y := by
      apply Subtype.ext
      rw [hy,C.capAnnulusInteriorChart_apply b (B b) z₀ q ⟨by linarith [hq.1],hq.2⟩]
      rfl
    have hlast : γ ⟨1,hq.2.le,le_rfl⟩ = g (T.coreBoundarySphere b (C.attaching b q.1)) := by
      apply Subtype.ext
      change C.cap b (radial _) = C.coreInclusion _
      have hrad : radial ⟨1,hq.2.le,le_rfl⟩ = sphereToClosedCell q.1 := by
        apply Subtype.ext
        exact one_smul ℝ q.1.val
      rw [hrad,C.boundary_eq]
    change f (γ _) = f (γ _) at heq
    rw [hfirst,hlast] at heq
    exact heq.trans (hall _)

end DifferentialGeometry.Topology.SphericalCapping
