import DifferentialGeometry.Topology.ThreeManifold.UncappingSmoothStructure

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Annulus" => S2 × Icc (1 / 4 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem eq_of_uncappingInteriorProjection {Y : Type*} (f : C.UncappingQuotient → Y)
    (hf : IsLocallyConstant f) (v : Y)
    (hi : ∀ y : C.uncappingInterior, f (C.uncappingInteriorProjection y) = v)
    (q : C.UncappingQuotient) : f q = v := by
  rcases C.uncappingQuotient_covered_by_interior_and_seam q with ⟨y,rfl⟩ | ⟨a,z,rfl⟩
  · exact hi y
  · let γ : Icc (1 / 4 : ℝ) 1 → C.UncappingQuotient := fun r =>
      Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨(a,false),-z,r⟩)
    have hγ : Continuous γ := continuous_quot_mk.comp
      ((continuous_adjunctionCell _ _).comp
        (continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)))
    let _ : PreconnectedSpace (Icc (1 / 4 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have heq := (hf.comp_continuous hγ).apply_eq_of_preconnectedSpace
      (⟨1 / 4,by norm_num⟩ : Icc (1 / 4 : ℝ) 1) ⟨1,by norm_num⟩
    have hfirst : C.uncappingSeam a (z,⟨0,by constructor <;> norm_num⟩) = γ ⟨1 / 4,by norm_num⟩ := by
      simpa only [add_zero] using C.uncappingSeam_of_nonneg a
        (z,⟨0,by constructor <;> norm_num⟩) (by norm_num)
    let x := T.coreBoundarySphere (a,false) (C.attaching (a,false) (-z))
    let y : C.uncappingInterior := ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩
    have hlast : C.uncappingInteriorProjection y = γ ⟨1,by norm_num⟩ := by
      apply C.uncappingProjection_annulus (a,false) (-z,⟨1,by norm_num⟩)
      change C.coreInclusion x = C.capAnnulusMap (a,false) (-z,⟨1,by norm_num⟩)
      rw [C.capAnnulusMap_outer]
    change f (γ _) = f (γ _) at heq
    rw [hfirst]
    exact heq.trans (hlast ▸ hi y)

end DifferentialGeometry.Topology.SphericalCapping
