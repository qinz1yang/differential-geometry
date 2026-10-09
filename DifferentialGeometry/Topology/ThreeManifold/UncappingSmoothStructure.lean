import DifferentialGeometry.Topology.ThreeManifold.SmoothUncapping
import DifferentialGeometry.Topology.ThreeManifold.UncappingCover
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def uncappingInteriorProjection : C(C.uncappingInterior,C.UncappingQuotient) :=
  ⟨C.uncappingProjection ∘ C.uncappingInteriorInclusion,
    C.uncappingProjection.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

theorem exists_uncapping_smooth_structure :
    ∃ charts : ChartedSpace E3 C.UncappingQuotient,
      let _ := charts
      ∃ _ : IsManifold (𝓡 3) ∞ C.UncappingQuotient,
        ∃ D : C.UncappingQuotient ≃ₘ⟮𝓡 3,𝓡 3⟯ M.Carrier,
          (∀ x : T.core, D (Quot.mk C.innerCapRelation
            (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
              (C.coreImageHomeomorph x))) = x.val) ∧
          IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection ∧
          ∀ (a : T.Index) (z : S2),
            IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
              (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)) := by
  obtain ⟨H,hcore,hinterior,hseam⟩ := C.exists_uncapping_homeomorph_localDiffeomorph
  let charts : ChartedSpace E3 C.UncappingQuotient := Handle.chartedSpaceOfHomeomorph H
  let _ := charts
  let smooth : IsManifold (𝓡 3) ∞ C.UncappingQuotient := Handle.isManifoldOfHomeomorph (𝓡 3) H
  let _ := smooth
  let D : C.UncappingQuotient ≃ₘ⟮𝓡 3,𝓡 3⟯ M.Carrier :=
    { toEquiv := H.toEquiv
      contMDiff_toFun := Handle.contMDiff_homeomorph_of_chartedSpaceOfHomeomorph H (𝓡 3) ∞
      contMDiff_invFun := Handle.contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph H (𝓡 3) ∞ }
  refine ⟨charts,smooth,D,hcore,?_,?_⟩
  · intro y
    have h := (hinterior y).comp (𝓡 3) C.UncappingQuotient (D.symm.isLocalDiffeomorph (C.uncappingInteriorMap H y))
    have heq : D.symm ∘ C.uncappingInteriorMap H = C.uncappingInteriorProjection := by
      funext x
      change D.symm (D (C.uncappingInteriorProjection x)) = C.uncappingInteriorProjection x
      exact D.symm_apply_apply _
    exact heq ▸ h
  · intro a z
    have h := (hseam a z).comp (𝓡 3) C.UncappingQuotient
      (D.symm.isLocalDiffeomorph (H (C.uncappingSeam a (z,⟨0,by constructor <;> norm_num⟩))))
    have heq : D.symm ∘ (H ∘ C.uncappingSeam a) = C.uncappingSeam a := by
      funext x
      exact D.symm_apply_apply _
    exact heq ▸ h

section Uniqueness

variable [ChartedSpace E3 C.UncappingQuotient]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E3 P]

theorem isLocalDiffeomorph_of_uncapping_generators
    (hinterior : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hseam : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (f : C.UncappingQuotient → P)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (f ∘ C.uncappingInteriorProjection))
    (hs : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (f ∘ C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := by
  intro q
  rcases C.uncappingQuotient_covered_by_interior_and_seam q with ⟨y,hy⟩ | ⟨a,z,hz⟩
  · change C.uncappingInteriorProjection y = q at hy
    rw [← hy]
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hi y) (hinterior y)
  · rw [← hz]
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hs a z) (hseam a z)

def uncappingDiffeomorphOfHomeomorph
    (hinterior : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hseam : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (H : C.UncappingQuotient ≃ₜ P)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (H ∘ C.uncappingInteriorProjection))
    (hs : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (H ∘ C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) :
    C.UncappingQuotient ≃ₘ⟮𝓡 3,𝓡 3⟯ P :=
  (C.isLocalDiffeomorph_of_uncapping_generators hinterior hseam H hi hs).diffeomorphOfBijective H.bijective

@[simp] theorem uncappingDiffeomorphOfHomeomorph_apply
    (hinterior : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hseam : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (H : C.UncappingQuotient ≃ₜ P)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (H ∘ C.uncappingInteriorProjection))
    (hs : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (H ∘ C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) (q : C.UncappingQuotient) :
    C.uncappingDiffeomorphOfHomeomorph hinterior hseam H hi hs q = H q := rfl

theorem uncappingDiffeomorphOfHomeomorph_symm_apply
    (hinterior : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hseam : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (H : C.UncappingQuotient ≃ₜ P)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (H ∘ C.uncappingInteriorProjection))
    (hs : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (H ∘ C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) (p : P) :
    (C.uncappingDiffeomorphOfHomeomorph hinterior hseam H hi hs).symm p = H.symm p := by
  apply H.injective
  exact (C.uncappingDiffeomorphOfHomeomorph hinterior hseam H hi hs).apply_symm_apply p |>.trans
    (H.apply_symm_apply p).symm

theorem exists_uncapping_diffeomorph
    (hinterior : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hseam : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) :
    ∃ D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier,
      ∀ x : T.core, D (Quot.mk C.innerCapRelation
        (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
          (C.coreImageHomeomorph x))) = x.val := by
  obtain ⟨H, hcore, hi, hs⟩ := C.exists_uncapping_homeomorph_localDiffeomorph
  exact ⟨C.uncappingDiffeomorphOfHomeomorph hinterior hseam H hi hs, hcore⟩

end Uniqueness

theorem contMDiff_id_of_uncapping_generators
    (α β : ChartedSpace E3 C.UncappingQuotient)
    (hαi : letI := α; IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hβi : letI := β; IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hαs : letI := α; ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (hβs : letI := β; ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) :
    @ContMDiff ℝ _ E3 _ _ E3 _ (𝓡 3) C.UncappingQuotient _ α
      E3 _ _ E3 _ (𝓡 3) C.UncappingQuotient _ β ∞ id := by
  let _ := β
  intro q
  rcases C.uncappingQuotient_covered_by_interior_and_seam q with ⟨y,hy⟩ | ⟨a,z,hz⟩
  · rw [← hy]
    exact @IsLocalDiffeomorphAt.contMDiffAt_of_comp ℝ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (𝓡 3) (𝓡 3) (𝓡 3) C.uncappingInterior _ _ _ _ _ α _ β
      ∞ _ y (hαi y) id ((hβi y).contMDiffAt)
  · rw [← hz]
    exact @IsLocalDiffeomorphAt.contMDiffAt_of_comp ℝ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (𝓡 3) _ _ _ _ _ _ α _ β
      ∞ _ _ (hαs a z) id ((hβs a z).contMDiffAt)

def uncappingStructureDiffeomorph
    (α β : ChartedSpace E3 C.UncappingQuotient)
    (hαi : letI := α; IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hβi : letI := β; IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hαs : letI := α; ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (hβs : letI := β; ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) :
    @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _ (𝓡 3) (𝓡 3)
      C.UncappingQuotient _ α C.UncappingQuotient _ β ∞ :=
  @Diffeomorph.mk ℝ _ _ _ _ _ _ _ _ _ _ _ (𝓡 3) (𝓡 3)
    _ _ α _ _ β ∞ (Equiv.refl _)
    (C.contMDiff_id_of_uncapping_generators α β hαi hβi hαs hβs)
    (C.contMDiff_id_of_uncapping_generators β α hβi hαi hβs hαs)

@[simp] theorem uncappingStructureDiffeomorph_apply
    (α β : ChartedSpace E3 C.UncappingQuotient)
    (hαi : letI := α; IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hβi : letI := β; IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hαs : letI := α; ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (hβs : letI := β; ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval))) (q : C.UncappingQuotient) :
    C.uncappingStructureDiffeomorph α β hαi hβi hαs hβs q = q := rfl

end DifferentialGeometry.Topology.SphericalCapping
