import DifferentialGeometry.Topology.ThreeManifold.OrientedUncapping
import DifferentialGeometry.Topology.ThreeManifold.UncappingQuotientLocallyConstant

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  [ChartedSpace E3 C.UncappingQuotient] [IsManifold (𝓡 3) ∞ C.UncappingQuotient]

theorem uncapping_orientation_unique
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (o₁ o₂ : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3)
    (h₁ : ∀ y : C.uncappingInterior,
      Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (N.orientation.orientation y.val) = o₁.orientation (C.uncappingInteriorProjection y))
    (h₂ : ∀ y : C.uncappingInterior,
      Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (N.orientation.orientation y.val) = o₂.orientation (C.uncappingInteriorProjection y)) : o₁ = o₂ := by
  have hf : IsLocallyConstant (fun q => o₁.orientation q = o₂.orientation q) := by
    let h := Diffeomorph.refl (𝓡 3) C.UncappingQuotient ∞
    have hc := h.isLocalDiffeomorph.orientation_agreement_isLocallyConstant o₁ o₂
    have heq (q : C.UncappingQuotient) :
        ((h.isLocalDiffeomorph q).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv =
          LinearEquiv.refl ℝ (TangentSpace (𝓡 3) q) := by
      apply LinearEquiv.ext
      intro w
      change mfderiv (𝓡 3) (𝓡 3) id q w = w
      rw [mfderiv_id]
      rfl
    have heqfun : (fun q => Orientation.map (Fin 3)
        ((h.isLocalDiffeomorph q).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
          (o₁.orientation q) = o₂.orientation (h q)) =
        (fun q => o₁.orientation q = o₂.orientation q) := by
      funext q
      erw [heq,Orientation.map_refl]
      rfl
    exact heqfun ▸ hc
  apply ManifoldOrientation.ext
  intro q
  apply of_eq_true
  exact C.eq_of_uncappingInteriorProjection _ hf True (fun y =>
    propext ⟨fun _ => trivial,fun _ => (h₁ y).symm.trans (h₂ y)⟩) q

theorem preservesOrientation_uncapping
    (o : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3)
    (D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
    (hcore : ∀ x : T.core, D (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hproj : ∀ y : C.uncappingInterior,
      Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (N.orientation.orientation y.val) = o.orientation (C.uncappingInteriorProjection y)) :
    D.preservesOrientation o M.orientation := by
  obtain ⟨o',hD,hproj'⟩ := C.exists_uncapping_orientation D hcore hi
  exact C.uncapping_orientation_unique hi o' o hproj' hproj ▸ hD

theorem exists_oriented_uncapping_diffeomorph
    (o : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (hs : ∀ (a : T.Index) (z : S2),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
        (z, (⟨0, by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)))
    (hproj : ∀ y : C.uncappingInterior,
      Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (N.orientation.orientation y.val) = o.orientation (C.uncappingInteriorProjection y)) :
    ∃ D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier,
      (∀ x : T.core, D (Quot.mk C.innerCapRelation
        (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
          (C.coreImageHomeomorph x))) = x.val) ∧ D.preservesOrientation o M.orientation := by
  obtain ⟨D,hcore⟩ := C.exists_uncapping_diffeomorph hi hs
  exact ⟨D,hcore,C.preservesOrientation_uncapping o D hcore hi hproj⟩

end DifferentialGeometry.Topology.SphericalCapping
