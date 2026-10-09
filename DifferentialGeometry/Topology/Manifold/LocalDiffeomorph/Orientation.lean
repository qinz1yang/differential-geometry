import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

theorem localDiffeomorph_orientation_dichotomy [ConnectedSpace M]
    (f : M → N) (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f) (hinj : Injective f)
    (oM : ManifoldOrientation (𝓡 n) M n) (oN : ManifoldOrientation (𝓡 n) N n) :
    (∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oM.orientation x) = oN.orientation (f x)) ∨
    (∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oM.orientation x) = -oN.orientation (f x)) := by
  let U : TopologicalSpace.Opens N := ⟨range f, hf.isOpenMap.isOpen_range⟩
  let g : M → U := fun x => ⟨f x, x, rfl⟩
  have hg : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ g :=
    fun x => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (V := U) (f := f) (fun y => ⟨y, rfl⟩) (hf x)
  let F := hg.diffeomorphOfBijective ⟨fun x y h => hinj (congrArg Subtype.val h), by
    rintro ⟨x, y, hy⟩
    exact ⟨y, Subtype.ext hy⟩⟩
  let _ : ConnectedSpace U := F.toHomeomorph.connectedSpace_iff.mp inferInstance
  have hder (x : M) : (F.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) (F : M → U) x v = mfderiv (𝓡 n) (𝓡 n) f x v
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp F x]
    rfl
  rcases F.preservesOrientation_or_preservesOrientation_opposite oM (oN.restrictOpen U) with hp | hn
  · left
    intro x
    have h := hp x
    rw [hder] at h
    exact h
  · right
    intro x
    have h := hn x
    rw [hder] at h
    exact h

theorem localDiffeomorph_orientation_comp
    (f : M → N) (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (oM : ManifoldOrientation (𝓡 n) M n) (oN oN' : ManifoldOrientation (𝓡 n) N n)
    (hfo : ∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oM.orientation x) = oN.orientation (f x))
    (r : N ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (hr : r.preservesOrientation oN oN') :
    ∀ x, Orientation.map (Fin n)
      ((DifferentialGeometry.isLocalDiffeomorph_comp r.isLocalDiffeomorph hf).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv (oM.orientation x) = oN'.orientation (r (f x)) := by
  intro x
  have he : ((DifferentialGeometry.isLocalDiffeomorph_comp r.isLocalDiffeomorph hf).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv =
      (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
        (r.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) (r ∘ f) x v = mfderiv (𝓡 n) (𝓡 n) r (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x v)
    exact mfderiv_comp_apply x (r.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v
  rw [he, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between, hfo]
  exact hr (f x)

theorem exists_orientationReversing_sphereTwoTimesCircleLift :
    ∃ r : sphereTwoTimesCircleLift.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier,
      r.preservesOrientation sphereTwoTimesCircleLift.orientation.opposite sphereTwoTimesCircleLift.orientation := by
  obtain ⟨r, hr⟩ := sphereTwoTimesCircleOrientationClosure_holds
  let E := sphereTwoTimesCircleModelCopy.equiv
  have hE := Diffeomorph.preservesOrientation_symm sphereTwoTimesCircleLift_preservesOrientation
  refine ⟨(E.symm.trans r).trans E, ?_⟩
  exact Diffeomorph.preservesOrientation_trans
    (Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_opposite sphereTwoTimesCircleLift_preservesOrientation) hr) hE

end DifferentialGeometry.Topology.Manifold

namespace IsLocalDiffeomorph

variable {E H K X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace K Y] [IsManifold J ∞ Y]
  {f : X → Y} {n : ℕ}

theorem orientation_agreement_isLocallyConstant
    (hf : IsLocalDiffeomorph I J ∞ f)
    (oX : DifferentialGeometry.ManifoldOrientation I X n)
    (oY : DifferentialGeometry.ManifoldOrientation J Y n) :
    IsLocallyConstant (fun x => Orientation.map (Fin n)
      ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv (oX.orientation x) =
        oY.orientation (f x)) := by
  have hd := oX.dimension_eq
  subst n
  let sX := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation I oX
  let sY := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation J oY
  let hb := fun x => ((hf x).mfderivToContinuousLinearEquiv (by simp)).bijective
  let sP := DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation I J f hf.contMDiff hb sY
  have hc := DifferentialGeometry.Topology.Manifold.smoothOrientation_agreement_locallyConstant I sP sX
  have heq : (fun x => sP.val x = sX.val x) =
      (fun x => Orientation.map (Fin (Module.finrank ℝ E))
        ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv (oX.orientation x) =
          oY.orientation (f x)) := by
    funext x
    apply propext
    have h := DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_eq_iff
      I J f hf.contMDiff hb sY sX x
    rw [DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_self] at h
    have hlin : (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective I J f hb x).toLinearEquiv =
        ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv := by
      apply LinearEquiv.ext
      intro w
      rfl
    rw [hlin] at h
    exact h
  exact heq ▸ hc

end IsLocalDiffeomorph
