import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

private abbrev RoundThreeCylinder :=
  Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real

private theorem roundThreeCylinderPotential_preserving_symm
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (x : RoundThreeCylinder) :
    roundThreeCylinderShrinkerPotential (Φ.symm x) =
      roundThreeCylinderShrinkerPotential x := by
  have h := hpotential (Φ.symm x)
  rw [Φ.apply_symm_apply] at h
  exact h.symm

private theorem roundThreeCylinderPotential_preserving_line_eq_zero
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (Φ (y, 0)).2 = 0 := by
  have hmem : Φ (y, 0) ∈ roundThreeCylinderCentralSlice := by
    rw [← roundThreeCylinderShrinkerPotential_eq_one_iff]
    rw [hpotential]
    exact (roundThreeCylinderShrinkerPotential_eq_one_iff (y, 0)).mpr rfl
  exact hmem

noncomputable def roundThreeCylinderCentralSliceDiffeomorph
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x) :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
      ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 where
  toFun y := (Φ (y, 0)).1
  invFun y := (Φ.symm (y, 0)).1
  left_inv y := by
    have hline := roundThreeCylinderPotential_preserving_line_eq_zero
      Φ hpotential y
    have hpair : ((Φ (y, 0)).1, (0 : Real)) = Φ (y, 0) := by
      exact Prod.ext rfl hline.symm
    change (Φ.symm ((Φ (y, 0)).1, 0)).1 = y
    rw [hpair, Φ.symm_apply_apply]
  right_inv y := by
    have hline := roundThreeCylinderPotential_preserving_line_eq_zero
      Φ.symm (roundThreeCylinderPotential_preserving_symm Φ hpotential) y
    have hpair : ((Φ.symm (y, 0)).1, (0 : Real)) = Φ.symm (y, 0) := by
      exact Prod.ext rfl hline.symm
    change (Φ ((Φ.symm (y, 0)).1, 0)).1 = y
    rw [hpair, Φ.apply_symm_apply]
  contMDiff_toFun := by
    exact (contMDiff_fst.comp
      (Φ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)))
  contMDiff_invFun := by
    exact (contMDiff_fst.comp
      (Φ.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)))

theorem roundThreeCylinderCentralSliceDiffeomorph_apply
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    Φ (y, 0) =
      (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential y, 0) := by
  apply Prod.ext
  · rfl
  · exact roundThreeCylinderPotential_preserving_line_eq_zero Φ hpotential y

private def roundThreeCylinderHorizontal
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) (y, s) :=
  show TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) (y, s) from
    (v, (0 : TangentSpace 𝓘(Real, Real) s))

@[simp] private theorem roundThreeCylinderHorizontal_fst
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    (ContinuousLinearMap.fst Real
      (TangentSpace (𝓡 2) y) (TangentSpace 𝓘(Real, Real) s))
        (roundThreeCylinderHorizontal y s v) = v := by
  rfl

@[simp] private theorem roundThreeCylinderHorizontal_snd
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    (ContinuousLinearMap.snd Real
      (TangentSpace (𝓡 2) y) (TangentSpace 𝓘(Real, Real) s))
        (roundThreeCylinderHorizontal y s v) = 0 := by
  rfl

@[simp] private theorem mfderiv_fst_roundThreeCylinderHorizontal
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2) Prod.fst (y, s)
        (roundThreeCylinderHorizontal y s v) =
      v := by
  rw [mfderiv_fst]
  exact roundThreeCylinderHorizontal_fst y s v

@[simp] private theorem mfderiv_snd_roundThreeCylinderHorizontal
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real) Prod.snd (y, s)
        (roundThreeCylinderHorizontal y s v) =
      0 := by
  rw [mfderiv_snd]
  exact roundThreeCylinderHorizontal_snd y s v

private theorem mfderiv_roundThreeCylinderCentralSliceInclusion
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) ((𝓡 2).prod 𝓘(Real, Real))
        (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          (z, (0 : Real))) y v =
      roundThreeCylinderHorizontal y 0 v := by
  have hid : MDifferentiableAt (𝓡 2) (𝓡 2)
      (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 => z) y :=
    mdifferentiableAt_id
  have hc : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun _ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (0 : Real)) y :=
    mdifferentiableAt_const
  have hprod := mfderiv_prodMk (hf := hid) (hg := hc)
  rw [hprod]
  change
    (mfderiv (𝓡 2) (𝓡 2) id y v,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun _ => (0 : Real)) y v) =
        (v, (0 : TangentSpace 𝓘(Real, Real) (0 : Real)))
  rw [mfderiv_id, mfderiv_const]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem roundThreeCylinderCentralSliceDiffeomorph_pullbackMetric
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (hmetric : Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Φ =
      roundThreeCylinderShrinkerMetric) :
    Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric
        (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential) =
      roundTwoSphereShrinkerMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rw [Diffeomorph.pullbackMetric_inner]
  let ι : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 →
      RoundThreeCylinder := fun z => (z, 0)
  let φ := roundThreeCylinderCentralSliceDiffeomorph Φ hpotential
  have hι (z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      MDifferentiableAt (𝓡 2)
        ((𝓡 2).prod 𝓘(Real, Real)) ι z :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hφ : MDifferentiableAt (𝓡 2) (𝓡 2) φ y :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt
      ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) Φ (ι y) :=
    Φ.contMDiff.mdifferentiableAt (by simp)
  have hcomp : (Φ : RoundThreeCylinder → RoundThreeCylinder) ∘ ι =
      ι ∘ (φ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 →
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
    funext z
    exact roundThreeCylinderCentralSliceDiffeomorph_apply Φ hpotential z
  have hhorizontal (u : TangentSpace (𝓡 2) y) :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
            (roundThreeCylinderHorizontal y 0 u) =
        roundThreeCylinderHorizontal (φ y) 0
          (mfderiv (𝓡 2) (𝓡 2) φ y u) := by
    have hleft := mfderiv_comp_apply y hΦ (hι y) u
    have hright := mfderiv_comp_apply y (hι (φ y)) hφ u
    rw [hcomp] at hleft
    rw [mfderiv_roundThreeCylinderCentralSliceInclusion] at hleft hright
    exact hleft.symm.trans hright
  have hinner :
      roundThreeCylinderShrinkerMetric.inner (Φ (y, 0))
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
              (roundThreeCylinderHorizontal y 0 v))
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
              (roundThreeCylinderHorizontal y 0 w)) =
        roundThreeCylinderShrinkerMetric.inner (y, 0)
          (roundThreeCylinderHorizontal y 0 v)
          (roundThreeCylinderHorizontal y 0 w) := by
    rw [← Diffeomorph.pullbackMetric_inner]
    exact congrArg
      (fun g : SmoothRiemannianMetric
          ((𝓡 2).prod 𝓘(Real, Real)) RoundThreeCylinder =>
        g.inner (y, 0)
          (roundThreeCylinderHorizontal y 0 v)
          (roundThreeCylinderHorizontal y 0 w)) hmetric
  rw [hhorizontal v, hhorizontal w] at hinner
  rw [roundThreeCylinderCentralSliceDiffeomorph_apply Φ hpotential y,
    roundThreeCylinderShrinkerMetric,
    SmoothRiemannianMetric.prod_inner,
    SmoothRiemannianMetric.prod_inner] at hinner
  rw [mfderiv_fst_roundThreeCylinderHorizontal,
    mfderiv_fst_roundThreeCylinderHorizontal,
    mfderiv_fst_roundThreeCylinderHorizontal,
    mfderiv_fst_roundThreeCylinderHorizontal,
    mfderiv_snd_roundThreeCylinderHorizontal,
    mfderiv_snd_roundThreeCylinderHorizontal,
    mfderiv_snd_roundThreeCylinderHorizontal,
    mfderiv_snd_roundThreeCylinderHorizontal] at hinner
  rw [DifferentialGeometry.euclideanMetric_inner] at hinner
  have hzero :
      inner Real
        (0 : TangentSpace 𝓘(Real, Real) (0 : Real))
        (0 : TangentSpace 𝓘(Real, Real) (0 : Real)) = 0 := by
    exact inner_zero_left _
  rw [hzero, add_zero, add_zero] at hinner
  simpa only [φ] using hinner

end DifferentialGeometry.Geometry
