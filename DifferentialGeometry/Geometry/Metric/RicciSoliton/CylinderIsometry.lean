import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.LocalIsometryRigidity
import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Product

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

private theorem mfderiv_fst_roundThreeCylinderHorizontal
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2) Prod.fst (y, s)
        (roundThreeCylinderHorizontal y s v) =
      v := by
  rw [mfderiv_fst]
  exact roundThreeCylinderHorizontal_fst y s v

private theorem mfderiv_snd_roundThreeCylinderHorizontal
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

private def roundThreeCylinderVertical
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (a : TangentSpace 𝓘(Real, Real) s) :
    TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) (y, s) :=
  show TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) (y, s) from
    ((0 : TangentSpace (𝓡 2) y), a)

private theorem mfderiv_fst_roundThreeCylinderVertical
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (a : TangentSpace 𝓘(Real, Real) s) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2) Prod.fst (y, s)
        (roundThreeCylinderVertical y s a) =
      0 := by
  rw [mfderiv_fst]
  rfl

private theorem mfderiv_snd_roundThreeCylinderVertical
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (a : TangentSpace 𝓘(Real, Real) s) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real) Prod.snd (y, s)
        (roundThreeCylinderVertical y s a) =
      a := by
  rw [mfderiv_snd]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem roundThreeCylinderShrinkerMetric_inner_horizontal
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (z : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) (y, s))
    (v : TangentSpace (𝓡 2) y) :
    roundThreeCylinderShrinkerMetric.inner (y, s) z
        (roundThreeCylinderHorizontal y s v) =
      roundTwoSphereShrinkerMetric.inner y
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2)
          Prod.fst (y, s) z) v := by
  rw [roundThreeCylinderShrinkerMetric,
    SmoothRiemannianMetric.prod_inner,
    mfderiv_fst_roundThreeCylinderHorizontal,
    mfderiv_snd_roundThreeCylinderHorizontal,
    DifferentialGeometry.euclideanMetric_inner,
    inner_zero_right, add_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem roundThreeCylinderShrinkerMetric_inner_vertical_vertical
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (a b : TangentSpace 𝓘(Real, Real) s) :
    roundThreeCylinderShrinkerMetric.inner (y, s)
        (roundThreeCylinderVertical y s a)
        (roundThreeCylinderVertical y s b) =
      inner Real a b := by
  rw [roundThreeCylinderShrinkerMetric,
    SmoothRiemannianMetric.prod_inner,
    mfderiv_fst_roundThreeCylinderVertical,
    mfderiv_fst_roundThreeCylinderVertical,
    mfderiv_snd_roundThreeCylinderVertical,
    mfderiv_snd_roundThreeCylinderVertical,
    DifferentialGeometry.euclideanMetric_inner]
  simp only [map_zero, zero_add]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem roundThreeCylinderShrinkerMetric_inner_vertical_horizontal
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (a : TangentSpace 𝓘(Real, Real) s)
    (v : TangentSpace (𝓡 2) y) :
    roundThreeCylinderShrinkerMetric.inner (y, s)
        (roundThreeCylinderVertical y s a)
        (roundThreeCylinderHorizontal y s v) =
      0 := by
  rw [roundThreeCylinderShrinkerMetric_inner_horizontal,
    mfderiv_fst_roundThreeCylinderVertical]
  have hzero := map_zero (roundTwoSphereShrinkerMetric.inner y)
  exact congrArg (fun L => L v) hzero

private theorem mfderiv_roundThreeCylinderCentralSliceDiffeomorph_horizontal
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real))
        ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
          (roundThreeCylinderHorizontal y 0 v) =
      roundThreeCylinderHorizontal
        (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential y) 0
        (mfderiv (𝓡 2) (𝓡 2)
          (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential) y v) := by
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
  have hleft := mfderiv_comp_apply y hΦ (hι y) v
  have hright := mfderiv_comp_apply y (hι (φ y)) hφ v
  rw [hcomp] at hleft
  rw [mfderiv_roundThreeCylinderCentralSliceInclusion] at hleft hright
  exact hleft.symm.trans hright

private def roundThreeCylinderLineUnit :
    TangentSpace 𝓘(Real, Real) (0 : Real) :=
  show TangentSpace 𝓘(Real, Real) (0 : Real) from (1 : Real)

private theorem roundThreeCylinderTangent_decompose
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (z : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) (y, s)) :
    z =
      roundThreeCylinderHorizontal y s
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2)
            Prod.fst (y, s) z) +
        roundThreeCylinderVertical y s
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real)
            Prod.snd (y, s) z) := by
  rw [mfderiv_fst, mfderiv_snd]
  apply Prod.ext
  · change z.1 = z.1 + 0
    rw [add_zero]
  · change z.2 = 0 + z.2
    rw [zero_add]

private theorem roundThreeCylinderVertical_eq_smul_lineUnit
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (a : TangentSpace 𝓘(Real, Real) (0 : Real)) :
    roundThreeCylinderVertical y 0 a =
      (show Real from a) •
        roundThreeCylinderVertical y 0 roundThreeCylinderLineUnit := by
  apply Prod.ext
  · change (0 : TangentSpace (𝓡 2) y) =
      (show Real from a) • (0 : TangentSpace (𝓡 2) y)
    rw [smul_zero]
  · change (show Real from a) = (show Real from a) * 1
    rw [mul_one]

private theorem mfderiv_prodCongr_roundThreeCylinderHorizontal
    (φ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
      ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (ψ : Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (v : TangentSpace (𝓡 2) y) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real))
        ((𝓡 2).prod 𝓘(Real, Real)) (φ.prodCongr ψ) (y, s)
          (roundThreeCylinderHorizontal y s v) =
      roundThreeCylinderHorizontal (φ y) (ψ s)
        (mfderiv (𝓡 2) (𝓡 2) φ y v) := by
  have hφ : MDifferentiableAt (𝓡 2) (𝓡 2) φ y :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hψ : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real) ψ s :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  rw [Diffeomorph.coe_prodCongr, mfderiv_prodMap hφ hψ]
  change
    (mfderiv (𝓡 2) (𝓡 2) φ y v,
      mfderiv 𝓘(Real, Real) 𝓘(Real, Real) ψ s 0) =
        (mfderiv (𝓡 2) (𝓡 2) φ y v,
          (0 : TangentSpace 𝓘(Real, Real) (ψ s)))
  rw [map_zero]

private theorem mfderiv_prodCongr_roundThreeCylinderVertical
    (φ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
      ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (ψ : Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real)
    (a : TangentSpace 𝓘(Real, Real) s) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real))
        ((𝓡 2).prod 𝓘(Real, Real)) (φ.prodCongr ψ) (y, s)
          (roundThreeCylinderVertical y s a) =
      roundThreeCylinderVertical (φ y) (ψ s)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) ψ s a) := by
  have hφ : MDifferentiableAt (𝓡 2) (𝓡 2) φ y :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hψ : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real) ψ s :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  rw [Diffeomorph.coe_prodCongr, mfderiv_prodMap hφ hψ]
  change
    (mfderiv (𝓡 2) (𝓡 2) φ y 0,
      mfderiv 𝓘(Real, Real) 𝓘(Real, Real) ψ s a) =
        ((0 : TangentSpace (𝓡 2) (φ y)),
          mfderiv 𝓘(Real, Real) 𝓘(Real, Real) ψ s a)
  rw [map_zero]

private theorem mfderiv_roundThreeCylinderDiffeomorph_vertical_of_unit
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (ε : Real)
    (hunit :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
            (roundThreeCylinderVertical y 0 roundThreeCylinderLineUnit) =
        roundThreeCylinderVertical
          (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential y) 0 ε)
    (a : TangentSpace 𝓘(Real, Real) (0 : Real)) :
    mfderiv ((𝓡 2).prod 𝓘(Real, Real))
        ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
          (roundThreeCylinderVertical y 0 a) =
      roundThreeCylinderVertical
        (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential y) 0
        ((show Real from a) * ε) := by
  rw [roundThreeCylinderVertical_eq_smul_lineUnit]
  rw [map_smul, hunit]
  apply Prod.ext
  · change (show Real from a) •
        (0 : TangentSpace (𝓡 2)
          (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential y)) = 0
    rw [smul_zero]
  · rfl

private theorem mfderiv_realNegDiffeomorph_zero
    (a : TangentSpace 𝓘(Real, Real) (0 : Real)) :
    mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (ContinuousLinearEquiv.neg Real).toDiffeomorph 0 a =
      show TangentSpace 𝓘(Real, Real) (0 : Real) from
        -(show Real from a) := by
  rw [mfderiv_eq_fderiv]
  change (fderiv Real (fun q : Real => -q) 0 (show Real from a)) =
    -(show Real from a)
  rw [show (fun q : Real => -q) = -(id : Real → Real) by rfl,
    fderiv_neg, fderiv_id]
  rfl

private theorem mfderiv_realReflDiffeomorph_zero
    (a : TangentSpace 𝓘(Real, Real) (0 : Real)) :
    mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (Diffeomorph.refl 𝓘(Real, Real) Real ∞) 0 a = a := by
  rw [Diffeomorph.coe_refl, mfderiv_id]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem roundThreeCylinderDiffeomorph_eq_of_point_mfderiv
    (Φ Ψ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hΦmetric :
      Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Φ =
        roundThreeCylinderShrinkerMetric)
    (hΨmetric :
      Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Ψ =
        roundThreeCylinderShrinkerMetric)
    (p : RoundThreeCylinder)
    (hpoint : Φ p = Ψ p)
    (hmfderiv :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Φ p =
        mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Ψ p) :
    Φ = Ψ := by
  have hfinrank :
      1 < Module.finrank Real (EuclideanSpace Real (Fin 3)) := by
    simp
  let : PreconnectedSpace
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank hfinrank)
        (0 : EuclideanSpace Real (Fin 3)) 1)
  have hΦpres
      (x : RoundThreeCylinder)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
      roundThreeCylinderShrinkerMetric.inner x v w =
        roundThreeCylinderShrinkerMetric.inner (Φ x)
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ x v)
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ x w) := by
    calc
      _ = (Diffeomorph.pullbackMetric
          roundThreeCylinderShrinkerMetric Φ).inner x v w := by
            rw [hΦmetric]
      _ = _ := Diffeomorph.pullbackMetric_inner _ _ _ _ _
  have hΨpres
      (x : RoundThreeCylinder)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
      roundThreeCylinderShrinkerMetric.inner x v w =
        roundThreeCylinderShrinkerMetric.inner (Ψ x)
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Ψ x v)
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Ψ x w) := by
    calc
      _ = (Diffeomorph.pullbackMetric
          roundThreeCylinderShrinkerMetric Ψ).inner x v w := by
            rw [hΨmetric]
      _ = _ := Diffeomorph.pullbackMetric_inner _ _ _ _ _
  have hfun :
      (Φ : RoundThreeCylinder → RoundThreeCylinder) =
        (Ψ : RoundThreeCylinder → RoundThreeCylinder) :=
    Riemannian.localIso_rigid
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerMetric
      Φ.isLocalDiffeomorph Ψ.isLocalDiffeomorph
      hΦpres hΨpres p hpoint hmfderiv
  apply Diffeomorph.ext
  exact congrFun hfun

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem mfderiv_roundThreeCylinderDiffeomorph_vertical_unit
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (hmetric : Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Φ =
      roundThreeCylinderShrinkerMetric)
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    ∃ ε : Real, (ε = 1 ∨ ε = -1) ∧
      mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
            (roundThreeCylinderVertical y 0 roundThreeCylinderLineUnit) =
        roundThreeCylinderVertical
          (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential y) 0 ε := by
  let φ := roundThreeCylinderCentralSliceDiffeomorph Φ hpotential
  let p : RoundThreeCylinder := (y, 0)
  let q : RoundThreeCylinder := (φ y, 0)
  let vin := roundThreeCylinderVertical y 0 roundThreeCylinderLineUnit
  let z : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) q :=
    mfderiv ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) Φ p vin
  let a : TangentSpace (𝓡 2) (φ y) :=
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2)
      Prod.fst q z
  let b : TangentSpace 𝓘(Real, Real) (0 : Real) :=
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      Prod.snd q z
  let L : TangentSpace (𝓡 2) y ≃L[Real] TangentSpace (𝓡 2) (φ y) :=
    φ.mfderivToContinuousLinearEquiv (by decide) y
  let u : TangentSpace (𝓡 2) y := L.symm a
  have hLu : mfderiv (𝓡 2) (𝓡 2) φ y u = a := by
    rw [← φ.mfderivToContinuousLinearEquiv_coe (by decide)]
    exact L.apply_symm_apply a
  have hhorizontal :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Φ p
            (roundThreeCylinderHorizontal y 0 u) =
        roundThreeCylinderHorizontal (φ y) 0 a := by
    simpa only [p, φ, hLu] using
      mfderiv_roundThreeCylinderCentralSliceDiffeomorph_horizontal
        Φ hpotential y u
  have hbase : Φ p = q := by
    simpa only [p, q, φ] using
      roundThreeCylinderCentralSliceDiffeomorph_apply Φ hpotential y
  have hisometry
      (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) p) :
      roundThreeCylinderShrinkerMetric.inner p v w =
        roundThreeCylinderShrinkerMetric.inner (Φ p)
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ p v)
          (mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ p w) := by
    calc
      _ = (Diffeomorph.pullbackMetric
          roundThreeCylinderShrinkerMetric Φ).inner p v w := by
            rw [hmetric]
      _ = _ := Diffeomorph.pullbackMetric_inner _ _ _ _ _
  have hcross := hisometry vin (roundThreeCylinderHorizontal y 0 u)
  dsimp only [vin] at hcross
  rw [hhorizontal, hbase, show p = (y, 0) from rfl,
    roundThreeCylinderShrinkerMetric_inner_vertical_horizontal] at hcross
  have haa : roundTwoSphereShrinkerMetric.inner (φ y) a a = 0 := by
    rw [roundThreeCylinderShrinkerMetric_inner_horizontal] at hcross
    exact hcross.symm
  have ha : a = 0 := by
    by_contra hne
    have hpos := roundTwoSphereShrinkerMetric.pos (φ y) a hne
    rw [haa] at hpos
    exact lt_irrefl 0 hpos
  have hz : z = roundThreeCylinderVertical (φ y) 0 b := by
    apply Prod.ext
    · change z.1 = 0
      dsimp only [a] at ha
      rw [mfderiv_fst] at ha
      exact ha
    · change z.2 = b
      dsimp only [b]
      rw [mfderiv_snd]
      rfl
  have hnorm := hisometry vin vin
  rw [show p = (y, 0) from rfl,
    roundThreeCylinderShrinkerMetric_inner_vertical_vertical,
    hbase] at hnorm
  dsimp only [roundThreeCylinderLineUnit] at hnorm
  change inner Real (1 : Real) 1 =
    roundThreeCylinderShrinkerMetric.inner q z z at hnorm
  rw [hz, show q = (φ y, 0) from rfl,
    roundThreeCylinderShrinkerMetric_inner_vertical_vertical] at hnorm
  let ε : Real := show Real from b
  have hnorm_real : (1 : Real) * 1 = ε * ε := by
    rw [← Real.inner_apply, ← Real.inner_apply]
    exact hnorm
  have hε : ε ^ 2 = 1 := by
    simpa only [pow_two, one_mul] using hnorm_real.symm
  have hε_sign : ε = 1 ∨ ε = -1 := sq_eq_one_iff.mp hε
  refine ⟨ε, hε_sign, ?_⟩
  have hz' := hbase.symm ▸ hz
  simpa only [p, q, φ, vin, z, ε] using hz'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem roundThreeCylinderDiffeomorph_eq_prodCongr_refl_or_neg
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (hmetric : Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Φ =
      roundThreeCylinderShrinkerMetric) :
    Φ =
        (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential).prodCongr
          (Diffeomorph.refl 𝓘(Real, Real) Real ∞) ∨
      Φ =
        (roundThreeCylinderCentralSliceDiffeomorph Φ hpotential).prodCongr
          (ContinuousLinearEquiv.neg Real).toDiffeomorph := by
  let φ := roundThreeCylinderCentralSliceDiffeomorph Φ hpotential
  let ψneg : Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real :=
    (ContinuousLinearEquiv.neg Real).toDiffeomorph
  have hφmetric :
      Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric φ =
        roundTwoSphereShrinkerMetric := by
    simpa only [φ] using
      roundThreeCylinderCentralSliceDiffeomorph_pullbackMetric
        Φ hpotential hmetric
  have hnegmetric :
      Diffeomorph.pullbackMetric (euclideanMetric (E := Real))
          ψneg =
        euclideanMetric := by
    have hdiffeo :
        ψneg =
          (LinearIsometryEquiv.neg Real : Real ≃ₗᵢ[Real] Real).toContinuousLinearEquiv.toDiffeomorph := by
      dsimp only [ψneg]
      apply Diffeomorph.ext
      intro x
      rfl
    rw [hdiffeo]
    exact
      LinearIsometryEquiv.pullbackMetric_euclidean
        (E := Real) (LinearIsometryEquiv.neg Real)
  have hreflmetric :
      Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
          (φ.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real ∞)) =
        roundThreeCylinderShrinkerMetric := by
    rw [roundThreeCylinderShrinkerMetric,
      Diffeomorph.pullbackMetric_prodCongr,
      hφmetric, Diffeomorph.pullbackMetric_refl]
  have hprodnegmetric :
      Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
          (φ.prodCongr ψneg) =
        roundThreeCylinderShrinkerMetric := by
    rw [roundThreeCylinderShrinkerMetric,
      Diffeomorph.pullbackMetric_prodCongr,
      hφmetric, hnegmetric]
  let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
  obtain ⟨ε, hε, hunit⟩ :=
    mfderiv_roundThreeCylinderDiffeomorph_vertical_unit
      Φ hpotential hmetric y
  have hhorizontal
      (v : TangentSpace (𝓡 2) y) :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real))
          ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
            (roundThreeCylinderHorizontal y 0 v) =
        roundThreeCylinderHorizontal (φ y) 0
          (mfderiv (𝓡 2) (𝓡 2) φ y v) := by
    simpa only [φ] using
      mfderiv_roundThreeCylinderCentralSliceDiffeomorph_horizontal
        Φ hpotential y v
  rcases hε with rfl | rfl
  · left
    have hvertical
        (a : TangentSpace 𝓘(Real, Real) (0 : Real)) :
        mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
              (roundThreeCylinderVertical y 0 a) =
          roundThreeCylinderVertical (φ y) 0
            (show Real from a) := by
      have hraw :=
        mfderiv_roundThreeCylinderDiffeomorph_vertical_of_unit
          Φ hpotential y 1 hunit a
      have hcoef : (show Real from a) * 1 = (show Real from a) :=
        mul_one _
      with_unfolding_all
        exact hraw.trans (congrArg
          (fun b : Real => roundThreeCylinderVertical (φ y) 0 b) hcoef)
    have hpoint :
        Φ (y, 0) =
          (φ.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real ∞)) (y, 0) := by
      change Φ (y, 0) = (φ y, 0)
      simpa only [φ] using
        roundThreeCylinderCentralSliceDiffeomorph_apply Φ hpotential y
    have hmfderiv :
        mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0) =
          mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real))
              (φ.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real ∞))
              (y, 0) := by
      apply ContinuousLinearMap.ext
      intro z
      let u : TangentSpace (𝓡 2) y :=
        mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2)
          Prod.fst (y, 0) z
      let a : TangentSpace 𝓘(Real, Real) (0 : Real) :=
        mfderiv ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real)
          Prod.snd (y, 0) z
      have hz : z = roundThreeCylinderHorizontal y 0 u +
          roundThreeCylinderVertical y 0 a := by
        simpa only [u, a] using roundThreeCylinderTangent_decompose y 0 z
      have hΦapply :
          mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0) z =
            roundThreeCylinderHorizontal (φ y) 0
                (mfderiv (𝓡 2) (𝓡 2) φ y u) +
              roundThreeCylinderVertical (φ y) 0 (show Real from a) := by
        calc
          _ = mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
                (roundThreeCylinderHorizontal y 0 u +
                  roundThreeCylinderVertical y 0 a) :=
            congrArg _ hz
          _ = _ := by
            rw [map_add, hhorizontal, hvertical]
            rfl
      have hprodapply :
          mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real))
                (φ.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real ∞))
                (y, 0) z =
            roundThreeCylinderHorizontal (φ y) 0
                (mfderiv (𝓡 2) (𝓡 2) φ y u) +
              roundThreeCylinderVertical (φ y) 0 (show Real from a) := by
        calc
          _ = mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real))
                (φ.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real ∞))
                (y, 0)
                (roundThreeCylinderHorizontal y 0 u +
                  roundThreeCylinderVertical y 0 a) :=
            congrArg _ hz
          _ = _ := by
            with_unfolding_all
              rw [map_add,
                mfderiv_prodCongr_roundThreeCylinderHorizontal,
                mfderiv_prodCongr_roundThreeCylinderVertical,
                mfderiv_realReflDiffeomorph_zero]
              rfl
      with_unfolding_all exact hΦapply.trans hprodapply.symm
    exact roundThreeCylinderDiffeomorph_eq_of_point_mfderiv
      Φ (φ.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real ∞))
      hmetric hreflmetric (y, 0) hpoint hmfderiv
  · right
    have hvertical
        (a : TangentSpace 𝓘(Real, Real) (0 : Real)) :
        mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
              (roundThreeCylinderVertical y 0 a) =
          roundThreeCylinderVertical (φ y) 0
            (-(show Real from a)) := by
      have hraw :=
        mfderiv_roundThreeCylinderDiffeomorph_vertical_of_unit
          Φ hpotential y (-1) hunit a
      have hcoef : (show Real from a) * (-1) = -(show Real from a) := by
        rw [mul_neg, mul_one]
      with_unfolding_all
        exact hraw.trans (congrArg
          (fun b : Real => roundThreeCylinderVertical (φ y) 0 b) hcoef)
    have hpoint :
        Φ (y, 0) =
          (φ.prodCongr ψneg) (y, 0) := by
      calc
        Φ (y, 0) = (φ y, 0) := by
          simpa only [φ] using
            roundThreeCylinderCentralSliceDiffeomorph_apply Φ hpotential y
        _ = (φ.prodCongr ψneg) (y, 0) := by
          dsimp only [ψneg]
          apply Prod.ext
          · rfl
          · simp
    have hmfderiv :
        mfderiv ((𝓡 2).prod 𝓘(Real, Real))
            ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0) =
          mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real))
              (φ.prodCongr ψneg)
              (y, 0) := by
      apply ContinuousLinearMap.ext
      intro z
      let u : TangentSpace (𝓡 2) y :=
        mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2)
          Prod.fst (y, 0) z
      let a : TangentSpace 𝓘(Real, Real) (0 : Real) :=
        mfderiv ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real)
          Prod.snd (y, 0) z
      have hz : z = roundThreeCylinderHorizontal y 0 u +
          roundThreeCylinderVertical y 0 a := by
        simpa only [u, a] using roundThreeCylinderTangent_decompose y 0 z
      have hΦapply :
          mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0) z =
            roundThreeCylinderHorizontal (φ y) 0
                (mfderiv (𝓡 2) (𝓡 2) φ y u) +
              roundThreeCylinderVertical (φ y) 0
                (-(show Real from a)) := by
        calc
          _ = mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real)) Φ (y, 0)
                (roundThreeCylinderHorizontal y 0 u +
                  roundThreeCylinderVertical y 0 a) :=
            congrArg _ hz
          _ = _ := by
            rw [map_add, hhorizontal, hvertical]
            rfl
      have hprodpoint : (φ.prodCongr ψneg) (y, 0) = (φ y, 0) := by
        change (φ y, ψneg 0) = (φ y, 0)
        apply Prod.ext
        · rfl
        · simp [ψneg]
      have hprodapply :
          mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real))
                (φ.prodCongr ψneg) (y, 0) z =
            roundThreeCylinderHorizontal (φ y) 0
                (mfderiv (𝓡 2) (𝓡 2) φ y u) +
              roundThreeCylinderVertical (φ y) 0
                (-(show Real from a)) := by
        rw [hprodpoint]
        calc
          _ = mfderiv ((𝓡 2).prod 𝓘(Real, Real))
              ((𝓡 2).prod 𝓘(Real, Real))
                (φ.prodCongr ψneg) (y, 0)
                (roundThreeCylinderHorizontal y 0 u +
                  roundThreeCylinderVertical y 0 a) :=
            congrArg _ hz
          _ = _ := by
            rw [map_add,
              mfderiv_prodCongr_roundThreeCylinderHorizontal,
              mfderiv_prodCongr_roundThreeCylinderVertical]
            have hψzero : ψneg 0 = 0 := by
              simp [ψneg]
            rw [hψzero]
            have hψderiv :
                mfderiv 𝓘(Real, Real) 𝓘(Real, Real) ψneg 0 a =
                  show TangentSpace 𝓘(Real, Real) (0 : Real) from
                    -(show Real from a) := by
              simpa only [ψneg] using mfderiv_realNegDiffeomorph_zero a
            have hsum := congrArg
              (fun b : TangentSpace 𝓘(Real, Real) (0 : Real) =>
                roundThreeCylinderHorizontal (φ y) 0
                    (mfderiv (𝓡 2) (𝓡 2) φ y u) +
                  roundThreeCylinderVertical (φ y) 0 b)
              hψderiv
            exact hprodpoint.symm ▸ hsum
      with_unfolding_all exact hΦapply.trans hprodapply.symm
    simpa only [ψneg] using
      roundThreeCylinderDiffeomorph_eq_of_point_mfderiv
        Φ (φ.prodCongr ψneg)
        hmetric hprodnegmetric (y, 0) hpoint hmfderiv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem roundThreeCylinderSolitonAutomorphism_normal_form
    (Φ : RoundThreeCylinder
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        RoundThreeCylinder)
    (hpotential : ∀ x,
      roundThreeCylinderShrinkerPotential (Φ x) =
        roundThreeCylinderShrinkerPotential x)
    (hmetric : Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Φ =
      roundThreeCylinderShrinkerMetric) :
    ∃ φ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
        ≃ₘ⟮𝓡 2, 𝓡 2⟯
          Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric φ =
        roundTwoSphereShrinkerMetric ∧
        (Φ = φ.prodCongr
            (Diffeomorph.refl 𝓘(Real, Real) Real ∞) ∨
          Φ = φ.prodCongr (ContinuousLinearEquiv.neg Real).toDiffeomorph) := by
  let φ := roundThreeCylinderCentralSliceDiffeomorph Φ hpotential
  have hφmetric :
      Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric φ =
        roundTwoSphereShrinkerMetric := by
    simpa only [φ] using
      roundThreeCylinderCentralSliceDiffeomorph_pullbackMetric
        Φ hpotential hmetric
  obtain hΦ | hΦ := roundThreeCylinderDiffeomorph_eq_prodCongr_refl_or_neg
    Φ hpotential hmetric
  · exact ⟨φ, hφmetric, Or.inl hΦ⟩
  · exact ⟨φ, hφmetric, Or.inr hΦ⟩

end DifferentialGeometry.Geometry
