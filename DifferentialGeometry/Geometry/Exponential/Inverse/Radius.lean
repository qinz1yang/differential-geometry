import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Exponential.Inverse.Branch
import DifferentialGeometry.Geometry.Exponential.Intrinsic.GaussLemma
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Operator.Operators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private noncomputable def modelMetricInner
    (g : SmoothRiemannianMetric I M) (p : M) : E →L[Real] E →L[Real] Real :=
  (ContinuousLinearMap.precompR E
    ((ContinuousLinearMap.precompL E (g.inner p)
      (tangentSpaceModelContinuousLinearEquiv
        (I := I) p).symm.toContinuousLinearMap).flip)).flip
          (tangentSpaceModelContinuousLinearEquiv
            (I := I) p).symm.toContinuousLinearMap

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private lemma modelMetricInner_apply
    (g : SmoothRiemannianMetric I M) (p : M) (u v : E) :
    modelMetricInner (I := I) g p u v =
      g.inner p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v) := by
  rfl

noncomputable def branchEnergy
    (g : SmoothRiemannianMetric I M)
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (z : M) : Real :=
  (1 / 2 : Real) *
    modelMetricInner (I := I) g p (B.inv z) (B.inv z)

noncomputable def branchRadius
    (g : SmoothRiemannianMetric I M)
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (z : M) : Real :=
  Real.sqrt
    (modelMetricInner (I := I) g p (B.inv z) (B.inv z))

theorem branchRadius_eq
    (g : SmoothRiemannianMetric I M)
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    branchRadius (I := I) g B =
      fun z => Real.sqrt (2 * branchEnergy (I := I) g B z) := by
  funext z
  simp only [branchRadius, branchEnergy]
  congr 1
  ring

theorem branchEnergy_exp
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source) :
    branchEnergy (I := I) g B
      (expMapIntrinsic (I := I) g hEnorm p u) =
        (1 / 2 : Real) * g.inner p u u := by
  have hinv :
      B.inv (expMapIntrinsic (I := I) g hEnorm p u) =
        tangentSpaceModelContinuousLinearEquiv (I := I) p u :=
    B.left_inv hu
  unfold branchEnergy
  rw [hinv, modelMetricInner_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem branchRadius_exp
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source) :
    branchRadius (I := I) g B
      (expMapIntrinsic (I := I) g hEnorm p u) =
        Real.sqrt (g.inner p u u) := by
  have hinv :
      B.inv (expMapIntrinsic (I := I) g hEnorm p u) =
        tangentSpaceModelContinuousLinearEquiv (I := I) p u :=
    B.left_inv hu
  unfold branchRadius
  rw [hinv, modelMetricInner_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem ExponentialInverseBranch.edist_le_radius
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p y : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hy : y ∈ B.dom) :
    riemannianEDist I p y ≤
      ENNReal.ofReal (branchRadius (I := I) g B y) := by
  let u : TangentSpace I p :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv y)
  have hdist :=
    intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p u
      (s := (0 : Real)) (t := (1 : Real)) zero_le_one
  have hright :
      expMapIntrinsic (I := I) g hEnorm p u = y :=
    B.right_inv hy
  rw [intrinsicGeodesic_zero, ← expMapIntrinsic_def, hright] at hdist
  simpa only [branchRadius, modelMetricInner_apply, u, sub_zero, mul_one] using hdist

theorem branchRadius_ray
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {x : TangentSpace I p} {t : Real}
    (ht : 0 < t)
    (hsrc : t • tangentSpaceModelContinuousLinearEquiv (I := I) p x ∈ B.hom.source) :
    (fun s : Real =>
      branchRadius (I := I) g B
        (intrinsicGeodesic (I := I) g hEnorm p x s))
      =ᶠ[𝓝 t]
    (fun s : Real => s * Real.sqrt (g.inner p x x)) := by
  have hlaunch : Continuous
      (fun s : Real => s • tangentSpaceModelContinuousLinearEquiv (I := I) p x) :=
    continuous_id.smul continuous_const
  have hsrc_ev :
      ∀ᶠ s in 𝓝 t,
        s • tangentSpaceModelContinuousLinearEquiv (I := I) p x ∈ B.hom.source :=
    hlaunch.continuousAt (B.hom.open_source.mem_nhds hsrc)
  have hpos_ev : ∀ᶠ s in 𝓝 t, 0 < s :=
    isOpen_Ioi.mem_nhds ht
  filter_upwards [hsrc_ev, hpos_ev] with s hs hsp
  have hs' :
      tangentSpaceModelContinuousLinearEquiv (I := I) p (s • x) ∈ B.hom.source := by
    simpa only [map_smul] using hs
  rw [← intrinsicGeodesic_smul (I := I) g hEnorm p x s,
    ← expMapIntrinsic_def,
    branchRadius_exp (I := I) B hs',
    sqrt_gInner_smul_self (I := I) g p hsp.le x]

omit [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem half_inner_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) :
    HasFDerivAt
      (fun v : E => (1 / 2 : Real) * modelMetricInner (I := I) g p v v)
      (modelMetricInner (I := I) g p u) u := by
  let gp : E →L[Real] E →L[Real] Real := modelMetricInner (I := I) g p
  change HasFDerivAt (fun v : E => (1 / 2 : Real) * gp v v) (gp u) u
  have h :=
    (gp.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)).const_mul
      (1 / 2 : Real)
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro w
  simp only [smul_apply, add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.id_apply, id_eq, ContinuousLinearMap.comp_apply]
  rw [show gp w u = gp u w by
    simpa only [gp, modelMetricInner_apply] using
      g.symm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm w)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)]
  ring

theorem branchEnergy_deriv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p q : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hq : q ∈ B.dom) :
    let invf : M → E := B.inv
    HasMFDerivAt I 𝓘(Real, Real)
      (branchEnergy (I := I) g B) q
      ((modelMetricInner (I := I) g p (invf q)).comp
        (mfderiv I 𝓘(Real, E) invf q)) := by
  dsimp only
  let invf : M → E := B.inv
  let U : Set M := B.dom
  have hUopen : IsOpen U := B.hom.open_target
  have hqU : q ∈ U := hq
  have hinv : MDifferentiableAt I 𝓘(Real, E) invf q := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using B.inv_contMDiffOn
    exact (hinf.contMDiffAt (hUopen.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hquad :=
    (half_inner_hasFDerivAt (I := I) g p (invf q)).hasMFDerivAt.comp q
      hinv.hasMFDerivAt
  have heq :
      branchEnergy (I := I) g B =ᶠ[𝓝 q]
        (fun z : M => (1 / 2 : Real) *
          modelMetricInner (I := I) g p (invf z) (invf z)) := by
    filter_upwards [hUopen.mem_nhds hqU] with z hz
    simp only [branchEnergy, invf]
  change HasMFDerivAt I 𝓘(Real, Real)
    (branchEnergy (I := I) g B) q
    ((modelMetricInner (I := I) g p (invf q)).comp
      (mfderiv I 𝓘(Real, E) invf q))
  exact hquad.congr_of_eventuallyEq heq

private theorem exp_inv_mfderiv_legacy
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p q : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hq : q ∈ B.dom)
    (Y : TangentSpace I q) :
    let uB : E := B.inv q
    let dInv : E :=
      mfderiv I 𝓘(Real, E) B.inv q Y
    ((mfderiv 𝓘(Real, E) I
        (fun u : E =>
          expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from u))
        uB dInv : TangentSpace I _) : E) = (Y : E) := by
  dsimp only
  let expf : E → M := fun u =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)
  let invf : M → E := B.inv
  let U : Set M := B.dom
  have hUopen : IsOpen U := B.hom.open_target
  have hqU : q ∈ U := hq
  have hinv : MDifferentiableAt I 𝓘(Real, E) invf q := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using B.inv_contMDiffOn
    exact (hinf.contMDiffAt (hUopen.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(Real, E) I expf (invf q) := by
    exact ((intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt).mdifferentiableAt
      (by simp)
  have hright : (expf ∘ invf) =ᶠ[𝓝 q] id := by
    filter_upwards [hUopen.mem_nhds hqU] with z hz
    simpa only [Function.comp_apply, id_eq, expf, invf, U] using B.right_inv hz
  have hchain :=
    mfderiv_comp_apply (I := I) (I' := 𝓘(Real, E)) (I'' := I)
      (x := q) (g := expf) hexp hinv Y
  have hchainE :
      ((mfderiv 𝓘(Real, E) I expf (invf q)
          (mfderiv I 𝓘(Real, E) invf q Y) : TangentSpace I _) : E) =
        ((mfderiv I I (expf ∘ invf) q Y : TangentSpace I _) : E) :=
    congrArg (fun V => (V : E)) hchain.symm
  have hidE :
      ((mfderiv I I (expf ∘ invf) q Y : TangentSpace I _) : E) =
        (Y : E) := by
    rw [hright.mfderiv_eq, mfderiv_id]
    rfl
  exact hchainE.trans hidE

theorem exp_inv_mfderiv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p q : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    (hq : q ∈ B.dom)
    (Y : TangentSpace I q) :
    let uB : E := B.inv q
    let dInv : E :=
      tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) uB
        (mfderiv I 𝓘(Real, E) B.inv q Y)
    tangentSpaceModelContinuousLinearEquiv
      (I := I)
      (expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm uB))
      (mfderiv 𝓘(Real, E) I
        (fun u : E =>
          expMapIntrinsic (I := I) g hEnorm p
            ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u))
        uB
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) uB).symm dInv))
      = tangentSpaceModelContinuousLinearEquiv (I := I) q Y := by
  dsimp only
  let uB : E := B.inv q
  let dInvT : TangentSpace 𝓘(Real, E) uB :=
    mfderiv I 𝓘(Real, E) B.inv q Y
  let eInv : TangentSpace 𝓘(Real, E) uB ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) uB
  let dInv : E := eInv dInvT
  let expOld : E → M := fun u =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  let expNew : E → M := fun u =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)
  have hexp : expOld = expNew := by
    funext u
    simp only [expOld, expNew,
      tangentSpaceModelContinuousLinearEquiv_symm_apply]
  have hdInv :
      (show TangentSpace 𝓘(Real, E) uB from (dInvT : E)) =
        eInv.symm dInv := by
    apply eInv.injective
    simp only [dInv, ContinuousLinearEquiv.apply_symm_apply]
  have h := exp_inv_mfderiv_legacy (I := I) B hq Y
  change
    ((mfderiv 𝓘(Real, E) I expOld uB
      (show TangentSpace 𝓘(Real, E) uB from (dInvT : E)) :
        TangentSpace I _) : E) = (Y : E) at h
  rw [hexp, hdInv] at h
  have hpoint : expNew uB = q := by
    simpa only [expNew, uB] using B.right_inv hq
  rw [hpoint] at h
  have hModel :=
    congrArg (tangentSpaceModelContinuousLinearEquiv (I := I) q) h
  change
    tangentSpaceModelContinuousLinearEquiv (I := I) (expNew uB)
        (mfderiv 𝓘(Real, E) I expNew uB (eInv.symm dInv)) =
      tangentSpaceModelContinuousLinearEquiv (I := I) q Y
  rw [hpoint]
  exact hModel

theorem inv_exp_mfderiv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : E}
    (hu : u ∈ B.hom.source)
    (w : E) :
    tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E))
      (B.inv (expMapIntrinsic (I := I) g hEnorm p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u)))
      (mfderiv I 𝓘(Real, E)
        B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm u))
        (mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v))
          u
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) u).symm w)))
      = w := by
  let expf : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v)
  let invf : M → E := B.inv
  let uE : E := u
  let wE : E := w
  let wT : TangentSpace 𝓘(Real, E) uE :=
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) uE).symm wE
  let V : Set E := B.hom.source
  have hVopen : IsOpen V := B.hom.open_source
  have huV : uE ∈ V := hu
  have htarget :
      expf uE ∈ B.dom := by
    rw [show expf uE = B.hom uE from B.hom_eq hu]
    exact B.hom.map_source hu
  let U : Set M := B.dom
  have hUopen : IsOpen U := B.hom.open_target
  have hqU : expf uE ∈ U := htarget
  have hinv : MDifferentiableAt I 𝓘(Real, E) invf (expf uE) := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using B.inv_contMDiffOn
    exact (hinf.contMDiffAt (hUopen.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(Real, E) I expf uE := by
    exact ((intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt).mdifferentiableAt
      (by simp)
  have hleft : (invf ∘ expf) =ᶠ[𝓝 uE] id := by
    filter_upwards [hVopen.mem_nhds huV] with v hv
    simpa only [Function.comp_apply, id_eq, expf, invf] using B.left_inv hv
  have hchain :=
    mfderiv_comp_apply (I := 𝓘(Real, E)) (I' := I)
      (I'' := 𝓘(Real, E)) (x := uE) (g := invf)
      hinv hexp wT
  have hid :
      mfderiv 𝓘(Real, E) 𝓘(Real, E)
          (invf ∘ expf) uE wT = wT := by
    have hmf :
        mfderiv 𝓘(Real, E) 𝓘(Real, E) (invf ∘ expf) uE =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) id uE :=
      hleft.mfderiv_eq
    rw [hmf, mfderiv_id]
    rfl
  have hE := congrArg (fun z => (z : E)) (hchain.symm.trans hid)
  rw [tangentSpaceModelContinuousLinearEquiv_apply]
  simpa only [expf, invf, uE, wE, wT,
    tangentSpaceModelContinuousLinearEquiv_symm_apply] using hE

theorem branchRadius_infAt
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (branchRadius (I := I) g B)
      (expMapIntrinsic (I := I) g hEnorm p u) := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let invf : M → E := B.inv
  let U : Set M := B.dom
  have hUopen : IsOpen U := B.hom.open_target
  have hqU : q ∈ U := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) from
      B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv : ContMDiffAt I 𝓘(Real, E) ∞ invf q := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using B.inv_contMDiffOn
    exact hinf.contMDiffAt (hUopen.mem_nhds hqU)
  have hinv_eq :
      B.inv q = tangentSpaceModelContinuousLinearEquiv (I := I) p u := by
    simpa only [q, ContinuousLinearEquiv.symm_apply_apply] using B.left_inv hu
  let gp : E →L[Real] E →L[Real] Real := modelMetricInner (I := I) g p
  have hinner : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun z : M => modelMetricInner (I := I) g p (invf z) (invf z)) q := by
    have hg : ContMDiffAt I
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun _ : M => gp) q :=
      contMDiffAt_const
    have hinner' := (hg.clm_apply hinv).clm_apply hinv
    refine hinner'.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hinner_ne :
      modelMetricInner (I := I) g p (invf q) (invf q) ≠ 0 := by
    rw [show invf q = tangentSpaceModelContinuousLinearEquiv (I := I) p u from hinv_eq,
      modelMetricInner_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact hu_pos.ne'
  have hsqrt : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun z : M => Real.sqrt
        (modelMetricInner (I := I) g p (invf z) (invf z))) q := by
    exact ((Real.contDiffAt_sqrt hinner_ne).contMDiffAt).comp q hinner
  have heq :
      branchRadius (I := I) g B =ᶠ[𝓝 q]
        (fun z : M => Real.sqrt
          (modelMetricInner (I := I) g p (invf z) (invf z))) := by
    filter_upwards [hUopen.mem_nhds hqU] with z hz
    simp only [branchRadius, invf]
  simpa only [q] using hsqrt.congr_of_eventuallyEq heq

theorem branchRadius_open
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    ∃ U : Set M,
      IsOpen U ∧
      expMapIntrinsic (I := I) g hEnorm p u ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞
        (branchRadius (I := I) g B) U := by
  let D : Set M := B.dom
  let invf : M → E := B.inv
  let sq : M → Real := fun z =>
    modelMetricInner (I := I) g p (invf z) (invf z)
  let U : Set M := D ∩ sq ⁻¹' Set.Ioi 0
  have hDopen : IsOpen D := B.hom.open_target
  have hinv : ContMDiffOn I 𝓘(Real, E) ∞ invf D := by
    simpa only [invf, D] using B.inv_contMDiffOn
  let gp : E →L[Real] E →L[Real] Real := modelMetricInner (I := I) g p
  have hsq : ContMDiffOn I 𝓘(Real, Real) ∞ sq D := by
    have hgp : ContMDiffOn I
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun _ : M => gp) D :=
      contMDiffOn_const
    have hsq' := (hgp.clm_apply hinv).clm_apply hinv
    refine hsq'.congr ?_
    exact fun _ _ => rfl
  have hUopen : IsOpen U := by
    exact hsq.continuousOn.isOpen_inter_preimage hDopen isOpen_Ioi
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  have hqD : q ∈ D := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) from
      B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv_q :
      B.inv q = tangentSpaceModelContinuousLinearEquiv (I := I) p u := by
    simpa only [q, ContinuousLinearEquiv.symm_apply_apply] using B.left_inv hu
  have hsq_q : sq q = g.inner p u u := by
    change modelMetricInner (I := I) g p (B.inv q) (B.inv q) = g.inner p u u
    rw [hinv_q, modelMetricInner_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  have hqU : q ∈ U := by
    refine ⟨hqD, ?_⟩
    change 0 < sq q
    rw [hsq_q]
    exact hu_pos
  have hsqU : ContMDiffOn I 𝓘(Real, Real) ∞ sq U :=
    hsq.mono Set.inter_subset_left
  have hsqrt : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z => Real.sqrt (sq z)) U := by
    intro z hz
    exact
      (Real.contDiffAt_sqrt hz.2.ne').contMDiffAt.comp_contMDiffWithinAt z
        (hsqU z hz)
  refine ⟨U, hUopen, hqU, ContMDiffOn.congr hsqrt ?_⟩
  intro z hz
  simp only [branchRadius, sq, invf]

theorem grad_branchEnergy
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source) :
    gradientFun (I := I) g
        (branchEnergy (I := I) g B)
        (expMapIntrinsic (I := I) g hEnorm p u) =
      (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let invf : M → E := B.inv
  let uB : E := invf q
  let eInv : TangentSpace 𝓘(Real, E) uB ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) uB
  let dInv : TangentSpace I q → E := fun Y =>
    eInv (mfderiv I 𝓘(Real, E) invf q Y)
  have hq : q ∈ B.dom := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) from
      B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv :
      B.inv q = tangentSpaceModelContinuousLinearEquiv (I := I) p u := by
    simpa only [q, ContinuousLinearEquiv.symm_apply_apply] using B.left_inv hu
  have huB : uB = tangentSpaceModelContinuousLinearEquiv (I := I) p u := hinv
  have hderiv := branchEnergy_deriv (I := I) B hq
  apply gradientFun_eq_of_flat (I := I) g
  apply LinearMap.ext
  intro Y
  change
    mfderiv I 𝓘(Real, Real)
        (branchEnergy (I := I) g B) q Y =
      g.inner q
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd Y
  rw [hderiv.mfderiv]
  change modelMetricInner (I := I) g p uB (dInv Y) =
    g.inner q
      (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd Y
  rw [huB, modelMetricInner_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  have hgauss :=
    intrinsic_gauss_modelEquiv (I := I) g hEnorm p uB (dInv Y)
  have hright :
      tangentSpaceModelContinuousLinearEquiv
        (I := I)
        (expMapIntrinsic (I := I) g hEnorm p
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm uB))
        (mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v))
          uB (eInv.symm (dInv Y)))
        =
      tangentSpaceModelContinuousLinearEquiv
        (I := I) q Y := by
    simpa only [uB, dInv, eInv, invf] using
      exp_inv_mfderiv (I := I) B hq Y
  rw [huB, ContinuousLinearEquiv.symm_apply_apply] at hgauss hright
  have hrightT :
      mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v))
          (tangentSpaceModelContinuousLinearEquiv (I := I) p u)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p u)).symm
              (dInv Y))
        = Y := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) q).injective
    exact hright
  have hpair :=
    congrArg
      ((g.inner (expMapIntrinsic (I := I) g hEnorm p u))
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd)
      hrightT
  exact hgauss.symm.trans hpair

theorem branchRadius_diff
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    MDifferentiableAt I 𝓘(Real, Real)
      (branchRadius (I := I) g B)
      (expMapIntrinsic (I := I) g hEnorm p u) := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let e : M → Real := branchEnergy (I := I) g B
  let e2 : M → Real := (2 : Real) • e
  have hq : q ∈ B.dom := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) from
      B.hom_eq hu]
    exact B.hom.map_source hu
  have he_diff : MDifferentiableAt I 𝓘(Real, Real) e q :=
    (branchEnergy_deriv (I := I) B hq).mdifferentiableAt
  have he2_diff : MDifferentiableAt I 𝓘(Real, Real) e2 q :=
    he_diff.const_smul 2
  have he2_val : e2 q = g.inner p u u := by
    simp only [e2, e, Pi.smul_apply, smul_eq_mul, q,
      branchEnergy_exp (I := I) B hu]
    ring
  have hsqrt : DifferentiableAt Real Real.sqrt (e2 q) := by
    rw [he2_val]
    exact (Real.hasDerivAt_sqrt hu_pos.ne').differentiableAt
  rw [branchRadius_eq (I := I) g B]
  change MDifferentiableAt I 𝓘(Real, Real) (fun z : M => Real.sqrt (e2 z)) q
  exact
    (hsqrt.hasFDerivAt.hasMFDerivAt.comp q
      he2_diff.hasMFDerivAt).mdifferentiableAt

theorem grad_branchRadius
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M}
    (B : ExponentialInverseBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    gradientFun (I := I) g
        (branchRadius (I := I) g B)
        (expMapIntrinsic (I := I) g hEnorm p u) =
      (Real.sqrt (g.inner p u u))⁻¹ •
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let e : M → Real := branchEnergy (I := I) g B
  let e2 : M → Real := (2 : Real) • e
  have hq : q ∈ B.dom := by
    rw [show q = B.hom (tangentSpaceModelContinuousLinearEquiv (I := I) p u) from
      B.hom_eq hu]
    exact B.hom.map_source hu
  have he_diff : MDifferentiableAt I 𝓘(Real, Real) e q := by
    exact (branchEnergy_deriv (I := I) B hq).mdifferentiableAt
  have he2_diff : MDifferentiableAt I 𝓘(Real, Real) e2 q := by
    exact he_diff.const_smul 2
  have he2_val : e2 q = g.inner p u u := by
    simp only [e2, e, Pi.smul_apply, smul_eq_mul, q,
      branchEnergy_exp (I := I) B hu]
    ring
  have hsqrt_diff : DifferentiableAt Real Real.sqrt (e2 q) := by
    rw [he2_val]
    exact (Real.hasDerivAt_sqrt hu_pos.ne').differentiableAt
  rw [branchRadius_eq (I := I) g B]
  change gradientFun (I := I) g
      (fun z : M => Real.sqrt (e2 z)) q =
    (Real.sqrt (g.inner p u u))⁻¹ •
      (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
  rw [gradientFun_comp (I := I) g hsqrt_diff he2_diff,
    gradientFun_const_smul (I := I) g 2 he_diff,
    show gradientFun (I := I) g e q =
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd by
      simpa only [e, q] using grad_branchEnergy (I := I) B hu,
    he2_val,
    (Real.hasDerivAt_sqrt hu_pos.ne').deriv]
  have hsqrt_ne : Real.sqrt (g.inner p u u) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hu_pos
  have hcoeff :
      (1 / (2 * Real.sqrt (g.inner p u u))) * 2 =
        (Real.sqrt (g.inner p u u))⁻¹ := by
    field_simp
  exact (smul_smul
    (1 / (2 * Real.sqrt (g.inner p u u))) 2
    (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd).trans
      (congrArg
        (fun c : Real =>
          c • (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd)
        hcoeff)

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
