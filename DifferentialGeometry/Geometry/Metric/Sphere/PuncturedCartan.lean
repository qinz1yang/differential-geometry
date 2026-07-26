import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import DifferentialGeometry.Geometry.Exponential.CartanNorm
import DifferentialGeometry.Geometry.Metric.Polarization
import DifferentialGeometry.Geometry.Metric.Sphere.RadialLog
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

/-!
# Punctured-sphere Cartan maps

The round logarithm based at `p` gives a single model-space coordinate on the
unit sphere with the antipode removed.  A tangent-space isometry followed by
the target exponential map produces the corresponding Cartan map into a
complete curvature-one manifold.
-/

noncomputable section

open Bundle Filter Function Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry

open Riemannian.Exponential

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)] [NeZero n]

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable
  [RiemannianBundle
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]
  [PseudoEMetricSpace (sphere (0 : A) 1)]
  [@CompleteSpace (sphere (0 : A) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : A) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : A) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]

variable {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
  [T2Space (TangentBundle J N)]

variable [RiemannianBundle (fun x : N => TangentSpace J x)]
  [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
  [ConnectedSpace N]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : N => TangentSpace J x)]

/-- The Cartan map from the round sphere with one antipode removed, totalized
on the whole sphere by the total round logarithm. -/
def punctCartan
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p' : N) (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (p x : sphere (0 : A) 1) : N :=
  expMapIntrinsic (I := J) g hEnorm p'
    (show TangentSpace J p' from i (roundLog (n := n) p x))

omit [FiniteDimensional ℝ A]
  [RiemannianBundle (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]
  [PseudoEMetricSpace (sphere (0 : A) 1)]
  [@CompleteSpace (sphere (0 : A) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : A) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : A) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]
  [T2Space (TangentBundle J N)] [ConnectedSpace N] in
/-- At its source center, the punctured Cartan map takes the prescribed
target-center value. -/
@[simp] theorem punctCartan_self
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p' : N) (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (p : sphere (0 : A) 1) :
    punctCartan g hEnorm p' i p p = p' := by
  simp only [punctCartan, roundLog_self, map_zero]
  exact expMapIntrinsic_zero (I := J) g hEnorm p'

omit [T2Space (TangentBundle J N)] [ConnectedSpace N] in
/-- The punctured Cartan map is smooth away from the antipode. -/
theorem punctCartan_smooth
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p' : N) (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (p : sphere (0 : A) 1) :
    ContMDiffOn (𝓡 n) J ∞
      (punctCartan g hEnorm p' i p) {x | x ≠ -p} := by
  have hlog :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (roundLog (n := n) p) {x | x ≠ -p} :=
    roundLog_smooth hRound p
  have hi :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun u : EuclideanSpace ℝ (Fin n) => i u) :=
    i.contDiff.contMDiff
  have hmid :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        ((fun u : EuclideanSpace ℝ (Fin n) => i u) ∘
          roundLog (n := n) p) {x | x ≠ -p} :=
    hi.comp_contMDiffOn hlog
  have hexp :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞
        (fun u : EuclideanSpace ℝ (Fin n) =>
          expMapIntrinsic (I := J) g hEnorm p'
            (show TangentSpace J p' from u)) :=
    intrinsicFiber_smooth (I := J) g hEnorm p'
  simpa only [punctCartan, Function.comp_apply] using
    hexp.comp_contMDiffOn hmid

omit [T2Space (TangentBundle J N)] [ConnectedSpace N] in
/-- At its source center, the differential of the punctured Cartan map is the
prescribed tangent-space equivalence. -/
theorem punctCartan_mfd
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p' : N) (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (p : sphere (0 : A) 1) :
    mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) p =
      (i : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) := by
  let logf : sphere (0 : A) 1 → EuclideanSpace ℝ (Fin n) :=
    roundLog (n := n) p
  let midf : sphere (0 : A) 1 → EuclideanSpace ℝ (Fin n) :=
    fun x => i (logf x)
  let expf : EuclideanSpace ℝ (Fin n) → N := fun u =>
    expMapIntrinsic (I := J) g hEnorm p'
      (show TangentSpace J p' from u)
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hUopen : IsOpen {x : sphere (0 : A) 1 | x ≠ -p} := by
    change IsOpen (({-p} : Set (sphere (0 : A) 1))ᶜ)
    exact isOpen_compl_singleton
  have hlog :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf p :=
    ((roundLog_smooth hRound p).contMDiffAt
      (hUopen.mem_nhds hpneg)).mdifferentiableAt (by simp)
  have hiDiff :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun u : EuclideanSpace ℝ (Fin n) => i u) (logf p) :=
    i.mdifferentiableAt
  have hmid :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) midf p := by
    simpa only [midf, Function.comp_apply] using hiDiff.comp p hlog
  have hexp :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf (midf p) :=
    (intrinsicFiber_smooth (I := J) g hEnorm p').contMDiffAt.mdifferentiableAt
      (by simp)
  have hmidDeriv :
      mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) midf p =
        (i : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) := by
    have hchain :=
      mfderiv_comp
        (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p hiDiff hlog
    rw [ContinuousLinearEquiv.mfderiv_eq,
      roundLog_mfd_self hRound p] at hchain
    ext v
    have hv := DFunLike.congr_fun hchain v
    simpa only [midf, logf, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hv
  have hmid0 : midf p = 0 := by
    simp only [midf, logf, roundLog_self, map_zero]
  have hexp0 :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf 0 =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [expf] using
      mfderiv_expMapIntrinsic_at_zero (I := J) g hEnorm p'
  have hchain :=
    mfderiv_comp
      (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I'' := J) p hexp hmid
  rw [hmid0, hexp0, hmidDeriv] at hchain
  ext v
  have hv := DFunLike.congr_fun hchain v
  simpa only [punctCartan, expf, midf, logf, Function.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hv

/-- The differential of the punctured Cartan map preserves the metric
quadratic form. -/
theorem punctCartan_sq
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : sphere (0 : A) 1) (p' : N)
    (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner p' (i a) (i b) =
        (roundMetric (E := A) (n := n)).inner p a b)
    (hR : ∀ (x : N) (X Y Z : TangentSpace J x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := J) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    {x : sphere (0 : A) 1} (hx : x ≠ -p)
    (Y : TangentSpace (𝓡 n) x) :
    g.inner (punctCartan g hEnorm p' i p x)
        (mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x Y)
        (mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x Y) =
      (roundMetric (E := A) (n := n)).inner x Y Y := by
  have hfr : 1 < Module.finrank ℝ A := by
    rw [show Module.finrank ℝ A = n + 1 from Fact.out]
    exact Nat.succ_lt_succ (Nat.pos_of_ne_zero (NeZero.ne n))
  letI : ConnectedSpace (sphere (0 : A) 1) :=
    { toPreconnectedSpace :=
        Subtype.preconnectedSpace
          (isPreconnected_sphere
            (Module.one_lt_rank_of_one_lt_finrank hfr) (0 : A) 1)
      toNonempty := ⟨p⟩ }
  let logf : sphere (0 : A) 1 → EuclideanSpace ℝ (Fin n) :=
    roundLog (n := n) p
  let midf : sphere (0 : A) 1 → EuclideanSpace ℝ (Fin n) :=
    fun z => i (logf z)
  let expf : EuclideanSpace ℝ (Fin n) → sphere (0 : A) 1 := fun u =>
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := A) (n := n))
      hRound p (show TangentSpace (𝓡 n) p from u)
  let expf' : EuclideanSpace ℝ (Fin n) → N := fun u =>
    expMapIntrinsic (I := J) g hEnorm p'
      (show TangentSpace J p' from u)
  let u : EuclideanSpace ℝ (Fin n) := logf x
  let w : EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf x Y
  let U : Set (sphere (0 : A) 1) := {z | z ≠ -p}
  have hUopen : IsOpen U := by
    change IsOpen (({-p} : Set (sphere (0 : A) 1))ᶜ)
    exact isOpen_compl_singleton
  have hxU : x ∈ U := hx
  have hlogInf :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ logf x := by
    exact (roundLog_smooth hRound p).contMDiffAt
      (hUopen.mem_nhds hxU)
  have hlog :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf x :=
    hlogInf.mdifferentiableAt (by simp)
  have hiDiff :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun z : EuclideanSpace ℝ (Fin n) => i z) (logf x) :=
    i.mdifferentiableAt
  have hmid :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) midf x := by
    simpa only [midf, Function.comp_apply] using hiDiff.comp x hlog
  have hexpInf :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞ expf' (midf x) :=
    (intrinsicFiber_smooth (I := J) g hEnorm p').contMDiffAt
  have hexp' :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf' (midf x) :=
    hexpInf.mdifferentiableAt (by simp)
  have hmidDeriv :
      mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) midf x Y =
        i w := by
    have hchain :=
      mfderiv_comp_apply
        (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (g := fun z : EuclideanSpace ℝ (Fin n) => i z)
        (f := logf) (x := x) hiDiff hlog Y
    rw [ContinuousLinearEquiv.mfderiv_eq] at hchain
    simpa only [midf, w, Function.comp_apply] using hchain
  have hmapDeriv :
      mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x Y =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf'
          (i u) (i w) := by
    have hchain :=
      mfderiv_comp_apply
        (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I'' := J) (g := expf') (f := midf) (x := x)
        hexp' hmid Y
    rw [hmidDeriv] at hchain
    simpa only [punctCartan, expf', midf, logf, u,
      Function.comp_apply] using hchain
  have hexp0Inf :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ expf u :=
    (intrinsicFiber_smooth (I := 𝓡 n)
      (roundMetric (E := A) (n := n)) hRound p).contMDiffAt
  have hexp0 :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf u :=
    hexp0Inf.mdifferentiableAt (by simp)
  have hident : (expf ∘ logf) =ᶠ[𝓝 x] id := by
    refine eventuallyEq_of_mem (hUopen.mem_nhds hxU) ?_
    intro z hz
    simpa only [expf, logf, Function.comp_apply, id_eq] using
      round_exp_log_ne hRound p z hz
  have hright :
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
          expf u w : TangentSpace (𝓡 n) (expf u)) :
        EuclideanSpace ℝ (Fin n)) = (Y : EuclideanSpace ℝ (Fin n)) := by
    have hchain :=
      mfderiv_comp_apply
        (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I'' := 𝓡 n) (g := expf) (f := logf) (x := x)
        hexp0 hlog Y
    rw [hident.mfderiv_eq, mfderiv_id] at hchain
    simpa only [expf, logf, u, w] using hchain.symm
  have hbase : expf u = x := by
    simpa only [expf, u, logf] using round_exp_log_ne hRound p x hx
  have htransfer :=
    expDiff_sq_xfer
      (I := 𝓡 n) (I' := J)
      (roundMetric (E := A) (n := n)) hRound g hEnorm p p' u w i hi
      (round_riemann_one (E := A) (n := n)) hR
  have htransfer' :
      g.inner (expf' (i u))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf' (i u) (i w))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf' (i u) (i w)) =
        (roundMetric (E := A) (n := n)).inner (expf u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf u w)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf u w) := by
    simpa only [expf, expf'] using htransfer
  have hsource :
      (roundMetric (E := A) (n := n)).inner (expf u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf u w)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf u w) =
        (roundMetric (E := A) (n := n)).inner x Y Y := by
    rw [hbase] at hright ⊢
    rw [hright]
  rw [hmapDeriv]
  change
    g.inner (expf' (i u))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf' (i u) (i w))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J expf' (i u) (i w)) =
      (roundMetric (E := A) (n := n)).inner x Y Y
  exact htransfer'.trans hsource

/-- The differential of the punctured Cartan map preserves the full
Riemannian inner product away from the antipode. -/
theorem punctCartan_inner
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : sphere (0 : A) 1) (p' : N)
    (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner p' (i a) (i b) =
        (roundMetric (E := A) (n := n)).inner p a b)
    (hR : ∀ (x : N) (X Y Z : TangentSpace J x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := J) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    {x : sphere (0 : A) 1} (hx : x ≠ -p)
    (Y Z : TangentSpace (𝓡 n) x) :
    g.inner (punctCartan g hEnorm p' i p x)
        (mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x Y)
        (mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x Z) =
      (roundMetric (E := A) (n := n)).inner x Y Z := by
  exact Riemannian.inner_eq_of_diag
    (roundMetric (E := A) (n := n)) g x
    (punctCartan g hEnorm p' i p x)
    (mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x)
    (punctCartan_sq hRound g hEnorm p p' i hi hR hx) Y Z

/-- The punctured Cartan map is a smooth local diffeomorphism away from the
antipode. -/
theorem punctCartan_local
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : sphere (0 : A) 1) (p' : N)
    (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner p' (i a) (i b) =
        (roundMetric (E := A) (n := n)).inner p a b)
    (hR : ∀ (x : N) (X Y Z : TangentSpace J x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := J) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y) :
    IsLocalDiffeomorphOn (𝓡 n) J ∞
      (punctCartan g hEnorm p' i p) {x | x ≠ -p} := by
  let U : Set (sphere (0 : A) 1) := {x | x ≠ -p}
  have hU : IsOpen U := by
    change IsOpen (({-p} : Set (sphere (0 : A) 1))ᶜ)
    exact isOpen_compl_singleton
  apply Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hU
  · exact punctCartan_smooth hRound g hEnorm p' i p
  · intro x hx
    have hmdiff :
        MDifferentiableAt (𝓡 n) J (punctCartan g hEnorm p' i p) x :=
      ((punctCartan_smooth hRound g hEnorm p' i p).contMDiffAt
        (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) :=
      mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x
    have hLinj : Function.Injective L := by
      intro v w hvw
      by_contra hvw'
      have hne : v - w ≠ 0 := sub_ne_zero.mpr hvw'
      have hzero :
          (roundMetric (E := A) (n := n)).inner x (v - w) (v - w) = 0 := by
        rw [← punctCartan_sq hRound g hEnorm p p' i hi hR hx (v - w)]
        change g.inner (punctCartan g hEnorm p' i p x)
          (L (v - w)) (L (v - w)) = 0
        rw [map_sub, hvw, sub_self]
        exact map_zero
          (g.inner (punctCartan g hEnorm p' i p x) 0)
      exact (ne_of_gt
        ((roundMetric (E := A) (n := n)).pos x (v - w) hne)) hzero
    have hLsurj : Function.Surjective L :=
      LinearMap.surjective_of_injective hLinj
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.ofBijective L
        (LinearMap.ker_eq_bot.mpr hLinj)
        (LinearMap.range_eq_top.mpr hLsurj)
    have hLinv : L.IsInvertible := by
      rw [← show (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) = L by
          simp only [e, ContinuousLinearEquiv.coe_ofBijective]]
      exact ContinuousLinearMap.isInvertible_equiv
    change
      (mfderiv (𝓡 n) J (punctCartan g hEnorm p' i p) x).IsInvertible
        at hLinv
    rw [hmdiff.mfderiv,
      ModelWithCorners.Boundaryless.range_eq_univ,
      fderivWithin_univ] at hLinv
    exact hLinv

end Geometry
end DifferentialGeometry
