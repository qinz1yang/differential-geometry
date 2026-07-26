import DifferentialGeometry.Geometry.Exponential.BranchRadius
import DifferentialGeometry.Geometry.Exponential.CartanNorm
import DifferentialGeometry.Geometry.Exponential.DiagInvFixed
import DifferentialGeometry.Geometry.Metric.Polarization

set_option autoImplicit false

/-!
# Local Cartan isometries

A fixed-first diagonal-exponential branch supplies smooth normal coordinates
on the source manifold.  Composing those coordinates with a tangent-space
linear isometry and the intrinsic exponential on a second curvature-one
manifold gives the local Cartan map.

The metric proof is pointwise and invariant.  The Jacobi-field producer
`expDiff_sq_xfer` transfers the target exponential differential square, while
`exp_inv_mfderiv` cancels the source exponential differential after taking the
canonical fixed-first projection of the diagonal branch.
Polarization then gives the full bilinear metric identity.
-/

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  [I'.Boundaryless]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M']
  [T2Space (TangentBundle I' M')]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [ConnectedSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  [PseudoEMetricSpace M'] [IsRiemannianManifold I' M'] [CompleteSpace M']
  [ConnectedSpace M']
  [IsContinuousRiemannianBundle E (fun x : M' ↦ TangentSpace I' x)]

/-- The fixed-branch Cartan map associated to a tangent-space linear
isometry.  It is totalized outside the selected branch domain, but all
geometric statements below are restricted to that domain. -/
def cartanMap
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) (p : M)
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    (p' : M') (i : E ≃L[ℝ] E) (x : M) : M' :=
  expMapIntrinsic (I := I') g' hEnorm' p'
    (show TangentSpace I' p' from i ((B.inv (p, x)).snd : E))

omit [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space (TangentBundle I' M')] [ConnectedSpace M] [ConnectedSpace M'] in
/-- A fixed-branch Cartan map is smooth on the fixed-first branch domain. -/
theorem cartanMap_smooth
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) (p : M)
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    (p' : M') (i : E ≃L[ℝ] E) :
    ContMDiffOn I I' ∞ (cartanMap B p g' hEnorm' p' i)
      ((fun x : M => (p, x)) ⁻¹' B.dom) := by
  let U : Set M := (fun x : M => (p, x)) ⁻¹' B.dom
  let invf : M → E := fun x => ((B.inv (p, x)).snd : E)
  have hinv : ContMDiffOn I 𝓘(ℝ, E) ∞ invf U := by
    simpa only [U, invf] using
      B.inv_fst_coord_inf (S := U) (fun x hx => hx)
  have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun u : E => i u) :=
    i.contDiff.contMDiff
  have hmid : ContMDiffOn I 𝓘(ℝ, E) ∞
      ((fun u : E => i u) ∘ invf) U :=
    hi.comp_contMDiffOn hinv
  have hexp : ContMDiff 𝓘(ℝ, E) I' ∞
      (fun u : E =>
        expMapIntrinsic (I := I') g' hEnorm' p'
          (show TangentSpace I' p' from u)) :=
    intrinsicFiber_smooth (I := I') g' hEnorm' p'
  simpa only [cartanMap, U, invf, Function.comp_apply] using
    hexp.comp_contMDiffOn hmid

/-- The differential of a fixed-branch Cartan map preserves the metric
quadratic form between curvature-one manifolds. -/
theorem cartanMap_sq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) (p : M)
    (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          g'.inner x Y Z • X - g'.inner x X Z • Y)
    {x : M} (hx : (p, x) ∈ B.dom) (Y : TangentSpace I x) :
    g'.inner (cartanMap B p g' hEnorm' p' i x)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y) =
      g.inner x Y Y := by
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let midf : M → E := fun z => i (invf z)
  let expf : E → M := fun u =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  let expf' : E → M' := fun u =>
    expMapIntrinsic (I := I') g' hEnorm' p'
      (show TangentSpace I' p' from u)
  let u : E := invf x
  let w : E := mfderiv I 𝓘(ℝ, E) invf x Y
  let U : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  have hUopen : IsOpen U := by
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hxU : x ∈ U := hx
  have hinvOn : ContMDiffOn I 𝓘(ℝ, E) ∞ invf U := by
    simpa only [invf, U] using
      B.inv_fst_coord_inf (S := U) (fun z hz => hz)
  have hinv : MDifferentiableAt I 𝓘(ℝ, E) invf x :=
    (hinvOn.contMDiffAt (hUopen.mem_nhds hxU)).mdifferentiableAt
      (by simp)
  have hiDiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun z : E => i z) (invf x) :=
    i.mdifferentiableAt
  have hmid : MDifferentiableAt I 𝓘(ℝ, E) midf x := by
    simpa only [midf, Function.comp_apply] using hiDiff.comp x hinv
  have hexpInf : ContMDiffAt 𝓘(ℝ, E) I' ∞ expf' (midf x) :=
    (intrinsicFiber_smooth (I := I') g' hEnorm' p').contMDiffAt
  have hexp' : MDifferentiableAt 𝓘(ℝ, E) I' expf' (midf x) :=
    hexpInf.mdifferentiableAt (by simp)
  have hmidDeriv :
      mfderiv I 𝓘(ℝ, E) midf x Y = i w := by
    have hchain :=
      mfderiv_comp_apply
        (I := I) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
        (g := fun z : E => i z) (f := invf) (x := x)
        hiDiff hinv Y
    rw [ContinuousLinearEquiv.mfderiv_eq] at hchain
    simpa only [midf, w, Function.comp_apply] using hchain
  have hmapDeriv :
      mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y =
        mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w) := by
    have hchain :=
      mfderiv_comp_apply
        (I := I) (I' := 𝓘(ℝ, E)) (I'' := I')
        (g := expf') (f := midf) (x := x)
        hexp' hmid Y
    rw [hmidDeriv] at hchain
    simpa only [cartanMap, expf', midf, invf, u,
      Function.comp_apply] using hchain
  have htransfer :=
    expDiff_sq_xfer (I := I) (I' := I')
      g hEnorm g' hEnorm' p p' u w i hi hR hR'
  have hright :
      ((mfderiv 𝓘(ℝ, E) I expf u w : TangentSpace I _) : E) =
        (Y : E) := by
    have hx' : x ∈ (B.fixed p).dom := by
      simpa only [DiagInvBranch.fixed_target] using hx
    simpa only [expf, invf, u, w] using
      exp_inv_mfderiv (I := I) (B.fixed p) hx' Y
  have hbase : expf u = x := by
    simpa only [expf, invf, u] using B.exp_eq hx
  have htransfer' :
      g'.inner (expf' (i u))
          (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w))
          (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w)) =
        g.inner (expf u)
          (mfderiv 𝓘(ℝ, E) I expf u w)
          (mfderiv 𝓘(ℝ, E) I expf u w) := by
    simpa only [expf, expf'] using htransfer
  have hsource :
      g.inner (expf u)
          (mfderiv 𝓘(ℝ, E) I expf u w)
          (mfderiv 𝓘(ℝ, E) I expf u w) =
        g.inner x Y Y := by
    rw [hbase] at hright ⊢
    rw [hright]
  rw [hmapDeriv]
  change
    g'.inner (expf' (i u))
        (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w))
        (mfderiv 𝓘(ℝ, E) I' expf' (i u) (i w)) =
      g.inner x Y Y
  exact htransfer'.trans hsource

/-- The differential of a fixed-branch Cartan map preserves the full
Riemannian inner product between curvature-one manifolds. -/
theorem cartanMap_inner
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) (p : M)
    (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          g'.inner x Y Z • X - g'.inner x X Z • Y)
    {x : M} (hx : (p, x) ∈ B.dom)
    (Y Z : TangentSpace I x) :
    g'.inner (cartanMap B p g' hEnorm' p' i x)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Y)
        (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x Z) =
      g.inner x Y Z := by
  exact inner_eq_of_diag g g' x (cartanMap B p g' hEnorm' p' i x)
    (mfderiv I I' (cartanMap B p g' hEnorm' p' i) x)
    (cartanMap_sq g hEnorm g' hEnorm' B p p' i hi hR hR' hx) Y Z

private noncomputable def pdTrans
    {H₀ H₁ H₂ : Type*}
    [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I₀ : ModelWithCorners ℝ E H₀}
    {I₁ : ModelWithCorners ℝ E H₁}
    {I₂ : ModelWithCorners ℝ E H₂}
    {M₀ M₁ M₂ : Type*}
    [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
    (Φ : PartialDiffeomorph I₀ I₁ M₀ M₁ ∞)
    (Ψ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) :
    PartialDiffeomorph I₀ I₂ M₀ M₂ ∞ where
  toPartialEquiv := Φ.toPartialEquiv.trans Ψ.toPartialEquiv
  open_source := by
    have hsrc :
        (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).source =
          Φ.source ∩ (Φ : M₀ → M₁) ⁻¹' Ψ.source := rfl
    rw [hsrc]
    exact Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      Φ.open_source Ψ.open_source
  open_target := by
    have htgt :
        (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).target =
          Ψ.target ∩ (Ψ.symm : M₂ → M₁) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Ψ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      Ψ.open_target Φ.open_target
  contMDiffOn_toFun := by
    have hsrc :
        (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).source =
          Φ.source ∩ (Φ : M₀ → M₁) ⁻¹' Ψ.source := rfl
    rw [hsrc]
    exact Ψ.contMDiffOn_toFun.comp
      (Φ.contMDiffOn_toFun.mono inter_subset_left)
      (fun _ hx => hx.2)
  contMDiffOn_invFun := by
    have htgt :
        (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).target =
          Ψ.target ∩ (Ψ.symm : M₂ → M₁) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ.symm.contMDiffOn_toFun.comp
      (Ψ.symm.contMDiffOn_toFun.mono inter_subset_left)
      (fun _ hx => hx.2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
@[simp]
private theorem pdTrans_source
    {H₀ H₁ H₂ : Type*}
    [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I₀ : ModelWithCorners ℝ E H₀}
    {I₁ : ModelWithCorners ℝ E H₁}
    {I₂ : ModelWithCorners ℝ E H₂}
    {M₀ M₁ M₂ : Type*}
    [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
    (Φ : PartialDiffeomorph I₀ I₁ M₀ M₁ ∞)
    (Ψ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) :
    (pdTrans Φ Ψ).source =
      Φ.source ∩ (Φ : M₀ → M₁) ⁻¹' Ψ.source :=
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
@[simp]
private theorem pdTrans_apply
    {H₀ H₁ H₂ : Type*}
    [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I₀ : ModelWithCorners ℝ E H₀}
    {I₁ : ModelWithCorners ℝ E H₁}
    {I₂ : ModelWithCorners ℝ E H₂}
    {M₀ M₁ M₂ : Type*}
    [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
    (Φ : PartialDiffeomorph I₀ I₁ M₀ M₁ ∞)
    (Ψ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (x : M₀) :
    pdTrans Φ Ψ x = Ψ (Φ x) :=
  rfl

/-- The Cartan map realized as a genuine smooth partial diffeomorphism near
the selected source and target centers. -/
def cartanPD
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {g' : SmoothRiemannianMetric I' M'}
    {hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w))}
    {p' : M'} (B' : DiagInvBranch (I := I') g' hEnorm' p')
    (i : E ≃L[ℝ] E) :
    PartialDiffeomorph I I' M M' ∞ :=
  let L : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    i.toDiffeomorph.toPartialDiffeomorph
  pdTrans (pdTrans B.fixedPD.symm L) B'.fixedPD

omit [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space (TangentBundle I' M')] [ConnectedSpace M] [ConnectedSpace M'] in
/-- The partial Cartan diffeomorphism has the expected totalized map. -/
theorem cartanPD_coe
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {g' : SmoothRiemannianMetric I' M'}
    {hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w))}
    {p' : M'} (B' : DiagInvBranch (I := I') g' hEnorm' p')
    (i : E ≃L[ℝ] E) :
    (cartanPD B B' i : M → M') =
      cartanMap B p g' hEnorm' p' i :=
  rfl

omit [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space (TangentBundle I' M')] [ConnectedSpace M] [ConnectedSpace M'] in
/-- The source center belongs to the Cartan partial diffeomorphism. -/
theorem cartanPD_center
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {g' : SmoothRiemannianMetric I' M'}
    {hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w))}
    {p' : M'} (B' : DiagInvBranch (I := I') g' hEnorm' p')
    (i : E ≃L[ℝ] E) :
    p ∈ (cartanPD B B' i).source := by
  change
    p ∈ B.fixedPD.target ∩
      (B.fixedPD.symm : M → E) ⁻¹' Set.univ ∩
        (fun x : M => i (B.fixedPD.symm x)) ⁻¹' B'.fixedPD.source
  refine ⟨⟨B.fixedPD_center_mem, Set.mem_univ _⟩, ?_⟩
  simp only [Set.mem_preimage, B.fixedPD_symm_center, map_zero]
  exact B'.fixedPD_zero_mem

/-- On its source, the Cartan partial diffeomorphism preserves the full
Riemannian inner product. -/
theorem cartanPD_inner
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (g' : SmoothRiemannianMetric I' M')
    (hEnorm' : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g'.inner x w w)))
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {p' : M'} (B' : DiagInvBranch (I := I') g' hEnorm' p')
    (i : E ≃L[ℝ] E)
    (hi : ∀ a b : E, g'.inner p' (i a) (i b) = g.inner p a b)
    (hR : ∀ (x : M) (X Y Z : TangentSpace I x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    (hR' : ∀ (x : M') (X Y Z : TangentSpace I' x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I') g') x)
        X Y Z =
          g'.inner x Y Z • X - g'.inner x X Z • Y)
    {x : M} (hx : x ∈ (cartanPD B B' i).source)
    (Y Z : TangentSpace I x) :
    g'.inner (cartanPD B B' i x)
        (mfderiv I I' (cartanPD B B' i) x Y)
        (mfderiv I I' (cartanPD B B' i) x Z) =
      g.inner x Y Z := by
  have hdom : (p, x) ∈ B.dom := by
    have hx' := hx.1.1
    change (p, x) ∈ B.dom at hx'
    exact hx'
  rw [cartanPD_coe B B' i]
  exact cartanMap_inner g hEnorm g' hEnorm' B p p' i hi hR hR'
    hdom Y Z

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
