import DifferentialGeometry.Geometry.Comparison.ConvexTangentSpace
import DifferentialGeometry.Geometry.Comparison.Nonnegative.RauchParallel

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem mfderiv_shift {f : ℝ → M} {s : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f s) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s + σ)) 0 1 : E)
      = (mfderiv 𝓘(ℝ, ℝ) I f s 1 : E) := by
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => s + σ) 0
      (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id (0 : ℝ)).const_add s).hasMFDerivAt
  have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s + σ) 0) := by
    simpa only [add_zero] using hf
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s + σ)) 0
      ((mfderiv 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s + σ) 0)).comp
        (ContinuousLinearMap.id ℝ ℝ)) :=
    HasMFDerivAt.comp (0 : ℝ) hf0.hasMFDerivAt hline
  rw [hcomp.mfderiv]
  exact congrArg (fun t : ℝ => (mfderiv 𝓘(ℝ, ℝ) I f t 1 : E)) (add_zero s)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem curveVelocity_mem_sliceTangent {S : Set M} {c : ℝ → M} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), c (t + σ) ∈ S) :
    (mfderiv 𝓘(ℝ, ℝ) I c t 1 : TangentSpace I (c t)) ∈ sliceTangent I S (c t) := by
  have hline : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => t + σ) 0 :=
    (((hasFDerivAt_id (0 : ℝ)).const_add t).hasMFDerivAt).mdifferentiableAt
  have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I c ((fun σ : ℝ => t + σ) 0) := by
    simpa only [add_zero] using hc
  have hshift : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => c (t + σ)) 0 :=
    MDifferentiableAt.comp (0 : ℝ) hf0 hline
  have h := mem_sliceTangent_of_curve (I := I) (S := S) (f := fun σ : ℝ => c (t + σ))
    (x := c t) (by simp) hev hshift
  have heq : (mfderiv 𝓘(ℝ, ℝ) I c t 1 : TangentSpace I (c t))
      = (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => c (t + σ)) 0 1 : TangentSpace I (c t)) :=
    (mfderiv_shift hc).symm
  rw [heq]
  exact h

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem curveVelocity_intrinsicGeodesic_mem_sliceTangent
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} {y : M} {u : TangentSpace I y} {L : ℝ}
    (hτ : ∀ s ∈ Icc (0 : ℝ) L,
      intrinsicGeodesic (I := I) g hEnorm y u s ∈ maxSliceLocus I C)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) L) :
    curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) t
      ∈ sliceTangent I (maxSliceLocus I C) (intrinsicGeodesic (I := I) g hEnorm y u t) := by
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm y u) :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm y u
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) t :=
    hsmooth.contMDiffAt.mdifferentiableAt (by simp)
  have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm y u (t + σ) ∈ maxSliceLocus I C := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.2)] with σ hσ
    exact hτ (t + σ) ⟨by linarith [hσ.1, ht.1], by linarith [hσ.2]⟩
  exact curveVelocity_mem_sliceTangent hc hev



theorem parallelShift_mem_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {t : ℝ}
    (hτt : intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C)
    (hunit : g.inner (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) (ξ t) = 1)
    (hξt : ξ t ∈
      sliceTangent I (maxSliceLocus I C) (intrinsicGeodesic (I := I) g hEnorm y u t))
    {h : ℝ} (hh : |h| < Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t)
      (relBoundary I C)) :
    parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C := by
  have hmem : h • ξ t ∈
      sliceTangent I (maxSliceLocus I C) (intrinsicGeodesic (I := I) g hEnorm y u t) :=
    (sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u t)).smul_mem h hξt
  have hlen : Real.sqrt (g.inner (intrinsicGeodesic (I := I) g hEnorm y u t)
      (h • ξ t) (h • ξ t)) = |h| := by
    rw [gInner_smul_self (I := I) g (intrinsicGeodesic (I := I) g hEnorm y u t) h (ξ t),
      hunit, mul_one, Real.sqrt_sq_eq_abs]
  have hexp := expMapIntrinsic_mem_maxSliceLocus hEnorm hC hCclosed hτt hmem
    (by rw [hlen]; exact hh)
  rw [parallelShift]
  exact hexp

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem mem_sliceTangent_of_parallelShift_mem
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {t : ℝ}
    (hmem : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C) :
    ξ t ∈ sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u t) := by
  refine mem_sliceTangent_of_isInnerDirection (g := g) (hEnorm := hEnorm) (C := C) ?_
  exact hmem



def HasSliceParallelTransport (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (C : Set M) : Prop :=
  ∀ (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)) (L : ℝ),
    IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
      (∀ t ∈ Icc (0 : ℝ) L,
        intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C) →
        ξ 0 ∈ sliceTangent I (maxSliceLocus I C)
            (intrinsicGeodesic (I := I) g hEnorm y u 0) →
          ∀ t ∈ Icc (0 : ℝ) L, ξ t ∈ sliceTangent I (maxSliceLocus I C)
            (intrinsicGeodesic (I := I) g hEnorm y u t)

theorem parallelShift_mem_maxSliceLocus_of_sliceParallelTransport
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hpar : HasSliceParallelTransport (I := I) g hEnorm C)
    {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {L : ℝ}
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L)
    (hτ : ∀ t ∈ Icc (0 : ℝ) L,
      intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C)
    (hξ0 : ξ 0 ∈ sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L)
    {h : ℝ} (hh : |h| < Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t)
      (relBoundary I C)) :
    parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C :=
  parallelShift_mem_maxSliceLocus hEnorm hC hCclosed (hτ t ht) (hξ.2.2.1 t ht)
    (hpar y u ξ L hξ hτ hξ0 t ht) hh

end DifferentialGeometry.Geometry.Topology
