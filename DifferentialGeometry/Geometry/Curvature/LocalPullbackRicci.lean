import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

section LocalCurvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N]

theorem metricRm04StdAt_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (localPullMetric (I := I) (J := J) g f hf) x X Y Z W =
      metricRm04StandardAt g (f x)
        (mfderiv I J f x X) (mfderiv I J f x Y)
        (mfderiv I J f x Z) (mfderiv I J f x W) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : IsManifold J 1 N := IsManifold.of_le (I := J) (M := N) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  obtain ⟨Phi, hx, hagrees⟩ := hf x
  let U : Opens M := ⟨Phi.source, Phi.open_source⟩
  have hU : (U : Set M) ⊆ Phi.source := Set.Subset.rfl
  let V : Opens N := ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let Psi : U ≃ₘ⟮I, J⟯ V :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let xu : U := ⟨x, hx⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen I U.isOpen)
  have hrange : Set.range Psi = Set.univ := Psi.surjective.range_eq
  let : SigmaCompactSpace V := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range Psi.continuous)
  have hpoint (y : U) : (Psi y : N) = f (y : M) := by
    change (Phi : M → N) (y : M) = f (y : M)
    exact (hagrees (hU y.property)).symm
  have hderiv (y : U) : mfderiv I J (Psi : U → V) y =
      mfderiv I J f (y : M) := by
    have hnear : f =ᶠ[𝓝 (y : M)] (Phi : M → N) :=
      Filter.eventuallyEq_of_mem (Phi.open_source.mem_nhds (hU y.property)) hagrees
    have hdf : mfderiv I J f (y : M) = mfderiv I J (Phi : M → N) (y : M) :=
      hnear.mfderiv_eq
    ext v
    rw [hdf]
    exact DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      Phi hU y v
  have hmetric : (localPullMetric (I := I) (J := J) g f hf).restrictOpen U =
      Diffeomorph.pullbackMetricCross (g.restrictOpen V) Psi := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have hv : (mfderiv I J Psi y v : F) = mfderiv I J f (y : M) v :=
      congrArg (fun A : E →L[ℝ] F => A v) (hderiv y)
    have hw : (mfderiv I J Psi y w : F) = mfderiv I J f (y : M) w :=
      congrArg (fun A : E →L[ℝ] F => A w) (hderiv y)
    have hp := congrArg (fun p : N =>
      g.inner p (mfderiv I J Psi y v) (mfderiv I J Psi y w)) (hpoint y)
    have hs := congrArg₂ (fun u z : F => g.inner (f (y : M)) u z) hv hw
    have hl := localPullMetric_inner g f hf (y : M)
      (v : TangentSpace I (y : M)) (w : TangentSpace I (y : M))
    have hr := Diffeomorph.pullbackMetricCross_inner (g.restrictOpen V) Psi y v w
    exact hl.trans (hr.trans (hp.trans hs)).symm
  have h := metricRm04Standard_pullbackCross (g.restrictOpen V) Psi xu X Y Z W
  rw [← hmetric] at h
  have hleft := metricRm04StandardAt_restrictOpen (localPullMetric g f hf) U xu
    (X : TangentSpace I xu) (Y : TangentSpace I xu)
    (Z : TangentSpace I xu) (W : TangentSpace I xu)
  have hright := metricRm04StandardAt_restrictOpen g V (Psi xu)
    (mfderiv I J Psi xu X) (mfderiv I J Psi xu Y)
    (mfderiv I J Psi xu Z) (mfderiv I J Psi xu W)
  have hfinal := hleft.symm.trans (h.trans hright)
  simp only [mfderiv_subtype_val_apply] at hfinal
  have hd (v : E) : (mfderiv I J Psi xu v : F) = mfderiv I J f x v :=
    congrArg (fun A : E →L[ℝ] F => A v) (hderiv xu)
  have htup :
      ((Psi xu : N), (mfderiv I J Psi xu X : F), (mfderiv I J Psi xu Y : F),
        (mfderiv I J Psi xu Z : F), (mfderiv I J Psi xu W : F)) =
      (f x, (mfderiv I J f x X : F), (mfderiv I J f x Y : F),
        (mfderiv I J f x Z : F), (mfderiv I J f x W : F)) :=
    Prod.ext (hpoint xu) (Prod.ext (hd X) (Prod.ext (hd Y) (Prod.ext (hd Z) (hd W))))
  have hslots := congrArg (fun p : N × F × F × F × F =>
    metricRm04StandardAt g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) htup
  have hi (v : E) : (mfderiv I I (Subtype.val : U → M) xu v : E) = v :=
    mfderiv_subtype_val_apply (I := I) U xu v
  have hsourceTuple :
      ((mfderiv I I (Subtype.val : U → M) xu X : E),
        (mfderiv I I (Subtype.val : U → M) xu Y : E),
        (mfderiv I I (Subtype.val : U → M) xu Z : E),
        (mfderiv I I (Subtype.val : U → M) xu W : E)) =
      ((X : E), (Y : E), (Z : E), (W : E)) :=
    Prod.ext (hi X) (Prod.ext (hi Y) (Prod.ext (hi Z) (hi W)))
  have hsource := congrArg (fun p : E × E × E × E =>
    metricRm04StandardAt (localPullMetric g f hf) x p.1 p.2.1 p.2.2.1 p.2.2.2) hsourceTuple
  exact hsource.symm.trans (hfinal.trans hslots)

variable [BoundarylessManifold I M] [BoundarylessManifold J N]

theorem ricciTensor_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (localPullMetric (I := I) (J := J) g f hf) x v w =
      ricciTensor g (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let gP := localPullMetric (I := I) (J := J) g f hf
  let e := hf.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have hcurv (u v' w' : TangentSpace I x) :
      mfderiv I J f x (riemannOp (LeviCivita gP) x u v' w') =
        riemannOp (LeviCivita g) (f x)
          (mfderiv I J f x u) (mfderiv I J f x v') (mfderiv I J f x w') := by
    apply tangentFlatLinear_injective (I := J) g (f x)
    ext z
    simp only [tangentFlatLinear_apply]
    obtain ⟨q, hq⟩ := e.surjective z
    have hq' : mfderiv I J f x q = z := hq
    rw [← hq']
    have h := metricRm04StdAt_localPullMetric (I := I) (J := J) g f hf x u v' w' q
    rw [metricRm04StandardAt_eq_inner_riemannOp,
      metricRm04StandardAt_eq_inner_riemannOp, localPullMetric_inner] at h
    exact (g.symm (f x) _ _).trans (h.trans (g.symm (f x) _ _))
  let A := ricciEndo g (f x) (e v) (e w)
  have hconj : ricciEndo gP x v w = e.toLinearEquiv.symm.conj A := by
    apply LinearMap.ext
    intro z
    apply e.injective
    change e (riemannOp (LeviCivita gP) x z v w) = e (e.symm (A (e z)))
    rw [e.apply_symm_apply]
    exact hcurv z v w
  change ricciTensor gP x v w = ricciTensor g (f x) (e v) (e w)
  rw [ricciTensor_apply, ricciTensor_apply, hconj]
  exact LinearMap.trace_conj' A e.toLinearEquiv.symm

end LocalCurvature
end DifferentialGeometry.Geometry.Curvature

end
