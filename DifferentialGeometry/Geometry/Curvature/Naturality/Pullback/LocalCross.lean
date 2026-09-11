import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open DifferentialGeometry.Tensor0SBundle
open Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

theorem metricRm04StandardAt_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := M)
        (localPullMetric (I := I) (J := J) g f hf) x X Y Z W =
      metricRm04StandardAt (I := J) (M := N) g (f x)
        (mfderiv I J f x X) (mfderiv I J f x Y)
        (mfderiv I J f x Z) (mfderiv I J f x W) := by
  let Φ : PartialDiffeomorph I J M N ∞ := Classical.choose (hf x)
  have hxΦ : x ∈ Φ.source := (hf x).choose_spec.1
  have hEq : Set.EqOn f (Φ : M → N) Φ.source := (hf x).choose_spec.2
  let U : Opens M :=
    ⟨Φ.source ∩ (chartAt H x).source, Φ.open_source.inter (chartAt H x).open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := fun _ hy => hy.1
  let V : Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : Diffeomorph I J U V ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU
  let xu : U := ⟨x, hxΦ, mem_chart_source H x⟩
  let toU (v : TangentSpace I x) : TangentSpace I xu :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) xu).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  have htoU (v : TangentSpace I x) :
      mfderiv I I (Subtype.val : U → M) xu (toU v) = v := by
    rw [mfderiv_subtype_val_apply]
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) xu).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) x v)) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) x v
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e : U ≃ₜ ((chartAt H x) '' (U : Set M)) :=
    (chartAt H x).homeomorphOfImageSubsetSource (fun _ hy => hy.2) rfl
  let _ : SecondCountableTopology U := e.secondCountableTopology
  let _ : SigmaCompactSpace U := inferInstance
  let _ : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_iff_isSigmaCompact_univ.mpr (by
        simpa using isSigmaCompact_univ.image Ψ.toHomeomorph.continuous))
  have hEqNhds : f =ᶠ[𝓝 x] (Φ : M → N) :=
    Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hxΦ) hEq
  have hdf : mfderiv I J f x = mfderiv I J (Φ : M → N) x :=
    hEqNhds.mfderiv_eq
  have hΨd (y : U) (v : TangentSpace I y) :
      mfderiv I J (Ψ : U → V) y v =
        mfderiv I J (Φ : M → N) (y : M) v := by
    simpa only [Ψ] using
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU y v
  have hΨdAmbient (y : U) (v : TangentSpace I y) :
      mfderiv J J (Subtype.val : V → N) (Ψ y)
          (mfderiv I J (Ψ : U → V) y v) =
        mfderiv I J (Φ : M → N) (y : M)
          (mfderiv I I (Subtype.val : U → M) y v) := by
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    exact hΨd y v
  have hΨval (y : U) : ((Ψ y : V) : N) = (Φ : M → N) (y : M) := by
    rfl
  have hmetric :
      (localPullMetric (I := I) (J := J) g f hf).restrictOpen (I := I) U =
        Diffeomorph.pullbackMetricCross (I := I) (J := J)
          (g.restrictOpen (I := J) V) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have hyΦ : (y : M) ∈ Φ.source := hU y.2
    have hEqYNhds : f =ᶠ[𝓝 (y : M)] (Φ : M → N) :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hyΦ) hEq
    have hdfY : mfderiv I J f (y : M) =
        mfderiv I J (Φ : M → N) (y : M) :=
      hEqYNhds.mfderiv_eq
    calc
      ((localPullMetric (I := I) (J := J) g f hf).restrictOpen (I := I) U).inner
          y v w =
          (localPullMetric (I := I) (J := J) g f hf).inner (y : M)
            (mfderiv I I (Subtype.val : U → M) y v)
            (mfderiv I I (Subtype.val : U → M) y w) := by
              rw [SmoothRiemannianMetric.restrictOpen_inner,
                mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
      _ = g.inner (f (y : M))
            (mfderiv I J f (y : M)
              (mfderiv I I (Subtype.val : U → M) y v))
            (mfderiv I J f (y : M)
              (mfderiv I I (Subtype.val : U → M) y w)) :=
        localPullMetric_inner (I := I) (J := J) g f hf (y : M)
          (mfderiv I I (Subtype.val : U → M) y v)
          (mfderiv I I (Subtype.val : U → M) y w)
      _ = g.inner ((Φ : M → N) (y : M))
            (mfderiv I J (Φ : M → N) (y : M)
              (mfderiv I I (Subtype.val : U → M) y v))
            (mfderiv I J (Φ : M → N) (y : M)
              (mfderiv I I (Subtype.val : U → M) y w)) := by
        rw [hEq hyΦ, hdfY]
      _ = (g.restrictOpen (I := J) V).inner (Ψ y)
            (mfderiv I J (Ψ : U → V) y v)
            (mfderiv I J (Ψ : U → V) y w) := by
        rw [SmoothRiemannianMetric.restrictOpen_inner,
          mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
          hΨd, hΨd, hΨval]
      _ = (Diffeomorph.pullbackMetricCross (I := I) (J := J)
            (g.restrictOpen (I := J) V) Ψ).inner y v w :=
        (Diffeomorph.pullbackMetricCross_inner
          (I := I) (J := J) (g.restrictOpen (I := J) V) Ψ y v w).symm
  calc
    metricRm04StandardAt (I := I) (M := M)
        (localPullMetric (I := I) (J := J) g f hf) x X Y Z W =
        metricRm04StandardAt (I := I) (M := U)
          ((localPullMetric (I := I) (J := J) g f hf).restrictOpen (I := I) U)
          xu (toU X) (toU Y) (toU Z) (toU W) := by
            rw [metricRm04StandardAt_restrictOpen, htoU, htoU, htoU, htoU]
    _ = metricRm04StandardAt (I := I) (M := U)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J)
            (g.restrictOpen (I := J) V) Ψ)
          xu (toU X) (toU Y) (toU Z) (toU W) := by rw [hmetric]
    _ = metricRm04StandardAt (I := J) (M := V)
          (g.restrictOpen (I := J) V) (Ψ xu)
          (mfderiv I J (Ψ : U → V) xu (toU X))
          (mfderiv I J (Ψ : U → V) xu (toU Y))
          (mfderiv I J (Ψ : U → V) xu (toU Z))
          (mfderiv I J (Ψ : U → V) xu (toU W)) :=
      metricRm04Standard_pullbackCross
        (I := I) (J := J) (g.restrictOpen (I := J) V) Ψ xu
          (toU X) (toU Y) (toU Z) (toU W)
    _ = metricRm04StandardAt (I := J) (M := N) g ((Ψ xu : V) : N)
          (mfderiv J J (Subtype.val : V → N) (Ψ xu)
            (mfderiv I J (Ψ : U → V) xu (toU X)))
          (mfderiv J J (Subtype.val : V → N) (Ψ xu)
            (mfderiv I J (Ψ : U → V) xu (toU Y)))
          (mfderiv J J (Subtype.val : V → N) (Ψ xu)
            (mfderiv I J (Ψ : U → V) xu (toU Z)))
          (mfderiv J J (Subtype.val : V → N) (Ψ xu)
            (mfderiv I J (Ψ : U → V) xu (toU W))) :=
      metricRm04StandardAt_restrictOpen
        (I := J) g V (Ψ xu)
          (mfderiv I J (Ψ : U → V) xu (toU X))
          (mfderiv I J (Ψ : U → V) xu (toU Y))
          (mfderiv I J (Ψ : U → V) xu (toU Z))
          (mfderiv I J (Ψ : U → V) xu (toU W))
    _ = metricRm04StandardAt (I := J) (M := N) g (f x)
          (mfderiv I J f x X) (mfderiv I J f x Y)
          (mfderiv I J f x Z) (mfderiv I J f x W) := by
      rw [hΨdAmbient, hΨdAmbient, hΨdAmbient, hΨdAmbient,
        htoU, htoU, htoU, htoU, hΨval, ← hdf]
      change metricRm04StandardAt (I := J) (M := N) g ((Φ : M → N) x)
          (mfderiv I J f x X) (mfderiv I J f x Y)
          (mfderiv I J f x Z) (mfderiv I J f x W) = _
      rw [← hEq hxΦ]

section Trace

variable [I.Boundaryless] [J.Boundaryless]

private theorem metricRm04StandardAt_eq_inner_riemannOp_local
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) g x X Y Z W =
      g.inner x W (riemannOp (cov := LeviCivita (I := I) g) x X Y Z) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  rw [metricRm04StandardAt_apply,
    show metricRm04At (I := I) g x =
        riemannCurvature04At g (metricCov (I := I) g)
          (metricCov_smooth (I := I) g) x from rfl,
    riemannCurvature04At_apply_const]
  have : CovariantDerivative.ContMDiffCovariantDerivative
      (metricCov (I := I) g) ∞ :=
    LeviCivita_isContMDiff g
  rw [DifferentialGeometry.connectionRiemannCurvatureField_tangentConst_eq_riemannOp
      (metricCov (I := I) g) (metricCov_smooth (I := I) g) x X Y Z,
    show riemannOp (cov := metricCov (I := I) g) x X Y Z =
        riemannOp (cov := LeviCivita (I := I) g) x X Y Z from rfl]

theorem ricciTensor_localPull
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I)
        (localPullMetric (I := I) (J := J) g Phi hPhi) x v w =
      ricciTensor (I := J) g (Phi x)
        (mfderiv I J Phi x v) (mfderiv I J Phi x w) := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (localPullMetric (I := I) (J := J) g Phi hPhi) x
  let dPhi : TangentSpace I x ≃L[Real] TangentSpace J (Phi x) :=
    hPhi.mfderivToContinuousLinearEquiv (by simp) x
  let idxEquiv :
      Fin (Module.finrank Real (TangentSpace I x)) ≃
        Fin (Module.finrank Real (TangentSpace J (Phi x))) :=
    finCongr dPhi.toLinearEquiv.finrank_eq
  let basis' :
      Module.Basis (Fin (Module.finrank Real (TangentSpace J (Phi x))))
        Real (TangentSpace J (Phi x)) :=
    (basis.map dPhi.toLinearEquiv).reindex idxEquiv
  have hdPhi_apply (z : TangentSpace I x) :
      dPhi z = mfderiv I J Phi x z := by
    have hco := hPhi.mfderivToContinuousLinearEquiv_coe
      (x := x) (by simp)
    exact congrArg
      (fun L : TangentSpace I x →L[Real] TangentSpace J (Phi x) ↦ L z) hco
  have hbasis'_apply (j) :
      basis' j = mfderiv I J Phi x (basis (idxEquiv.symm j)) := by
    change ((basis.map dPhi.toLinearEquiv).reindex idxEquiv) j = _
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
    exact hdPhi_apply _
  have hON' : ∀ i j,
      g.inner (Phi x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hbasis'_apply, hbasis'_apply,
      ← localPullMetric_inner (I := I) (J := J) g Phi hPhi x
        (basis (idxEquiv.symm i)) (basis (idxEquiv.symm j))]
    simpa using hON (idxEquiv.symm i) (idxEquiv.symm j)
  rw [ricciTensor_eq_orthonormal_trace
        (I := I) (localPullMetric (I := I) (J := J) g Phi hPhi)
        x v w (fun i ↦ basis i) hON,
      ricciTensor_eq_orthonormal_trace
        (I := J) g (Phi x) (mfderiv I J Phi x v)
        (mfderiv I J Phi x w) (fun i ↦ basis' i) hON']
  refine Fintype.sum_equiv idxEquiv _ _ ?_
  intro i
  have hbasis'_comp :
      basis' (idxEquiv i) = mfderiv I J Phi x (basis i) := by
    simpa using hbasis'_apply (idxEquiv i)
  rw [hbasis'_comp]
  rw [(localPullMetric (I := I) (J := J) g Phi hPhi).symm x
        (riemannOp
          (cov := LeviCivita (I := I)
            (localPullMetric (I := I) (J := J) g Phi hPhi))
          x (basis i) v w) (basis i),
      ← metricRm04StandardAt_eq_inner_riemannOp_local
        (I := I) (localPullMetric (I := I) (J := J) g Phi hPhi)
        x (basis i) v w (basis i),
      metricRm04StandardAt_localPullMetric
        (I := I) (J := J) g Phi hPhi x (basis i) v w (basis i),
      metricRm04StandardAt_eq_inner_riemannOp_local
        (I := J) g (Phi x) (mfderiv I J Phi x (basis i))
        (mfderiv I J Phi x v) (mfderiv I J Phi x w)
        (mfderiv I J Phi x (basis i)),
      g.symm (Phi x) (mfderiv I J Phi x (basis i))
        (riemannOp (cov := LeviCivita (I := J) g) (Phi x)
          (mfderiv I J Phi x (basis i))
          (mfderiv I J Phi x v) (mfderiv I J Phi x w))]

theorem metricScalarAt_eq_orthonormal_trace
    (g : SmoothRiemannianMetric I M) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0) :
    metricScalarAt (I := I) g x =
      ∑ i : Idx, ricciTensor (I := I) g x (basis i) (basis i) := by
  classical
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis hON
  rw [metricScalarAt_def,
    Operator.metricTracePair0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx)) hinv
      (metricRicciAt (I := I) (M := M) g x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul,
      DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor]
  · intro j _ hji
    have hij : i ≠ j := fun hij ↦ hji hij.symm
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hij, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem metricScalarAt_localPull
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi) (x : M) :
    metricScalarAt (I := I)
        (localPullMetric (I := I) (J := J) g Phi hPhi) x =
      metricScalarAt (I := J) g (Phi x) := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (localPullMetric (I := I) (J := J) g Phi hPhi) x
  let dPhi : TangentSpace I x ≃L[Real] TangentSpace J (Phi x) :=
    hPhi.mfderivToContinuousLinearEquiv (by simp) x
  let idxEquiv :
      Fin (Module.finrank Real (TangentSpace I x)) ≃
        Fin (Module.finrank Real (TangentSpace J (Phi x))) :=
    finCongr dPhi.toLinearEquiv.finrank_eq
  let basis' :
      Module.Basis (Fin (Module.finrank Real (TangentSpace J (Phi x))))
        Real (TangentSpace J (Phi x)) :=
    (basis.map dPhi.toLinearEquiv).reindex idxEquiv
  have hdPhi_apply (z : TangentSpace I x) :
      dPhi z = mfderiv I J Phi x z := by
    have hco := hPhi.mfderivToContinuousLinearEquiv_coe
      (x := x) (by simp)
    exact congrArg
      (fun L : TangentSpace I x →L[Real] TangentSpace J (Phi x) ↦ L z) hco
  have hbasis'_apply (j) :
      basis' j = mfderiv I J Phi x (basis (idxEquiv.symm j)) := by
    change ((basis.map dPhi.toLinearEquiv).reindex idxEquiv) j = _
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
    exact hdPhi_apply _
  have hON' : ∀ i j,
      g.inner (Phi x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hbasis'_apply, hbasis'_apply,
      ← localPullMetric_inner (I := I) (J := J) g Phi hPhi x
        (basis (idxEquiv.symm i)) (basis (idxEquiv.symm j))]
    simpa using hON (idxEquiv.symm i) (idxEquiv.symm j)
  rw [metricScalarAt_eq_orthonormal_trace
      (I := I) (localPullMetric (I := I) (J := J) g Phi hPhi)
      x basis hON,
    metricScalarAt_eq_orthonormal_trace
      (I := J) g (Phi x) basis' hON']
  refine Fintype.sum_equiv idxEquiv _ _ ?_
  intro i
  have hbasis'_comp :
      basis' (idxEquiv i) = mfderiv I J Phi x (basis i) := by
    simpa using hbasis'_apply (idxEquiv i)
  rw [hbasis'_comp,
    ricciTensor_localPull (I := I) (J := J) g Phi hPhi x]

end Trace

end DifferentialGeometry.Geometry.Curvature
