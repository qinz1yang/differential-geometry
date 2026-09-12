import DifferentialGeometry.Tensor.Metric.IsometryNorm
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PartialDiffeomorph
open Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem iter_cov_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := J) (M := N) ∞ r)
    (hAB : ∀ (y : M) (v : Fin r → TangentSpace I y),
      A y v = B (f y) (fun i => mfderiv I J f y (v i)))
    (k : ℕ) (x : M) (v : Fin (r + k) → TangentSpace I x) :
    iterCov (DifferentialGeometry.localPullMetric (I := I) (J := J) g f hf) r A k x v =
      iterCov g r B k (f x) (fun i => mfderiv I J f x (v i)) := by
  obtain ⟨Phi, hx, hagrees⟩ := hf x
  let U : TopologicalSpace.Opens M := ⟨Phi.source, Phi.open_source⟩
  have hU : (U : Set M) ⊆ Phi.source := Set.Subset.rfl
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let Psi : U ≃ₘ⟮I, J⟯ V := toOpensDiffeo Phi hU
  have hpoint (y : U) : (Psi y : N) = f (y : M) := by
    change (Phi : M → N) (y : M) = f (y : M)
    exact (hagrees (hU y.property)).symm
  have hderiv (y : U) : mfderiv I J (Psi : U → V) y = mfderiv I J f (y : M) := by
    have hnear : f =ᶠ[𝓝 (y : M)] (Phi : M → N) :=
      Filter.eventuallyEq_of_mem (Phi.open_source.mem_nhds (hU y.property)) hagrees
    have hdf : mfderiv I J f (y : M) = mfderiv I J (Phi : M → N) (y : M) :=
      hnear.mfderiv_eq
    ext w
    rw [hdf]
    exact mfderiv_toOpensDiffeo Phi hU y w
  have hmetric : ∀ (y : U) (v w : TangentSpace I y),
      (DifferentialGeometry.localPullMetric (I := I) (J := J) g f hf).inner (y : M) v w =
        g.inner (Psi y : N) (mfderiv I J (Psi : U → V) y v)
          (mfderiv I J (Psi : U → V) y w) := by
    intro y v w
    have hv : (mfderiv I J (Psi : U → V) y v : F) = mfderiv I J f (y : M) v :=
      congrArg (fun L : E →L[ℝ] F => L v) (hderiv y)
    have hw : (mfderiv I J (Psi : U → V) y w : F) = mfderiv I J f (y : M) w :=
      congrArg (fun L : E →L[ℝ] F => L w) (hderiv y)
    have hl := DifferentialGeometry.localPullMetric_inner (I := I) (J := J) g f hf (y : M) v w
    have hp := congrArg (fun p : N =>
      g.inner p (mfderiv I J f (y : M) v) (mfderiv I J f (y : M) w)) (hpoint y)
    have hs := congrArg₂ (fun a b : F => g.inner (Psi y : N) a b) hv hw
    exact (hs.trans (hp.trans hl.symm)).symm
  have hAB' : ∀ (y : U) (v : Fin r → TangentSpace I y),
      A (y : M) v = B (Psi y : N) (fun i => mfderiv I J (Psi : U → V) y (v i)) := by
    intro y v
    have hv : (fun i => mfderiv I J (Psi : U → V) y (v i)) =
        (fun i => mfderiv I J f (y : M) (v i)) := by
      funext i
      exact congrArg (fun L : E →L[ℝ] F => L (v i)) (hderiv y)
    rw [hAB (y : M) v, hpoint y, hv]
  have hmain := iter_cov_of_metric_isometry_on_opens
    (DifferentialGeometry.localPullMetric (I := I) (J := J) g f hf) g U V Psi hmetric A B hAB'
    k (⟨x, hx⟩ : U) v
  have hpt : (↑(Psi (⟨x, hx⟩ : U)) : N) = f x := hpoint ⟨x, hx⟩
  have hgoal : (fun i => mfderiv I J (Psi : U → V) (⟨x, hx⟩ : U) (v i)) =
      (fun i => mfderiv I J f x (v i)) := by
    funext i
    exact congrArg (fun L : E →L[ℝ] F => L (v i)) (hderiv ⟨x, hx⟩)
  rw [hgoal, hpt] at hmain
  exact hmain




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem normSq0S_iterCov_localPullMetric
    (g : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := I) (M := N) ∞ r)
    (hAB : ∀ (y : M) (v : Fin r → TangentSpace I y),
      A y v = B (f y) (fun i => mfderiv I I f y (v i)))
    (k : ℕ) (x : M) :
    normSq0S (DifferentialGeometry.localPullMetric (I := I) (J := I) g f hf) x (r + k)
        (iterCov (DifferentialGeometry.localPullMetric (I := I) (J := I) g f hf) r A k x) =
      normSq0S g (f x) (r + k) (iterCov g r B k (f x)) := by
  obtain ⟨Phi, hx, hagrees⟩ := hf x
  let U : TopologicalSpace.Opens M := ⟨Phi.source, Phi.open_source⟩
  have hU : (U : Set M) ⊆ Phi.source := Set.Subset.rfl
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let Psi : U ≃ₘ⟮I, I⟯ V := toOpensDiffeo Phi hU
  have hpoint (y : U) : (Psi y : N) = f (y : M) := by
    change (Phi : M → N) (y : M) = f (y : M)
    exact (hagrees (hU y.property)).symm
  have hderiv (y : U) : mfderiv I I (Psi : U → V) y = mfderiv I I f (y : M) := by
    have hnear : f =ᶠ[𝓝 (y : M)] (Phi : M → N) :=
      Filter.eventuallyEq_of_mem (Phi.open_source.mem_nhds (hU y.property)) hagrees
    have hdf : mfderiv I I f (y : M) = mfderiv I I (Phi : M → N) (y : M) :=
      hnear.mfderiv_eq
    ext w
    rw [hdf]
    exact mfderiv_toOpensDiffeo Phi hU y w
  have hmetric : ∀ (y : U) (v w : TangentSpace I y),
      (DifferentialGeometry.localPullMetric (I := I) (J := I) g f hf).inner (y : M) v w =
        g.inner (Psi y : N) (mfderiv I I (Psi : U → V) y v)
          (mfderiv I I (Psi : U → V) y w) := by
    intro y v w
    have hv : (mfderiv I I (Psi : U → V) y v : E) = mfderiv I I f (y : M) v :=
      congrArg (fun L : E →L[ℝ] E => L v) (hderiv y)
    have hw : (mfderiv I I (Psi : U → V) y w : E) = mfderiv I I f (y : M) w :=
      congrArg (fun L : E →L[ℝ] E => L w) (hderiv y)
    have hl := DifferentialGeometry.localPullMetric_inner (I := I) (J := I) g f hf (y : M) v w
    have hp := congrArg (fun p : N =>
      g.inner p (mfderiv I I f (y : M) v) (mfderiv I I f (y : M) w)) (hpoint y)
    have hs := congrArg₂ (fun a b : E => g.inner (Psi y : N) a b) hv hw
    exact (hs.trans (hp.trans hl.symm)).symm
  have hAB' : ∀ (y : U) (v : Fin r → TangentSpace I y),
      A (y : M) v = B (Psi y : N) (fun i => mfderiv I I (Psi : U → V) y (v i)) := by
    intro y v
    have hv : (fun i => mfderiv I I (Psi : U → V) y (v i)) =
        (fun i => mfderiv I I f (y : M) (v i)) := by
      funext i
      exact congrArg (fun L : E →L[ℝ] E => L (v i)) (hderiv y)
    rw [hAB (y : M) v, hpoint y, hv]
  have hmain := normSq0S_iterCov_of_metric_isometry_on_opens
    (DifferentialGeometry.localPullMetric (I := I) (J := I) g f hf) g U V Psi hmetric A B hAB'
    k (⟨x, hx⟩ : U)
  have hpt : (↑(Psi (⟨x, hx⟩ : U)) : N) = f x := hpoint ⟨x, hx⟩
  rw [hpt] at hmain
  exact hmain




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem metricRm04At_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) (v : Fin 4 → TangentSpace I x) :
    metricRm04At (I := I) (DifferentialGeometry.localPullMetric (I := I) (J := J) g f hf) x v =
      metricRm04At (I := J) g (f x) (fun i => mfderiv I J f x (v i)) := by
  have hv : v = vec4 (I := I) (x := x) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  have hv' : (fun i => mfderiv I J f x (v i)) =
      vec4 (I := J) (x := f x) (mfderiv I J f x (v 0)) (mfderiv I J f x (v 1))
        (mfderiv I J f x (v 2)) (mfderiv I J f x (v 3)) := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  rw [hv']
  exact metricRm04StandardAt_localPullMetric g f hf x (v 0) (v 1) (v 2) (v 3)

theorem metricRicciAt_localPullMetric [I.Boundaryless] [J.Boundaryless]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) (v : Fin 2 → TangentSpace I x) :
    metricRicciAt (I := I) (DifferentialGeometry.localPullMetric (I := I) (J := J) g f hf) x v =
      metricRicciAt (I := J) g (f x) (fun i => mfderiv I J f x (v i)) := by
  have hv : v = vec2 (I := I) (x := x) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  have hv' : (fun i => mfderiv I J f x (v i)) =
      vec2 (I := J) (x := f x) (mfderiv I J f x (v 0)) (mfderiv I J f x (v 1)) := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  rw [hv']
  rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
  exact ricciTensor_localPull g f hf x (v 0) (v 1)


end DifferentialGeometry.Geometry.Tensor
