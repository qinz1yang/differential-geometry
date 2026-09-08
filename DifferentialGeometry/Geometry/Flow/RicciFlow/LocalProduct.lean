import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityLocalCross
import DifferentialGeometry.Geometry.Metric.Product

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N] [J.Boundaryless]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [FiniteDimensional ℝ F']
  {G' : Type*} [TopologicalSpace G'] {K : ModelWithCorners ℝ F' G'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G' P]
  [IsManifold K ∞ P] [T2Space P] [SigmaCompactSpace P] [K.Boundaryless]

theorem metric_hasDerivWithinAt_fst_of_local_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (Phi : N × P → M)
    (hPhi : IsLocalDiffeomorph (J.prod K) I ∞ Phi)
    (g : ℝ → SmoothRiemannianMetric J N) (h : ℝ → SmoothRiemannianMetric K P)
    {A : Set ℝ} {t : ℝ} (ht : t ∈ A) (htD : t ∈ D.regular)
    (hprod : ∀ s ∈ A, localPullMetric (S.family.metric s) Phi hPhi = (g s).prod (h s))
    (x : N) (y : P) (u v : TangentSpace J x) :
    HasDerivWithinAt (fun s => (g s).inner x u v)
      (-2 * ricciTensor (g t) x u v) A t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : CompleteSpace F' := FiniteDimensional.complete ℝ F'
  let U : TangentSpace (J.prod K) (x, y) := (u, 0)
  let V : TangentSpace (J.prod K) (x, y) := (v, 0)
  have heq (s : ℝ) (hs : s ∈ A) :
      (g s).inner x u v = (S.family.metric s).inner (Phi (x, y))
        (mfderiv (J.prod K) I Phi (x, y) U)
        (mfderiv (J.prod K) I Phi (x, y) V) := by
    rw [← localPullMetric_inner (S.family.metric s) Phi hPhi, hprod s hs,
      SmoothRiemannianMetric.prod_inner,
      mfderiv_fst, mfderiv_snd]
    change (g s).inner x u v = (g s).inner x u v + (h s).inner y 0 0
    rw [map_zero, add_zero]
  have hricci : ricciTensor (g t) x u v =
      ricciTensor (S.family.metric t) (Phi (x, y))
        (mfderiv (J.prod K) I Phi (x, y) U)
        (mfderiv (J.prod K) I Phi (x, y) V) := by
    rw [← ricciTensor_localPull (S.family.metric t) Phi hPhi, hprod t ht,
      ricciTensor_prod]
    change ricciTensor (g t) x u v =
      ricciTensor (g t) x u v + ricciTensor (h t) y 0 0
    rw [map_zero, add_zero]
  have hd := (metricDerivAt S hS ⟨t, htD⟩ (Phi (x, y))
    (mfderiv (J.prod K) I Phi (x, y) U)
    (mfderiv (J.prod K) I Phi (x, y) V)).hasDerivWithinAt (s := A)
  rw [hricci]
  apply HasDerivWithinAt.congr _ heq (heq t ht)
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using hd


theorem metric_hasDerivWithinAt_snd_of_local_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (Phi : N × P → M)
    (hPhi : IsLocalDiffeomorph (J.prod K) I ∞ Phi)
    (g : ℝ → SmoothRiemannianMetric J N) (h : ℝ → SmoothRiemannianMetric K P)
    {A : Set ℝ} {t : ℝ} (ht : t ∈ A) (htD : t ∈ D.regular)
    (hprod : ∀ s ∈ A, localPullMetric (S.family.metric s) Phi hPhi = (g s).prod (h s))
    (x : N) (y : P) (u v : TangentSpace K y) :
    HasDerivWithinAt (fun s => (h s).inner y u v)
      (-2 * ricciTensor (h t) y u v) A t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : CompleteSpace F' := FiniteDimensional.complete ℝ F'
  let U : TangentSpace (J.prod K) (x, y) := (0, u)
  let V : TangentSpace (J.prod K) (x, y) := (0, v)
  have heq (s : ℝ) (hs : s ∈ A) :
      (h s).inner y u v = (S.family.metric s).inner (Phi (x, y))
        (mfderiv (J.prod K) I Phi (x, y) U)
        (mfderiv (J.prod K) I Phi (x, y) V) := by
    rw [← localPullMetric_inner (S.family.metric s) Phi hPhi, hprod s hs,
      SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
    change (h s).inner y u v = (g s).inner x 0 0 + (h s).inner y u v
    rw [map_zero, zero_add]
  have hricci : ricciTensor (h t) y u v =
      ricciTensor (S.family.metric t) (Phi (x, y))
        (mfderiv (J.prod K) I Phi (x, y) U)
        (mfderiv (J.prod K) I Phi (x, y) V) := by
    rw [← ricciTensor_localPull (S.family.metric t) Phi hPhi, hprod t ht,
      ricciTensor_prod]
    change ricciTensor (h t) y u v =
      ricciTensor (g t) x 0 0 + ricciTensor (h t) y u v
    rw [map_zero, zero_add]
  have hd := (metricDerivAt S hS ⟨t, htD⟩ (Phi (x, y))
    (mfderiv (J.prod K) I Phi (x, y) U)
    (mfderiv (J.prod K) I Phi (x, y) V)).hasDerivWithinAt (s := A)
  rw [hricci]
  apply HasDerivWithinAt.congr _ heq (heq t ht)
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using hd


theorem metric_hasDerivAt_fst_of_local_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (Phi : N × P → M)
    (hPhi : IsLocalDiffeomorph (J.prod K) I ∞ Phi)
    (g : ℝ → SmoothRiemannianMetric J N) (h : ℝ → SmoothRiemannianMetric K P)
    {A : Set ℝ} {t : ℝ} (hA : A ∈ 𝓝 t) (htD : t ∈ D.regular)
    (hprod : ∀ s ∈ A, localPullMetric (S.family.metric s) Phi hPhi = (g s).prod (h s))
    (x : N) (y : P) (u v : TangentSpace J x) :
    HasDerivAt (fun s => (g s).inner x u v)
      (-2 * ricciTensor (g t) x u v) t :=
  (metric_hasDerivWithinAt_fst_of_local_product S hS Phi hPhi g h
    (mem_of_mem_nhds hA) htD hprod x y u v).hasDerivAt hA


theorem metric_hasDerivAt_snd_of_local_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (Phi : N × P → M)
    (hPhi : IsLocalDiffeomorph (J.prod K) I ∞ Phi)
    (g : ℝ → SmoothRiemannianMetric J N) (h : ℝ → SmoothRiemannianMetric K P)
    {A : Set ℝ} {t : ℝ} (hA : A ∈ 𝓝 t) (htD : t ∈ D.regular)
    (hprod : ∀ s ∈ A, localPullMetric (S.family.metric s) Phi hPhi = (g s).prod (h s))
    (x : N) (y : P) (u v : TangentSpace K y) :
    HasDerivAt (fun s => (h s).inner y u v)
      (-2 * ricciTensor (h t) y u v) t :=
  (metric_hasDerivWithinAt_snd_of_local_product S hS Phi hPhi g h
    (mem_of_mem_nhds hA) htD hprod x y u v).hasDerivAt hA

end DifferentialGeometry.PDE.RicciFlow
