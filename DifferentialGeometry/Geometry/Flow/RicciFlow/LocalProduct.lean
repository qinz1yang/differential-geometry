import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
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

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G' : Type*} [TopologicalSpace G'] {K : ModelWithCorners ℝ F' G'} [K.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G' P] [IsManifold K ∞ P] [T2Space P]
  [SigmaCompactSpace P]

theorem isSolutionOn_fst_of_local_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : ℝ → SmoothRiemannianMetric J N) (h : ℝ → SmoothRiemannianMetric K P)
    (Phi : N × P → M) (hPhi : IsLocalDiffeomorph (J.prod K) I ∞ Phi) (y₀ : P)
    {α β a : ℝ} (ha : a ∈ Ioo α β) (hreg : Ioo α β ⊆ D.regular)
    (hprod : ∀ t ∈ Ioo α β, localPullMetric (S.family.metric t) Phi hPhi = (g t).prod (h t)) :
    IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := J) (M := N) (RealTimeInterval.openInterval α β a ha)) := by
  let Y : N → M := fun x => Phi (x, y₀)
  have hY : ContMDiff J I ∞ Y :=
    hPhi.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hYder x : mfderiv J I Y x = (mfderiv (J.prod K) I Phi (x, y₀)).comp
      (ContinuousLinearMap.inl ℝ F F') := by
    have hcomp := mfderiv_comp x ((hPhi (x, y₀)).contMDiffAt.mdifferentiableAt (by decide))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    change mfderiv J I Y x = (mfderiv (J.prod K) I Phi (x, y₀)).comp
      (mfderiv J (J.prod K) (fun z : N => (z, y₀)) x) at hcomp
    rw [mfderiv_prod_left] at hcomp
    exact hcomp
  have hinner t (ht : t ∈ Ioo α β) x (u v : TangentSpace J x) :
      (g t).inner x u v = (S.family.metric t).inner (Y x)
        (mfderiv J I Y x u) (mfderiv J I Y x v) := by
    rw [hYder]
    let U : TangentSpace (J.prod K) (x, y₀) := (u, 0)
    let V : TangentSpace (J.prod K) (x, y₀) := (v, 0)
    have hh := congrArg (fun q : SmoothRiemannianMetric (J.prod K) (N × P) =>
      q.inner (x, y₀) U V) (hprod t ht)
    rw [localPullMetric_inner, SmoothRiemannianMetric.prod_inner,
      mfderiv_fst, mfderiv_snd] at hh
    change (S.family.metric t).inner (Phi (x, y₀))
      (mfderiv (J.prod K) I Phi (x, y₀) (u, 0))
      (mfderiv (J.prod K) I Phi (x, y₀) (v, 0)) =
        (g t).inner x u v + (h t).inner y₀ 0 0 at hh
    rw [map_zero, add_zero] at hh
    exact hh.symm
  have hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)))
      (Ioo α β ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hreg hp.1))).contMDiffWithinAt
  have hgram := chartGramMatrix_joint_contMDiffOn_of_pullback
    S.family.metric (Ioo α β) hmetric g Y hY hinner
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_Ioo g α β hgram
  apply isSolutionOn_of_joint_metric (RealTimeInterval.openInterval α β a ha)
    isOpen_Ioo.uniqueDiffOn g hjoint
  intro t ht x u v
  exact metric_hasDerivWithinAt_fst_of_local_product S hS Phi hPhi g h
    ht (hreg ht) hprod x y₀ u v

end DifferentialGeometry.PDE.RicciFlow
