import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Restriction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponentVolume
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section OpenTarget

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

private def liftPartialDiffeomorphTarget {U : TopologicalSpace.Opens N} [Nonempty U]
    (Φ : PartialDiffeomorph I J M U (∞ : WithTop ℕ∞)) :
    PartialDiffeomorph I J M N (∞ : WithTop ℕ∞) := by
  let inclusion := DifferentialGeometry.PartialDiffeomorph.liftTargetOpen
    (DifferentialGeometry.PartialDiffeomorph.refl (I := J) U) rfl
  let Ψ := Φ.trans inclusion
  have hs : Ψ.source = Φ.source := by
    change Φ.source ∩ Φ ⁻¹' Set.univ = Φ.source
    simp
  exact {
    toPartialEquiv := Ψ.toPartialEquiv.copy Ψ rfl Ψ.symm rfl Φ.source hs Ψ.target rfl
    open_source := Φ.open_source
    open_target := Ψ.open_target
    contMDiffOn_toFun := by
      change ContMDiffOn I J ∞ (Ψ : M → N) Φ.source
      rw [← hs]
      exact Ψ.contMDiffOn_toFun
    contMDiffOn_invFun := Ψ.contMDiffOn_invFun }

end OpenTarget

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {S : PointedRiemannianSeq I} {L : PointedRiemannianManifold I} {subseq : ℕ → ℕ}

local instance : TopologicalSpace L.M := L.topology
local instance : ChartedSpace H L.M := L.charted
local instance (i : ℕ) : TopologicalSpace (S.obj i).M := (S.obj i).topology
local instance (i : ℕ) : ChartedSpace H (S.obj i).M := (S.obj i).charted

variable (U : ∀ i, TopologicalSpace.Opens (S.obj i).M)
  (hp : ∀ i, (S.obj i).basepoint ∈ U i)

def PointedRiemannianConvergenceMaps.liftTargetOpen
    (Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq) :
    PointedRiemannianConvergenceMaps S L subseq where
  partialDiffeomorph k := by
    let : Nonempty (U (subseq k)) := ⟨⟨(S.obj (subseq k)).basepoint, hp (subseq k)⟩⟩
    exact liftPartialDiffeomorphTarget (Φ.partialDiffeomorph k)
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map k := congrArg Subtype.val (Φ.basepoint_map k)

theorem PointedRiemannianConvergenceMaps.liftTargetOpen_source
    (Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq) :
    (Φ.liftTargetOpen U hp).source = Φ.source := rfl

theorem PointedRiemannianConvergenceMaps.liftTargetOpen_map
    (Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq) (k : ℕ) (x : L.M) :
    (Φ.liftTargetOpen U hp).map k x =
      Subtype.val (show U (subseq k) from Φ.map k x) := rfl

theorem PointedRiemannianConvergenceMaps.liftTargetOpen_target
    (Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq) (k : ℕ) :
    (Φ.liftTargetOpen U hp).target k =
      Subtype.val '' (show Set (U (subseq k)) from Φ.target k) := by
  let f : L.M → U (subseq k) := fun x => Φ.map k x
  have hf : f '' Φ.source k = (show Set (U (subseq k)) from Φ.target k) :=
    (Φ.partialDiffeomorph k).toPartialEquiv.image_source_eq_target
  calc
    (Φ.liftTargetOpen U hp).target k =
        (fun x => (f x : (S.obj (subseq k)).M)) '' Φ.source k :=
      ((Φ.liftTargetOpen U hp).partialDiffeomorph k).toPartialEquiv.image_source_eq_target.symm
    _ = Subtype.val '' (f '' Φ.source k) := (Set.image_image _ _ _).symm
    _ = _ := congrArg (fun A : Set (U (subseq k)) => Subtype.val '' A) hf

theorem PointedRiemannianConvergenceMaps.liftTargetOpen_symm_apply
    (Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq) (k : ℕ)
    (x : U (subseq k)) :
    ((Φ.liftTargetOpen U hp).partialDiffeomorph k).symm (x : (S.obj (subseq k)).M) =
      (Φ.partialDiffeomorph k).symm (show ((S.restrictOpen U hp).obj (subseq k)).M from x) := by
  let : Nonempty (U (subseq k)) := ⟨x⟩
  exact congrArg (fun y : U (subseq k) =>
    (Φ.partialDiffeomorph k).symm (show ((S.restrictOpen U hp).obj (subseq k)).M from y))
    (Function.leftInverse_invFun (U (subseq k)).isOpenEmbedding'.injective x)

def MetricSourceData.liftTargetOpen
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    {k : ℕ} (D : MetricSourceData Φ k) : MetricSourceData (Φ.liftTargetOpen U hp) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := by
    let : TopologicalSpace (MetricSourceDomain Φ k) := D.topology
    let : ChartedSpace H (MetricSourceDomain Φ k) := D.charted
    let : IsManifold I ∞ (S.obj (subseq k)).M := (S.obj (subseq k)).smooth
    intro x v w
    let f : MetricSourceDomain Φ k → U (subseq k) := fun y => Φ.map k (y : L.M)
    have hd := mfderiv_subtypeVal_comp (I := I) (J := I) f x
    have hv := congrArg (fun A => A v) hd
    have hw := congrArg (fun A => A w) hd
    refine (D.pullback_inner x v w).trans ?_
    change (S.obj (subseq k)).metric.inner (f x : (S.obj (subseq k)).M)
        (mfderiv I I f x v) (mfderiv I I f x w) =
      (S.obj (subseq k)).metric.inner (f x : (S.obj (subseq k)).M)
        (mfderiv I I (fun y => (f y : (S.obj (subseq k)).M)) x v)
        (mfderiv I I (fun y => (f y : (S.obj (subseq k)).M)) x w)
    exact congrArg₂ (fun (a b : TangentSpace I (f x : (S.obj (subseq k)).M)) =>
      (S.obj (subseq k)).metric.inner (f x : (S.obj (subseq k)).M) a b)
      hv.symm hw.symm

theorem MetricSourceData.liftTargetOpen_limitMetric
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    {k : ℕ} (D : MetricSourceData Φ k) :
    (D.liftTargetOpen U hp).limitMetric = D.limitMetric := rfl

theorem MetricSourceData.liftTargetOpen_pullbackMetric
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    {k : ℕ} (D : MetricSourceData Φ k) :
    (D.liftTargetOpen U hp).pullbackMetric = D.pullbackMetric := rfl

theorem MetricSourceData.liftTargetOpen_referenceMetric
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    {k : ℕ} (D : MetricSourceData Φ k) :
    (D.liftTargetOpen U hp).referenceMetric = D.referenceMetric := rfl

theorem MetricSourceData.liftTargetOpen_deriv_norm_sup_on
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    {k : ℕ} (D : MetricSourceData Φ k) (K : Set L.M) (p : ℕ) :
    (D.liftTargetOpen U hp).derivNormSupOn K p = D.derivNormSupOn K p := rfl

def MetricConvergenceData.liftTargetOpen
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    (C : MetricConvergenceData Φ) : MetricConvergenceData (Φ.liftTargetOpen U hp) where
  domain k := (C.domain k).liftTargetOpen U hp
  converges := C.converges

theorem MetricConvergenceData.liftTargetOpen_domain
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    (C : MetricConvergenceData Φ) (k : ℕ) :
    (C.liftTargetOpen U hp).domain k = (C.domain k).liftTargetOpen U hp := rfl

def PointedRiemannianConverges.liftTargetOpen
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    (C : PointedRiemannianConverges (S.restrictOpen U hp) L subseq Φ) :
    PointedRiemannianConverges S L subseq (Φ.liftTargetOpen U hp) where
  metrics := C.metrics.liftTargetOpen U hp

theorem PointedRiemannianConverges.liftTargetOpen_metrics
    {Φ : PointedRiemannianConvergenceMaps (S.restrictOpen U hp) L subseq}
    (C : PointedRiemannianConverges (S.restrictOpen U hp) L subseq Φ) :
    (C.liftTargetOpen U hp).metrics = C.metrics.liftTargetOpen U hp := rfl

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem canonicalSourceData_derivNormSupOn_liftTargetOpen
    {X : PointedRiemannianSeq.{u, uE, uH} I} {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (U : ∀ n, TopologicalSpace.Opens (X.obj n).M) (hp : ∀ n, (X.obj n).basepoint ∈ U n)
    (F : PointedRiemannianConvergenceMaps (X.restrictOpen U hp) L f)
    (n : ℕ) (K : Set L.M) (hK : K ⊆ F.source n) (p : ℕ) :
    (CanonicalMetricCompactness.canonicalSourceData (F.liftTargetOpen U hp) n).derivNormSupOn K p =
      (CanonicalMetricCompactness.canonicalSourceData F n).derivNormSupOn K p := by
  let D := CanonicalMetricCompactness.canonicalSourceData F n
  let V : TopologicalSpace.Opens L.M := metricSourceOpenSubset F n
  let A : SmoothRiemannianMetric I V := D.pullbackMetric
  have hA : ∀ (x : V) (v w : TangentSpace I x),
      A.inner x v w = ((X.restrictOpen U hp).obj (f n)).metric.inner (F.map n x)
        (mfderiv I I (F.map n) x v) (mfderiv I I (F.map n) x w) := by
    intro x v w
    have hh := D.pullback_inner x v w
    have hd (z : TangentSpace I x) :
        mfderiv I I (fun y : V => F.map n (y : L.M)) x z = mfderiv I I (F.map n) (x : L.M) z :=
      congrArg (fun d => d z) (DifferentialGeometry.mfderiv_restrict_open (I := I) (J := I) (F.map n) V x)
    exact hh.trans (congrArg₂ (fun v' w' => ((X.restrictOpen U hp).obj (f n)).metric.inner (F.map n x) v' w')
      (hd v) (hd w))
  have hAlift : ∀ (x : V) (v w : TangentSpace I x),
      A.inner x v w = (X.obj (f n)).metric.inner ((F.liftTargetOpen U hp).map n x)
        (mfderiv I I ((F.liftTargetOpen U hp).map n) x v)
        (mfderiv I I ((F.liftTargetOpen U hp).map n) x w) := by
    intro x v w
    have hd := DifferentialGeometry.mfderiv_subtypeVal_comp (I := I) (J := I)
      (F.map n : L.M → U (f n)) (x : L.M)
    change A.inner x v w = (X.obj (f n)).metric.inner (F.map n x).val
      (mfderiv I I (fun z => (F.map n z).val) x v) (mfderiv I I (fun z => (F.map n z).val) x w)
    rw [hd]
    exact hA x v w
  rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback (F.liftTargetOpen U hp) n V (Subset.refl _)
      A K hK p hAlift,
    canonicalSourceData_derivNormSupOn_eq_of_open_pullback F n V (Subset.refl _) A K hK p hA]

theorem PointedRiemannianConvergenceMaps.exists_canonical_metric_convergence_liftTargetOpen
    {X : PointedRiemannianSeq.{u, uE, uH} I} {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (U : ∀ n, TopologicalSpace.Opens (X.obj n).M) (hp : ∀ n, (X.obj n).basepoint ∈ U n)
    (F : PointedRiemannianConvergenceMaps (X.restrictOpen U hp) L f)
    (C : MetricConvergenceData F)
    (hC : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) :
    ∃ C' : MetricConvergenceData (F.liftTargetOpen U hp),
      ∀ n, C'.domain n = CanonicalMetricCompactness.canonicalSourceData (F.liftTargetOpen U hp) n := by
  obtain ⟨C', hC', _⟩ := exists_metricConvergenceData_canonicalSourceData (F.liftTargetOpen U hp) (by
    intro K hK p eps heps
    obtain ⟨N, hN⟩ := C.converges K hK p eps heps
    refine ⟨N, fun n hn => ?_⟩
    have hh := hN n hn
    rw [canonicalSourceData_derivNormSupOn_liftTargetOpen U hp F n K hh.1 p, ← hC n]
    exact hh.2)
  refine ⟨C', hC'⟩

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Set Filter DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianConvergenceMaps.liftTargetOpen_closedBall_subset_target
    {X : PointedRiemannianSeq.{u, uE, uH} I} {L : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X.connectedComponent L f)
    (r : ℕ → ℝ)
    (hcapture : ∀ n, riemannianClosedBallOf
        (X.connectedComponent.obj (f n)).metric
        (X.connectedComponent.obj (f n)).basepoint (r n) ⊆ F.target n) :
    ∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
      (F.liftTargetOpen
        (fun i => connectedComponentOpen (I := I) (X.obj i).basepoint)
        (fun i => (mem_connectedComponent :
          (X.obj i).basepoint ∈ (connectedComponentOpen (I := I) (X.obj i).basepoint :
            Set (X.obj i).M)))).target n := by
  intro n y hy
  let U : TopologicalSpace.Opens (X.obj (f n)).M :=
    connectedComponentOpen (I := I) (X.obj (f n)).basepoint
  have hyU : y ∈ (U : Set (X.obj (f n)).M) := by
    apply Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I) (X.obj (f n)).metric (X.obj (f n)).basepoint (max (r n) 0 + 1)
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by linarith [le_max_left (r n) 0]))
  let y' : (X.connectedComponent.obj (f n)).M := ⟨y, hyU⟩
  have hy' : y' ∈ riemannianClosedBallOf
      (X.connectedComponent.obj (f n)).metric
      (X.connectedComponent.obj (f n)).basepoint (r n) := by
    exact (Set.ext_iff.mp ((X.obj (f n)).connectedComponent_closedBall (r n)) y').mpr hy
  have hyt : y' ∈ F.target n := hcapture n hy'
  rw [PointedRiemannianConvergenceMaps.liftTargetOpen_target
    (U := fun i => connectedComponentOpen (I := I) (X.obj i).basepoint)
    (hp := fun i => (mem_connectedComponent :
      (X.obj i).basepoint ∈ (connectedComponentOpen (I := I) (X.obj i).basepoint :
        Set (X.obj i).M))) F n]
  exact ⟨y', hyt, rfl⟩

end DifferentialGeometry.CheegerGromovCompactness

end
