import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Restriction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

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
