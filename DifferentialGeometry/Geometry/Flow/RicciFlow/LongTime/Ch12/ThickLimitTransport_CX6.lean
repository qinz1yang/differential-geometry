import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension

set_option autoImplicit false

/-! # CH12-CX6: canonical convergence survives isometric change of the limit carrier -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12
universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def pullback_limit_maps_CX6 {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L N : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (e : N.M ≃ₘ⟮ThreeModel, ThreeModel⟯ L.M) (hp : e N.basepoint = L.basepoint) :
    PointedRiemannianConvergenceMaps X N σ where
  partialDiffeomorph n := e.toPartialDiffeomorph.trans (Φ.partialDiffeomorph n)
  source_exhausts := by
    have hsrc (n : ℕ) : (e.toPartialDiffeomorph.trans (Φ.partialDiffeomorph n)).source =
        e ⁻¹' Φ.source n := by
      ext x
      simp [PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph, PointedRiemannianConvergenceMaps.source]
    simp_rw [hsrc]
    refine ⟨fun n => (Φ.source_exhausts.isOpen n).preimage e.continuous,
      fun n x hx => Φ.source_exhausts.mono_step n hx, ?_⟩
    intro K hK
    obtain ⟨n, hn⟩ := Φ.source_subset (hK.image e.continuous)
    exact ⟨n, fun j hj x hx => hn j hj ⟨x, hx, rfl⟩⟩
  base_mem n := by
    change N.basepoint ∈ univ ∧ e N.basepoint ∈ Φ.source n
    exact ⟨mem_univ _, hp ▸ Φ.base_mem n⟩
  basepoint_map n := by
    change Φ.map n (e N.basepoint) = (X.obj (σ n)).basepoint
    rw [hp]; exact Φ.basepoint_map n

theorem pullback_limit_source_CX6 {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L N : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (e : N.M ≃ₘ⟮ThreeModel, ThreeModel⟯ L.M) (hp : e N.basepoint = L.basepoint) (n : ℕ) :
    (pullback_limit_maps_CX6 Φ e hp).source n = e ⁻¹' Φ.source n := by
  ext x
  change (x ∈ univ ∧ e x ∈ Φ.source n) ↔ e x ∈ Φ.source n
  simp

theorem exists_canonical_pullback_limit_CX6 {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L N : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) (C : MetricConvergenceData Φ)
    (hcan : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n)
    (e : N.M ≃ₘ⟮ThreeModel, ThreeModel⟯ L.M) (hp : e N.basepoint = L.basepoint)
    (hg : N.metric = Diffeomorph.pullbackMetricCross L.metric e) :
    ∃ C' : MetricConvergenceData (pullback_limit_maps_CX6 Φ e hp),
      ∀ n, C'.domain n = CanonicalMetricCompactness.canonicalSourceData (pullback_limit_maps_CX6 Φ e hp) n := by
  let Ψ := pullback_limit_maps_CX6 Φ e hp
  obtain ⟨C', hC', _⟩ := exists_metricConvergenceData_canonicalSourceData Ψ (by
    intro K hK p ε hε
    obtain ⟨n₀, hn₀⟩ := C.converges (e '' K) (hK.image e.continuous) p ε hε
    refine ⟨n₀, fun n hn => ?_⟩
    have hsrc : K ⊆ Ψ.source n := by
      rw [pullback_limit_source_CX6]
      exact fun x hx => (hn₀ n hn).1 ⟨x, hx, rfl⟩
    let U := metricSourceOpenSubset Ψ n
    have hU : e '' (U : Set N.M) ⊆ Φ.source n := by
      rintro _ ⟨x, hx, rfl⟩
      exact (show x ∈ e ⁻¹' Φ.source n from (pullback_limit_source_CX6 Φ e hp n) ▸ hx)
    let A := immersionInducedMetric (X.obj (σ n)).metric
      (pointedMaps_restrict_isSmoothEmbedding Φ e U n hU).isImmersion
    have hA : ∀ (x : U) (v w : TangentSpace ThreeModel x),
        A.inner x v w = (X.obj (σ n)).metric.inner (Ψ.map n x)
          (mfderiv ThreeModel ThreeModel (Ψ.map n) x v)
          (mfderiv ThreeModel ThreeModel (Ψ.map n) x w) := by
      intro x v w
      rw [immersionInducedMetric_inner]
      have hd : mfderiv ThreeModel ThreeModel (fun y : U => Φ.map n (e y)) x =
          mfderiv ThreeModel ThreeModel (Ψ.map n) (x : N.M) :=
        mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel) (Ψ.map n) U x
      rw [hd]
      rfl
    rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback Ψ n U (Subset.refl _) A K hsrc p hA, hg]
    rw [canonicalSource_fixedDomain_sup_eq Φ e U n hU]
    have himage : (Subtype.val : U → N.M) '' ((Subtype.val : U → N.M) ⁻¹' K) = K := by
      apply image_preimage_eq_of_subset
      intro x hx
      exact ⟨⟨x, hsrc hx⟩, rfl⟩
    rw [himage, ← hcan n]
    exact (hn₀ n hn).2)
  exact ⟨C', hC'⟩

def sequence_subseq_maps_CX6 {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) :
    PointedRiemannianConvergenceMaps (X.subseq σ) L id where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := Φ.basepoint_map

theorem exists_canonical_subseq_convergence_CX6
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) (C : MetricConvergenceData Φ)
    (hcan : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n) :
    ∃ C' : MetricConvergenceData (sequence_subseq_maps_CX6 Φ),
      ∀ n, C'.domain n = CanonicalMetricCompactness.canonicalSourceData (sequence_subseq_maps_CX6 Φ) n := by
  obtain ⟨C', hC', _⟩ := exists_metricConvergenceData_canonicalSourceData
    (sequence_subseq_maps_CX6 Φ) (by
      intro K hK p ε hε
      obtain ⟨n₀, hn₀⟩ := C.converges K hK p ε hε
      refine ⟨n₀, fun n hn => ?_⟩
      change (CanonicalMetricCompactness.canonicalSourceData Φ n).derivNormSupOn K p < ε
      rw [← hcan n]
      exact (hn₀ n hn).2)
  exact ⟨C', hC'⟩

end GC.LongTime.Ch12
