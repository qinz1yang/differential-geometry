import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence
import DifferentialGeometry.Topology.Manifold.OrientationExhaustion
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.Manifold

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_preserves_tangentOrientation
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f)
    (hconn : ∀ i, IsPreconnected (F.partialDiffeomorph i).source)
    (o : ∀ i, TangentOrientationSection (X.obj i).M) :
    ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ O : TangentOrientationSection P.M,
      ∀ i y, y ∈ ((F.compSubseq σ hσ).partialDiffeomorph i).source →
        ∃ hf : Function.Bijective
            (mfderiv I3 I3 ((F.compSubseq σ hσ).partialDiffeomorph i) y),
          PreservesTangentOrientationAt O (o ((f ∘ σ) i))
            ((F.compSubseq σ hσ).partialDiffeomorph i) y hf := by
  let U : ℕ → TopologicalSpace.Opens P.M := fun i =>
    ⟨(F.partialDiffeomorph i).source, (F.partialDiffeomorph i).open_source⟩
  have hU : Monotone U := F.source_exhausts.monotone
  have hcover : ∀ x : P.M, ∃ i, x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := F.source_exhausts.subset {x} isCompact_singleton
    exact ⟨i, hi i le_rfl (Set.mem_singleton x)⟩
  have hmain (n : ℕ) (hn : Module.finrank ℝ ThreeSpace = n)
      (oN : ∀ i, ManifoldOrientation I3 (X.obj (f i)).M n) :
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ O : ManifoldOrientation I3 P.M n,
        ∀ i y, y ∈ (F.partialDiffeomorph (σ i)).source →
          ∃ hf : Function.Bijective (mfderiv I3 I3 (F.partialDiffeomorph (σ i)) y),
            Orientation.map (Fin n)
              (LinearEquiv.ofBijective
                (mfderiv I3 I3 (F.partialDiffeomorph (σ i)) y).toLinearMap hf)
              (O.orientation y) = (oN (σ i)).orientation (F.partialDiffeomorph (σ i) y) := by
    cases hn
    let oS := fun i => smoothOrientationOfManifoldOrientation I3 (oN i)
    obtain ⟨σ, hσ, O, hO⟩ :=
      exists_subsequence_preserves_smoothOrientation_on_monotone_open_cover I3
        U hU hcover hconn P.basepoint F.base_mem F.partialDiffeomorph
        (fun _ => Set.Subset.rfl) oS
    obtain ⟨O', hO'⟩ := exists_manifoldOrientation_eq_of_smoothOrientation I3 O
    refine ⟨σ, hσ, O', fun i y hy => ?_⟩
    rw [hO']
    exact hO i y hy
  let oN : ∀ i, ManifoldOrientation I3 (X.obj (f i)).M 3 := fun i =>
    { dimension_eq := by simp [ThreeSpace]
      orientation := (o (f i)).orientation
      locally_constant := (o (f i)).locally_constant }
  obtain ⟨σ, hσ, O, hO⟩ := hmain 3 (by simp [ThreeSpace]) oN
  exact ⟨σ, hσ, ⟨O.orientation, O.locally_constant⟩, hO⟩

theorem exists_oriented_subsequence_with_canonical_domains
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (hf : StrictMono f) (F : PointedRiemannianConvergenceMaps X P f)
    (C : MetricConvergenceData F)
    (hC : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    (hcapture : MetricSourceCapture F)
    (hcompact : ∀ i, IsCompact (closure (F.partialDiffeomorph i).source))
    (hconn : ∀ i, IsConnected (F.partialDiffeomorph i).source)
    (hnested : ∀ i,
      closure (F.partialDiffeomorph i).source ⊆ (F.partialDiffeomorph (i + 1)).source)
    (o : ∀ i, TangentOrientationSection (X.obj i).M) :
    ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ O : TangentOrientationSection P.M,
      StrictMono (f ∘ σ) ∧
      (∀ k, (C.compSubseq σ hσ).domain k =
        CanonicalMetricCompactness.canonicalSourceData (F.compSubseq σ hσ) k) ∧
      MetricSourceCapture (F.compSubseq σ hσ) ∧
      (∀ i, IsCompact (closure ((F.compSubseq σ hσ).partialDiffeomorph i).source)) ∧
      (∀ i, IsConnected ((F.compSubseq σ hσ).partialDiffeomorph i).source) ∧
      (∀ i, closure ((F.compSubseq σ hσ).partialDiffeomorph i).source ⊆
        ((F.compSubseq σ hσ).partialDiffeomorph (i + 1)).source) ∧
      ∀ i y, y ∈ ((F.compSubseq σ hσ).partialDiffeomorph i).source →
        ∃ hg : Function.Bijective
            (mfderiv I3 I3 ((F.compSubseq σ hσ).partialDiffeomorph i) y),
          PreservesTangentOrientationAt O (o ((f ∘ σ) i))
            ((F.compSubseq σ hσ).partialDiffeomorph i) y hg := by
  obtain ⟨σ, hσ, O, hO⟩ :=
    exists_subsequence_preserves_tangentOrientation F (fun i => (hconn i).isPreconnected) o
  refine ⟨σ, hσ, O, hf.comp hσ, ?_, ?_, fun i => hcompact (σ i),
    fun i => hconn (σ i), ?_, hO⟩
  · intro k
    change MetricSourceData.compSubseq σ hσ k (C.domain (σ k)) = _
    rw [hC (σ k)]
    rfl
  · intro r hr
    exact hσ.tendsto_atTop.eventually (hcapture r hr)
  · intro i
    exact (hnested (σ i)).trans
      (F.source_exhausts.subset_of_le (hσ (Nat.lt_succ_self i)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
