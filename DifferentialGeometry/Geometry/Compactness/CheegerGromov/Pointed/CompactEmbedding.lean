import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Separation.Hausdorff
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedCompactLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedCompactLimitCharted : ChartedSpace H L.M := L.charted
private local instance pointedCompactApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance pointedCompactApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance pointedCompactApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

theorem pointedMaps_eventually_compactEmbedding
    {S : Type*} [TopologicalSpace S] [CompactSpace S]
    (e : S → L.M) (he : IsEmbedding e) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(S, (X.obj (subseq k)).M),
        IsClosedEmbedding f ∧ ∀ x : S, f x = Phi.map k (e x) := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset (isCompact_range he.continuous)
  refine ⟨k0, fun k hk => ?_⟩
  have hsource : ∀ x : S, e x ∈ Phi.source k :=
    fun x => hk0 k hk (Set.mem_range_self x)
  have hcontinuous : Continuous (fun x : S => Phi.map k (e x)) := by
    apply continuousOn_univ.mp
    exact (Phi.partialDiffeomorph k).toOpenPartialHomeomorph.continuousOn.comp
      he.continuous.continuousOn (fun x _ => hsource x)
  have hinjective : Function.Injective (fun x : S => Phi.map k (e x)) := by
    intro x y hxy
    exact he.injective ((Phi.partialDiffeomorph k).toPartialEquiv.injOn
      (hsource x) (hsource y) hxy)
  exact ⟨⟨_, hcontinuous⟩, hcontinuous.isClosedEmbedding hinjective, fun _ => rfl⟩

open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S] [CompactSpace S]

theorem pointedMaps_eventually_compactSmoothEmbedding
    (e : S → L.M) (he : Manifold.IsSmoothEmbedding J I ∞ e) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(S, (X.obj (subseq k)).M),
        Manifold.IsSmoothEmbedding J I ∞ f ∧
          _root_.Topology.IsClosedEmbedding f ∧ ∀ x : S, f x = Phi.map k (e x) := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset (isCompact_range he.isEmbedding.continuous)
  refine ⟨k0, fun k hk => ?_⟩
  have hsource : Set.range e ⊆ (Phi.partialDiffeomorph k).source := hk0 k hk
  let : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  have hs : Manifold.IsSmoothEmbedding J I ∞ (Phi.map k ∘ e) :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph
      (Phi.partialDiffeomorph k) he hsource
  let f : C(S, (X.obj (subseq k)).M) := ⟨Phi.map k ∘ e, hs.isEmbedding.continuous⟩
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  exact ⟨f, hs, hs.isEmbedding.continuous.isClosedEmbedding hs.isEmbedding.injective,
    fun _ => rfl⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
