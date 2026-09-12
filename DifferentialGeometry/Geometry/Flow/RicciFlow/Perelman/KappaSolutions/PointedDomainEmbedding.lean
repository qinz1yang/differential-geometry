import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Function Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedDomainLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedDomainLimitCharted : ChartedSpace H L.M := L.charted
private local instance pointedDomainLimitSmooth : IsManifold I ∞ L.M := L.smooth

private local instance pointedDomainApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance pointedDomainApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance pointedDomainApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

theorem pointedMaps_restrict_isSmoothEmbedding
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) :
    IsSmoothEmbedding J I ∞ (fun x : U => Phi.map k (e x)) := by
  have hlocal : IsLocalDiffeomorphOn J I ∞ (Phi.map k ∘ e) U := by
    intro x
    exact (e.isLocalDiffeomorph (x : S)).comp (K := I) (X.obj (subseq k)).M
      ((Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ (hU ⟨x, x.2, rfl⟩))
  have hrestricted : IsLocalDiffeomorph J I ∞ (fun x : U => Phi.map k (e x)) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U hlocal
  apply localDiffeomorph_isSmoothEmbedding_of_injective hrestricted
  intro x y hxy
  apply Subtype.ext
  apply e.injective
  exact (Phi.partialDiffeomorph k).toPartialEquiv.injOn
    (hU ⟨x, x.2, rfl⟩) (hU ⟨y, y.2, rfl⟩) hxy

def pointedDomainEmbedding
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) : C(U, (X.obj (subseq k)).M) where
  toFun x := Phi.map k (e x)
  continuous_toFun :=
    (pointedMaps_restrict_isSmoothEmbedding Phi e U k hU).isEmbedding.continuous

@[simp] theorem pointedDomainEmbedding_apply
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) (x : U) :
    pointedDomainEmbedding Phi e U k hU x = Phi.map k (e x) := rfl

theorem pointedMaps_eventually_fixedDomainEmbedding
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S)
    (K : Set S) (hK : IsCompact K) (hUK : (U : Set S) ⊆ K) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(U, (X.obj (subseq k)).M),
        IsSmoothEmbedding J I ∞ f ∧ ∀ x : U, f x = Phi.map k (e x) := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset (hK.image e.continuous)
  refine ⟨k0, fun k hk => ?_⟩
  have hU : e '' (U : Set S) ⊆ Phi.source k :=
    (image_mono hUK).trans (hk0 k hk)
  exact ⟨pointedDomainEmbedding Phi e U k hU,
    pointedMaps_restrict_isSmoothEmbedding Phi e U k hU, fun _ => rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
