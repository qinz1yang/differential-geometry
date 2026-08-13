import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.NearIdentity

noncomputable section

open Filter Set Uniformity UniformSpace
open scoped Manifold ContDiff SetRel Topology

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [UniformSpace M] [ChartedSpace H M]
  [CompactSpace M] [T2Space M] [LocallyConnectedSpace M]
variable {ι : Type*}
structure HmfC1Data (F : ι → M → M) (l : Filter ι) where
  cover : M → Set M
  cover_nhds : ∀ x, cover x ∈ nhds x
  toId : TendstoUniformly F id l
  localInj : ∀ᶠ i in l, ∀ z, Set.InjOn (F i) (cover z)
  localDiff : ∀ᶠ i in l, IsLocalDiffeomorph I I ∞ (F i)

theorem HmfC1Data.bij {F : ι → M → M} {l : Filter ι}
    (h : HmfC1Data I F l) :
    ∀ᶠ i in l, Function.Bijective (F i) := by
  have hrange : ∀ᶠ i in l, IsClopen (Set.range (F i)) :=
    h.localDiff.mono fun _ hi ↦ localDiff_clopen I hi
  exact eventually_bijective F h.cover h.cover_nhds h.toId h.localInj hrange

theorem HmfC1Data.diffeo {F : ι → M → M} {l : Filter ι}
    (h : HmfC1Data I F l) :
    ∀ᶠ i in l, ∃ Φ : M ≃ₘ⟮I, I⟯ M, (Φ : M → M) = F i := by
  filter_upwards [h.localDiff, h.bij] with i hlocal hbij
  exact ⟨IsLocalDiffeomorph.diffeomorphOfBijective hlocal hbij, rfl⟩
end DifferentialGeometry.PDE.RicciFlow.Pullback

end
