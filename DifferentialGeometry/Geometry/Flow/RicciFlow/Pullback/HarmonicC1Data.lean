import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.NearIdentity

/-!
# C1 persistence data for a local-addition harmonic-map family

A rough HMF fixed point first produces self-maps.  To use the existing gauge
identities, the positive-time maps must be promoted to diffeomorphisms on one
common edge window.  The key uniformity is a fixed local-injectivity cover;
pointwise inverse-function neighborhoods chosen after fixing time are not
enough.

`HmfC1Data` packages exactly the output expected from the local-addition
`C1` estimate.  The two short theorems below reuse `NearIdentity` to obtain
eventual bijectivity and genuine diffeomorphisms.
-/

noncomputable section

open Filter Set Uniformity UniformSpace
open scoped Manifold ContDiff SetRel Topology

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [UniformSpace M] [ChartedSpace H M]
  [CompactSpace M] [T2Space M] [LocallyConnectedSpace M]
variable {ι : Type*}

/-- Uniform `C1` persistence data for a family of local-addition self-maps.

`localInj` uses one fixed neighborhood cover for all sufficiently late
parameters.  `localDiff` is the differential-invertibility output, while
`toId` is supplied by the vanishing local-addition section. -/
structure HmfC1Data (F : ι → M → M) (l : Filter ι) : Prop where
  cover : M → Set M
  cover_nhds : ∀ x, cover x ∈ 𝒩 x
  toId : TendstoUniformly F id l
  localInj : ∀ᶠ i in l, ∀ z, Set.InjOn (F i) (cover z)
  localDiff : ∀ᶠ i in l, IsLocalDiffeomorph I I ∞ (F i)

/-- The near-identity compactness argument promotes `HmfC1Data` to eventual
bijectivity. -/
theorem HmfC1Data.bij {F : ι → M → M} {l : Filter ι}
    (h : HmfC1Data I F l) :
    ∀ᶠ i in l, Function.Bijective (F i) := by
  have hrange : ∀ᶠ i in l, IsClopen (Set.range (F i)) :=
    h.localDiff.mono fun _ hi ↦ localDiff_clopen I hi
  exact eventually_bijective F h.cover h.cover_nhds h.toId h.localInj hrange

/-- Consequently every sufficiently late HMF slice is represented by a
genuine smooth self-diffeomorphism. -/
theorem HmfC1Data.diffeo {F : ι → M → M} {l : Filter ι}
    (h : HmfC1Data I F l) :
    ∀ᶠ i in l, ∃ Φ : M ≃ₘ⟮I, I⟯ M, (Φ : M → M) = F i := by
  filter_upwards [h.localDiff, h.bij] with i hlocal hbij
  exact ⟨hlocal.diffeomorphOfBijective hbij, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
