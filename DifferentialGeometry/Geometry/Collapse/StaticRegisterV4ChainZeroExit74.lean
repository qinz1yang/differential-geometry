import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainZeroDomains74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExports74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsLink74
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZSelectedCores74

/-!
# Draft 74, G32: the closed-route zero exit `ZSP02SmoothExit74 S` without the cores as data

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. Z2 (`zeroDomainsOfExits74` on the zero exits of the
source's chain) with the selected cores PRODUCED by the LFR54 bridge
(`LocalChartPacketsC14Z.nonempty_selectedCore74`, G27b) instead of taken as data, and the whole
`ZeroLink_LND74` (ranges and boundaries `M.ψ(Z_k)`, `M.ψ(∂Z_k)` with `∂Z_k = frontier Z_k`,
(ZB) from `e₀ ≤ 1/1000`, the buffer ratio `u/v − 2/5`, the global ratio `F_k ∘ M.ψ⁻¹`):

* `ClosedChainEZRowsSource_RGC.nonempty_zsp02SmoothExit74 S hεr : Nonempty (ZSP02SmoothExit74 S)`;
* `ClosedChainEZRowsSource_RGC.zsp02SmoothExit74 S hεr : ZSP02SmoothExit74 S`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open GC.GraphManifold.Assembly.FC39P0 (pieceBoundary)

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The link's retained ratio `zeroUV74` is the buffer expression of ZSP02's exits (the chain's
`E` is the underlying chain's `E`). -/
theorem ClosedChainEZRowsSource_RGC.zeroUV74_eq_R74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} {R : ClosedRegisterV4 (earlyDataSharedV4 K) T}
    {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {M : ClosedModel W g} {δ εr Λz : ℝ} (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (k : S.ZeroIdx74) (z : M.X) : S.zeroUV74 k z =
      ((S.chain.toGaf02ChainE.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (S.chain.toGaf02ChainE.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 := by
  unfold ClosedChainEZRowsSource_RGC.zeroUV74 Gaf02ChainE.E
  rfl

/-- **The zero table from the exits** (abstract kernel): `Zr` with its pieces, boundaries, buffer
and ratio read back from Z0's definers `F` and buffers `N` is `ZeroLink_LND74`. -/
theorem zeroLink_of_exits74 {X : Type} [TopologicalSpace X] {W : CompactCarrier.{0}}
    (ψ : X ≃ W.Carrier) (Zr : ZeroDomains W) {ι : Type} (dom inner outer : ι → Set X) (uv : ι → X → ℝ)
    (σ : Fin Zr.count ≃ ι) (F : ι → X → ℝ) (N : ι → Set X)
    (hrange : ∀ i, range (Zr.piece i).map = ψ '' dom (σ i))
    (hbd : ∀ i, pieceBoundary (Zr.piece i) = ψ '' frontier (dom (σ i)))
    (hin : ∀ i, ψ '' inner (σ i) ⊆ interior (ψ '' dom (σ i)))
    (hout : ∀ i, ψ '' dom (σ i) ⊆ ψ '' outer (σ i))
    (hratio : ∀ i x, Zr.ratio i x = F (σ i) (ψ.symm x))
    (hnear : ∀ i, (Zr.near i : Set W.Carrier) = ψ '' N (σ i))
    (hN : ∀ k, IsOpen (N k)) (hfn : ∀ k, frontier (dom k) ⊆ N k)
    (huv : ∀ k z, z ∈ N k → F k z = uv k z) :
    ZeroLink_LND74 ψ Zr dom inner outer uv := by
  refine ⟨σ, fun i => ⟨hrange i, hbd i, ?_, ?_, ?_, F (σ i), N (σ i), hN _, hfn _, huv _, ?_⟩⟩
  · rw [hrange i]
    exact hin i
  · rw [hrange i]
    exact hout i
  · intro x hx
    rw [hnear i] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [hratio, ψ.symm_apply_apply]
    exact huv _ z hz
  · intro x
    exact hratio i x

/-- **The `ZSP02SmoothExit74` assembler**: the exits of the zero stratum written on the link's own
tables `zeroDom74 / zeroInner74 / zeroOuter74 / zeroUV74` give the exit. -/
def ClosedChainEZRowsSource_RGC.zsp02SmoothExit_of_exits74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} {R : ClosedRegisterV4 (earlyDataSharedV4 K) T}
    {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {M : ClosedModel W g} {δ εr Λz : ℝ} (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    {A : S.ZeroIdx74 → Set M.X} (Q : ∀ k, SelectedSmoothCore74.{0, 0} (A k))
    (Ψ : S.ZeroIdx74 → M.X ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.X) (N : S.ZeroIdx74 → Set M.X)
    (F : S.ZeroIdx74 → M.X → ℝ)
    (hΨ : ∀ k, Ψ k '' A k = S.zeroDom74 k)
    (hdisj : ∀ k k', k ≠ k' → Disjoint (S.zeroDom74 k) (S.zeroDom74 k'))
    (hN : ∀ k, IsOpen (N k)) (hFs : ∀ k, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (F k))
    (hreg : ∀ k x, F k x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (F k) x ≠ 0)
    (hle : ∀ k, {x | F k x ≤ 0} = S.zeroDom74 k)
    (hfr : ∀ k, {x | F k x = 0} = frontier (S.zeroDom74 k))
    (hzn : ∀ k, {x | F k x = 0} ⊆ N k) (hFeq : ∀ k, ∀ z ∈ N k, F k z = S.zeroUV74 k z)
    (hin : ∀ k, S.zeroInner74 k ⊆ interior (S.zeroDom74 k))
    (hout : ∀ k, S.zeroDom74 k ⊆ S.zeroOuter74 k) : ZSP02SmoothExit74 S := by
  refine ⟨zeroDomainsOfExits74 (ι := S.ZeroIdx74) M.ψ M.boundary_empty_R74 Q Ψ S.zeroDom74 N F
    hΨ hdisj hN hFs hreg hle hfr hzn, ?_⟩
  refine zeroLink_of_exits74 M.ψ.toEquiv _ S.zeroDom74 S.zeroInner74 S.zeroOuter74 S.zeroUV74
    (by exact idx74 _) F N ?_ ?_ ?_ ?_ ?_ ?_ hN ?_ hFeq
  · exact fun i => zeroDomainsOfExits74_range M.ψ M.boundary_empty_R74 Q Ψ _ N F hΨ hdisj hN hFs
      hreg hle hfr hzn i
  · intro i
    refine (zeroDomainsOfExits74 (ι := S.ZeroIdx74) M.ψ M.boundary_empty_R74 Q Ψ S.zeroDom74 N F
      hΨ hdisj hN hFs hreg hle hfr hzn).boundary_eq i |>.trans ?_
    exact (preimage_symm_R74 M.ψ (F (idx74 _ i)) {0}).trans
      (congrArg (fun B => M.ψ '' B) (hfr (idx74 _ i)))
  · intro i
    exact (image_mono (hin _)).trans
      (M.ψ.toHomeomorph.image_interior (S.zeroDom74 (idx74 _ i))).subset
  · exact fun i => image_mono (hout _)
  · exact fun i x => rfl
  · exact fun i => rfl
  · intro k
    rw [← hfr k]
    exact hzn k

/-- **The closed-route zero exit** (clause (a) of the FC39 gate): ZSP02's zero domains carried by
`M.ψ`, the cores from LFR54, the full `ZeroLink`. -/
theorem ClosedChainEZRowsSource_RGC.nonempty_zsp02SmoothExit74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} {R : ClosedRegisterV4 (earlyDataSharedV4 K) T}
    {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {M : ClosedModel W g} {δ εr Λz : ℝ} (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (hεr : εr < 1 / 2) : Nonempty (ZSP02SmoothExit74 S) := by
  have he : R.later.err.co.e₀ ≤ 1 / 1000 := (R.later.e₀_lt.trans_le (min_le_left _ _)).le
  let Q : ∀ k : S.ZeroIdx74, SelectedSmoothCore74.{0, 0}
      {z | (S.F.family.toLocalChartPacketsC14.zero.zero k.1
        ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} := fun k =>
    (S.F.family.nonempty_selectedCore74 ((Set.Finite.mem_toFinset _).mp k.2)
      ⟨by norm_num, by norm_num⟩).some
  obtain ⟨Ψ, F, N, hΨ, hdisj, hN, hFs, hreg, hle, hfr, hzn, hzf, hFN, hFeq⟩ :=
    S.chain.toGaf02ChainE.zero_exits_data74 hεr
  exact ⟨S.zsp02SmoothExit_of_exits74 Q Ψ N F hΨ hdisj hN hFs hreg hle hfr hzn
    (fun k z hz => (hFeq k z hz).trans (S.zeroUV74_eq_R74 k z).symm)
    (fun k => (S.chain.toGaf02ChainE.zsp02_ZB_ZSP35 hεr he k).1)
    (fun k => (S.chain.toGaf02ChainE.zsp02_ZB_ZSP35 hεr he k).2)⟩

/-- **The closed-route zero exit `ZSP02SmoothExit74 S`** as a term. -/
def ClosedChainEZRowsSource_RGC.zsp02SmoothExit74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} {R : ClosedRegisterV4 (earlyDataSharedV4 K) T}
    {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {M : ClosedModel W g} {δ εr Λz : ℝ} (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (hεr : εr < 1 / 2) : ZSP02SmoothExit74 S :=
  (S.nonempty_zsp02SmoothExit74 hεr).some

end DifferentialGeometry.Geometry.Collapse
