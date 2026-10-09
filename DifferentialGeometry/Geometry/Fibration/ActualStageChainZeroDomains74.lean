import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroRatio
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomains
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ZeroDomainsOfExits74

/-!
# Draft 74, package Z2 on the chain: ZSP02's zero exits + Z0's global ratio + Z1's solid cores
# give `ZeroDomains W`

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G28 (chain binding). For a chain `Ĉ : Gaf02ChainE` over the
original source `X` and `εr < 1/2`, with ZSP02's index set `k : P.zero.finite_centres.toFinset`:

* `Gaf02ChainE.zero_exits_data74`: the exits of the zero stratum in the format of the assembler
  `zeroDomainsOfExits74` — ZSP02's ambient diffeomorphisms `Ψ k` with `Ψ k {η_k ≤ 2/5} = Z_k`,
  pairwise disjointness of the `Z_k`, and Z0's definers `F k` with open buffers `N k ⊇ (ZF)`:
  `{F k ≤ 0} = Z_k`, `{F k = 0} = frontier Z_k`, smooth, regular on the zero level, and the EXACT
  buffer normalization `F k = u_k/v_k − 2/5` on `N k` (D74-7: not `rfl`; it is Z0's output);
* **`Gaf02ChainE.zeroDomains_of_actual_zero_exit74`** (Z2): with the selected solid cores `Q k`
  of the sublevels `{η_k ≤ 2/5}` (Z1 data) and a diffeomorphism `φ` of `X` onto a member `W` with
  empty boundary (`M.ψ`), there is a `ZeroDomains W` whose pieces are the `φ`-images of the
  zero domains `Z_k` (range and model boundary), whose ratios are Z0's definers pulled back by
  `φ⁻¹` with the exact normalization on the buffers `φ(N k)`, and whose models are the selected
  cores' branches.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open GC.GraphManifold.Assembly.FC39P0 (pieceBoundary)

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The zero exits in the assembler's format** (ZSP02 + Z0): for a chain `Ĉ` with `εr < 1/2`,
ambient diffeomorphisms `Ψ k` carrying the SAME original sublevel `{η_k ≤ 2/5}` onto `Z_k`,
pairwise disjoint domains, and Z0's global definers `F k` with buffers `N k` (exact normalization
`F k = u_k/v_k − 2/5` on `N k`). -/
theorem Gaf02ChainE.zero_exits_data74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) :
    ∃ (Ψ : P.zero.finite_centres.toFinset → X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X)
      (F : P.zero.finite_centres.toFinset → X → ℝ) (N : P.zero.finite_centres.toFinset → Set X),
      (∀ k, Ψ k '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (∀ k k', k ≠ k' → Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E)) ∧
      (∀ k, IsOpen (N k)) ∧ (∀ k, ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F k)) ∧
      (∀ k x, F k x = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F k) x ≠ 0) ∧
      (∀ k, {x | F k x ≤ 0} = zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (∀ k, {x | F k x = 0} = frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) ∧
      (∀ k, {x | F k x = 0} ⊆ N k) ∧
      (∀ k, {x | F k x = 0} = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (∀ k, zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆ N k) ∧
      (∀ k, ∀ z ∈ N k, F k z = ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) := by
  have hd : ∀ k : P.zero.finite_centres.toFinset, ∃ Ψ : X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
      Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E := fun k => by
    obtain ⟨-, ⟨Ψ, h1, -⟩, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
    exact ⟨Ψ, h1⟩
  have hf : ∀ k : P.zero.finite_centres.toFinset, ∃ (F : X → ℝ) (N : Set X), IsOpen N ∧
      zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆ N ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ z ∈ N, F z = ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) ∧
      {z | F z ≤ 0} = zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      {z | F z = 0} = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      ∀ x, F x = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ≠ 0 := fun k => by
    obtain ⟨F, N, hN, hFN, -, hFs, hFeq, hle, hz, hreg⟩ := Ĉ.zsp02_global_ratio_ZSP35 hεr k
    exact ⟨F, N, hN, hFN, hFs, hFeq, hle, hz, hreg⟩
  choose Ψ hΨ using hd
  choose F N hN hFN hFs hFeq hle hz hreg using hf
  refine ⟨Ψ, F, N, hΨ, fun k k' hkk => Ĉ.zsp02_disjoint_ZSP35 hεr hkk, hN, hFs, hreg, hle,
    fun k => ?_, fun k => ?_, hz, hFN, hFeq⟩
  · rw [hz k]
    exact (Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1.symm
  · rw [hz k]
    exact hFN k

universe u

/-- **Z2, `zeroDomains_of_actual_zero_exit74`** (draft 74 §3.1, D74-7 / D74-8): ZSP02's zero
domains, Z0's exact global ratio and Z1's selected solid cores assemble to `ZeroDomains W`. The
pieces are the `φ`-images of the solid cores (range `φ(Z_k)`, model boundary `φ(∂Z_k)`), the ratios
are Z0's definers pulled back by `φ⁻¹` with the EXACT normalization `u_k/v_k − 2/5` on the buffers
`φ(N k)` (an open neighbourhood of the whole face), and the models are the branches of the
selected cores (the closed branch is a `ClosedZeroPiece`). -/
theorem Gaf02ChainE.zeroDomains_of_actual_zero_exit74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {W : CompactCarrier.{u}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅)
    (Q : ∀ k : P.zero.finite_centres.toFinset, SelectedSmoothCore74.{u, 0}
      {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5}) :
    ∃ (D : ZeroDomains W) (κ : Fin D.count ≃ P.zero.finite_centres.toFinset),
      D.count = Fintype.card P.zero.finite_centres.toFinset ∧ ∀ j : Fin D.count,
        range (D.piece j).map = φ '' zspDomain_ZSP35 P.toLocalChartFamily P.zero (κ j) Ĉ.E ∧
        pieceBoundary (D.piece j) = φ '' zspFace_ZSP35 P.toLocalChartFamily P.zero (κ j) Ĉ.E ∧
        (∃ N : Set X, IsOpen N ∧ zspFace_ZSP35 P.toLocalChartFamily P.zero (κ j) Ĉ.E ⊆ N ∧
          (D.near j : Set W.Carrier) = φ '' N ∧
          ∀ z ∈ N, D.ratio j (φ z) =
            ((Ĉ.E z (.inr (.inr (.inr (.inl (κ j)))))).fst : ℝ²) 0 /
              (Ĉ.E z (.inr (.inr (.inr (.inl (κ j)))))).snd - 2 / 5) ∧
        ((D.model j).isRight = true ↔ (Q (κ j)).IsClosed) := by
  obtain ⟨Ψ, F, N, hΨ, hdisj, hN, hFs, hreg, hle, hfr, hzn, hzf, hFN, hFeq⟩ :=
    Ĉ.zero_exits_data74 hεr
  refine ⟨zeroDomainsOfExits74 (ι := P.zero.finite_centres.toFinset) φ hW Q Ψ
    (fun k => zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) N F hΨ hdisj hN hFs hreg hle hfr
    hzn, idx74 _, rfl, fun j => ⟨?_, ?_, ⟨N (idx74 _ j), hN _, hFN _, rfl, fun z hz => ?_⟩, ?_⟩⟩
  · exact zeroDomainsOfExits74_range φ hW Q Ψ _ N F hΨ hdisj hN hFs hreg hle hfr hzn j
  · refine ((zeroDomainsOfExits74 φ hW Q Ψ _ N F hΨ hdisj hN hFs hreg hle hfr
      hzn).boundary_eq j).trans ?_
    exact (preimage_symm_R74 φ (F (idx74 _ j)) {0}).trans
      (congrArg (fun A => φ '' A) (hzf (idx74 _ j)))
  · change F (idx74 _ j) (φ.symm (φ z)) = _
    rw [φ.symm_apply_apply]
    exact hFeq _ z hz
  · exact SelectedSmoothCore74.model_isRight_iff (Q := Q (idx74 _ j)) _ _

end DifferentialGeometry.Geometry.Collapse
