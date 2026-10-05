import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainEstimates
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge

/-!
# ZSP02 on the boundary family (lane B-BCG-ROWS): ZSP02 original radial / annulus estimates on the boundary family

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualZeroDomainEstimates.lean` by `build-logs/scratch/B-BCG-ROWSb/gen_zsp02.py` (engine B-PORT-A's
`portlib2.py`). Closed family → boundary family (`LocalPacketsOnB`, `ZeroModelFamilyOn`, complete
σ-compact carrier); every ported declaration `x` ↦ `x_BGR`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- FC01's zero block of `𝓔⁰` in coordinates: `⟨(J_k F)_vec, e₀⟩ = R ζ η` and `(J_k F)_mark = R ζ`. -/
theorem cgpGlobalMap_zeroBlock_GAF2_BGR
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (p : X) :
    ((cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius *
          Calculus.annularCutoff Calculus.cutoffProfile
            ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) *
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∧
      (cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))).snd =
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius *
          Calculus.annularCutoff Calculus.cutoffProfile
            ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) := by
  refine ⟨?_, rfl⟩
  change (((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius *
      Calculus.annularCutoff Calculus.cutoffProfile
        ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p)) •
      planeAxis ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) : ℝ²) 0 = _
  rw [PiLp.smul_apply, planeAxis_apply_zero_GAF2, smul_eq_mul]

/-- **ZSP02 (ZR)** on the actual zero blocks: for every map `f` with ZSP01's (ZE)
`|J_k(f p - F p)| < δ₀R_k` (`δ₀ < 1/1000`) and every point `p` of the carrier, an adjusted marker
`v ≥ .9R_k` forces `ζ_k(p) > .899`; with `u ≤ .4v` also `η_k(p) < .402`; with `u = .4v` also
`|η_k(p) − .4| < .002`. -/
theorem zsp02_original_radial_BGR
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) :
    ∀ p, 9 / 10 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
        (f p (.inr (.inr (.inr (.inl k))))).snd →
      899 / 1000 < Calculus.annularCutoff Calculus.cutoffProfile
          ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) ∧
        (((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 ≤
            4 / 10 * (f p (.inr (.inr (.inr (.inl k))))).snd →
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 402 / 1000) ∧
        (((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
            4 / 10 * (f p (.inr (.inr (.inr (.inl k))))).snd →
          |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p - 4 / 10| < 2 / 1000) := by
  intro p hv9
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hF1, hF2⟩ := cgpGlobalMap_zeroBlock_GAF2_BGR L Z k p
  obtain ⟨hc1, hc2⟩ := abs_block_components_le_GAF2 (f p (.inr (.inr (.inr (.inl k)))) -
    cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k)))))
  rw [WithLp.sub_fst, PiLp.sub_apply, hF1] at hc1
  rw [WithLp.sub_snd, hF2] at hc2
  exact zero_domain_radial_bounds hR hδ₀ (hc1.trans_lt (hZE p)) (hc2.trans_lt (hZE p)) hv9

/-- **ZSP02, the enclosing annulus** on the actual zero blocks: on `.3 ≤ η_k(p) < .381` the
original annular cutoff is one, and for every `f` with (ZE) the adjusted marker exceeds `.999R_k`
and the ratio `u/v` is below `.4`. -/
theorem zsp02_original_annulus_BGR
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) :
    ∀ p, 3 / 10 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p →
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p < 381 / 1000 →
      Calculus.annularCutoff Calculus.cutoffProfile
          ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) = 1 ∧
        999 / 1000 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
          (f p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((f p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 <
          4 / 10 * (f p (.inr (.inr (.inr (.inl k))))).snd := by
  intro p h3 h381
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hone : Calculus.annularCutoff Calculus.cutoffProfile
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) = 1 :=
    Calculus.annularCutoff_eq_one (fun _ ht => Calculus.cutoffProfile_eq_one ht)
      ⟨h3, by linarith⟩
  obtain ⟨hF1, hF2⟩ := cgpGlobalMap_zeroBlock_GAF2_BGR L Z k p
  obtain ⟨hc1, hc2⟩ := abs_block_components_le_GAF2 (f p (.inr (.inr (.inr (.inl k)))) -
    cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k)))))
  rw [WithLp.sub_fst, PiLp.sub_apply, hF1, hone, mul_one] at hc1
  rw [WithLp.sub_snd, hF2, hone, mul_one] at hc2
  exact ⟨hone, zero_domain_annulus_ratio_lt hR hδ₀ h381 (hc1.trans_lt (hZE p))
    (hc2.trans_lt (hZE p))⟩


end DifferentialGeometry.Geometry.Collapse
