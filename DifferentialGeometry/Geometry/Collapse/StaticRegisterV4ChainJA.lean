import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainNumbers
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJA

/-!
# Register V4's early choices give GAF01's (JA) and the CHOICE evidence of the chain

Lane C14-REG-CHAIN (review 66, D66-3: the CHOICE evidence of the SAME numeric choice travels with
the chain; never re-call GAF01's existence theorem, never choose small quantities after the
family). GAF01's (JA) (B:5705–5711) reads `Σ_j ≤ ε_j/10000` and `c₃ < min{c_adjust, 1/1000, 1/512}`.
The record of lane C14-GAF-C is `Gaf02RoughDataJA C cadj` (BASES' `Gaf02RoughData C` plus
`c 2 < cadj`, `c 2 < 1/1000`). Here every numeric clause is filled from the register's OWN stage
choice `st : ClosedStage (earlyDataSharedV4 K)` (PR04–PR09), chosen first in V4's order:

* `registerCadj_RGC K := closedC₃Bound (earlyDataSharedV4 K)`: the early target of `c₃`
  (`min{c_adjust, 1/1000, 1/512, 10⁻⁵, 1/(10⁵(P+1))}`, fixed before the stage), with
  `registerCadj_le_RGC` (`≤ 1/1000`, `≤ 10⁻⁵`, `≤ 1/(10⁵(P+1))`);
* `ClosedStage.c_two_bounds_RGC`: `c₃ < cadj`, `c₃ < 1/1000` (GAF06, GAF07, FDC02), `c₃ < 10⁻⁵`
  (EDP-E's height rows), and FDC02's `(1 + 2P_cgp)(5c₃/4) < 1/1000`;
* `earlyDataSharedV4_Ω_RGC`: GAF01's `Ω` of the register is BASES' `gafGraphOmega_BAS`;
* `ClosedStage.choice_RGC`: GAF01's (OS), the one-sheet budget (SN), the CGP06 rank margin,
  `Σ_j < ε_j/10000` and `0 ≤ c_w^{(j)}`, verbatim the non-row fields of `Gaf02RoughData`, at
  `(Ξ_j(Γ_j), Σ_j, e_j, c_w^{(j)} = stageCwAt_V4C st j)`;
* `ClosedStage.roughData_RGC`, `ClosedStage.roughDataJA_RGC`: on ANY chain at the register's stage
  data, the three rough-graph rows (TCP05, EGP06, SGP04 at `e_j`) complete the record
  `Gaf02RoughData C`, and with the register's `c₃` the (JA) record `Gaf02RoughDataJA C cadj`;
* `Gaf02ChainE.withRegisterJA_RGC` (consumer): a chain on the enhanced planes at the register's
  stage data is a `Gaf02ChainEJA … (registerCadj_RGC K)` (lane C14-GAF-C's `withJA_GAFC`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The register's early target of `c₃` (GAF01's `c_adjust` part of (JA), merged with EDP-E's and
FDC02's requests): `closedC₃Bound (earlyDataSharedV4 K)`, fixed before the stage choice. -/
def registerCadj_RGC (K : ℕ) : ℝ :=
  closedC₃Bound (earlyDataSharedV4 K)

/-- The early target is below `1/1000`, `10⁻⁵` and `1/(10⁵(P+1))`. -/
theorem registerCadj_le_RGC (K : ℕ) :
    registerCadj_RGC K ≤ 1 / 1000 ∧ registerCadj_RGC K ≤ 1 / 100000 ∧
      registerCadj_RGC K ≤ 1 / (10 ^ 5 * ((earlyDataSharedV4 K).P + 1)) := by
  unfold registerCadj_RGC closedC₃Bound
  refine ⟨(min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)), ?_, ?_⟩
  · refine (min_le_right _ _).trans ((min_le_left _ _).trans (le_of_eq ?_))
    norm_num
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- GAF01's `Ω` of the register's early data is BASES' `Ω`. -/
theorem earlyDataSharedV4_Ω_RGC (K : ℕ) : (earlyDataSharedV4 K).Ω = gafGraphOmega_BAS :=
  rfl

namespace ClosedStage

variable {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K))

/-- **The register's `c₃` meets every early request on it**: `c₃ < cadj`, `c₃ < 1/1000`
(GAF06, GAF07, FDC02), `c₃ < 10⁻⁵` (EDP-E) and FDC02's `(1 + 2P_cgp)(5c₃/4) < 1/1000`. -/
theorem c_two_bounds_RGC :
    st.c 2 < registerCadj_RGC K ∧ st.c 2 < 1 / 1000 ∧ st.c 2 < 1 / 100000 ∧
      (1 + 2 * cgpProfileBound) * (5 / 4 * st.c 2) < 1 / 1000 := by
  obtain ⟨h1, h2, h3⟩ := registerCadj_le_RGC K
  have hc : st.c 2 < registerCadj_RGC K := st.c₃_lt
  have hc0 := st.c_pos 2
  refine ⟨hc, hc.trans_le h1, hc.trans_le h2, ?_⟩
  have hP1 : 1 ≤ (earlyDataSharedV4 K).P := (earlyDataSharedV4 K).one_le_P
  have hPc : cgpProfileBound ≤ (earlyDataSharedV4 K).P :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hlt : st.c 2 * (10 ^ 5 * ((earlyDataSharedV4 K).P + 1)) < 1 := by
    have h := hc.trans_le h3
    rwa [lt_div_iff₀ (by positivity)] at h
  have hle : (1 + 2 * cgpProfileBound) * (5 / 4 * st.c 2) ≤
      (1 + 2 * (earlyDataSharedV4 K).P) * (5 / 4 * st.c 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  nlinarith

/-- **GAF01's CHOICE evidence at the register's stage values** (the non-row fields of
`Gaf02RoughData`, verbatim): (OS) `ε_j < 1/(1000(Ω+1))`, `e_j < Σ_j/1000`, `2e_j < 1/(48Ω)`; the
one-sheet budget (SN); the CGP06 rank margin; `Σ_j < ε_j/10000`; `0 ≤ c_w^{(j)}`. -/
theorem choice_RGC :
    (∀ j, (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧
      st.e j < st.Sig j / 1000 ∧ 2 * st.e j < 1 / (48 * gafGraphOmega_BAS)) ∧
    (∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * st.Sig j * Rr ≤ rx →
      (2 * st.e j + 25 / 12 * (1 + gafGraphOmega_BAS) * (earlyDataSharedV4 K).Ξ j (st.Γ j) *
          st.Sig j) * Rr < st.Sig j * Rr / 100 ∧
        st.Sig j * Rr / 100 < rx / 4 ∧
        (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / (2 * gafGraphOmega_BAS)) ∧
    (∀ j (ν : ℝ), ν ≤ st.e j → ν + st.e j ≤ 1 / (48 * gafGraphOmega_BAS)) ∧
    (∀ j, st.Sig j < (earlyDataSharedV4 K).Ξ j (st.Γ j) / 10000) ∧
    (∀ j, 0 ≤ stageCwAt_V4C st j) := by
  have hΩ : 1 ≤ gafGraphOmega_BAS := one_le_gafGraphOmega_BAS
  have hΞ : ∀ j, (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / (1000 * (gafGraphOmega_BAS + 1)) := by
    intro j
    have h := st.Ξ_lt j
    unfold closedAccuracyBound at h
    rw [earlyDataSharedV4_Ω_RGC] at h
    exact h.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have he : ∀ j, st.e j < 1 / (200 * gafGraphOmega_BAS) := by
    intro j
    have h := st.e_lt j
    unfold closedErrorBound at h
    rw [earlyDataSharedV4_Ω_RGC] at h
    exact h.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h2e : ∀ j, 2 * st.e j < 1 / (48 * gafGraphOmega_BAS) := by
    intro j
    have h := he j
    have hΩp : 0 < gafGraphOmega_BAS := by linarith
    have hep := st.e_pos j
    rw [lt_div_iff₀ (by positivity)] at h
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hΞ2 : ∀ j, (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / (2 * gafGraphOmega_BAS) := fun j =>
    (hΞ j).trans_le (one_div_le_one_div_of_le (by positivity) (by linarith))
  refine ⟨fun j => ⟨hΞ j, (st.stage_bounds_RGC j).2.2.2.2.2.2.2.2.2.2.2.1, h2e j⟩,
    fun j Rr rx hR hrx => ⟨?_, ?_, hΞ2 j⟩, fun j ν hν => by linarith [h2e j],
    fun j => (st.stage_bounds_RGC j).2.2.2.2.2.1, stageCwAt_nonneg_V4C st⟩
  · have hS := st.Sig_pos j
    have heS := (st.stage_bounds_RGC j).2.2.2.2.2.2.2.2.2.2.2.1
    have hΞp := (st.stage_bounds_RGC j).1
    have hΞΩ : (1 + gafGraphOmega_BAS) * (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / 1000 := by
      have h := hΞ j
      rw [lt_div_iff₀ (by positivity)] at h
      linarith
    have hsum : 2 * st.e j + 25 / 12 * (1 + gafGraphOmega_BAS) *
        (earlyDataSharedV4 K).Ξ j (st.Γ j) * st.Sig j < st.Sig j / 100 := by
      nlinarith
    have := mul_lt_mul_of_pos_right hsum hR
    linarith
  · have hS := st.Sig_pos j
    nlinarith

/-- **The rough-graph record at the register's stage data** (BASES' `Gaf02RoughData`): on any chain
at the register's stage values, the three rough-graph rows complete GAF01's CHOICE evidence. -/
theorem roughData_RGC {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain P.toLocalChartPackets K (fun j => (earlyDataSharedV4 K).Ξ j (st.Γ j)) st.Γ
      st.Sig st.e st.c (stageCwAt_V4C st))
    (hT05 : Tcp05OutV2 P (st.e 0)) (hE06 : Egp06OutV2 P.toLocalChartPacketsRVZ (st.e 1))
    (hS04 : Sgp04OutV2 P.toLocalChartPacketsRVZ (st.e 2)) : Gaf02RoughData C := by
  obtain ⟨hos, hone, hrank, hsig, hcw⟩ := st.choice_RGC
  exact ⟨hT05, hE06, hS04, hos, hone, hrank, hsig, hcw⟩

/-- **The (JA) record at the register's stage data** (lane C14-GAF-C's `Gaf02RoughDataJA`): the
rough-graph record together with `c₃ < cadj` and `c₃ < 1/1000` for the register's early target
`cadj = registerCadj_RGC K`. -/
theorem roughDataJA_RGC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain P.toLocalChartPackets K (fun j => (earlyDataSharedV4 K).Ξ j (st.Γ j)) st.Γ
      st.Sig st.e st.c (stageCwAt_V4C st))
    (hR : Gaf02RoughData C) : Gaf02RoughDataJA C (registerCadj_RGC K) :=
  { hR with
    c_lt_adj := st.c_two_bounds_RGC.1
    c_two_lt := st.c_two_bounds_RGC.2.1 }

end ClosedStage

namespace Gaf02ChainE

/-- **A chain on the enhanced planes at the register's stage data carries (JA)** (consumer): it is a
`Gaf02ChainEJA` for the register's early target `cadj = registerCadj_RGC K`, with the same
`Gaf02ChainE`. -/
def withRegisterJA_RGC {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K)) {X : Type}
    [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02ChainE P K (fun j => (earlyDataSharedV4 K).Ξ j (st.Γ j)) st.Γ st.Sig st.e st.c
      (stageCwAt_V4C st)) :
    Gaf02ChainEJA P K (fun j => (earlyDataSharedV4 K).Ξ j (st.Γ j)) st.Γ st.Sig st.e st.c
      (stageCwAt_V4C st) (registerCadj_RGC K) :=
  C.withJA_GAFC (st.roughDataJA_RGC C.toChain C.rough)

/-- `withRegisterJA_RGC` keeps the chain on the enhanced planes. -/
theorem withRegisterJA_toGaf02ChainE_RGC {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K))
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02ChainE P K (fun j => (earlyDataSharedV4 K).Ξ j (st.Γ j)) st.Γ st.Sig st.e st.c
      (stageCwAt_V4C st)) :
    (C.withRegisterJA_RGC st).toGaf02ChainE = C :=
  rfl

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
