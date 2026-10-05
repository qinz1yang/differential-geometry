import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ

/-!
# GAF01's full (JB) and (SE) certificates of the register's ONE early choice

Lane C14-REG-CHAIN, G10 (review 71 D71-10 / D71-13: "(JA) is not a pass for all later budgets; the
full (JB) (`e_j < 1/(200Ω)`, `Σ_j < Γ_j³/(100C_j)`, …) is not stored on the chain — a consumer that
needs it asks for the certificate of the SAME early choice (register side), never a re-choice";
BASES' row entry is `CE : Gaf02ChainEJA` plus the (JB)/(SE) certificates still needed, on the same
`CE`). The register keeps them as fields of its stage `R.stage : ClosedStage (earlyDataSharedV4 K)`
(PR04–PR09); here they are exported in the chain's parameter form (`ε_j = Ξ_j(Γ_j)`, `Σ_j`, `e_j`,
`c_j`, BASES' `Ω = gafGraphOmega_BAS`, graph moduli `gafGraphConst`):

* `ClosedStage.jb_RGC`: (JB) verbatim — `ε_j < min{1/10, α(c_j), 1/(1000(Ω+1))}`,
  `Σ_j < min{1/2, ε_j/10⁴, Γ_j/200, Γ_j³/(100C_j)}`, `e_j < min{1/100, Γ_jΣ_j/100, Σ_j/1000,
  1/(200Ω)}`, `0 < Γ_j ≤ c_j/16`;
* `ClosedStage.se_RGC`: (SE)'s early part `c₃ < min{10⁻⁵, 1/(10⁵(P₀+1))}` with
  `P₀ = max{1, P_cgp, P_sgp, P_zero}` (`earlyDataSharedV4_P_RGC`), from the register's early target
  `registerCadj_RGC K`; the late part `C_ρΔΛ < 10⁻⁶` is the register field `regScale_Cρ`;
* consumer `ClosedChainEZRowsSource_RGC.coframe_bound_RGC`: on the rows' source (C14Z, D71-3), the
  coframe kernel's `8e_j(1 + Ω) ≤ 1` for the chain's own `e_j` (D71-10: the stored bound suffices
  there; here it comes from (JB)'s `e_j < 1/(200Ω)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- `P₀` of the register's early data: the maximum of `1` and the three profile bounds. -/
theorem earlyDataSharedV4_P_RGC (K : ℕ) :
    (earlyDataSharedV4 K).P = max 1 (max cgpProfileBound (max sgpProfileBound zeroProfileBound)) :=
  rfl

namespace ClosedStage

variable {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K))

/-- **GAF01's full (JB) at the register's stage values** (the certificate of the same early
choice, in the chain's parameter form). -/
theorem jb_RGC (j : Fin 3) :
    (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / 10 ∧
      (earlyDataSharedV4 K).Ξ j (st.Γ j) < (earlyDataSharedV4 K).α (st.c j) ∧
      (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧
      st.Sig j < 1 / 2 ∧ st.Sig j < (earlyDataSharedV4 K).Ξ j (st.Γ j) / 10000 ∧
      st.Sig j < st.Γ j / 200 ∧ st.Sig j < st.Γ j ^ 3 / (100 * gafGraphConst j) ∧
      st.e j < 1 / 100 ∧ st.e j < st.Γ j * st.Sig j / 100 ∧ st.e j < st.Sig j / 1000 ∧
      st.e j < 1 / (200 * gafGraphOmega_BAS) ∧ 0 < st.Γ j ∧ st.Γ j ≤ st.c j / 16 := by
  have hΞ := st.Ξ_lt j
  have hS := st.Sig_lt j
  have he := st.e_lt j
  unfold closedAccuracyBound at hΞ
  unfold closedSigmaBound at hS
  unfold closedErrorBound at he
  rw [earlyDataSharedV4_Ω_RGC] at hΞ he
  simp only [lt_min_iff] at hΞ hS he
  exact ⟨hΞ.1, hΞ.2.1, hΞ.2.2, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, he.1, he.2.1, he.2.2.1, he.2.2.2,
    st.Γ_pos j, st.Γ_le j⟩

/-- **(SE)'s early part at the register**: `c₃ < 10⁻⁵` and `c₃ < 1/(10⁵(P₀+1))`. -/
theorem se_RGC :
    st.c 2 < 1 / 100000 ∧ st.c 2 < 1 / (10 ^ 5 * ((earlyDataSharedV4 K).P + 1)) := by
  obtain ⟨-, h2, h3⟩ := registerCadj_le_RGC K
  have hc : st.c 2 < registerCadj_RGC K := st.c₃_lt
  exact ⟨hc.trans_le h2, hc.trans_le h3⟩

end ClosedStage

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The coframe kernel's bound for the rows' chain** (consumer): `8e_j(1 + Ω) ≤ 1` for the stage
errors `e_j = R.stage.e j` that index the source's chain, from the register's (JB) certificate
`e_j < 1/(200Ω)`, next to the chain's OWN stored rough-data bound `2e_j < 1/(48Ω)` (D71-10: both
on the same early choice). -/
theorem coframe_bound_RGC (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (j : Fin 3) :
    8 * R.stage.e j * (1 + gafGraphOmega_BAS) ≤ 1 ∧
      2 * R.stage.e j < 1 / (48 * gafGraphOmega_BAS) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, he, -, -⟩ := R.stage.jb_RGC j
  have hΩ : 1 ≤ gafGraphOmega_BAS := one_le_gafGraphOmega_BAS
  have hep := R.stage.e_pos j
  rw [lt_div_iff₀ (by positivity)] at he
  exact ⟨by nlinarith, (S.chain.rough.os j).2.2⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
