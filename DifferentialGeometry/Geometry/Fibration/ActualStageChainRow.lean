import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Fibration.ActualStageMeanSharedRowApplications
import DifferentialGeometry.Geometry.Fibration.ActualCfs15StageOutputMean
import DifferentialGeometry.Geometry.Fibration.ActualStageFirstScale
import DifferentialGeometry.Geometry.Fibration.ActualStageEdgeTestPP
import DifferentialGeometry.Geometry.Fibration.ActualStageNearApplications
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphApprox
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraph

/-!
# GAF02 CORE: the chain object is produced on the final family (`gaf02_chain_row_GAF8`)

Blueprint `master207B.tex`, GAF02 (B:5797); draft 59 §3 (D59-4). The producer of `Gaf02Chain`:
GAF01's shared moduli `θ, Ξ` at the jet order `Kj` and its CHOICE `c, Γ, Σ, e` (graph moduli
`C = (C_TCP, C_EGP, C_SGP)`), FC27's three stage tests at `(Γ_j, Σ_j, e_j)` (first with the scale
clause, edge, slim; all with (PP)) and, per stage, CFS15's native stage output
`Cfs15StageOutput` (`cfs15StageOutput_of_modulusAtV2_C15`, one kernel call, weight constant
`c_w`) on the stage cloud with the test's plane in its plane slot. Ordered quantifiers: the moduli
and the choice first, the tests' thresholds next, then every packet of the final family with the
tests' hypotheses (verbatim union) and every selection of original preimages.

* `sgpGraphBound_pos_GAF8`: `0 < C_SGP`.
* `gaf02_chain_row_GAF8 Kj`: the producer, `∃ C : Gaf02Chain …, C.sel = sel`.
* `gaf02_core_of_chain_GAF8` (consumer): the present GAF02 CORE conjunct form, read off `C.core`:
  `E` smooth, `‖E − 𝓔⁰‖ < c₃ρ`, the derivative budget, (AM0) on `[𝓔⁰ p, E p]`, `s = ℓ_ρ(E) > 0`.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF8r {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF8r {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF8r {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The slim graph modulus is positive. -/
theorem sgpGraphBound_pos_GAF8 : 0 < sgpGraphBound := by
  have h1 : 0 < max sgpProfileBound zeroProfileBound + 1 := by
    linarith [le_max_left sgpProfileBound zeroProfileBound, sgpProfileBound_spec.1]
  have h2 : 0 < egp02SlimCount + 2 := by linarith [egp02SlimCount_pos_SGP4]
  rw [sgpGraphBound]
  exact mul_pos (mul_pos (by norm_num) h2) h1

/-- **CFS15's native stage output on the actual stage clouds** (D59-3 at the GAF01 moduli): for a
stage `st`, `0 < Γ` with CFS15's modulus at `(k_st, Kj, 5/3, Ξ, Γ)` and the interior condition,
there
is a weight constant `c_w ≥ 0` such that on every packet of the final family (CFS14's inputs), for
every selection of original preimages over `S̃_st`, `0 < Σ` with `128Ξ(Γ)⁻¹Σ ≤ 1/5` and planes of
the
stage dimension passing the (CS) test at quality `Γ` and radius `Σρ ∘ sel`, there is a
`Cfs15StageOutput` on `S_st ⊆ S̃_st` with radius `Σρ ∘ sel` and these planes in its plane slot. -/
theorem gafStage_output_GAF8 {Kj : ℕ} {Ξ : ℝ → ℝ} {Γ : ℝ} (st : Fin 3) (hΓ : 0 < Γ)
    (hat : Cfs15ModulusAtV2 (gafStageDim st) Kj (5 / 3) Ξ Γ)
    (hint : Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
        {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
        {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
        {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 → 1000000 * Δ * Λ < 1 / 100000 →
        ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st, cgpProjMap P.toLocalChartFamily
            P.zero (gafStageTags P.toLocalChartFamily P.zero st) (sel x) = x) →
        ∀ sg : ℝ, 0 < sg → 128 * (Ξ Γ)⁻¹ * sg ≤ 1 / 5 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, Module.finrank ℝ (plane x) = gafStageDim
            st) →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩ ball x (sg * ρ (sel x)
              / Γ))
            ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily
                P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) →
        Nonempty (Cfs15StageOutput (gafStageDim st) Kj (Ξ Γ) cw (gafCloud P.toLocalChartFamily
            P.zero st)
          (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)) plane) := by
  have hε : 0 < Ξ Γ := by
    obtain ⟨⟨m, hm⟩, -⟩ := hat
    rw [hm]
    positivity
  obtain ⟨cw, hcw, hout⟩ := cfs15StageOutput_of_modulusAtV2_C15 hΓ hat hint
  refine ⟨cw, hcw, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hmo plane hdim hcloud
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hε hsg
    hmo
  have hR := Classical.choose_spec (Classical.choose_spec hin.2.2.1)
  exact hout (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (gafCloud
      P.toLocalChartFamily P.zero st)
    (gafCloudEnlarged P.toLocalChartFamily P.zero st) hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane
        hdim _ _ hR.1
    hR.2.1 hR.2.2 hin.2.2.2 hcloud

/-- **GAF01's moduli and CHOICE in the chain's form**: GAF01's shared moduli `θ, Ξ` at jet order
`Kj` and a CHOICE `c, Γ, Σ, e` (graph moduli `C_TCP, C_EGP, C_SGP`, `c₃ < c_adj`) with the stage
tests' parameter ranges (`Γ_j < 1`, `Σ_j < Γ_j/200`, `Σ_j < Γ_j³/(100C_j)`,
`e_j < min(1/100, Γ_jΣ_j/100,
Σ_j/1000)`), CFS15's modulus and interior condition at `Γ_j`, and the kernel's numbers
(`128Ξ⁻¹Σ ≤ 1/5`, `(5/3)ΞΣ < c₁`, the derivative budgets, `c_j ≤ 4κ/5`, `c_j ≤ 3Σ_{j+1}/10`, …). -/
theorem gaf02_chain_choice_GAF8 (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg : Fin 3 → ℝ),
      (∀ j, 0 < θ j ∧ 0 < Γ j ∧ Γ j < θ j ∧ Γ j < 1 ∧ 0 < Ξ j (Γ j) ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξ j) (Γ j) ∧
        Γ j * ((80 * (5 / 3) + 31) * (Ξ j (Γ j))⁻¹ + 2) < 1 ∧ 0 < S j ∧
        S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧ 0 < eg j ∧ eg j < 1 / 100 ∧
        eg j < Γ j * S j / 100 ∧ eg j < S j / 1000 ∧ 0 < c j) ∧
      S 0 < Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ S 1 < Γ 1 ^ 3 / (100 * egpGraphConst) ∧
      S 2 < Γ 2 ^ 3 / (100 * sgpGraphBound) ∧ c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < cadj ∧
      (∀ j, 0 < Ξ j (Γ j) ∧ 0 < S j ∧ 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 (Γ 0) * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 (Γ 0) * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 (Γ 0) * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0) * gafCutoffConstant * (gafDerivativeBound +
        c 0) +
        Ξ 1 (Γ 1) * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1) * gafCutoffConstant * (gafDerivativeBound +
        c 1) +
        Ξ 2 (Γ 2) * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2 := by
  obtain ⟨θ, Ξ, hnear, hchoice⟩ := gaf01_row_nearest_shared_GAFS4 Kj
  have hCg : ∀ j, 0 < (![tcpGraphConst, egpGraphConst, sgpGraphBound] : Fin 3 → ℝ) j := by
    intro j
    fin_cases j
    · exact lt_of_lt_of_le one_pos one_le_tcpGraphConst
    · exact egpGraphConst_pos_KC4
    · exact sgpGraphBound_pos_GAF8
  obtain ⟨c, Γ, S, eg, hA, hB, hC, hj⟩ := hchoice _ hCg cadj hcadj
  obtain ⟨hθΓ₀, hc₀, hc1₀, hΓ₀, hΓc₀, -, -, -, hS₀, hS2₀, hSΞ₀, hSΓ₀, hSC₀, he₀, he1₀, heΓ₀, heS₀,
      -⟩ := (hj 0).1
  obtain ⟨hθΓ₁, hc₁, hc1₁, hΓ₁, hΓc₁, -, -, -, hS₁, hS2₁, hSΞ₁, hSΓ₁, hSC₁, he₁, he1₁, heΓ₁, heS₁,
      -⟩ := (hj 1).1
  obtain ⟨hθΓ₂, hc₂, hc1₂, hΓ₂, hΓc₂, -, -, -, hS₂, hS2₂, hSΞ₂, hSΓ₂, hSC₂, he₂, he1₂, heΓ₂, heS₂,
      -⟩ := (hj 2).1
  have hν₀ : eg 0 ≤ Γ 0 := by
    have h' : Γ 0 * S 0 ≤ Γ 0 * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2₀])
      hΓ₀.le
    linarith only [h', heΓ₀]
  have hν₁ : eg 1 ≤ Γ 1 := by
    have h' : Γ 1 * S 1 ≤ Γ 1 * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2₁])
      hΓ₁.le
    linarith only [h', heΓ₁]
  have hν₂ : eg 2 ≤ Γ 2 := by
    have h' : Γ 2 * S 2 ≤ Γ 2 * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2₂])
      hΓ₂.le
    linarith only [h', heΓ₂]
  have hΞpos : ∀ j, 0 < Ξ j (Γ j) := fun j =>
    ((hnear j).2.2 (Γ j) (hj j).1.2.2.2.1 (hj j).1.1).1
  have hmo : ∀ j, 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hSΞ, -⟩ := (hj j).1
    have hΞj := hΞpos j
    have h1 : 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 128 * (Ξ j (Γ j))⁻¹ * (Ξ j (Γ j) / 10000) :=
      mul_le_mul_of_nonneg_left hSΞ.le (mul_nonneg (by norm_num) (inv_nonneg.mpr hΞj.le))
    have h2 : 128 * (Ξ j (Γ j))⁻¹ * (Ξ j (Γ j) / 10000) = 128 / 10000 := by
      rw [show 128 * (Ξ j (Γ j))⁻¹ * (Ξ j (Γ j) / 10000) =
        128 / 10000 * ((Ξ j (Γ j))⁻¹ * Ξ j (Γ j)) by ring, inv_mul_cancel₀ hΞj.ne', mul_one]
    linarith only [h1, h2]
  have hb0 : 0 < 16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound) :=
    mul_pos (mul_pos (by norm_num) (by linarith only [gafCutoffConstant_nonneg]))
      (by linarith only [one_le_gafDerivativeBound])
  have hb1 : 0 < 8 * (1 + gafDerivativeBound) :=
    mul_pos (by norm_num) (by linarith only [one_le_gafDerivativeBound])
  have ht₀ : (0 : ℝ) ≤ min (3 * S 0 / 10) (min (min (c 0 / (16 * (1 + gafCutoffConstant) * (1 +
      gafDerivativeBound)))
      ((1 / 2) / (8 * (1 + gafDerivativeBound)))) 1) :=
    le_min (by linarith only [hS₀]) (le_min (le_min (div_nonneg hc₀.le hb0.le) (div_nonneg (by
        norm_num) hb1.le))
      zero_le_one)
  have k₀ := (hj 0).2.1 0 0 (eg 0) (S 0) le_rfl ht₀ le_rfl ht₀ hν₀ hS2₀.le
  have k₀v := k₀.1
  have k₀d := k₀.2.1
  simp only [mul_zero, add_zero, zero_add] at k₀v k₀d
  have k₁ := (hj 1).2.1 (c 0) (c 0) (eg 1) (S 1) hc₀.le hC.2.1 hc₀.le hC.2.1 hν₁ hS2₁.le
  have k₂ := (hj 2).2.1 (c 1) (c 1) (eg 2) (S 2) hc₁.le hB.2.1 hc₁.le hB.2.1 hν₂ hS2₂.le
  have hnum : (∀ j, 0 < Ξ j (Γ j) ∧ 0 < S j ∧ 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 (Γ 0) * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 (Γ 0) * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 (Γ 0) * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0) * gafCutoffConstant * (gafDerivativeBound +
        c 0) +
        Ξ 1 (Γ 1) * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1) * gafCutoffConstant * (gafDerivativeBound +
        c 1) +
        Ξ 2 (Γ 2) * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2 :=
    ⟨fun j => ⟨hΞpos j, (hj j).1.2.2.2.2.2.2.2.2.1, hmo j, (hj j).1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le⟩,
      k₀v, hC.2.2.2.2, k₀d, hC.2.2.1, hC.2.1.trans (min_le_left _ _), k₁.1, hB.2.2.2.2, k₁.2.1,
      hB.2.2.1, hB.2.1.trans (min_le_left _ _), k₂.1, hA.2.2.le, k₂.2.1⟩
  refine ⟨θ, Ξ, c, Γ, S, eg, fun j => ?_, hSC₀, hSC₁, hSC₂, hC.1, hB.1, hA.1, hnum⟩
  obtain ⟨hθΓ, hcj, hcj1, hΓ, hΓc, -, -, -, hS, -, hSΞ, hSΓ, -, he, he1, heΓ, heS, -⟩ := (hj j).1
  obtain ⟨hΞ, -, hat, hint, -⟩ := (hnear j).2.2 (Γ j) hΓ hθΓ
  exact ⟨(hnear j).1, hΓ, hθΓ, by linarith only [hΓc, hcj1], hΞ, hat, hint, hS, hSΞ, hSΓ, he, he1,
      heΓ,
    heS, hcj⟩

/-- **GAF02 CORE: the chain object on the final family** (draft 59 §3, D59-4; ordered quantifiers).
GAF01's shared moduli `θ, Ξ` (jet order `Kj`) and its CHOICE `c, Γ, Σ, e` with the graph moduli
`(C_TCP, C_EGP, C_SGP)` and `c₃ < c_adj`; the weight constants `c_w` of the stage outputs; FC27's
first-test thresholds `σ, η₂, γ₀ ≤ 1, ηc, θt`; for every `Δ ≥ 1200` the first test's `η₁`, the edge
test's `L_c, η₀` and the slim test's `θs, L_c', η₀'`; then for every packet of the final family
`LocalChartPacketsC14` with the three tests' hypotheses (verbatim union, with `β₂ = β 2`) and
`0 ≤ εr` (the zero-model ratio range of CFS31's kernel), and every selection `sel` of original
preimages over the enlarged stage clouds, there is a chain `C` with these selections: its planes
are the tests' planes, its slots are CFS15 stage outputs, its `E` is `Ψ₃ ∘ Ψ₂ ∘ Ψ₁ ∘ 𝓔⁰`. -/
theorem gaf02_chain_row_GAF8 (Kj : ℕ) {ν β₂ cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hcadj : 0 < cadj) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg cw : Fin 3 → ℝ),
      (∀ j, 0 < θ j ∧ 0 < Γ j ∧ Γ j < θ j ∧ 0 < Ξ j (Γ j) ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξ j) (Γ j) ∧ 0 < S j ∧
        S j < Ξ j (Γ j) / 10000 ∧ 0 < eg j ∧ eg j < Γ j * S j / 100 ∧ 0 < c j ∧ 0 ≤ cw j) ∧
      c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < cadj ∧
      ∃ σ η₂ γ₀ ηc θt : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧ 0 < γ₀ ∧ γ₀ ≤ 1 ∧ 0 < ηc ∧
        0 < θt ∧ θt < 1 ∧
      ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ Lc₁ η₀₁ θs Lc₂ η₀₂ : ℝ, 0 < η₁ ∧ 0 < Lc₁ ∧ 0 < η₀₁ ∧
        0 < θs ∧ θs < 1 ∧ 0 < Lc₂ ∧ 0 < η₀₂ ∧
      ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
        {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
        {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
        {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 → 3 * ν ≤ β 3 → β 3 < 1 →
        3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs →
        σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ → ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 →
        20 * Λz ≤ T → σ⁻¹ ≤ Lmax → 1000 * tcpGraphConst * Δ * Λ < eg 0 → b ≤ η₀₁ →
        s < 1 / 1000000 → β 1 ≤ η₀₁ → Lc₁ ≤ Lmax →
        σc ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg 1 / (20 * egpGraphConst) / 100 →
        σs ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → vs < eg 1 / (20 * egpGraphConst) / 100 →
        ζ ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg 1 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ → β 1 ≤ η₀₂ →
        Lc₂ ≤ Lmax → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 → ζ < θs ^ 2 / 10 ^ 6 →
        ζ < 1 / (100 * (1000000 * Δ)) → εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
        ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) (sel
              st x) = x) →
        ∃ C : Gaf02Chain P.toLocalChartPackets Kj (fun j => Ξ j (Γ j)) Γ S eg c cw,
          C.sel = sel := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, hj, hSC₀, hSC₁, hSC₂, hc01, hc12, hc2, hnum⟩ :=
    gaf02_chain_choice_GAF8 Kj hcadj
  obtain ⟨-, hΓ₀, -, hΓ1₀, -, hat₀, hint₀, hS₀, -, hSΓ₀, he₀, he1₀, heΓ₀, -, -⟩ := hj 0
  obtain ⟨-, hΓ₁, -, hΓ1₁, -, hat₁, hint₁, hS₁, -, hSΓ₁, he₁, he1₁, heΓ₁, heS₁, -⟩ := hj 1
  obtain ⟨-, hΓ₂, -, hΓ1₂, -, hat₂, hint₂, hS₂, -, hSΓ₂, he₂, he1₂, heΓ₂, -, -⟩ := hj 2
  obtain ⟨cw₀, hcw₀, hout₀⟩ := gafStage_output_GAF8 0 hΓ₀ hat₀ hint₀
  obtain ⟨cw₁, hcw₁, hout₁⟩ := gafStage_output_GAF8 1 hΓ₁ hat₁ hint₁
  obtain ⟨cw₂, hcw₂, hout₂⟩ := gafStage_output_GAF8 2 hΓ₂ hat₂ hint₂
  have hmo : ∀ j, 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => (hnum.1 j).2.2.1
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hrow1⟩ :=
    fc27_first_test_pps_GAF5 hΓ₀ hΓ1₀ hS₀ hSΓ₀ hSC₀ he₀ he1₀ heΓ₀ hν hν1
  refine ⟨θ, Ξ, c, Γ, S, eg, ![cw₀, cw₁, cw₂], fun j => ?_, hc01, hc12, hc2, σ, η₂, min γ₀ 1, ηc,
    θt, hσ, hσ1, hη₂, lt_min hγ₀ one_pos, min_le_right _ _, hηc, hθt, hθt1, fun Δ hΔ => ?_⟩
  · obtain ⟨hθ, hΓ, hθΓ, -, hΞ, hat, -, hS, hSΞ, -, he, -, heΓ, -, hcj⟩ := hj j
    refine ⟨hθ, hΓ, hθΓ, hΞ, hat, hS, hSΞ, he, heΓ, hcj, ?_⟩
    fin_cases j
    exacts [hcw₀, hcw₁, hcw₂]
  obtain ⟨η₁, hη₁, hrow1'⟩ := hrow1 Δ hΔ
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  obtain ⟨Lc₁, η₀₁, hLc₁, hη₀₁, hrowE⟩ := fc27_edge_test_pp_GAF4 (Γ := Γ 1) (Sg := S 1) (eg := eg 1)
    hΔ1 hβ₂ hβ₂1 ⟨hΓ₁, hΓ1₁⟩ hS₁ (lt_min hSΓ₁ hSC₁) he₁ (lt_min he1₁ (lt_min heΓ₁ heS₁))
  obtain ⟨θs, hθs, hθs1, Lc₂, η₀₂, hLc₂, hη₀₂, hrowS⟩ :=
    fc27_slim_test_pp_C14_GAF4 hΔ1 hβ₂ (by linarith only [hβ₂1]) hΓ₂ hΓ1₂ hS₂ hSΓ₂ hSC₂ he₂ he1₂
        heΓ₂
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, hη₁, hLc₁, hη₀₁, hθs, hθs1, hLc₂, hη₀₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
        f27 f28 f29 f30 f31
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    m1 m2 m3 m4 m5 m6 m7 m8 hεr0 sel hsel
  obtain ⟨plane₀, hp₀⟩ := hrow1' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
    (f17.trans (min_le_left _ _)) f18 (f19.trans (min_le_left _ _)) f20 f21 f22 f23 f24 f25 f26
    f27 f28 f29 f30 f31
  obtain ⟨plane₁, hp₁⟩ := hrowE X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz P d1 d2 d3 d4 f1 f4 f2 f3 d5 d6 f23 d7 d8 f6 f7 f29 f26 d9 d10 d11
  obtain ⟨plane₂, hp₂⟩ := hrowS X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz P m1 m2 m3 f1 f4 f6 f7 f29 f23 m4 m5 f26 m6 m7 m8
  have he8 : e ≤ 1 / 8 := by linarith only [f6]
  have O₀ := (hout₀ P f1 hΔ1 f2 f3 he8 f4 (sel 0) (hsel 0) (S 0) hS₀ (hmo 0)
    plane₀ (fun x hx => (hp₀.1 x hx).1) (hp₀.2.1 (sel 0) (hsel 0))).some
  have O₁ := (hout₁ P f1 hΔ1 f2 f3 he8 f4 (sel 1) (hsel 1) (S 1) hS₁ (hmo 1)
    plane₁ (fun x hx => (hp₁.1 x hx).1) (hp₁.2.1 (sel 1) (hsel 1))).some
  have O₂ := (hout₂ P f1 hΔ1 f2 f3 he8 f4 (sel 2) (hsel 2) (S 2) hS₂ (hmo 2)
    plane₂ (fun x hx => (hp₂.1 x hx).1) (hp₂.2.1 (sel 2) (hsel 2))).some
  have hθt2 : θt ^ 2 < 1 := by nlinarith only [mul_lt_mul_of_pos_left hθt1 hθt, hθt1]
  refine ⟨{
    std := ⟨f1, hΔ1, f2, f3, f4, f5, f6, f7, f23.le, by linarith only [f24, hθt2],
      ⟨f10, by linarith only [f11, hθt2]⟩, ⟨f18.le, f19.trans (min_le_right _ _)⟩,
      ⟨hεr0, by linarith only [f28, hθt1]⟩⟩
    numbers := hnum
    sel := sel
    hsel := hsel
    plane := ![plane₀, plane₁, plane₂]
    test0 := hp₀
    test1 := hp₁
    test2 := hp₂
    slot := fun st => match st with
      | ⟨0, _⟩ => .active O₀
      | ⟨1, _⟩ => .active O₁
      | ⟨2, _⟩ => .active O₂
      | ⟨k + 3, hk⟩ => absurd hk (by omega) }, rfl⟩

/-- **Consumer: the GAF02 CORE conjunct form read off the chain object** (D59-4: the present
conjunct theorem is `C.core`'s forgetful consequence): for a chain on the final family, `E` is
smooth, `‖E − 𝓔⁰‖ < c₃ρ`, the derivative error has a budget `H < c₃`, (AM0) holds on
`[𝓔⁰ p, E p]`, and the scale `s = ℓ_ρ(E) = ℓ_ρ(g₁)` is positive. -/
theorem gaf02_core_of_chain_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.E ∧
      (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 2 * ρ p) ∧
      (∃ Hd : ℝ, Hd < c 2 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner
            p w w)) ∧
      (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
        cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
        ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (C.E p),
        |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
          ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
      ∀ p, C.scale p = gafScaleMarker P.toLocalChartFamily P.zero (C.g₁ p) ∧ 0 < C.scale p :=
  ⟨C.stage_smooth.2.2, C.stage_error_lt.2.2, C.stage_derivative_lt.2.2, C.segment_am0,
    fun p => ⟨(C.scale_eq_first_blend p).1, (C.scale_pos p).2⟩⟩

end DifferentialGeometry.Geometry.Collapse
