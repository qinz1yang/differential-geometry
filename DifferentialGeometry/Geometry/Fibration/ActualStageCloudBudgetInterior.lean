import DifferentialGeometry.Geometry.Fibration.ActualStageCloudBudget

/-!
# `N_b` and `c_w` for every admissible selection under CFS12's interior condition only

Blueprint `master207B.tex`, CFS11 (LM) and `N_b` (B:2451–2472) and CFS12's weight bound
(B:2536–2545), for an ARBITRARY finite selection `I ⊆ S` with disjoint balls `B(x_i, r_i)` (the
selection made inside CFS15 at GAF01's buffer `b = Ξ(Γ)⁻¹`), under CFS12's interior condition
`δ((80B + 31)b + 2) < 1` only, NOT CFS11's (DS) `δ ≤ d_b` (which is needed only for CFS11's own
greedy selection, `stage_cloud_budget_kernel_GAFS3`). (DS) implies the interior condition
(`ds_interior_GAFS3`), so these statements are strictly more general on the selection part.

* `stage_selection_budget_kernel_GAFS3`: `c_w ≥ 0` depending only on `k, b`; for every cloud
  `S ⊆ S̃` with positive radius, `k`-planes, (MCb) on `S`, the (CS) tests at quality `δ` with the
  interior condition, and every finite disjoint selection `I ⊆ S`: `|J| ≤ N_b`, (LM), and under
  the tube inclusion `Σ_i ‖Dw_i‖ ≤ c_w / r_x`.
* `nb_cw_stage_selection_GAFS3`: the same on `LocalChartPacketsC14` at every stage, `c_w = cw st b`
  chosen before the family.
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

/-- **`N_b` and `c_w` for every admissible selection, kernel.** For `k` and `b ≥ 1` there is
`c_w ≥ 0` (depending only on `k, b`) such that for every cloud `S ⊆ S̃` in a finite-dimensional
Euclidean space with positive radius, `k`-planes, (MCb) on `S` at the buffer `128b` with
`B = 5/3`, the (CS) tests at a quality `δ > 0` with `δ((80B + 31)b + 2) < 1`, and every finite
selection `I ⊆ S` with disjoint balls: `|J| ≤ N_b = ⌈(1 + 2·(5/3)·165·b)^k⌉` and (LM) for the
reference ball `B(x, 30br_x)` of every `x ∈ S`, and under the tube inclusion
`Σ_i ‖Dw_i‖ ≤ c_w / r_x` on `B(x, 8br_x)`. -/
theorem stage_selection_budget_kernel_GAFS3 (k : ℕ) (bb : ℝ) :
    ∃ cw : ℝ, 0 ≤ cw ∧ (1 ≤ bb →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (S St : Set H), S ⊆ St → ∀ r : H → ℝ, (∀ x ∈ S, 0 < r x) →
        ∀ plane : H → Submodule ℝ H, (∀ x ∈ S, Module.finrank ℝ (plane x) = k) →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * bb * max (r y) (r x) →
          r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
        ∀ δc : ℝ, 0 < δc → δc * ((80 * (5 / 3) + 31) * bb + 2) < 1 →
        (∀ x ∈ S, hausdorffEDist (St ∩ ball x (r x / δc))
          ((AffineSubspace.mk' x (plane x) : Set H) ∩ ball x (r x / δc)) ≤
            ENNReal.ofReal (δc * r x)) →
        ∀ (I : Set H) (hI : I.Finite), I ⊆ S → I.PairwiseDisjoint (fun i => ball i (r i)) →
          (∀ x ∈ S,
            ((I ∩ {i | (closedBall i (80 * bb * r i) ∩ ball x (30 * bb * r x)).Nonempty}).ncard :
                ℝ) ≤ (⌈(1 + 2 * (5 / 3) * 165 * bb) ^ k⌉₊ : ℝ) ∧
            ∀ i ∈ I, (closedBall i (80 * bb * r i) ∩ ball x (30 * bb * r x)).Nonempty →
              r x / (5 / 3) ≤ r i ∧ r i ≤ (5 / 3) * r x ∧ dist i x < 165 * bb * r x) ∧
          ((⋃ x ∈ S, ball x (8 * bb * r x)) ⊆ ⋃ i ∈ I, ball i (20 * bb * r i) →
            ∀ x ∈ S, ∀ y ∈ ball x (8 * bb * r x),
              (∑ i ∈ hI.toFinset, ‖fderiv ℝ (fun y' => ballCutoff i (40 * bb * r i)
                  (2 * (40 * bb * r i)) y' / (∑ a ∈ hI.toFinset,
                    ballCutoff a (40 * bb * r a) (2 * (40 * bb * r a)) y')) y‖) ≤ cw / r x)) := by
  classical
  by_cases hbb : 1 ≤ bb
  swap
  · exact ⟨0, le_rfl, fun h => (hbb h).elim⟩
  obtain ⟨cw, hcw, hW⟩ :=
    exists_selection_weight_deriv_bound_GAFS2.{0} k bb (5 / 3) hbb (by norm_num)
  refine ⟨cw, hcw, fun _ => ?_⟩
  intro H _ _ _ S St hSSt r hr plane hdim hscale δc hδ hint hcloud I hI hIS hdisj
  refine ⟨fun x hx => ?_, fun htube x hx y hy => ?_⟩
  · have hgeo := large_cloud_selected_center_geometry S St hSSt r (fun x : S => plane x) k
      (fun x => hdim x x.2) I hIS hI hdisj hr bb (5 / 3) δc hbb (by norm_num) hδ hint hscale
      (fun x => hcloud x x.2) ⟨x, hx⟩
    have hrx := hr x hx
    refine ⟨hgeo.1.trans ?_, fun i hi hmeet => ?_⟩
    · have hbase : (1 + 2 * (5 / 3) * (80 * (5 / 3) + 31) * bb : ℝ) ≤
          1 + 2 * (5 / 3) * 165 * bb := by linarith
      have h0 : (0 : ℝ) ≤ 1 + 2 * (5 / 3) * (80 * (5 / 3) + 31) * bb := by linarith
      exact (pow_le_pow_left₀ h0 hbase k).trans (Nat.le_ceil _)
    · obtain ⟨h1, h2, h3, -⟩ := hgeo.2 i ⟨hi, hmeet⟩
      refine ⟨h1, h2, h3.trans_le ?_⟩
      have h0 : 0 ≤ bb * r x := by positivity
      nlinarith
  · exact hW H S St hSSt r plane hdim hr δc hδ hint hscale hcloud I hI hIS hdisj htube x hx y hy

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14SI_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SI_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SI_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **`N_b` and `c_w` for every admissible selection on the actual stage clouds.** There is
`c_w : Fin 3 → ℝ → ℝ`, `c_w st b ≥ 0` for `b ≥ 1`, chosen before the family, such that on every
`LocalChartPacketsC14` in FC07's range, at every stage `st`, for every selection `sel` of preimages
over `S̃_st`, `0 < Σ` with `128bΣ ≤ 1/5`, quality `Γ > 0` with CFS12's interior condition
`Γ((80B + 31)b + 2) < 1` and planes of the stage dimension with the (CS) tests at quality `Γ`
(radius `r = Σρ ∘ sel`): for every finite selection `I ⊆ S_st` with disjoint balls,
`|J| ≤ N_b = ⌈(1 + 2·(5/3)·165·b)^{k_st}⌉` and (LM), and under the tube inclusion
`Σ_i ‖Dw_i‖ ≤ c_w st b / r_x` on `B(x, 8br_x)`. -/
theorem nb_cw_stage_selection_GAFS3 :
    ∃ cw : Fin 3 → ℝ → ℝ, ∀ st : Fin 3, ∀ bb : ℝ, 1 ≤ bb → 0 ≤ cw st bb ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
            (sel x) = x) →
        ∀ sg : ℝ, 0 < sg → 128 * bb * sg ≤ 1 / 5 →
        ∀ Γ : ℝ, 0 < Γ → Γ * ((80 * (5 / 3) + 31) * bb + 2) < 1 →
        ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane x) = gafStageDim st) →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
              ball x (sg * ρ (sel x) / Γ))
            ((AffineSubspace.mk' x (plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) →
        ∀ (I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
          (hI : I.Finite), I ⊆ gafCloud P.toLocalChartFamily P.zero st →
          I.PairwiseDisjoint (fun i => ball i (sg * ρ (sel i))) →
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            ((I ∩ {i | (closedBall i (80 * bb * (sg * ρ (sel i))) ∩
                ball x (30 * bb * (sg * ρ (sel x)))).Nonempty}).ncard : ℝ) ≤
              (⌈(1 + 2 * (5 / 3) * 165 * bb) ^ gafStageDim st⌉₊ : ℝ) ∧
            ∀ i ∈ I, (closedBall i (80 * bb * (sg * ρ (sel i))) ∩
                ball x (30 * bb * (sg * ρ (sel x)))).Nonempty →
              sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel i) ∧
              sg * ρ (sel i) ≤ (5 / 3) * (sg * ρ (sel x)) ∧
              dist i x < 165 * bb * (sg * ρ (sel x))) ∧
          ((⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
              ball x (8 * bb * (sg * ρ (sel x)))) ⊆
            ⋃ i ∈ I, ball i (20 * bb * (sg * ρ (sel i))) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            ∀ y ∈ ball x (8 * bb * (sg * ρ (sel x))),
              (∑ i ∈ hI.toFinset, ‖fderiv ℝ (fun y' => ballCutoff i (40 * bb * (sg * ρ (sel i)))
                  (2 * (40 * bb * (sg * ρ (sel i)))) y' / (∑ a ∈ hI.toFinset,
                    ballCutoff a (40 * bb * (sg * ρ (sel a))) (2 * (40 * bb * (sg * ρ (sel a))))
                      y')) y‖) ≤ cw st bb / (sg * ρ (sel x))) := by
  have hex := fun (st : Fin 3) (bb : ℝ) => stage_selection_budget_kernel_GAFS3 (gafStageDim st) bb
  choose cw hcw using hex
  refine ⟨cw, fun st bb hbb => ⟨(hcw st bb).1, ?_⟩⟩
  have hK := (hcw st bb).2 hbb
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hbsg Γ hΓ hint plane hdim hcloud
  have hbinv : 0 < bb⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hbb)
  have hmo : 128 * bb⁻¹⁻¹ * sg ≤ 1 / 5 := by rwa [inv_inv]
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hbinv
    hsg hmo
  exact hK (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 (fun x => sg * ρ (sel x)) (fun x _ => mul_pos hsg (hρ (sel x))) plane hdim
    (fun x hx y hy hd => hin.2.2.2 x (hin.1 hx) y (hin.1 hy) (by rwa [inv_inv])) Γ hΓ hint hcloud

end DifferentialGeometry.Geometry.Collapse
