import DifferentialGeometry.Geometry.Fibration.ActualStageMean

/-!
# CFS11–CFS12's `N_b` and `c_w` on the actual stage clouds

Blueprint `master207B.tex`, CFS11 (`lem:fibration-cloud-large-cover`, B:2451: `N_b = ⌈(1+2BDb)^k⌉`,
(LM)), CFS12's weight bound (B:2536–2545: `‖Dw_i‖ ≤ c_1 r_x⁻¹` from the fixed list `J`) and PR10
(B:10109: "CFS11–CFS12 supply finite `N_b, c_w`"), with the standing hypotheses of B:2425–2449
(`B = 5/3`, `D = 165`, (MCb) at the buffer `128b`, (DS) `δ ≤ d_b`), on the three actual stage
clouds `S_st = gafCloud st` of GAF01/GAF02 with FC26's selected radius `r = Σρ ∘ sel`.

* `stage_cloud_budget_kernel_GAFS3`: for `k`, `b` a constant `c_w ≥ 0` (depending only on `k, b`)
  such that for every bounded cloud `S ⊆ S̃` with `k`-planes, radius bounds, (MCb) on `S` and the
  (CS) tests at a quality `δ ≤ d_b`: CFS11's selection (finite, disjoint balls, greedy cover, tube
  inclusions), and for EVERY finite selection `I ⊆ S` with disjoint balls `B(x_i, r_i)` (CFS11's
  own, or the one made inside CFS15): the list `J` of selected centres whose `80br_i`-ball meets
  `B(x, 30br_x)` has `|J| ≤ N_b` and (LM); with the tube inclusion, the normalized cutoff weights
  at `40br_i` satisfy `Σ_i ‖Dw_i‖ ≤ c_w / r_x` on `B(x, 8br_x)`. (DS) implies CFS12's interior
  condition `δ((80B + 31)b + 2) < 1`.
* `nb_cw_stage_cloud_GAFS3`: the same on `LocalChartPacketsC14` in FC07's range, for every stage,
  with `c_w = cw st b` chosen BEFORE the family and `N_b = ⌈(1 + 2·(5/3)·165·b)^{k_st}⌉`,
  `k_st = gafStageDim st`; boundedness, the radius bounds and (MCb) from
  `cfs14_stage_inputs_GAF2`. The (CS) tests are exactly the per-stage conclusion of
  `fc27_row_GAF2` (consumer `fc27_row_nb_cw_GAFS3`).
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

/-- (DS) implies CFS12's interior condition `δ((80B + 31)b + 2) < 1` at `B = 5/3`. -/
theorem ds_interior_GAFS3 {bb δc : ℝ} (hbb : 1 ≤ bb) (hδ : 0 < δc)
    (hds : δc ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1))))) :
    δc * ((80 * (5 / 3) + 31) * bb + 2) < 1 := by
  have h1 : δc ≤ 1 / (4 * (128 * bb * (5 / 3) + 3)) :=
    hds.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hpos : 0 < 4 * (128 * bb * (5 / 3) + 3) := by linarith
  have h2 : δc * (4 * (128 * bb * (5 / 3) + 3)) ≤ 1 := (le_div_iff₀ hpos).mp h1
  have h3 : (80 * (5 / 3) + 31) * bb + 2 < 4 * (128 * bb * (5 / 3) + 3) := by linarith
  exact (mul_lt_mul_of_pos_left h3 hδ).trans_le h2

/-- **CFS11–CFS12's `N_b` and `c_w`, kernel.** For `k` and a buffer `b ≥ 1` there is `c_w ≥ 0`
(depending only on `k, b`) such that for every totally bounded cloud `S ⊆ S̃` in a
finite-dimensional Euclidean space, radius `r` bounded above and away from zero on `S`, `k`-planes,
(MCb) on `S` at the buffer `128b` with `B = 5/3` and the (CS) tests at a quality `0 < δ ≤ d_b`:
CFS11's selection, and for every finite selection `I ⊆ S` with disjoint balls: `|J| ≤ N_b` and (LM)
for the reference ball `B(x, 30br_x)` of every `x ∈ S`, and under the tube inclusion
`Σ_i ‖Dw_i‖ ≤ c_w / r_x` on `B(x, 8br_x)`. -/
theorem stage_cloud_budget_kernel_GAFS3 (k : ℕ) (bb : ℝ) :
    ∃ cw : ℝ, 0 ≤ cw ∧ (1 ≤ bb →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (S St : Set H), S ⊆ St → TotallyBounded S → ∀ (r : H → ℝ) (rmin R : ℝ), 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        ∀ plane : H → Submodule ℝ H, (∀ x ∈ S, Module.finrank ℝ (plane x) = k) →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * bb * max (r y) (r x) →
          r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
        ∀ δc : ℝ, 0 < δc → δc ≤ min (1 / (8 * (5 / 3)))
          (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))) →
        (∀ x ∈ S, hausdorffEDist (St ∩ ball x (r x / δc))
          ((AffineSubspace.mk' x (plane x) : Set H) ∩ ball x (r x / δc)) ≤
            ENNReal.ofReal (δc * r x)) →
        (∃ T : Set H, T ⊆ S ∧ T.Finite ∧ T.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ T, dist x i < 3 * r i ∧ r x ≤ 2 * r i) ∧
          (⋃ x ∈ S, ball x (8 * bb * r x)) ⊆ ⋃ i ∈ T, ball i (20 * bb * r i) ∧
          (⋃ i ∈ T, ball i (20 * bb * r i)) ⊆ ⋃ i ∈ T, ball i (30 * bb * r i)) ∧
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
  intro H _ _ _ S St hSSt hS r rmin R hrmin hlower hupper plane hdim hscale δc hδ hds hcloud
  have hr : ∀ x ∈ S, 0 < r x := fun x hx => hrmin.trans_le (hlower x hx)
  have hint := ds_interior_GAFS3 hbb hδ hds
  have hTB := cfs11_of_scale_ratio_KA3 S St hSSt hS r hrmin hlower hupper k plane hdim hbb
    hscale hδ hds hcloud
  refine ⟨?_, fun I hI hIS hdisj => ⟨fun x hx => ?_, fun htube x hx y hy => ?_⟩⟩
  · obtain ⟨T, h1, h2, h3, h4, h5, h6, -⟩ := hTB
    exact ⟨T, h1, h2, h3, h4, h5, h6⟩
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
local instance instMetricNC14SB_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SB_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SB_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **`N_b` and `c_w` on the actual stage clouds** (CFS11–CFS12, PR10). There is
`c_w : Fin 3 → ℝ → ℝ`, `c_w st b ≥ 0` for `b ≥ 1`, chosen before the family, such that on every
`LocalChartPacketsC14` in FC07's range, at every stage `st`, for every selection `sel` of preimages
over `S̃_st`, radius factor `0 < Σ` with `128bΣ ≤ 1/5`, quality `0 < Γ ≤ d_b` and planes of the
stage dimension with the (CS) tests at quality `Γ` and radius `r = Σρ ∘ sel` (the per-stage
conclusion of `fc27_row_GAF2`): CFS11's selection on `S_st`, and for every finite selection
`I ⊆ S_st` with disjoint balls, `|J| ≤ N_b = ⌈(1 + 2·(5/3)·165·b)^{k_st}⌉` and (LM) on the
reference ball `B(x, 30br_x)` of every `x ∈ S_st`, and under the tube inclusion the weight
derivative budget `Σ_i ‖Dw_i‖ ≤ c_w st b / r_x` on `B(x, 8br_x)`. -/
theorem nb_cw_stage_cloud_GAFS3 :
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
        ∀ Γ : ℝ, 0 < Γ → Γ ≤ min (1 / (8 * (5 / 3)))
          (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1)))) →
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
        (∃ T' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          T' ⊆ gafCloud P.toLocalChartFamily P.zero st ∧ T'.Finite ∧
          T'.PairwiseDisjoint (fun i => ball i (sg * ρ (sel i))) ∧
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∃ i ∈ T',
            dist x i < 3 * (sg * ρ (sel i)) ∧ sg * ρ (sel x) ≤ 2 * (sg * ρ (sel i))) ∧
          (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (8 * bb * (sg * ρ (sel x)))) ⊆
            ⋃ i ∈ T', ball i (20 * bb * (sg * ρ (sel i))) ∧
          (⋃ i ∈ T', ball i (20 * bb * (sg * ρ (sel i)))) ⊆
            ⋃ i ∈ T', ball i (30 * bb * (sg * ρ (sel i)))) ∧
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
  have hex := fun (st : Fin 3) (bb : ℝ) => stage_cloud_budget_kernel_GAFS3 (gafStageDim st) bb
  choose cw hcw using hex
  refine ⟨cw, fun st bb hbb => ⟨(hcw st bb).1, ?_⟩⟩
  have hK := (hcw st bb).2 hbb
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hbsg Γ hΓ hds plane hdim hcloud
  have hbinv : 0 < bb⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hbb)
  have hmo : 128 * bb⁻¹⁻¹ * sg ≤ 1 / 5 := by rwa [inv_inv]
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hbinv
    hsg hmo
  have hR := Classical.choose_spec (Classical.choose_spec hin.2.2.1)
  exact hK (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) _ _ hR.1 hR.2.1 hR.2.2 plane hdim
    (fun x hx y hy hd => hin.2.2.2 x (hin.1 hx) y (hin.1 hy) (by rwa [inv_inv])) Γ hΓ hds hcloud

end DifferentialGeometry.Geometry.Collapse
