import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffOne
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainChoice

/-!
# BCG03: CFS22's slim cutoff `ψ₂` of the boundary chain, bound to the actual map (lane BAUG-PSI)

Part (a) of target A2-mk, second half: the third component of `BoundaryGaf02Chain.cutoff_bindings`
on the ACTUAL slot (`actualSlotsV2_BAUGD`, cutoff `ψ₂ = cutoffTwo_BAUGD`, CFS22's uniform one-axis
cutoff on the slim blocks of `H^∂`, `ℓ = 10⁵Δ`), stated — as on the closed side
(`gaf02_stageThree_cutoff`) — for ANY map `f` with `‖f − F_∂‖ ≤ (4κ/5)ρ` and the zero-marker clause,
at the actual augmented map `F_∂` on the WHOLE original carrier `W` (kernel `cfs22_row`).

* FC27 (slim) on a regional slim centre: `SlimCentreOn.cutoff_eq_one_of_abs_coord_le_BAUGP2`
  (plateau `|η_j| ≤ 8·10⁵Δ` on `B(j, 10⁶Δρ_j)`), `SlimCentreOn.abs_coord_le_of_mem_tsupport_BAUGP2`
  (`|η_j| ≤ 89·10⁴Δ` on the closed support) — the closed `SlimCentre` lemmas with the carrier's own
  completeness;
* the slim blocks of `F_∂` on `W`: `slimCutoffW_BAUGP2`, `slimCoordW_BAUGP2` (zero extensions),
  `slimBlock_boundaryOriginalMap_BAUGP2`, the count `slim_count_BAUGP2` (the slim family's own
  `multiplicity`), the comparability `slim_scale_comparable_BAUGP2`, the plateau
  `slimCutoffW_eq_one_BAUGP2`;
* **`cutoffTwo_binding_BAUGP2`** (the chain's `cutoff_bindings.2.2` verbatim with `f` for the stage
  input, at every `b_cut ≥ b₂`);
* consumer **`boundaryChain_choice_cutoffs_BAUGP2`**: BAUG-D's CHOICE `boundaryChain_choice_BAUGD`
  at `b_cut = max(b₀, b₁, b₂)` and `κ = cutoffKappa_BAUGP2`; on every supply with the six register
  premises the three cutoff bindings hold for any stage inputs with value errors `< c₀ρ`, `< c₁ρ`
  and the zero-marker clause (part (b)).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section SlimOn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

namespace SlimCentreOn

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- FC27 (slim) on a regional slim centre: the cutoff is one where `|η_j| ≤ 8·10⁵Δ` in
`B(j, 10⁶Δρ(j))`. -/
theorem cutoff_eq_one_of_abs_coord_le_BAUGP2 (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j)
    {x : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (hc : |c.coord_BCG2 x| ≤ 8 * 10 ^ 5 * Δ) :
    c.cutoff_BCNT x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.cutoff_eq_one x hd hc

/-- FC27 (slim) on a regional slim centre: on the closed support of the cutoff
`|η_j| ≤ 89·10⁴Δ`. -/
theorem abs_coord_le_of_mem_tsupport_BAUGP2 (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j)
    {x : X} (hx : x ∈ tsupport c.cutoff_BCNT) : |c.coord_BCG2 x| ≤ 89 * 10 ^ 4 * Δ := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact (P.tsupport_cutoff hx).2

end SlimCentreOn

end SlimOn

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-! ### The slim blocks of `F_∂` on `W` -/

/-- The slim cutoff `ζ_j` on `W` (zero extension from `W°`). -/
def slimCutoffW_BAUGP2 (j : S.SlimIdx_BAUGD) : W.Carrier → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  Subtype.val.extend (S.family.slim.cutoff_BCNT j.1) 0

/-- The slim coordinate `η_j` on the axis of `ℝ²`, on `W` (zero extension from `W°`). -/
def slimCoordW_BAUGP2 (j : S.SlimIdx_BAUGD) : W.Carrier → ℝ² :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  Subtype.val.extend (fun x => planeAxis
    ((S.family.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x)) 0

/-- The slim chart domain `B(j, 10⁶Δρ_j)` (in `d_ĝ`) as a subset of `W`. -/
def slimDomW_BAUGP2 (j : S.SlimIdx_BAUGD) : Set W.Carrier :=
  letI := inducedMetricSpace S.completion.metric
  Subtype.val '' ball j.1 (1000000 * Δ * S.rho j.1)

theorem slimCutoffW_val_BAUGP2 (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.slimCutoffW_BAUGP2 j q.val =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.slim.cutoff_BCNT j.1 q) :=
  Subtype.val_injective.extend_apply _ _ q

theorem slimCoordW_val_BAUGP2 (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.slimCoordW_BAUGP2 j q.val =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       planeAxis ((S.family.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 q)) :=
  Subtype.val_injective.extend_apply _ _ q

theorem slimCutoffW_of_notMem_BAUGP2 (j : S.SlimIdx_BAUGD) {p : W.Carrier}
    (hp : ¬ ∃ q : W.pieceInterior ⊤, q.val = p) : S.slimCutoffW_BAUGP2 j p = 0 := by
  unfold slimCutoffW_BAUGP2
  rw [Function.extend_apply' _ _ _ hp]
  rfl

theorem slimCoordW_of_notMem_BAUGP2 (j : S.SlimIdx_BAUGD) {p : W.Carrier}
    (hp : ¬ ∃ q : W.pieceInterior ⊤, q.val = p) : S.slimCoordW_BAUGP2 j p = 0 := by
  unfold slimCoordW_BAUGP2
  rw [Function.extend_apply' _ _ _ hp]
  rfl

/-- The slim reference coordinate is the slim block coordinate on `W°`. -/
theorem slimEta_eq_coord_BAUGP2 (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.slimEta_BIF j.1 q =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       (S.family.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 q) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  simp only [slimEta_BIF, hj, ↓reduceDIte]

/-- `‖η_j‖ = |slimEta_j|` at an interior point. -/
theorem norm_slimCoordW_val_BAUGP2 (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    ‖S.slimCoordW_BAUGP2 j q.val‖ = |S.slimEta_BIF j.1 q| := by
  rw [S.slimCoordW_val_BAUGP2, norm_planeAxis, S.slimEta_eq_coord_BAUGP2]

/-- **The slim blocks of `F_∂` on `W`**: `u_j(F_∂ p) = (ρ_j ζ_j(p)) • η_j(p)` and
`v_j(F_∂ p) = ρ_j ζ_j(p)` (both zero at boundary points). -/
theorem slimBlock_boundaryOriginalMap_BAUGP2 (j : S.SlimIdx_BAUGD) (p : W.Carrier) :
    S.slimVector_BAUGD j (S.boundaryOriginalMap p) =
        (S.rho j.1 * S.slimCutoffW_BAUGP2 j p) • S.slimCoordW_BAUGP2 j p ∧
      S.slimMarker_BAUGD j (S.boundaryOriginalMap p) =
        S.rho j.1 * S.slimCutoffW_BAUGP2 j p := by
  have hne : (.inr (.inl j) : S.IntTag_BAUGA) ≠ S.scaleTag_BAUGA := by
    simp [scaleTag_BAUGA]
  have hslot : S.boundaryOriginalMap p (Sum.inl (.inr (.inl j))) =
      Subtype.val.extend (fun x => S.interiorMapOn_BAUGA x (.inr (.inl j))) 0 p := by
    change S.intSlotW_BAUGA (.inr (.inl j)) p = _
    simp only [intSlotW_BAUGA, hne, ↓reduceIte]
  by_cases hp : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hp
    rw [Subtype.val_injective.extend_apply] at hslot
    rw [S.slimCutoffW_val_BAUGP2, S.slimCoordW_val_BAUGP2]
    simp only [slimVector_BAUGD, slimMarker_BAUGD, blockVectorCLM_apply,
      blockMarkerCLM_apply, hslot]
    exact ⟨rfl, rfl⟩
  · rw [Function.extend_apply' _ _ _ hp] at hslot
    rw [S.slimCutoffW_of_notMem_BAUGP2 j hp, S.slimCoordW_of_notMem_BAUGP2 j hp]
    simp only [slimVector_BAUGD, slimMarker_BAUGD, blockVectorCLM_apply,
      blockMarkerCLM_apply, hslot, Pi.zero_apply, mul_zero, zero_smul]
    exact ⟨rfl, rfl⟩

/-- A point of the closed support of a slim cutoff lies in `B(j, 10⁶Δρ_j)`. -/
theorem mem_ball_of_mem_tsupport_slim_BAUGP2 (hΔ : 0 < Δ) (j : S.SlimIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : q ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      tsupport (S.family.slim.cutoff_BCNT j.1))) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 < 1000000 * Δ * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have h := S.family.slim.tsupport_cutoff_subset_BCNT j.1 hq
  have hrj := S.rho_pos j.1
  rw [mem_closedBall] at h
  have hlt : 91 / 100 * (10 ^ 6 * Δ) * S.rho j.1 < 1000000 * Δ * S.rho j.1 := by
    have := mul_pos hΔ hrj
    nlinarith
  exact h.trans_lt hlt

/-- The slim cutoff vanishes off its chart domain. -/
theorem slimCutoffW_eq_zero_BAUGP2 (hΔ : 0 < Δ) (j : S.SlimIdx_BAUGD) (p : W.Carrier)
    (hp : p ∉ S.slimDomW_BAUGP2 j) : S.slimCutoffW_BAUGP2 j p = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hq
    rw [S.slimCutoffW_val_BAUGP2]
    by_contra h
    exact hp ⟨q, S.mem_ball_of_mem_tsupport_slim_BAUGP2 hΔ j (subset_tsupport _ h), rfl⟩
  · exact S.slimCutoffW_of_notMem_BAUGP2 j hq

/-- The slim cutoffs on `W` take values in `[0, 1]`. -/
theorem slimCutoffW_mem_Icc_BAUGP2 (j : S.SlimIdx_BAUGD) (p : W.Carrier) :
    S.slimCutoffW_BAUGP2 j p ∈ Icc (0 : ℝ) 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hq
    rw [S.slimCutoffW_val_BAUGP2]
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    rw [S.family.slim.cutoff_BCNT_of_mem hj]
    exact (S.family.slim.centre j.1 hj).cutoff_mem_Icc_BCNT q
  · rw [S.slimCutoffW_of_notMem_BAUGP2 j hq]
    exact ⟨le_rfl, zero_le_one⟩

/-- **The slim count**: at every point of `W` at most `N₂` slim cutoffs are positive (the family's
own `multiplicity` field). -/
theorem slim_count_BAUGP2 (hΔ : 0 < Δ) (p : W.Carrier) :
    (Finset.univ.filter fun j : S.SlimIdx_BAUGD => 0 < S.slimCutoffW_BAUGP2 j p).card ≤
      slimCount_BAUGP2 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  swap
  · have h0 : (Finset.univ.filter fun j : S.SlimIdx_BAUGD => 0 < S.slimCutoffW_BAUGP2 j p) =
        ∅ := by
      refine Finset.filter_false_of_mem fun j _ => ?_
      rw [S.slimCutoffW_of_notMem_BAUGP2 j hq]
      exact lt_irrefl 0
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨q, rfl⟩ := hq
  have hM := S.family.slim.multiplicity q
  set A : Set (W.pieceInterior ⊤) := S.family.slim.centres ∩
    {j | q ∈ ball j (2000000 * (Δ * S.rho j))} with hA
  let F := Finset.univ.filter fun j : S.SlimIdx_BAUGD => 0 < S.slimCutoffW_BAUGP2 j q.val
  have hsub : ((F.map ⟨fun j : S.SlimIdx_BAUGD => j.1, Subtype.val_injective⟩ :
      Finset (W.pieceInterior ⊤)) : Set (W.pieceInterior ⊤)) ⊆ A := by
    intro x hx
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe] at hx
    obtain ⟨j, hjF, rfl⟩ := hx
    have hpos : 0 < S.slimCutoffW_BAUGP2 j q.val := (Finset.mem_filter.mp hjF).2
    rw [S.slimCutoffW_val_BAUGP2] at hpos
    have hd := S.mem_ball_of_mem_tsupport_slim_BAUGP2 hΔ j (subset_tsupport _ hpos.ne')
    refine ⟨(Set.Finite.mem_toFinset _).mp j.2, ?_⟩
    have hrj := S.rho_pos j.1
    change dist q j.1 < 2000000 * (Δ * S.rho j.1)
    have := mul_pos hΔ hrj
    nlinarith
  have hfin : A.Finite := S.family.slim.finite_centres.subset Set.inter_subset_left
  have hcard : (F.card : ℝ) ≤ A.ncard := by
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_map] at this
    exact_mod_cast this
  exact Nat.le_floor (hcard.trans hM)

/-- **Comparability on the slim supports**: `ζ_j(p) > 0 ⟹ 3ρ_j/4 ≤ ρ(p) ≤ 5ρ_j/4` and
`‖η_j(p)‖ ≤ 9·10⁵Δ`. -/
theorem slim_scale_comparable_BAUGP2 (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (j : S.SlimIdx_BAUGD) (p : W.Carrier) (hpos : 0 < S.slimCutoffW_BAUGP2 j p) :
    3 / 4 * S.rho j.1 ≤ S.rho p ∧ S.rho p ≤ 5 / 4 * S.rho j.1 ∧
      ‖S.slimCoordW_BAUGP2 j p‖ ≤ 9 * (10 ^ 5 * Δ) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  swap
  · rw [S.slimCutoffW_of_notMem_BAUGP2 j hq] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨q, rfl⟩ := hq
  rw [S.slimCutoffW_val_BAUGP2] at hpos
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hts : q ∈ tsupport (S.family.slim.cutoff_BCNT j.1) := subset_tsupport _ hpos.ne'
  have hd := S.mem_ball_of_mem_tsupport_slim_BAUGP2 hΔ j hts
  have hj10 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
    (S.family.slim.centres_subset hj).1
  have hΛr : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  obtain ⟨h1, h2⟩ := S.rho_comparable_of_dist_lt_BAUGP2 hΛ hΔ1 hV hβ1 hb hj10
    (by positivity) (by nlinarith) hΛr hd
  refine ⟨h1, h2, ?_⟩
  rw [S.family.slim.cutoff_BCNT_of_mem hj] at hts
  have hc := (S.family.slim.centre j.1 hj).abs_coord_le_of_mem_tsupport_BAUGP2 hts
  rw [S.slimCoordW_val_BAUGP2, norm_planeAxis]
  linarith

/-- **The slim plateau**: on the chart domain, `‖η_j‖ < 6·10⁵Δ ⟹ ζ_j = 1`. -/
theorem slimCutoffW_eq_one_BAUGP2 (hΔ : 0 < Δ) (j : S.SlimIdx_BAUGD) (p : W.Carrier)
    (hp : p ∈ S.slimDomW_BAUGP2 j) (hη : ‖S.slimCoordW_BAUGP2 j p‖ < 6 * (10 ^ 5 * Δ)) :
    S.slimCutoffW_BAUGP2 j p = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, rfl⟩ := hp
  rw [S.slimCoordW_val_BAUGP2, norm_planeAxis] at hη
  rw [S.slimCutoffW_val_BAUGP2]
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.family.slim.cutoff_BCNT_of_mem hj]
  refine (S.family.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le_BAUGP2 ?_ (by linarith)
  convert hq using 2
  norm_num

end BoundarySupplyCore

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **`ψ₂` bound to the actual map** (CFS22 on the actual slim blocks of `F_∂`, `ℓ = 10⁵Δ`; the
chain's `cutoff_bindings.2.2` verbatim with `f` for the stage input, at every `b_cut ≥ b₂`). -/
theorem cutoffTwo_binding_BAUGP2 (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (f : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hpert : ∀ p, ‖f p - S.boundaryOriginalMap p‖ ≤ 4 * cutoffKappa_BAUGP2 / 5 * S.rho p)
    (hZM : ∀ (j : S.SlimIdx_BAUGD) (p : W.Carrier), S.slimCutoffW_BAUGP2 j p = 0 →
      |S.slimMarker_BAUGD j (f p)| ≤ S.rho j.1 / 32)
    {bcut : ℝ} (hbcut : cutoffTwoConst_BAUGP2 ≤ bcut) :
    letI := inducedMetricSpace S.completion.metric
    ContDiff ℝ ∞ ((actualSlotsV2_BAUGD S).cutoff 2) ∧
      (∀ z, (actualSlotsV2_BAUGD S).cutoff 2 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 2,
          dist p j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j p| < 6 * (10 ^ 5 * Δ)) →
        (actualSlotsV2_BAUGD S).cutoff 2 (f p.val) = 1) ∧
      (∀ p : W.Carrier, f p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 2) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 2,
          dist q j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j q| < 7 * (10 ^ 5 * Δ)) ∧
      ∀ p : W.Carrier, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 2)
          ((1 - t) • S.boundaryOriginalMap p + t • f p)‖ ≤ bcut / S.rho p := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hψ : (actualSlotsV2_BAUGD S).cutoff 2 = S.cutoffTwo_BAUGD :=
    (actualSlotsV2_cutoff_BAUGD S).2.2
  have hpert' : ∀ p, ‖f p - S.boundaryOriginalMap p‖ ≤
      4 * (1 / (1000 * ((slimCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2)) / 5 * S.rho p := by
    intro p
    refine (hpert p).trans (mul_le_mul_of_nonneg_right ?_ (S.rho_pos p).le)
    have := min_le_right (1 / (1000 * ((edgeCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2))
      (1 / (1000 * ((slimCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2))
    unfold cutoffKappa_BAUGP2
    linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := cfs22_row lc87EdgeTransition_contDiff
    (fun _ ht => lc87EdgeTransition_eq_zero ht) (fun _ ht => lc87EdgeTransition_eq_one ht)
    lc87EdgeTransition_mem_Icc cgpProfileBound_spec.1 abs_deriv_lc87EdgeTransition_le_cgp
    slimCount_BAUGP2 S.slimVector_BAUGD S.slimMarker_BAUGD (fun _ => norm_blockVectorCLM_le _)
    (fun _ => norm_blockMarkerCLM_le _) hℓ (fun j : S.SlimIdx_BAUGD => S.rho j.1)
    (fun _ => S.rho_pos _) S.rho S.rho_pos S.slimDomW_BAUGP2 S.slimCoordW_BAUGP2
    S.slimCutoffW_BAUGP2 S.slimCutoffW_mem_Icc_BAUGP2 S.boundaryOriginalMap f
    (S.slimCutoffW_eq_zero_BAUGP2 hΔ) S.slimBlock_boundaryOriginalMap_BAUGP2
    (S.slim_count_BAUGP2 hΔ)
    (fun j p hp => S.slim_scale_comparable_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb j p hp)
    (fun j p hp hη => S.slimCutoffW_eq_one_BAUGP2 hΔ j p hp hη) hpert' hZM
  rw [hψ]
  refine ⟨h1, h2, fun p hp => h3 p.val ?_, fun p hp => ?_, fun p t ht => ?_⟩
  · obtain ⟨j, hj, hd, hη⟩ := hp
    have hj' : j ∈ S.family.slim.centres := hj
    let jj : S.SlimIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    refine ⟨jj, ⟨p, hd, rfl⟩, ?_⟩
    rw [S.norm_slimCoordW_val_BAUGP2 jj p]
    exact hη
  · obtain ⟨jj, ⟨q, hq, rfl⟩, hη⟩ := h4 p hp
    refine ⟨q, rfl, jj.1, (Set.Finite.mem_toFinset _).mp jj.2, hq, ?_⟩
    rw [← S.norm_slimCoordW_val_BAUGP2 jj q]
    exact hη
  · exact (h5 p t ht).trans (div_le_div_of_nonneg_right hbcut (S.rho_pos p).le)

end BoundarySupply

/-- **Consumer under BAUG-D's CHOICE**: with `b_cut = max(b₀, b₁, b₂)` and `κ = cutoffKappa_BAUGP2`
the numbers are chosen once (the `numbers` clause of `BoundaryGaf02Chain` for every `c_w ≥ 0`,
`c₂ < c_adj`); then on EVERY supply with the six register premises the three cutoff bindings hold:
`ψ₀` at `F_∂`, `ψ₁` for any stage input with value error `< c₀ρ` and the `edgeB` zero-marker clause,
`ψ₂` for any stage input with value error `< c₁ρ` and the slim zero-marker clause (derivative
budgets `≤ b_cut/ρ` along the segments from `F_∂`). -/
theorem boundaryChain_choice_cutoffs_BAUGP2 (Kj : ℕ) {cadj L₀ : ℝ} (hcadj : 0 < cadj)
    (hL : 0 ≤ L₀) :
    ∃ (Ξ c Sg eg : Fin 3 → ℝ),
      (∀ cw : Fin 3 → ℝ, (∀ j, 0 ≤ cw j) →
        ((∀ j, 0 < Ξ j ∧ 0 < Sg j ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 ≤ eg j ∧
            Sg j ≤ Ξ j / 10000 ∧ 0 ≤ cw j) ∧
          5 / 3 * Ξ 0 * Sg 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
          (5 / 3 * Ξ 0 * Sg 0 * max cutoffZeroConst_BAUGD
              (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) * L₀ + Ξ 0 * L₀ + eg 0) < c 0 ∧
          c 0 ≤ 4 * cutoffKappa_BAUGP2 / 5 ∧ c 0 ≤ 3 * Sg 1 / 10 ∧
          (c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
          ((5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * max cutoffZeroConst_BAUGD
              (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) * (L₀ + c 0) +
            Ξ 1 * (L₀ + c 0) + eg 1 + 2 * c 0) < c 1 ∧
          c 1 ≤ 4 * cutoffKappa_BAUGP2 / 5 ∧ c 1 ≤ 3 * Sg 2 / 10 ∧
          (c 1 + (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
          ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * max cutoffZeroConst_BAUGD
              (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) * (L₀ + c 1) +
            Ξ 2 * (L₀ + c 1) + eg 2 + 2 * c 1) < c 2)) ∧
      c 2 < cadj ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM),
        0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → 0 ≤ V → 0 < β 1 → 0 < b →
        (∀ p : W.Carrier, ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 0) (S.boundaryOriginalMap p)‖ ≤
          max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) /
            S.rho p) ∧
        (∀ f : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
          (∀ p, ‖f p - S.boundaryOriginalMap p‖ < c 0 * S.rho p) →
          (∀ (j : S.EdgeIdx_BAUGD) (p : W.Carrier), S.edgeCutoffW_BAUGP2 j p = 0 →
            |S.edgeMarker_BAUGD j (f p)| ≤ S.rho j.1 / 32) →
          ∀ p : W.Carrier, ∀ t ∈ Icc (0 : ℝ) 1,
            0 < S.scaleMarker_BIF ((1 - t) • S.boundaryOriginalMap p + t • f p) ∧
            ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 1)
              ((1 - t) • S.boundaryOriginalMap p + t • f p)‖ ≤
              max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) /
                S.rho p) ∧
        ∀ f : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
          (∀ p, ‖f p - S.boundaryOriginalMap p‖ < c 1 * S.rho p) →
          (∀ (j : S.SlimIdx_BAUGD) (p : W.Carrier), S.slimCutoffW_BAUGP2 j p = 0 →
            |S.slimMarker_BAUGD j (f p)| ≤ S.rho j.1 / 32) →
          ∀ p : W.Carrier, ∀ t ∈ Icc (0 : ℝ) 1,
            ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 2)
              ((1 - t) • S.boundaryOriginalMap p + t • f p)‖ ≤
              max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) /
                S.rho p := by
  have hB : 0 ≤ max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) :=
    le_max_of_le_left cutoffZeroConst_nonneg_BAUGD
  obtain ⟨-, Ξ, c, -, Sg, eg, -, -, -, -, -, -, hc2, hnum⟩ :=
    boundaryChain_choice_BAUGD Kj hcadj hB cutoffKappa_pos_BAUGP2 hL
  refine ⟨Ξ, c, Sg, eg, hnum, hc2, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ1 hΛΔ hV hβ1 hb
  have hN := hnum (fun _ => 0) (fun _ => le_rfl)
  have hc0 : c 0 ≤ 4 * cutoffKappa_BAUGP2 / 5 := hN.2.2.2.2.1
  have hc1 : c 1 ≤ 4 * cutoffKappa_BAUGP2 / 5 := hN.2.2.2.2.2.2.2.2.2.1
  have hb0 : cutoffZeroConst_BAUGD ≤
      max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) :=
    le_max_left _ _
  have hb1 : cutoffOneConst_BAUGP2 ≤
      max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hb2 : cutoffTwoConst_BAUGP2 ≤
      max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(S.cutoffZero_binding_of_le_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb hb0).2.2.2.2,
    fun f herr hZM => ?_, fun f herr hZM => ?_⟩
  · have hpert : ∀ p, ‖f p - S.boundaryOriginalMap p‖ ≤ 4 * cutoffKappa_BAUGP2 / 5 * S.rho p :=
      fun p => (herr p).le.trans (mul_le_mul_of_nonneg_right hc0 (S.rho_pos p).le)
    exact (S.cutoffOne_binding_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb f hpert hZM hb1).2.2.2.2
  · have hpert : ∀ p, ‖f p - S.boundaryOriginalMap p‖ ≤ 4 * cutoffKappa_BAUGP2 / 5 * S.rho p :=
      fun p => (herr p).le.trans (mul_le_mul_of_nonneg_right hc1 (S.rho_pos p).le)
    exact (S.cutoffTwo_binding_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb f hpert hZM hb2).2.2.2.2

end DifferentialGeometry.Geometry.Collapse
