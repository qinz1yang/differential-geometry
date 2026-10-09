import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimQ3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBF
import DifferentialGeometry.Geometry.Fibration.ActualModelMarkerPlanes
import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneData
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneFullMarker

/-!
# Facts on SGP04's full model graph and the zero blocks on the boundary family (lane B-PORT-SLIMb)

Hand-written ports (no closed compactness is used) of the model-graph facts that the slim stage
table reads, on the ported model `sgpFullGraph_BAUGP L Z` (G2a, `L : LocalPacketsOnB`,
`Z : ZeroModelFamilyOn`) and the boundary family `LocalPacketsOnBF`:

* `sgpFullGraph_blockRestrict_BPS` — the model is `Q₃`-valued (twin `sgpFullGraph_blockRestrict_GAF3`);
* `sgpFullGraph_marker_fderiv_BPS` — the slim marker of `j` annihilates `DΦ_i(a)` when `j = i`, `j` is
  unlisted, or its argument lies in the plateau (twin `sgpFullGraph_marker_fderiv_GAFS`);
* `sgpFullGraph_slim_block_eq_zero_BPS`, `sgpFullGraph_circle_block_BPS`, `sgpFullGraph_edge_block_BPS`
  — the whole block of a small slim marker (`ρ(j) ≤ .99ρ(i)`), of every circle and edge tag is zero
  (twins `SlimStagePlanes_PLN.small_block_zero`, `sgpFullGraph_smallMarker_GAF4`);
* `sgpFullGraph_zero_block_of_not_meets_BPS` — the zero block of a zero support missing `D_i`;
* `fderiv_block_eq_zero_of_block_zero_BPS` (generic) — a vanishing block has vanishing derivative;
* `zero_cutoff_ratio_BPS`, `zsp01_original_zero_block_BPS` — LPA05 on the zero supports and ZSP01's
  original zero block (twins `zero_cutoff_ratio_GAF`, `zsp01_original_zero_block`), from the boundary
  family's own `zero_local_comparison` and the band `zero_cutoff_tsupport_band_BCNT`.
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

section Generic

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A block that vanishes identically has vanishing derivative: `(DΦ(a)h)_t = 0`. -/
theorem fderiv_block_eq_zero_of_block_zero_BPS [Finite κ] (Φ : E → BlockSpace V) (t : κ)
    (h0 : ∀ u, Φ u t = 0) (a h : E) : fderiv ℝ Φ a h t = 0 := by
  have := Fintype.ofFinite κ
  by_cases hd : DifferentiableAt ℝ Φ a
  · have h1 : HasFDerivAt (fun u => blockProjCLM_PLN (V := V) t (Φ u))
        ((blockProjCLM_PLN (V := V) t).comp (fderiv ℝ Φ a)) a :=
      (blockProjCLM_PLN (V := V) t).hasFDerivAt.comp a hd.hasFDerivAt
    have hfun : (fun u => blockProjCLM_PLN (V := V) t (Φ u)) = fun _ => 0 := funext h0
    rw [hfun] at h1
    have h3 := h1.unique (hasFDerivAt_const 0 a)
    have h4 := congrArg (fun L : E →L[ℝ] WithLp 2 (V t × ℝ) => L h) h3
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      zero_apply] at h4
    rw [blockProjCLM_apply_PLN] at h4
    exact h4
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

end Generic

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

open Classical in
/-- SGP04's full model graph is `Q₃`-valued: `π_{Q₃}(Φ_i(u)) = Φ_i(u)`. -/
theorem sgpFullGraph_blockRestrict_BPS (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (u : ℝ) :
    blockRestrict (cgpQ3Tags_BPS L Z) (sgpFullGraph_BAUGP L Z i sgn c zsgn zc u) =
      sgpFullGraph_BAUGP L Z i sgn c zsgn zc u := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · rw [sgpFullGraph_apply_BAUGP]
    rcases t with j | j | j | j | j
    · rfl
    · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
    · rfl
    · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
    · rfl

/-- **GAF04's plane half for SGP04's model** (slim tags): the marker of the slim block `j` of
`Φ_i = sgpFullGraph_BAUGP` annihilates `DΦ_i(a)` when `j = i`, `j` is unlisted, or listed with
`|s_j⁻¹(sgn_j a + c_j)| < 8·10⁵Δ` (`s_j = ρ(j)/ρ(i)`). -/
theorem sgpFullGraph_marker_fderiv_BPS (hΔ : 0 < Δ) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (j : L.slim.finite_centres.toFinset) (a : ℝ)
    (hplat : j ≠ i → j.1 ∈ sgpSlimList_BAUGP L.slim i.1 →
      |(ρ j.1 / ρ i.1)⁻¹ * (sgn j.1 * a + c j.1)| < 8 * (10 ^ 5 * Δ)) (h : ℝ) :
    blockMarkerCLM (.inr (.inl j) : CGPTag_BAUGP L Z)
      (fderiv ℝ (sgpFullGraph_BAUGP L Z i sgn c zsgn zc) a h) = 0 := by
  classical
  have hΦ : DifferentiableAt ℝ (sgpFullGraph_BAUGP L Z i sgn c zsgn zc) a :=
    ((contDiff_sgpFullGraph_BAUGP L Z i sgn c zsgn zc).differentiable (by simp)) a
  have hval : ∀ y, sgpFullGraph_BAUGP L Z i sgn c zsgn zc y (.inr (.inl j)) =
      sgpSlimModelBlock_BAUGP L i sgn c j y := fun _ => rfl
  by_cases hji : j = i
  · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 1) _ hΦ (Eventually.of_forall fun y => ?_) h
    dsimp only
    rw [hval]
    simp only [sgpSlimModelBlock_BAUGP, hji, ite_true]
    rfl
  · by_cases hS : j.1 ∈ sgpSlimList_BAUGP L.slim i.1
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := ρ j.1 / ρ i.1) _ hΦ ?_ h
      have hℓ : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
      have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ρ j.1 / ρ i.1)
        (r := 8 * (10 ^ 5 * Δ)) (φ := sgpProfile (10 ^ 5 * Δ))
        (fun z hz => sgpProfile_eq_one hℓ (by rwa [Real.norm_eq_abs] at hz))
        (u := fun y => sgn j.1 * y + c j.1)
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt
        (by rw [smul_eq_mul, Real.norm_eq_abs]; exact hplat hji hS)
      filter_upwards [hev] with y hy
      rw [hval]
      simp only [sgpSlimModelBlock_BAUGP, hji, hS, ite_true, ite_false]
      exact hy
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 0) _ hΦ (Eventually.of_forall fun y => ?_) h
      dsimp only
      rw [hval]
      simp only [sgpSlimModelBlock_BAUGP, hji, hS, ite_false]
      rfl

/-- **Whole small slim block** (CGP04): a slim tag `j` with `ρ(j) ≤ .99ρ(i)` is neither the own tag
nor listed (listed tags have ratio `> 99/100`), so the WHOLE block of `Φ_i` vanishes. -/
theorem sgpFullGraph_slim_block_eq_zero_BPS (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (j : L.slim.finite_centres.toFinset)
    (hj : ρ j.1 ≤ 99 / 100 * ρ i.1) (u : ℝ) :
    sgpFullGraph_BAUGP L Z i sgn c zsgn zc u (.inr (.inl j)) = 0 := by
  classical
  have hri := hρ i.1
  have hji : j ≠ i := by
    rintro rfl
    linarith [hρ j.1]
  have hS : j.1 ∉ sgpSlimList_BAUGP L.slim i.1 := by
    intro hS
    have h1 := (sgpSlimList_bounds_BAUGP L hΔ hΛ hLΛ hS).2.1
    have h2 := (lt_div_iff₀ hri).mp h1
    linarith
  change sgpSlimModelBlock_BAUGP L i sgn c j u = 0
  unfold sgpSlimModelBlock_BAUGP
  rw [ite_eq_right hji, ite_eq_right hS]

/-- The circle blocks of `Φ_i` vanish. -/
theorem sgpFullGraph_circle_block_BPS (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (j : L.circle.finite_centres.toFinset) (u : ℝ) :
    sgpFullGraph_BAUGP L Z i sgn c zsgn zc u (.inl j) = 0 :=
  rfl

/-- The `edgeB` blocks of `Φ_i` vanish. -/
theorem sgpFullGraph_edge_block_BPS (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (j : L.edgeB.finite_centres.toFinset) (u : ℝ) :
    sgpFullGraph_BAUGP L Z i sgn c zsgn zc u (.inr (.inr (.inl j))) = 0 :=
  rfl

/-- The zero block of a zero support missing `D_i` vanishes. -/
theorem sgpFullGraph_zero_block_of_not_meets_BPS (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (k : Z.finite_centres.toFinset)
    (habs : ¬ sgpZeroMeets_BAUGP Z (Δ := Δ) (ρ := ρ) i.1 k.1 ((Set.Finite.mem_toFinset _).mp k.2))
    (u : ℝ) : sgpFullGraph_BAUGP L Z i sgn c zsgn zc u (.inr (.inr (.inr (.inl k)))) = 0 := by
  classical
  change sgpZeroModelBlock_BAUGP L Z i zsgn zc k u = 0
  unfold sgpZeroModelBlock_BAUGP
  rw [ite_eq_right habs]

/-- The slim block of the ported map: `𝓔⁰(q)_i = (ρ(i)ζ_i(q) η_i(q), ρ(i)ζ_i(q))`. -/
theorem cgpGlobalMap_slim_block_BPS (i : L.slim.finite_centres.toFinset) (q : X) :
    cgpGlobalMap_BAUGP L Z q (.inr (.inl i)) =
      WithLp.toLp 2 ((ρ i.1 * L.slim.cutoff_BCNT i.1 q) •
        planeAxis ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord_BCG2 q),
        ρ i.1 * L.slim.cutoff_BCNT i.1 q) :=
  rfl

/-- **SGP06, the own coordinate** (twin `sgp06_own_coordinate_SGP5`): a `1`-Lipschitz functional `P`
(the first axis coordinate of the own block of `i`) with `P ∘ Φ_i = id` and
`P(ρ(i)⁻¹π₃𝓔⁰(q)) = η_i(q)` wherever the slim cutoff of `i` is `1`. -/
theorem sgp06_own_coordinate_BPS (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) :
    ∃ Pc : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) →L[ℝ] ℝ, (∀ z, ‖Pc z‖ ≤ ‖z‖) ∧
      (∀ u, Pc (sgpFullGraph_BAUGP L Z i sgn c zsgn zc u) = u) ∧
      ∀ q, L.slim.cutoff_BCNT i.1 q = 1 →
        Pc ((ρ i.1)⁻¹ • cgpProjMap_BPS L Z (cgpQ3Tags_BPS L Z) q) =
          (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord_BCG2 q := by
  let f : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) →ₗ[ℝ] ℝ :=
    { toFun := fun z => (z (.inr (.inl i))).fst 0
      map_add' := fun z w => by simp
      map_smul' := fun a z => by simp }
  have hf : ∀ z, ‖f z‖ ≤ 1 * ‖z‖ := by
    intro z
    rw [one_mul]
    calc ‖f z‖ = ‖(z (.inr (.inl i))).fst 0‖ := rfl
      _ ≤ ‖(z (.inr (.inl i))).fst‖ := PiLp.norm_apply_le _ 0
      _ ≤ ‖z (.inr (.inl i))‖ := WithLp.norm_fst_le _ _
      _ ≤ ‖z‖ := PiLp.norm_apply_le _ _
  refine ⟨f.mkContinuous 1 hf, fun z => ?_, fun u => ?_, fun q hq => ?_⟩
  · rw [LinearMap.mkContinuous_apply]
    simpa using hf z
  · rw [LinearMap.mkContinuous_apply]
    change (sgpFullGraph_BAUGP L Z i sgn c zsgn zc u (.inr (.inl i))).fst 0 = u
    rw [sgpFullGraph_own_BAUGP]
    simp [planeAxis_apply]
  · rw [LinearMap.mkContinuous_apply]
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have h1 : cgpProjMap_BPS L Z (cgpQ3Tags_BPS L Z) q (.inr (.inl i)) =
        cgpGlobalMap_BAUGP L Z q (.inr (.inl i)) :=
      cgpProjMap_apply_of_mem_BPS L Z (cgpQ3Tags_slim_mem_BPS L Z i) q
    change (((ρ i.1)⁻¹ • cgpProjMap_BPS L Z (cgpQ3Tags_BPS L Z) q) (.inr (.inl i))).fst 0 = _
    rw [PiLp.smul_apply, h1, cgpGlobalMap_slim_block_BPS, hq, mul_one]
    have hc : (ρ i.1)⁻¹ * (ρ i.1 * (L.slim.centre i.1 hi).coord_BCG2 q) =
        (L.slim.centre i.1 hi).coord_BCG2 q := by
      rw [← mul_assoc, inv_mul_cancel₀ (hρ i.1).ne', one_mul]
    simpa [planeAxis_apply] using hc

/-- **(FM*)'s plane half from a (TG) value bound** (closed `SlimStagePlanes_PLN.full_marker`, plateau
step): if `‖ρ(a)⁻¹y − Φ_a(u)‖ < e` with `e < 1/100`, the `i`-block of `y` is the full block
`(ρ(i)·1 η, ρ(i)·1)` with `|η| ≤ (351/49)ℓ` and `ρ(i)/ρ(a) ≥ 99/100`, then the slim marker of `i`
annihilates `DΦ_a(u)`. -/
theorem sgpFullGraph_marker_fderiv_of_close_BPS (hΔ : 0 < Δ) (i a : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) {y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)} {u η eg : ℝ}
    (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) (hs : 99 / 100 ≤ ρ i.1 / ρ a.1)
    (hη : |η| ≤ 351 / 49 * (10 ^ 5 * Δ)) (hℓ : 1 ≤ 10 ^ 5 * Δ)
    (hTG : ‖(ρ a.1)⁻¹ • y - sgpFullGraph_BAUGP L Z a sgn c zsgn zc u‖ < eg)
    (hy : y (.inr (.inl i)) = WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis η, ρ i.1 * 1)) (v : ℝ) :
    ((fderiv ℝ (sgpFullGraph_BAUGP L Z a sgn c zsgn zc) u v) (.inr (.inl i))).snd = 0 := by
  classical
  have hnum := plateau_numbers_PLN hℓ (s := ρ i.1 / ρ a.1) hs heg0 heg
  have hplat : i ≠ a → i.1 ∈ sgpSlimList_BAUGP L.slim a.1 →
      |(ρ i.1 / ρ a.1)⁻¹ * (sgn i.1 * u + c i.1)| < 8 * (10 ^ 5 * Δ) := by
    intro hia hlist
    have hmt : sgpFullGraph_BAUGP L Z a sgn c zsgn zc u (.inr (.inl i)) =
        sgpBlockEmbed (sgpModelBlock (10 ^ 5 * Δ) (ρ i.1 / ρ a.1) (sgn i.1 * u + c i.1)) := by
      change sgpSlimModelBlock_BAUGP L a sgn c i u = _
      simp only [sgpSlimModelBlock_BAUGP, hia, hlist, ite_true, ite_false]
    have hcl := embed_block_close_PLN _ hTG hy hmt
    have harg := scaledCutoffBlock_arg_lt_of_close_PLN (div_pos (hρ i.1) (hρ a.1)) hnum.1
      (by rw [Real.norm_eq_abs]; exact hη) hcl hnum.2
    rw [smul_eq_mul, Real.norm_eq_abs] at harg
    exact harg
  exact sgpFullGraph_marker_fderiv_BPS L Z hΔ a sgn c zsgn zc i u hplat v

/-- **A small slim block of SGP04's model is zero** (block level): `ρ(j) ≤ .99ρ(i)` excludes the own tag
and the listed tags. -/
theorem sgpSlimModelBlock_eq_zero_of_small_BPS (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset) (sgn c : X → ℝ)
    (j : L.slim.finite_centres.toFinset) (hj : ρ j.1 ≤ 99 / 100 * ρ i.1) (u : ℝ) :
    sgpSlimModelBlock_BAUGP L i sgn c j u = 0 := by
  classical
  have hri := hρ i.1
  have hji : j ≠ i := by
    rintro rfl
    linarith [hρ j.1]
  have hS : j.1 ∉ sgpSlimList_BAUGP L.slim i.1 := by
    intro hS
    have h1 := (sgpSlimList_bounds_BAUGP L hΔ hΛ hLΛ hS).2.1
    have h2 := (lt_div_iff₀ hri).mp h1
    linarith
  unfold sgpSlimModelBlock_BAUGP
  rw [ite_eq_right hji, ite_eq_right hS]

end Model

section Zero

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricNBF_BPSm
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalPacketsOnBF`, as a named local instance. -/
local instance instChartedNBF_BPSm
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricCBF_BPSm
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LPA05 on the zero supports** of the boundary family: on the closed support of LC31's annular
cutoff of the zero ball at `c`, `ρ(p) ≤ 20R_c/T` (`e < 1/40`). -/
theorem zero_cutoff_ratio_BPS
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (hT : 0 < T) (he : e < 1 / 40) {c : X} (hc : c ∈ P.zero.centres) {p : X}
    (hp : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero c hc).radial y))) :
    ρ p ≤ 20 * (P.zero.zero c hc).radius / T := by
  have hband := zero_cutoff_tsupport_band_BCNT P.zero he hc hp
  have hr := (P.zero.zero c hc).radius_pos
  have hcp : dist c p ≤ 10 * (P.zero.zero c hc).radius := by linarith [hband.2]
  have hratio := P.zero_local_comparison c hc p hcp
  have hρp := hρ p
  rw [le_div_iff₀ hρp] at hratio
  rw [le_div_iff₀ hT]
  linarith

/-- **ZSP01 (ZI), original half** on the boundary family: if `20R_c/T < ρ(p)` the WHOLE zero block of
`𝓔⁰(p)` at the zero ball of `c` vanishes. -/
theorem zsp01_original_zero_block_BPS
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (hT : 0 < T) (he : e < 1 / 40) (i : P.zero.finite_centres.toFinset)
    {p : X} (hρp : 20 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero p (.inr (.inr (.inr (.inl i)))) = 0 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcut :
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p) = 0 := by
    by_contra h
    have hmem : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero i.1 hi).radial y)) := subset_tsupport _ h
    have := zero_cutoff_ratio_BPS P hT he hi hmem
    linarith
  change WithLp.toLp 2 ((cgpRadius_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) •
      cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p,
    cgpRadius_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) = 0
  rw [hcut, mul_zero, zero_smul]
  rfl

end Zero

end DifferentialGeometry.Geometry.Collapse
