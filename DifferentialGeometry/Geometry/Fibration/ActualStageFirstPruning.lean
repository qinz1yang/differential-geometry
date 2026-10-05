import DifferentialGeometry.Geometry.Fibration.ActualFirstCloud
import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers

/-!
# CFS27's pruning of TCP05's first-cloud graphs (small markers at stage `0`)

Blueprint `master207B.tex`, CFS27 (B:3626–3686): from a reference chart's model delete every
retained block whose radius is at most half the reference radius; the pruned model has the same
own block, the same `C²` bounds and the same (TG) comparisons on the reference chart domain, and
its planes lie in the kernels of the deleted markers (rule (PP)).

TCP05's graph `Φ_i` (`tcp05_row`) is opaque: only its own block, its `C²` bounds and (TG) are
known. Pruning with `K_i = π_{keep_i}` (`keep_i` = all tags except the retained markers `a` with
`ρ(c_a) ≤ ρ(i)/2`): on `B(i, 200ρ(i))` every deleted block of `𝓔⁰` is zero (a positive cutoff of
such a marker forces `ρ ≤ 5ρ(i)/8`, while `ρ ≥ 3ρ(i)/4` on the chart domain), so `K_i𝓔⁰ = 𝓔⁰`
there, and `K_i ∘ Φ_i` satisfies all of TCP05's clauses.

* `clm_mvfderiv_eq_of_eventuallyEq_GAF5`: a linear map fixing `f` near `x` fixes `df_x`.
* `clm_comp_bounds_GAF5`: postcomposition with `‖A‖ ≤ 1` keeps `C²` bounds.
* `firstKeepTags_GAF5`, `firstKeep_own_GAF5`, `firstKeep_marker_GAF5`: the kept tags.
* `firstPrune_globalMap_GAF5`, `firstPrune_mvfderiv_GAF5`: `K_i𝓔⁰ = 𝓔⁰` and `K_i d𝓔⁰ = d𝓔⁰` on
  `B(i, 200ρ(i))`.
* `tcp05_pruned_GAF5`: TCP05's data at every circle centre gives pruned data with all of TCP05's
  clauses AND `v_a ∘ DΦ_i = 0` for every retained marker with `ρ(c_a) ≤ ρ(i)/2`.
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

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_GAF5 : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map that fixes `f` near `x` fixes the derivative of `f` at `x`. -/
theorem clm_mvfderiv_eq_of_eventuallyEq_GAF5 (A : F →L[ℝ] F) {f : M → F} {x : M}
    (h : (fun y => A (f y)) =ᶠ[𝓝 x] f) (v : TangentSpace I x) :
    A (mvfderiv I f x v) = mvfderiv I f x v := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, F) f x
  · rw [← mvfderiv_clm_comp hf A v, mvfderiv_apply_LC, mvfderiv_apply_LC,
      Filter.EventuallyEq.mfderiv_eq h]
    rfl
  · rw [mvfderiv_apply_LC, mfderiv_zero_of_not_mdifferentiableAt hf]
    exact map_zero A

/-- Postcomposition with a continuous linear map of norm at most one keeps `C²` bounds (any
domain). -/
theorem clm_comp_bounds_GAF5 {G K : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K] (A : G →L[ℝ] K) (hA : ‖A‖ ≤ 1) {h : E → G}
    (hh : ContDiff ℝ 2 h) {B : ℝ} (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B)
    (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B) (a : E) :
    ‖fderiv ℝ (A ∘ h) a‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (A ∘ h)) a‖ ≤ B := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hDh : Differentiable ℝ (fderiv ℝ h) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hh).2.2.differentiable (by norm_num)
  have hDA : fderiv ℝ A = fun _ => A := funext fun y => A.fderiv
  have hDDA : fderiv ℝ (fderiv ℝ A) (h a) = 0 := by
    rw [hDA]
    exact fderiv_const_apply A
  have hB : 0 ≤ B := (norm_nonneg _).trans (h1 a)
  constructor
  · rw [fderiv_comp a A.differentiableAt (hhd a), A.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hA (h1 a) (norm_nonneg _) zero_le_one).trans (by linarith))
  · have hDAd : DifferentiableAt ℝ (fderiv ℝ A) (h a) := by
      rw [hDA]
      exact differentiableAt_const A
    refine (norm_second_fderiv_comp_le A.differentiable hhd hDAd (hDh a)).trans ?_
    rw [hDDA, norm_zero, zero_mul, zero_add, A.fderiv]
    exact (mul_le_mul hA (h2 a) (norm_nonneg _) zero_le_one).trans (by linarith)

end Generic

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- CFS27's kept tags at reference radius `r`: every tag except the retained markers `a` with
`ρ(c_a) ≤ r/2`. -/
def firstKeepTags_GAF5 (r : ℝ) : Finset (CGPTag L Z) :=
  Finset.univ.filter fun t => ∀ a : CGPMarkerIndex L, cgpMarkerTag L Z a = t →
    r / 2 < ρ (cgpMarkerCentre L a)

open Classical in
/-- The own circle tag of a centre `j` is kept at the reference radius `ρ(j)`. -/
theorem firstKeep_own_GAF5 (j : L.circle.finite_centres.toFinset) :
    (.inl j : CGPTag L Z) ∈ firstKeepTags_GAF5 L Z (ρ j.1) := by
  rw [firstKeepTags_GAF5, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
  have hr := hρ j.1
  rcases a with j' | j' | j'
  · have hj : j' = j := Sum.inl_injective ha
    subst hj
    change ρ j'.1 / 2 < ρ j'.1
    linarith
  · exact absurd ha (by simp [cgpMarkerTag])
  · exact absurd ha (by simp [cgpMarkerTag])

open Classical in
/-- A retained marker with `ρ(c_a) ≤ r/2` is deleted. -/
theorem firstKeep_marker_GAF5 {r : ℝ} (a : CGPMarkerIndex L)
    (ha : ρ (cgpMarkerCentre L a) ≤ r / 2) : cgpMarkerTag L Z a ∉ firstKeepTags_GAF5 L Z r := by
  rw [firstKeepTags_GAF5, Finset.mem_filter]
  rintro ⟨-, h⟩
  exact absurd (h a rfl) (not_lt.mpr ha)

open Classical in
/-- The marker of a deleted block vanishes on the range of the pruning. -/
theorem firstPrune_marker_GAF5 {r : ℝ} (a : CGPMarkerIndex L)
    (ha : ρ (cgpMarkerCentre L a) ≤ r / 2) (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    blockMarkerCLM (cgpMarkerTag L Z a) (blockRestrict (firstKeepTags_GAF5 L Z r) y) = 0 := by
  rw [blockMarkerCLM_apply, blockRestrict_apply, ite_eq_right (firstKeep_marker_GAF5 L Z a ha)]
  rfl

open Classical in
/-- **The pruning fixes `𝓔⁰` on the chart domain** `B(i, 200ρ(i))` (`Λ·200 ≤ 1/4`): every deleted
block of `𝓔⁰(x)` is zero there. -/
theorem firstPrune_globalMap_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4) {i x : X}
    (hx : x ∈ ball i (200 * ρ i)) :
    blockRestrict (firstKeepTags_GAF5 L Z (ρ i)) (cgpGlobalMap L Z x) = cgpGlobalMap L Z x := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · rw [firstKeepTags_GAF5, Finset.mem_filter] at ht
    push Not at ht
    obtain ⟨a, rfl, ha⟩ := ht (Finset.mem_univ _)
    have hcut : cgpMarkerCutoff L a x = 0 := by
      by_contra hne
      have h1 := cgpMarkerCutoff_scale_lip_GAF4 L hΔ hΛ hsmall a x hne
      have h2 := scale_mem_of_dist_lt_KC L.lipschitz_scale hΛ (hρ i) (mem_ball.mp hx) hΛ200
      have hri := hρ i
      linarith [h1.2, h2.1]
    have hb := cgpGlobalMap_markerBlock_GAF2 L Z a x
    rw [hcut, mul_zero, zero_smul] at hb
    rw [blockVectorCLM_apply] at hb
    rw [blockMarkerCLM_apply] at hb
    symm
    apply WithLp.ofLp_injective
    exact Prod.ext hb.1 hb.2

open Classical in
/-- **The pruning fixes `d𝓔⁰` on the chart domain** `B(i, 200ρ(i))`. -/
theorem firstPrune_mvfderiv_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4) {i x : X}
    (hx : x ∈ ball i (200 * ρ i)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    blockRestrict (firstKeepTags_GAF5 L Z (ρ i)) (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) x w) =
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) x w :=
  clm_mvfderiv_eq_of_eventuallyEq_GAF5 _
    (Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun _ hy =>
      firstPrune_globalMap_GAF5 L Z hΔ hΛ hsmall hΛ200 hy) w

end Family

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF5p
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5p
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5p
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP05 with CFS27's pruning.** With `1 ≤ Δ`, `0 ≤ Λ`, `Λ·10⁶Δ ≤ 1/4`, `Λ·200 ≤ 1/4`: TCP05's
data at every circle centre `i` (a smooth `Φ_i` with own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` and
(TG) on `{‖η_i‖ ≤ 8} ∩ B(i, 200ρ(i))` with error `e`) gives data with the same clauses whose
derivative is annihilated by the marker of every retained block with `ρ(c_a) ≤ ρ(i)/2`
(`Φ_i' = π_{keep_i} ∘ Φ_i`). -/
theorem tcp05_pruned_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4)
    {eg : ℝ}
    (hTCP : ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ i / 2 → ∀ u v,
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0 := by
  classical
  intro i hi
  refine Exists.elim (hTCP i hi) (fun Φ hΦ => ?_)
  have hsm : ContDiff ℝ ∞ Φ := hΦ.1
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hd : Differentiable ℝ Φ := hsm.differentiable (by simp)
  let Kp := blockRestrict (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
  have hD : ∀ u, fderiv ℝ (Kp ∘ Φ) u = Kp.comp (fderiv ℝ Φ u) := fun u => by
    rw [fderiv_comp u Kp.differentiableAt (hd u), Kp.fderiv]
  refine ⟨Kp ∘ Φ, Kp.contDiff.comp hsm, fun j hj a => ?_,
    fun a => clm_comp_bounds_GAF5 Kp (norm_blockRestrict_le _) hsm2 (fun y => (hΦ.2.2.1 y).1)
      (fun y => (hΦ.2.2.1 y).2) a, fun x hx hx8 => ⟨?_, fun w => ?_⟩, fun a ha u v => ?_⟩
  · change blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i)) (Φ a) (.inl j) = _
    have hk : (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈
        firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i) := by
      rw [← hj]
      exact firstKeep_own_GAF5 P.toLocalChartFamily P.zero j
    rw [blockRestrict_apply, ite_eq_left hk]
    exact hΦ.2.1 j hj a
  · have hfix := firstPrune_globalMap_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall hΛ200 hx
    have h1 : (ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
        (Kp ∘ Φ) (cgpCircleCoord P.toLocalChartFamily i hi x) =
        Kp ((ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
          Φ (cgpCircleCoord P.toLocalChartFamily i hi x)) := by
      rw [map_sub, map_smul]
      change _ = (ρ i)⁻¹ • blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
        (cgpGlobalMap P.toLocalChartFamily P.zero x) - _
      rw [hfix]
      rfl
    rw [h1]
    exact lt_of_le_of_lt (norm_blockRestrict_apply_le _ _) (hΦ.2.2.2 x hx hx8).1
  · have hfix := firstPrune_mvfderiv_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall hΛ200 hx w
    have h1 : (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
        fderiv ℝ (Kp ∘ Φ) (cgpCircleCoord P.toLocalChartFamily i hi x)
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) =
        Kp ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
          fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)) := by
      rw [hD, map_sub, map_smul]
      change _ = (ρ i)⁻¹ • blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
        (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w) - _
      rw [hfix]
      rfl
    rw [h1]
    exact (norm_blockRestrict_apply_le _ _).trans ((hΦ.2.2.2 x hx hx8).2 w)
  · rw [hD]
    exact firstPrune_marker_GAF5 P.toLocalChartFamily P.zero a ha _

end Packets

end DifferentialGeometry.Geometry.Collapse
