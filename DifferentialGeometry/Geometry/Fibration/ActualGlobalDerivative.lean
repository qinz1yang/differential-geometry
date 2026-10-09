import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgetsApplications
import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacketApplications
import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.GlobalBlockDerivative

/-!
# CGP02: the early derivative constant of the actual global map `𝓔⁰`

Blueprint `master207B.tex`, CGP02 (`prop:fibration-actual-global-derivative`, B:3956–4002):
"Let `N ≥ 1` be LPA06's early nonzero-family multiplicity bound, and `P₀ ≥ 1` bound the first
derivatives of the fixed unit profiles. Retain `Δ ≥ 1`. The original map in CGP01 satisfies
`‖DF‖ ≤ L₀ := 1000 (N + 2) P₀²`. This constant is fixed before `Δ`, noncollapse, the total number of
charts and the global scale range."

On the final LC87 family `P : LocalChartPackets` (`𝓔⁰ = cgpGlobalMap P.toLocalChartFamily P.zero`):

* `cgp_active_tags_ncard_le`: the number of circle, slim, edge and zero tags whose cutoff's closed
  support contains `x` is at most FC07's count of the supports meeting `B(x, 10ρ(x))`;
* `cgp_active_tags_ncard_le_fc07`, `cgp_active_edge_card_le_fc07`: hence at most `fc07ActiveBound`
  (`N`, numerical);
* `cgp02_row`: `‖d𝓔⁰(v)‖ ≤ 1000 (N + 2) P₀² √(g_x(v, v))` for every tangent vector, with
  `N = fc07ActiveBound` and `P₀ = cgpProfileBound`, both numerical (fixed before `Δ`, noncollapse,
  the number of charts and the scale range), from FC02 on the manifold
  (`norm_mvfderiv_blockMap_apply_le_fc02`), the block budgets of CGP02 (b) and
  `GlobalBlockDerivative.early_derivative_constant`.

Parameter ranges used (all are parameter choices, no conclusion is assumed): FC07's
(`Δ ≥ 1`, `μ, τ ≤ 1/100`, `10⁶ΔΛ < 10⁻⁵`, `Lmax`, `e < 1/40`, `T`) and `σ_s, σ_c, γ_c, ε_r ∈ [0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- Subtype elements of a finite set whose property holds have at most as many elements as the
corresponding subset of the ambient type. -/
theorem ncard_subtype_le_KA2 {Y : Type*} {S : Set Y} (hS : S.Finite) {p : Y → Prop}
    {q : Y → Prop} (hpq : ∀ y ∈ S, p y → q y) :
    {i : hS.toFinset | p i}.ncard ≤ {y | y ∈ S ∧ q y}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  refine Set.ncard_le_ncard ?_ (hS.subset fun _ hy => hy.1)
  rintro _ ⟨i, hi, rfl⟩
  have hiS := (Set.Finite.mem_toFinset _).mp i.2
  exact ⟨hiS, hpq i.1 hiS hi⟩

/-- **The active tags of `𝓔⁰` at `x`** (circle, slim, edge, zero tags whose cutoff's closed support
contains `x`) are at most FC07's count of the supports meeting `B(x, 10ρ(x))`. -/
theorem cgp_active_tags_ncard_le
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (x : X) :
    ({i : CGPTag P.toLocalChartFamily P.zero | i ≠ cgpScaleTag P.toLocalChartFamily P.zero ∧
        i ≠ cgpEdgeTag P.toLocalChartFamily P.zero ∧
        x ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero i)}.ncard : ℝ) ≤
      ({j | j ∈ P.circle.centres ∧
          (tsupport (P.circle.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard : ℝ) +
        {j | j ∈ P.slim.centres ∧
          (tsupport (P.slim.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard +
        {j | j ∈ P.edge.centres ∧
          (tsupport (P.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard +
        (zeroMeetingList P.zero x 10).ncard := by
  have hx : x ∈ ball x (10 * ρ x) := mem_ball_self (mul_pos (by norm_num) (hρ x))
  set L := P.toLocalChartFamily with hL
  set Z := P.zero with hZ
  let SC : Set L.circle.finite_centres.toFinset := {j | x ∈ tsupport (L.circle.cutoff j)}
  let SS : Set L.slim.finite_centres.toFinset := {j | x ∈ tsupport (L.slim.cutoff j)}
  let SE : Set L.edge.finite_centres.toFinset := {j | x ∈ tsupport (L.edge.cutoff j)}
  let SZ : Set Z.finite_centres.toFinset := {i | x ∈ tsupport (fun y =>
    Calculus.annularCutoff Calculus.cutoffProfile
      ((Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial y))}
  let fC : L.circle.finite_centres.toFinset → CGPTag L Z := Sum.inl
  let fS : L.slim.finite_centres.toFinset → CGPTag L Z := fun j => Sum.inr (Sum.inl j)
  let fE : L.edge.finite_centres.toFinset → CGPTag L Z := fun j => Sum.inr (Sum.inr (Sum.inl j))
  let fZ : Z.finite_centres.toFinset → CGPTag L Z :=
    fun i => Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
  have hsub : {i : CGPTag L Z | i ≠ cgpScaleTag L Z ∧ i ≠ cgpEdgeTag L Z ∧
      x ∈ tsupport (cgpCutoff L Z i)} ⊆ fC '' SC ∪ fS '' SS ∪ fE '' SE ∪ fZ '' SZ := by
    rintro (j | j | j | i | bb) ⟨h1, h2, h3⟩
    · exact Or.inl (Or.inl (Or.inl ⟨j, h3, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨j, h3, rfl⟩))
    · exact Or.inl (Or.inr ⟨j, h3, rfl⟩)
    · exact Or.inr ⟨i, h3, rfl⟩
    · cases bb
      · exact absurd rfl h1
      · exact absurd rfl h2
  have h1 := Set.ncard_le_ncard hsub
  have h2 := (Set.ncard_union_le (fC '' SC ∪ fS '' SS ∪ fE '' SE) (fZ '' SZ)).trans
    (Nat.add_le_add_right ((Set.ncard_union_le (fC '' SC ∪ fS '' SS) (fE '' SE)).trans
      (Nat.add_le_add_right (Set.ncard_union_le (fC '' SC) (fS '' SS)) _)) _)
  have hC : (fC '' SC).ncard ≤ {j | j ∈ P.circle.centres ∧
      (tsupport (P.circle.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard :=
    (Set.ncard_image_le).trans (ncard_subtype_le_KA2 L.circle.finite_centres
      (p := fun y => x ∈ tsupport (P.circle.cutoff y))
      (q := fun y => (tsupport (P.circle.cutoff y) ∩ ball x (10 * ρ x)).Nonempty)
      fun _ _ hy => ⟨x, hy, hx⟩)
  have hS : (fS '' SS).ncard ≤ {j | j ∈ P.slim.centres ∧
      (tsupport (P.slim.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard :=
    (Set.ncard_image_le).trans (ncard_subtype_le_KA2 L.slim.finite_centres
      (p := fun y => x ∈ tsupport (P.slim.cutoff y))
      (q := fun y => (tsupport (P.slim.cutoff y) ∩ ball x (10 * ρ x)).Nonempty)
      fun _ _ hy => ⟨x, hy, hx⟩)
  have hE : (fE '' SE).ncard ≤ {j | j ∈ P.edge.centres ∧
      (tsupport (P.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard :=
    (Set.ncard_image_le).trans (ncard_subtype_le_KA2 L.edge.finite_centres
      (p := fun y => x ∈ tsupport (P.edge.cutoff y))
      (q := fun y => (tsupport (P.edge.cutoff y) ∩ ball x (10 * ρ x)).Nonempty)
      fun _ _ hy => ⟨x, hy, hx⟩)
  have hZc : (fZ '' SZ).ncard ≤ (zeroMeetingList P.zero x 10).ncard := by
    refine (Set.ncard_image_le).trans ?_
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    refine Set.ncard_le_ncard ?_ (P.zero.finite_centres.subset fun _ hk => hk.choose)
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨(Set.Finite.mem_toFinset _).mp i.2, x, hi, hx⟩
  have htot := h1.trans (h2.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hC hS) hE) hZc))
  exact_mod_cast htot

/-- The active tags of `𝓔⁰` at `x` are at most `fc07ActiveBound` (FC07's input packet). -/
theorem cgp_active_tags_ncard_le_fc07
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (x : X) :
    ({i : CGPTag P.toLocalChartFamily P.zero | i ≠ cgpScaleTag P.toLocalChartFamily P.zero ∧
        i ≠ cgpEdgeTag P.toLocalChartFamily P.zero ∧
        x ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero i)}.ncard : ℝ) ≤ fc07ActiveBound :=
  (cgp_active_tags_ncard_le P x).trans (fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT x).1

open Classical in
/-- The edge cutoffs whose closed support contains `x` are at most `fc07ActiveBound`. -/
theorem cgp_active_edge_card_le_fc07
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (x : X) :
    ((Finset.univ.filter fun i : P.edge.finite_centres.toFinset =>
        x ∈ tsupport (P.edge.cutoff i)).card : ℝ) ≤ fc07ActiveBound := by
  have hx : x ∈ ball x (10 * ρ x) := mem_ball_self (mul_pos (by norm_num) (hρ x))
  have hcard : (Finset.univ.filter fun i : P.edge.finite_centres.toFinset =>
      x ∈ tsupport (P.edge.cutoff i)).card ≤ {j | j ∈ P.edge.centres ∧
        (tsupport (P.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp only [Finset.mem_univ, true_and]
    exact ncard_subtype_le_KA2 P.edge.finite_centres
      (p := fun y => x ∈ tsupport (P.edge.cutoff y))
      (q := fun y => (tsupport (P.edge.cutoff y) ∩ ball x (10 * ρ x)).Nonempty)
      fun _ _ hy => ⟨x, hy, hx⟩
  have hcard' : ((Finset.univ.filter fun i : P.edge.finite_centres.toFinset =>
      x ∈ tsupport (P.edge.cutoff i)).card : ℝ) ≤ {j | j ∈ P.edge.centres ∧
        (tsupport (P.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard := by
    exact_mod_cast hcard
  have hpk := (fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT x).1
  have h0 : (0 : ℝ) ≤ ({j | j ∈ P.circle.centres ∧
      (tsupport (P.circle.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard : ℝ) +
        {j | j ∈ P.slim.centres ∧
          (tsupport (P.slim.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard := by positivity
  have h1 : (0 : ℝ) ≤ (zeroMeetingList P.zero x 10).ncard := by positivity
  linarith

/-- **CGP02** (`prop:fibration-actual-global-derivative`) on the final LC87 family: the actual
original global map `𝓔⁰ = cgpGlobalMap P.toLocalChartFamily P.zero` satisfies
`‖d𝓔⁰(v)‖ ≤ L₀ √(g_x(v, v))`, `L₀ = 1000 (N + 2) P₀²`, for every tangent vector `v`, where
`N = fc07ActiveBound` (the pointwise multiplicity) and `P₀ = cgpProfileBound` (the profile
derivative bound) are numerical constants fixed before `Δ`, noncollapse, the number of charts and
the scale range. -/
theorem cgp02_row
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) (x : X)
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x v‖ ≤
      1000 * (fc07ActiveBound + 2) * cgpProfileBound ^ 2 * Real.sqrt (g.inner x v v) := by
  have hP1 := cgpProfileBound_spec.1
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hΛ1 : Λ ≤ 1 := by nlinarith
  have hmargin := edge_margin_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ
  have hF : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²)) (cgpGlobalMap P.toLocalChartFamily P.zero) x :=
    (cgp01_rowE P.toLocalChartFamilyE P.zero hΛ hΔ0 hμ hτ hΔΛ (by linarith) x).mdifferentiableAt
      (by simp)
  have hNb0 : (0 : ℝ) ≤ fc07ActiveBound :=
    (Nat.cast_nonneg _).trans (cgp_active_tags_ncard_le_fc07 P hΛ hΔ hμ hτ hLΛ hLmax he hT x)
  have hρE : cgpScaleTag P.toLocalChartFamily P.zero ≠ cgpEdgeTag P.toLocalChartFamily P.zero := by
    simp
  have hscale := cgp02_scale_tag_budget P.toLocalChartFamily P.zero hΛ x v
  have hEblock : x ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero
      (cgpEdgeTag P.toLocalChartFamily P.zero)) →
      ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y
        (cgpEdgeTag P.toLocalChartFamily P.zero)) x v‖ ≤
        500 * (fc07ActiveBound + 1) * cgpProfileBound ^ 2 * Real.sqrt (g.inner x v v) := by
    intro hx
    refine (cgp02_edgeMarker_tag_budget P.toLocalChartFamily P.zero hΔ hΛ hΔΛ hσc hγc hmargin hx
      v).trans (mul_le_mul_of_nonneg_right ?_ hν)
    have hn := cgp_active_edge_card_le_fc07 P hΛ hΔ hμ hτ hLΛ hLmax he hT x
    have hP2 : 0 ≤ cgpProfileBound ^ 2 := sq_nonneg _
    gcongr
  have hblock : ∀ i, i ≠ cgpScaleTag P.toLocalChartFamily P.zero →
      i ≠ cgpEdgeTag P.toLocalChartFamily P.zero →
      x ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero i) →
      ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y i) x v‖ ≤
        (2 + 80 * cgpProfileBound) * Real.sqrt (g.inner x v v) := fun i h1 h2 hx =>
    cgp02_constant_radius_tag_budget P.toLocalChartFamilyQ P.zero hΔ hσs hσc hγc hεr
      (by linarith) hmargin i h1 h2 hx v
  have hcount : {i : CGPTag P.toLocalChartFamily P.zero |
      i ≠ cgpScaleTag P.toLocalChartFamily P.zero ∧ i ≠ cgpEdgeTag P.toLocalChartFamily P.zero ∧
        x ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero i)}.ncard ≤ ⌊fc07ActiveBound⌋₊ :=
    Nat.le_floor (cgp_active_tags_ncard_le_fc07 P hΛ hΔ hμ hτ hLΛ hLmax he hT x)
  have h := norm_mvfderiv_blockMap_apply_le_fc02 (R := cgpRadius P.toLocalChartFamily P.zero)
    (ζ := cgpCutoff P.toLocalChartFamily P.zero) (η := cgpCoord P.toLocalChartFamily P.zero) hF v
    hν _ _ hρE hscale hEblock hblock hcount
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hν)
  have hfl : (⌊fc07ActiveBound⌋₊ : ℝ) ≤ fc07ActiveBound + 1 :=
    (Nat.floor_le hNb0).trans (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 + 80 * cgpProfileBound := by linarith
  have hsq : Λ ^ 2 + (⌊fc07ActiveBound⌋₊ : ℝ) * (2 + 80 * cgpProfileBound) ^ 2 +
      (500 * (fc07ActiveBound + 1) * cgpProfileBound ^ 2) ^ 2 ≤
      Λ ^ 2 + (fc07ActiveBound + 1) * (2 + 80 * cgpProfileBound) ^ 2 +
      (500 * (fc07ActiveBound + 1) * cgpProfileBound ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hfl (sq_nonneg (2 + 80 * cgpProfileBound))
    linarith
  exact (Real.sqrt_le_sqrt hsq).trans (early_derivative_constant hNb0 hP1 hΛ hΛ1 hB0 le_rfl
    (by positivity) le_rfl)

end DifferentialGeometry.Geometry.Collapse
