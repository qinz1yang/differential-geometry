import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphBlocks
import DifferentialGeometry.Geometry.Fibration.ActualEdgeZeroComparisonApplications

/-!
# EGP06 (EG): the pointwise comparison on the edge core (kernel form)

Blueprint `master207B.tex`, EGP06 (B:5088–5139). Kernel form of (EG) at one point: given EGP04's
(EC) on `D_i` for every listed tag (with the chosen signs `a_t = ±1`), at every
`x ∈ B(i, 100Δρ_i)` with `|η_i(x)| ≤ 8Δ` and `t(x) ≤ 8Δ` the projected actual map
`R_i⁻¹π₂𝓔⁰` and its derivative on `ρ_i⁻²g`-unit vectors are within `(N† + 2) · 4Bθ`
(`B = 50(P† + 1)`) of EGP06's model `Φ_i(η_i)` and its derivative.

* `signClamp_KC4`, `egpTagSign_KC4`, `egpTagShift_KC4`: the model's signs (`a_t`, clamped to
  `[−1, 1]` so that unlisted tags carry a harmless sign) and translations
  (`s_j u_j(p_i)`, `s_j u_j^s(p_i)`, `s₀η₀(p_i)`).
* `egp06_tags_KC4`: tag by tag — listed tags within `4Bθ`, unlisted `Q₂` tags exactly `0`.
* `egp06_point_KC4`: the assembly (orthogonal blocks, at most `N† + 2` listed tags).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- A real number clamped to `[−1, 1]`. -/
def signClamp_KC4 (a : ℝ) : ℝ := max (-1) (min 1 a)

theorem abs_signClamp_le_KC4 (a : ℝ) : |signClamp_KC4 a| ≤ 1 := by
  rw [signClamp_KC4, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem signClamp_of_sign_KC4 {a : ℝ} (ha : a = 1 ∨ a = -1) : signClamp_KC4 a = a := by
  rcases ha with rfl | rfl <;> norm_num [signClamp_KC4]

section Defs

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The signs of EGP06's model at an edge reference: EGP04's signs `a_t` (slim `aS`, edge `aE`,
zero `aZ`), clamped to `[−1, 1]`; `1` on the circle and special tags. -/
def egpTagSign_KC4 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (aS aE aZ : X → ℝ) :
    CGPTag L Z → ℝ
  | .inl _ => 1
  | .inr (.inl j) => signClamp_KC4 (aS j.1)
  | .inr (.inr (.inl j)) => signClamp_KC4 (aE j.1)
  | .inr (.inr (.inr (.inl k))) => signClamp_KC4 (aZ k.1)
  | .inr (.inr (.inr (.inr _))) => 1

/-- The translations of EGP06's model at an edge reference `i`: `s_j u_j(p_i)` (edge),
`s_j u_j^s(p_i)` (slim), `s₀η₀(p_i)` (zero); `0` elsewhere. -/
def egpTagShift_KC4 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X) : CGPTag L Z → ℝ
  | .inl _ => 0
  | .inr (.inl j) => ρ j.1 / ρ i * sgpRaw L.slim j.1 i
  | .inr (.inr (.inl j)) => ρ j.1 / ρ i * egpRaw L.edge j.1 i
  | .inr (.inr (.inr (.inl k))) =>
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i *
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial i
  | .inr (.inr (.inr (.inr _))) => 0

theorem abs_egpTagSign_le_KC4
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (aS aE aZ : X → ℝ)
    (t : CGPTag L Z) : |egpTagSign_KC4 L Z aS aE aZ t| ≤ 1 := by
  rcases t with j | j | j | k | q
  · simp [egpTagSign_KC4]
  · exact abs_signClamp_le_KC4 _
  · exact abs_signClamp_le_KC4 _
  · exact abs_signClamp_le_KC4 _
  · simp [egpTagSign_KC4]

end Defs

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricN_KC4
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedN_KC4
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricC_KC4
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EGP06 tag by tag.** Under EGP04's (EC) on `D_i` with signs `aS, aE, aZ` (the hypotheses
`hEe, hEs, hEz` are EGP04's conclusion), at a core point `x` of the edge reference `i`: every
listed tag of the model has value and derivative error at most `4Bθ` (`B = 50(P† + 1)`), and every
unlisted tag of `Q₂` has error `0`. -/
theorem egp06_tags_KC4
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσc : σc ≤ 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {i : X} (hi : i ∈ P.edge.centres)
    (aS aE aZ : X → ℝ)
    (hEe : ∀ j ∈ egpEdgeList P.toLocalChartFamily i, (aE j = 1 ∨ aE j = -1) ∧
      ∀ y ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * P.edge.coord j y - (aE j * P.edge.coord i y + ρ j / ρ i * egpRaw P.edge j i)| <
            θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) y, (ρ i)⁻¹ ^ 2 * g.inner y w w = 1 →
            |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) y w -
              aE j * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) y w| < θ)
    (hEs : ∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      (aS j = 1 ∨ aS j = -1) ∧ ∀ y ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * (P.slim.centre j hj).coord y -
            (aS j * P.edge.coord i y + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) y, (ρ i)⁻¹ ^ 2 * g.inner y w w = 1 →
            |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord y w -
              aS j * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) y w| < θ)
    (hEz : ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => annularCutoff cutoffProfile ((P.zero.zero k hk).radial y)) ∩
        ball i (20 * Δ * ρ i)).Nonempty →
      (aZ k = 1 ∨ aZ k = -1) ∧ ∀ y ∈ ball i (20 * Δ * ρ i),
        |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial y -
            (aZ k * P.edge.coord i y +
              (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) y, (ρ i)⁻¹ ^ 2 * g.inner y w w = 1 →
            |(P.zero.zero k hk).radius / ρ i * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial y w -
              aZ k * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) y w| < θ)
    {x : X} (hx : x ∈ ball i (100 * Δ * ρ i)) (hη : |P.edge.coord i x| ≤ 8 * Δ)
    (ht : cgpHeight P.toLocalChartFamily x ≤ 8 * Δ) (t : CGPTag P.toLocalChartFamily P.zero) :
    (egpModelListed P.toLocalChartFamily P.zero i t →
      ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x t -
          egpModelComponent P.toLocalChartFamily P.zero i
            (egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ)
            (egpTagShift_KC4 P.toLocalChartFamily P.zero i) t (P.edge.coord i x)‖ ≤
          4 * (50 * (egpProfileConst + 1)) * θ ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y t) x w -
            fderiv ℝ (egpModelComponent P.toLocalChartFamily P.zero i
              (egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ)
              (egpTagShift_KC4 P.toLocalChartFamily P.zero i) t) (P.edge.coord i x)
              (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ ≤
            4 * (50 * (egpProfileConst + 1)) * θ) ∧
      (¬ egpModelListed P.toLocalChartFamily P.zero i t →
        x ∉ tsupport (cgpCutoff P.toLocalChartFamily P.zero t) ∨
          t ∉ cgpQ2Tags P.toLocalChartFamily P.zero) := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := P.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  have hmargin := edge_margin_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ
  -- the point lies in `D_i`
  have hζ1 : P.edge.cutoff i x = 1 := P.edge.cutoff_eq_one_of_le hΔ0 hi hx hη ht
  have hxD : x ∈ ball i (20 * Δ * ρ i) := by
    have hts : x ∈ tsupport (P.edge.cutoff i) :=
      subset_tsupport _ (by rw [Function.mem_support, hζ1]; exact one_ne_zero)
    have h14 := (fc18_edge_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ hi).1 hts
    exact (fc18_edge_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ hi).2.1 h14
  have hda : ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
      |mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| ≤ 2 := by
    intro w hw
    refine (P.edge.abs_deriv_le_max_KC4 hi hx w hw).trans ?_
    exact max_le (by linarith) (by norm_num)
  -- zero clauses on `D_i`
  have hT0 : 0 < T := by
    have : (0 : ℝ) < 1600 * (1000000 * Δ) := by positivity
    linarith
  have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * Λ) ≤ 1 / 40 := by
    have h1 : 20 * Δ / T ≤ 1 / 80000 := by
      rw [div_le_iff₀ hT0]
      linarith
    have h2 : 20 * Δ * Λ ≤ 1 / 5000000 := by nlinarith
    linarith
  obtain ⟨-, hcl⟩ := zero_meeting_clauses_ZERO P hΛ he hT0 i (by positivity) hsmall
  have hT20 : 1 ≤ T / 20 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (20 : ℝ) ≤ 1600 * (1000000 * Δ) := by nlinarith
    linarith
  obtain ⟨sgn, hsgn⟩ : ∃ f : CGPTag P.toLocalChartFamily P.zero → ℝ,
      f = egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ f : CGPTag P.toLocalChartFamily P.zero → ℝ,
      f = egpTagShift_KC4 P.toLocalChartFamily P.zero i := ⟨_, rfl⟩
  rw [← hsgn, ← hcdef]
  rcases t with j | j | j | k | q
  · exact ⟨fun hl => hl.elim, fun _ => Or.inr fun h =>
      Bool.false_ne_true (Finset.mem_filter.mp h).2⟩
  · -- slim tag
    have hjc : j.1 ∈ P.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
    refine ⟨fun hl => ?_, fun hl => Or.inl fun hxs => hl ⟨hjc, x, hxs, hxD⟩⟩
    have hjl : j.1 ∈ egpSlimList P.toLocalChartFamily i := hl
    obtain ⟨hr1, hball⟩ := slim_meeting_ball_KC3 P.toLocalChartFamilyE hΔ hΛ hLΛ hjc hjl.2
    have hs : 99 / 100 ≤ ρ j.1 / ρ i := by
      obtain ⟨y₀, hy1, hy2⟩ := hjl.2
      have hsl := fc18_slim_row P.toLocalChartFamily hΔ0 hjc
      have hm : (closedBall j.1 ((910000 * Δ) * ρ j.1) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
        ⟨y₀, hsl.1 hy1, hy2⟩
      have hΛ1 : 250 * (Λ * (20 * Δ)) ≤ 1 := by
        have e : Λ * (20 * Δ) = 1 / 50000 * (1000000 * Δ * Λ) := by ring
        linarith
      have hΛ2 : 250 * (Λ * (910000 * Δ)) ≤ 1 := by
        have e : Λ * (910000 * Δ) = 91 / 100 * (1000000 * Δ * Λ) := by ring
        linarith
      exact (support_meeting_sharp_bounds hρL hri (hρ j.1) (a := 20 * Δ) (c := 910000 * Δ)
        (by positivity) (by positivity) (by rw [hc]; exact hΛ1) (by rw [hc]; exact hΛ2) hm).1.le
    obtain ⟨ha, hEC⟩ := hEs j.1 hjc hjl.2
    have hsg : sgn (.inr (.inl j)) = aS j.1 := by
      rw [hsgn]; exact signClamp_of_sign_KC4 ha
    have hσ : |sgn (.inr (.inl j))| ≤ 1 := by
      rw [hsgn]; exact abs_egpTagSign_le_KC4 _ P.zero aS aE aZ _
    have hval := (egp06_slim_tag_KC4 P.toLocalChartFamilyQ P.zero hΔ sgn c j hjl hs hθ1 hσ
      (hball hxD) 0 (by rw [hsg, hcdef]; exact (hEC x hxD).1)
      (by rw [map_zero, map_zero, mul_zero, mul_zero, sub_zero, abs_zero]; exact hθ0)
      (by rw [map_zero, abs_zero]; norm_num)).1
    refine ⟨hval, fun w hw => ?_⟩
    exact (egp06_slim_tag_KC4 P.toLocalChartFamilyQ P.zero hΔ sgn c j hjl hs hθ1 hσ
      (hball hxD) w (by rw [hsg, hcdef]; exact (hEC x hxD).1)
      (by rw [hsg]; exact (hEC x hxD).2 w hw) (hda w hw)).2
  · -- edge tag
    have hjc : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
    refine ⟨fun hl => ?_, fun hl => Or.inl fun hxs => hl (Or.inr ⟨hjc, x, hxs, hxD⟩)⟩
    by_cases hji : j.1 = i
    · obtain ⟨hB0, -, -, -⟩ := egp06_block_bounds_KC4
      have hδ : 0 ≤ 4 * (50 * (egpProfileConst + 1)) * θ := by positivity
      refine ⟨?_, fun w _ => ?_⟩
      · rw [(egp06_own_tag_KC4 P.toLocalChartFamily P.zero hΔ0 hmargin hi sgn c j hji hx hη ht
          0).1, sub_self, norm_zero]
        exact hδ
      · rw [(egp06_own_tag_KC4 P.toLocalChartFamily P.zero hΔ0 hmargin hi sgn c j hji hx hη ht
          w).2, sub_self, norm_zero]
        exact hδ
    have hjl : j.1 ∈ egpEdgeList P.toLocalChartFamily i := hl.resolve_left hji
    obtain ⟨-, y₀, hy1, hy2⟩ := hjl
    have h14 := (fc18_edge_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ hjc).1 hy1
    have hm : (closedBall j.1 (15 * Δ * ρ j.1) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
      refine ⟨y₀, closedBall_subset_closedBall ?_ h14, hy2⟩
      nlinarith [hρ j.1]
    obtain ⟨hs1, -, -, hsub⟩ := edge_comparison_list_edge_bounds hρL hri (hρ j.1) hΔ hLΛ' hm
    have hxj : x ∈ ball j.1 (100 * Δ * ρ j.1) := by
      have h57 : dist x j.1 < 57 * Δ * ρ j.1 := hsub hxD
      have hΔρj : 0 < Δ * ρ j.1 := mul_pos hΔ0 (hρ j.1)
      exact mem_ball.mpr (by linarith)
    have hjl' : j.1 ∈ egpEdgeList P.toLocalChartFamily i := hl.resolve_left hji
    obtain ⟨ha, hEC⟩ := hEe j.1 hjl'
    have hsg : sgn (.inr (.inr (.inl j))) = aE j.1 := by
      rw [hsgn]; exact signClamp_of_sign_KC4 ha
    have hσ : |sgn (.inr (.inr (.inl j)))| ≤ 1 := by
      rw [hsgn]; exact abs_egpTagSign_le_KC4 _ P.zero aS aE aZ _
    have hval := (egp06_edge_tag_KC4 P.toLocalChartFamily P.zero hΔ hmargin sgn c j hji hjl'
      hs1.le hθ1 hσ hxj ht 0
      (by rw [hsg, hcdef]; exact (hEC x hxD).1)
      (by rw [map_zero, map_zero, mul_zero, mul_zero, sub_zero, abs_zero]; exact hθ0)
      (by rw [map_zero, abs_zero]; norm_num)).1
    refine ⟨hval, fun w hw => ?_⟩
    exact (egp06_edge_tag_KC4 P.toLocalChartFamily P.zero hΔ hmargin sgn c j hji hjl' hs1.le hθ1
      hσ hxj ht w
      (by rw [hsg, hcdef]; exact (hEC x hxD).1) (by rw [hsg]; exact (hEC x hxD).2 w hw)
      (hda w hw)).2
  · -- zero tag
    have hkc : k.1 ∈ P.zero.centres := (Set.Finite.mem_toFinset _).mp k.2
    refine ⟨fun hl => ?_, fun hl => Or.inl fun hxs => hl ⟨hkc, x, hxs, hxD⟩⟩
    have hkl : k.1 ∈ zeroMeetingList P.zero i (20 * Δ) := hl
    obtain ⟨hk', hmeet⟩ := hkl
    obtain ⟨hshell, O, hO, hDO, hsm⟩ := hcl k.1 hk' hmeet
    have hrad : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k.1 hkc).radial x :=
      (hsm.contMDiffAt (hO.mem_nhds (hDO hxD))).mdifferentiableAt (by simp)
    have hs : 1 ≤ (P.zero.zero k.1 hkc).radius / ρ i :=
      hT20.trans ((hshell i (mem_ball_self (by positivity))).2.2.2.2)
    obtain ⟨ha, hEC⟩ := hEz k.1 hkc hmeet
    have hsg : sgn (.inr (.inr (.inr (.inl k)))) = aZ k.1 := by
      rw [hsgn]; exact signClamp_of_sign_KC4 ha
    have hσ : |sgn (.inr (.inr (.inr (.inl k))))| ≤ 1 :=
      by
      rw [hsgn]; exact abs_egpTagSign_le_KC4 _ P.zero aS aE aZ _
    have hval := (egp06_zero_tag_KC4 P.toLocalChartFamily P.zero sgn c k hl hs hθ1 hσ hrad 0
      (by rw [hsg, hcdef]; exact (hEC x hxD).1)
      (by rw [map_zero, map_zero, mul_zero, mul_zero, sub_zero, abs_zero]; exact hθ0)
      (by rw [map_zero, abs_zero]; norm_num)).1
    refine ⟨hval, fun w hw => ?_⟩
    exact (egp06_zero_tag_KC4 P.toLocalChartFamily P.zero sgn c k hl hs hθ1 hσ hrad w
      (by rw [hsg, hcdef]; exact (hEC x hxD).1) (by rw [hsg]; exact (hEC x hxD).2 w hw)
      (hda w hw)).2
  · exact ⟨fun hl => hl.elim, fun _ => Or.inr fun h =>
      Bool.false_ne_true (Finset.mem_filter.mp h).2⟩

open Classical in
/-- **EGP06 (EG) at one point, kernel form.** Under EGP04's (EC) on `D_i` (hypotheses `hEe, hEs,
hEz` with signs `aS, aE, aZ`), at every core point `x` of the edge reference `i`
(`x ∈ B(i, 100Δρ_i)`, `|η_i(x)| ≤ 8Δ`, `t(x) ≤ 8Δ`): with the model
`Φ_i = egpModelGraph L Z i sgn c` (`sgn = egpTagSign_KC4`, `c = egpTagShift_KC4`),
`‖R_i⁻¹π₂𝓔⁰(x) − Φ_i(η_i(x))‖ ≤ (N† + 2)·4Bθ` and, on every `ρ_i⁻²g`-unit vector `w`,
`‖R_i⁻¹d(π₂𝓔⁰)_x(w) − DΦ_i(η_i(x))(dη_i(w))‖ ≤ (N† + 2)·4Bθ`, `B = 50(P† + 1)`. -/
theorem egp06_point_KC4
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσc : σc ≤ 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {i : X} (hi : i ∈ P.edge.centres)
    (aS aE aZ : X → ℝ)
    (hEe : ∀ j ∈ egpEdgeList P.toLocalChartFamily i, (aE j = 1 ∨ aE j = -1) ∧
      ∀ y ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * P.edge.coord j y - (aE j * P.edge.coord i y + ρ j / ρ i * egpRaw P.edge j i)| <
            θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) y, (ρ i)⁻¹ ^ 2 * g.inner y w w = 1 →
            |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) y w -
              aE j * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) y w| < θ)
    (hEs : ∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      (aS j = 1 ∨ aS j = -1) ∧ ∀ y ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * (P.slim.centre j hj).coord y -
            (aS j * P.edge.coord i y + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) y, (ρ i)⁻¹ ^ 2 * g.inner y w w = 1 →
            |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord y w -
              aS j * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) y w| < θ)
    (hEz : ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => annularCutoff cutoffProfile ((P.zero.zero k hk).radial y)) ∩
        ball i (20 * Δ * ρ i)).Nonempty →
      (aZ k = 1 ∨ aZ k = -1) ∧ ∀ y ∈ ball i (20 * Δ * ρ i),
        |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial y -
            (aZ k * P.edge.coord i y +
              (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) y, (ρ i)⁻¹ ^ 2 * g.inner y w w = 1 →
            |(P.zero.zero k hk).radius / ρ i * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial y w -
              aZ k * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) y w| < θ)
    {x : X} (hx : x ∈ ball i (100 * Δ * ρ i)) (hη : |P.edge.coord i x| ≤ 8 * Δ)
    (ht : cgpHeight P.toLocalChartFamily x ≤ 8 * Δ) :
    ‖(ρ i)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) x -
        egpModelGraph P.toLocalChartFamily P.zero i
          (egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ)
          (egpTagShift_KC4 P.toLocalChartFamily P.zero i) (P.edge.coord i x)‖ ≤
        (egp02ListBound + 2) * (4 * (50 * (egpProfileConst + 1)) * θ) ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i
            (egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ)
            (egpTagShift_KC4 P.toLocalChartFamily P.zero i)) (P.edge.coord i x)
            (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ ≤
          (egp02ListBound + 2) * (4 * (50 * (egpProfileConst + 1)) * θ) := by
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hF : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) x :=
    (cgp01_rowE P.toLocalChartFamilyE P.zero hΛ hΔ0 hμ hτ hΔΛ (by linarith)
      x).mdifferentiableAt (by simp)
  have htag := fun t => egp06_tags_KC4 P hΛ hΔ hLΛ hμ hτ he hT hσc hθ0 hθ1 hi aS aE aZ hEe hEs
    hEz hx hη ht t
  obtain ⟨sgn, hsgn⟩ : ∃ f : CGPTag P.toLocalChartFamily P.zero → ℝ,
      f = egpTagSign_KC4 P.toLocalChartFamily P.zero aS aE aZ := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ f : CGPTag P.toLocalChartFamily P.zero → ℝ,
      f = egpTagShift_KC4 P.toLocalChartFamily P.zero i := ⟨_, rfl⟩
  rw [← hsgn, ← hcdef] at htag ⊢
  obtain ⟨hB0, -, -, -⟩ := egp06_block_bounds_KC4
  have hδ : 0 ≤ 4 * (50 * (egpProfileConst + 1)) * θ := by positivity
  have hcard := egpModelListed_card_le P hΛ hΔ hLΛ he hT i
  have hcomp0 := egpModelComponent_eq_zero P.toLocalChartFamily P.zero i sgn c
  have hdiff : ∀ t, Differentiable ℝ (egpModelComponent P.toLocalChartFamily P.zero i sgn c t) :=
    fun t => (contDiff_egpModelComponent P.toLocalChartFamily P.zero i sgn c t).differentiable
      (by simp)
  have hQ : ∀ t, egpModelListed P.toLocalChartFamily P.zero i t →
      t ∈ cgpQ2Tags P.toLocalChartFamily P.zero := by
    intro t hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases t with j | j | j | k | q
    · exact hl.elim
    · rfl
    · rfl
    · rfl
    · exact hl.elim
  have hfin : ((Finset.univ.filter (egpModelListed P.toLocalChartFamily P.zero i)).card : ℝ) *
      (4 * (50 * (egpProfileConst + 1)) * θ) ≤
      (egp02ListBound + 2) * (4 * (50 * (egpProfileConst + 1)) * θ) :=
    mul_le_mul_of_nonneg_right hcard hδ
  constructor
  · refine (norm_le_card_mul_of_blocks_KC4 _
      (Finset.univ.filter (egpModelListed P.toLocalChartFamily P.zero i)) hδ ?_ ?_).trans hfin
    · intro t htS
      have hl := (Finset.mem_filter.mp htS).2
      rw [PiLp.sub_apply, PiLp.smul_apply]
      change ‖(ρ i)⁻¹ • blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
          (cgpGlobalMap P.toLocalChartFamily P.zero x) t -
        egpModelComponent P.toLocalChartFamily P.zero i sgn c t (P.edge.coord i x)‖ ≤ _
      rw [blockRestrict_apply]
      simp only [hQ t hl, ↓reduceIte]
      exact ((htag t).1 hl).1
    · intro t htS
      have hl : ¬ egpModelListed P.toLocalChartFamily P.zero i t := fun h =>
        htS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [PiLp.sub_apply, PiLp.smul_apply]
      change (ρ i)⁻¹ • blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
          (cgpGlobalMap P.toLocalChartFamily P.zero x) t -
        egpModelComponent P.toLocalChartFamily P.zero i sgn c t (P.edge.coord i x) = 0
      rw [blockRestrict_apply]
      by_cases hQt : t ∈ cgpQ2Tags P.toLocalChartFamily P.zero
      · simp only [hQt, ↓reduceIte]
        rcases (htag t).2 hl with hxs | hQ'
        · exact (egp06_unlisted_tag_KC4 P.toLocalChartFamily P.zero i sgn c t hl hxs 0).1
        · exact absurd hQt hQ'
      · simp only [hQt, ↓reduceIte, smul_zero, hcomp0 t hl]
        simp
  · intro w hw
    have hfun : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) =
        fun y => blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
          (cgpGlobalMap P.toLocalChartFamily P.zero y) := rfl
    have hD := mvfderiv_clm_comp_apply_KC4 (I := 𝓘(ℝ, E3))
      (blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero))
      (f := cgpGlobalMap P.toLocalChartFamily P.zero) hF w
    rw [hfun]
    have hcompD : ∀ t, mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w t =
        mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y t) x w :=
      fun t => mvfderiv_blockMap_apply_apply (R := cgpRadius P.toLocalChartFamily P.zero)
        (ζ := cgpCutoff P.toLocalChartFamily P.zero) (η := cgpCoord P.toLocalChartFamily P.zero)
        hF w t
    have hΦD : ∀ t, fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
        (P.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w) t =
        fderiv ℝ (egpModelComponent P.toLocalChartFamily P.zero i sgn c t) (P.edge.coord i x)
          (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w) :=
      fun t => fderiv_blockGraph_apply_KC3 hdiff _ _ t
    rw [hD]
    refine (norm_le_card_mul_of_blocks_KC4 _
      (Finset.univ.filter (egpModelListed P.toLocalChartFamily P.zero i)) hδ ?_ ?_).trans hfin
    · intro t htS
      have hl := (Finset.mem_filter.mp htS).2
      rw [PiLp.sub_apply, PiLp.smul_apply, blockRestrict_apply, hΦD t]
      simp only [hQ t hl, ↓reduceIte]
      rw [hcompD t]
      exact ((htag t).1 hl).2 w hw
    · intro t htS
      have hl : ¬ egpModelListed P.toLocalChartFamily P.zero i t := fun h =>
        htS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [PiLp.sub_apply, PiLp.smul_apply, blockRestrict_apply, hΦD t]
      by_cases hQt : t ∈ cgpQ2Tags P.toLocalChartFamily P.zero
      · simp only [hQt, ↓reduceIte]
        rw [hcompD t]
        rcases (htag t).2 hl with hxs | hQ'
        · exact (egp06_unlisted_tag_KC4 P.toLocalChartFamily P.zero i sgn c t hl hxs w).2
        · exact absurd hQt hQ'
      · simp only [hQt, ↓reduceIte, smul_zero, hcomp0 t hl, fderiv_zero]
        simp

end Family

end DifferentialGeometry.Geometry.Collapse
