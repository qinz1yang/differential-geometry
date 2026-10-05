import DifferentialGeometry.Geometry.Fibration.ActualSlimComparisonList

/-!
# ZSP04's original input: the closed slim slabs are compact

Blueprint `master207B.tex`, ZSP04 (`thm:fibration-actual-compact-slim-piece`, B:6531–6595), first
step of the proof: "Each original closed `3.5·10⁵Δ` slab is compact by LFR20's whole proper
bundle. Their finite union is compact". This part involves only the original slim charts.

* `slimSlab_eq_GAFS`: for `a ≤ 905·10³Δ`, the slab `{p ∈ B(c_i, 10⁶Δρ(c_i)) : |η_i(p)| ≤ a}` equals
  `{p ∈ B̄(c_i, .91·10⁶Δρ(c_i)) : |η_i(p)| ≤ a}` (LFR20.2's enclosure,
  `SlimCentre.dist_lt_of_abs_coord_le_ZERO`).
* `isCompact_slimSlab_GAFS`: that slab is compact (closed in the compact carrier; `η_i` is
  continuous on the closed `.91`-ball, inside its smooth domain).
* `isCompact_iUnion_slimSlab_GAFS`: the finite union over all slim centres is compact.
The inclusion of this union in `X₃` (GAF07) and (SK) need the adjusted map and are not part of this
module.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}

/-- The slab of a slim centre: by LFR20.2, the points of `B(c_i, 10⁶Δρ(c_i))` with `|η_i| ≤ a`
(`0 < Δ`, `a ≤ 905·10³Δ`) are the points of `B̄(c_i, .91·10⁶Δρ(c_i))` with `|η_i| ≤ a`. -/
theorem slimSlab_eq_GAFS (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (i : L.slim.finite_centres.toFinset) {a : ℝ} (ha : a ≤ 905 * 10 ^ 3 * Δ) :
    {p | p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ a} =
      closedBall i.1 (91 / 100 * (10 ^ 6 * Δ) * ρ i.1) ∩
        (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord ⁻¹' Icc (-a) a := by
  have hri := hρ i.1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc, ← abs_le]
  constructor
  · rintro ⟨hp, hη⟩
    exact ⟨mem_closedBall.mpr (SlimCentre.dist_lt_of_abs_coord_le_ZERO _ hp (hη.trans ha)).le, hη⟩
  · rintro ⟨hp, hη⟩
    refine ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hp) ?_), hη⟩
    have : 0 < 10 ^ 6 * Δ * ρ i.1 := by positivity
    nlinarith

/-- **The closed slim slab is compact** (`0 < Δ`, `a ≤ 905·10³Δ`). -/
theorem isCompact_slimSlab_GAFS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (i : L.slim.finite_centres.toFinset) {a : ℝ} (ha : a ≤ 905 * 10 ^ 3 * Δ) :
    IsCompact {p | p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ a} := by
  have hri := hρ i.1
  rw [slimSlab_eq_GAFS L hΔ i ha]
  have hsub : closedBall i.1 (91 / 100 * (10 ^ 6 * Δ) * ρ i.1) ⊆
      ball i.1 (10 ^ 6 * Δ * ρ i.1) := by
    apply closedBall_subset_ball
    have : 0 < 10 ^ 6 * Δ * ρ i.1 := by positivity
    nlinarith
  have hcont : ContinuousOn (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord
      (closedBall i.1 (91 / 100 * (10 ^ 6 * Δ) * ρ i.1)) :=
    ((SlimCentre.contMDiffOn_coord _).mono hsub).continuousOn
  exact (hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Icc).isCompact

/-- **ZSP04's compact union of original slabs**: the union over all slim centres of the closed
`a`-slabs (`0 < Δ`, `a ≤ 905·10³Δ`; ZSP04 uses `a = 3.5·10⁵Δ`) is compact. -/
theorem isCompact_iUnion_slimSlab_GAFS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) {a : ℝ} (ha : a ≤ 905 * 10 ^ 3 * Δ) :
    IsCompact (⋃ i : L.slim.finite_centres.toFinset,
      {p | p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ a}) :=
  isCompact_iUnion fun i => isCompact_slimSlab_GAFS L hΔ i ha

end DifferentialGeometry.Geometry.Collapse
