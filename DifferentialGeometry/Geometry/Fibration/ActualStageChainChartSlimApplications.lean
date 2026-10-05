import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartSlim

/-!
# Consumers of CGP06 / CGP07 on the chain, slim charts

* `Gaf02Chain.slimPatch_existsUnique_of_graph_BASP`: for a GIVEN SGP04 graph (the assembly's one
  choice, D71-2), each target `a ∈ B(0, 5.5·10⁵Δ)` is the retained coordinate of exactly one point
  of the slim patch `V_j⁰`.
* `Gaf02Chain.slimPatch_existsUnique_BASP`: the same from `R` (frozen form).
* `Gaf02Chain.slimPatch_compact_core_BASP`: the part of `V_j⁰` over the closed `4·10⁵Δ`-ball is
  compact.
* `Gaf02Chain.slim_retained_coordinate_ne_zero_BASP`: CGP06 makes `u_j` injective on every plane `L_x`
  of the slim cloud (a nonzero `v ∈ L_x` has `u_j v ≠ 0`).
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

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **One sheet over every target, for a given rough graph**: each `a ∈ B(0, 5.5·10⁵Δ)` is the
retained coordinate of exactly one point of the slim patch `V_j⁰`. -/
theorem slimPatch_existsUnique_of_graph_BASP
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc
          ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
            ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j.1
              ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)‖ ≤
          eg 2 * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    {a : ℝ} (ha : a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ))) :
    ∃! w, w ∈ C.slimPatch_BAS j ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) w = a := by
  have hbij := (C.cgp07_slim_of_graph_BASP R j sgn cc zsgn zc hsgn hzsgn hcl).1
  obtain ⟨w, hw, hwa⟩ := hbij.surjOn ha
  exact ⟨w, ⟨hw, hwa⟩, fun w' hw' => hbij.injOn hw'.1 hw (hw'.2.trans hwa.symm)⟩

/-- **One sheet over every target** (from `R`): each `a ∈ B(0, 5.5·10⁵Δ)` is the retained
coordinate of exactly one point of the slim patch `V_j⁰`. -/
theorem slimPatch_existsUnique_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) {a : ℝ}
    (ha : a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ))) :
    ∃! w, w ∈ C.slimPatch_BAS j ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) w = a :=
  Exists.elim (R.slim j) fun sgn h1 => Exists.elim h1 fun cc h2 => Exists.elim h2 fun zsgn h3 =>
    Exists.elim h3 fun zc h4 =>
      C.slimPatch_existsUnique_of_graph_BASP R j sgn cc zsgn zc h4.1 h4.2.1 h4.2.2 ha

/-- **The compact core of the slim patch**: `V_j⁰ ∩ {|R_j⁻¹u_j| ≤ 4·10⁵Δ}` is compact. -/
theorem slimPatch_compact_core_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) :
    IsCompact (C.slimPatch_BAS j ∩
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) ⁻¹'
        closedBall 0 (4 * (10 ^ 5 * Δ))) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  have hK := (C.cgp07_slim_BAS R j).2.2
  obtain ⟨-, -, -, -, hK⟩ := hK
  exact hK _ (closedBall_subset_ball (by linarith)) (isCompact_closedBall 0 _)

/-- **The retained coordinate is injective on the slim planes** (CGP06): at a slim-cloud point `x`
with a preimage `q` in chart `j` (`|η_j(q)| ≤ 8·10⁵Δ`), a nonzero `v ∈ L_x` has `u_j v ≠ 0`. -/
theorem slim_retained_coordinate_ne_zero_BASP
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2) {q : X}
    (hq : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x)
    (hqj : q ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| ≤ 8 * 10 ^ 5 * Δ)
    {v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hv : v ∈ C.plane 2 x)
    (hv0 : v ≠ 0) :
    axisCoordCLM_BAS (gafSlimVector P.toLocalChartFamily P.zero j v) ≠ 0 := by
  intro h0
  have h := C.cgp06_slim_BAS R j hx hq hqj hη v hv
  rw [h0, norm_zero, mul_zero] at h
  exact hv0 (norm_le_zero_iff.mp h)

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
