import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersRim

/-!
# FC39 producer, packet P0 (gate 1): why `cycleRimChart` cannot be the labelled rim chart layer

Evidence for the gate-1 report (lead decision 02:45, condition 3): the linearity clause
`LabelledCornerCompatibility.height_eq` (`height − level = λ x` on the WHOLE rim source, one
constant `λ`) is a real constraint. Along the compiled rim chart `cycleRimChart false false` the disk
coordinate of the south handle is `(1 + x/16) • planeOfCircle θ`, so the S³ edge height minus level
is `(1 + x/16)² − 1 = x/8 + x²/256` (`edgeHeightR_cycleRimChart`): `x = 1` forces `λ = 33/256`,
`x = −1` forces `λ = 31/256` (`not_linear_height_cycleRimChart`). Hence there is NO
`LabelledCornerCompatibility` over a rim chart layer of `sphereEdgeLayer` whose south-end rim chart
is `cycleRimChart false false`, for any prepared rows with the S³ edge bundle and any circle region
(`isEmpty_labelled_cycleRimChart`). The adapted charts `circRim` use `√(1 + x/16)` instead.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The closed form of the compiled south rim chart at the end `0`. -/
theorem cycleRimChart_false_false_apply (p : Circle × (ℝ × ℝ)) :
    cycleRimChart false false p = cycleBallAmbient false ((1 + (1 / 16 : ℝ) * p.2.2) •
      ((Handle.stereoChart northPole).symm ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) :
        E3)) :=
  rfl

/-- On the axis `y = 0` the compiled south rim chart is the south handle chart at `t = 0`. -/
theorem cycleRimChart_false_false_eq_handle (θ : Circle) (x : ℝ) :
    cycleRimChart false false (θ, (x, 0)) =
      cycleHandleChart false ((1 + (1 / 16 : ℝ) * x) • planeOfCircle θ, 0) := by
  rw [cycleRimChart_false_false_apply, cycleHandleChart_eq_FC39P0]
  simp only [mul_zero, add_zero, one_smul, Bool.false_eq_true, ↓reduceIte]
  rw [cycleHandleRadius_inner (by norm_num), add_zero, one_smul]

/-- **The S³ edge height along the compiled rim chart** is `(1 + x/16)²` (not affine in `x`). -/
theorem edgeHeightR_cycleRimChart (θ : Circle) {x : ℝ} (hx : |x| < 2) :
    edgeHeightR (cycleRimChart false false (θ, (x, 0))) = (1 + (1 / 16 : ℝ) * x) ^ 2 := by
  have hpos : 0 < 1 + (1 / 16 : ℝ) * x := by
    have := (abs_lt.1 hx).1
    linarith
  have hbox : ((1 + (1 / 16 : ℝ) * x) • planeOfCircle θ, (0 : ℝ)) ∈ edgeBox := by
    refine ⟨?_, by norm_num, by norm_num⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul_planeOfCircle_CIRCA hpos]
    have := (abs_lt.1 hx).2
    linarith
  rw [cycleRimChart_false_false_eq_handle, edgeHeightR_chart hbox,
    norm_smul_planeOfCircle_CIRCA hpos]

/-- **No constant `λ`** makes `height − level = λ x` along the compiled south rim chart. -/
theorem not_linear_height_cycleRimChart (lam : ℝ) :
    ¬ ∀ p ∈ (cycleRimChart false false).source,
      ∃ hx : cycleRimChart false false p ∈ sphereEdgeBundle.source,
        sphereEdgeBundle.height ⟨cycleRimChart false false p, hx⟩ - sphereEdgeBundle.level =
          lam * p.2.1 := by
  intro h
  have hmem : ∀ x : ℝ, |x| < 2 →
      ((1 : Circle), (x, (0 : ℝ))) ∈ (cycleRimChart false false).source := fun x hx => by
      rw [cycleRimChart_source]
      exact ⟨mem_univ _, hx, by norm_num⟩
  have hval : ∀ x : ℝ, |x| < 2 → (1 + (1 / 16 : ℝ) * x) ^ 2 - 1 = lam * x := by
    intro x hx
    obtain ⟨hx', heq⟩ := h _ (hmem x hx)
    change edgeHeightR (cycleRimChart false false ((1 : Circle), (x, (0 : ℝ)))) - 1 = lam * x at heq
    rw [edgeHeightR_cycleRimChart 1 hx] at heq
    exact heq
  have h1 := hval 1 (by norm_num)
  have h2 := hval (-1) (by norm_num)
  linarith

/-- The south polar disk handle of the S³ edge layer. -/
def sphereSouthHandle_CIRCB : Fin sphereEdgeLayer.handleCount :=
  (0 : Fin 2)

/-- **No labelled compatibility over the compiled rim charts**: for every prepared rows with the S³
edge bundle, every circle region and every rim chart layer of `sphereEdgeLayer` whose south-end rim
chart is `cycleRimChart false false`. -/
theorem isEmpty_labelled_cycleRimChart {n : ℕ} {E : BoundaryTori sphereW n}
    (Pr : FC39Prepared sphereW E) (hP : Pr.rows.edge = sphereEdgeBundle)
    {circ : CircleRegion sphereW} (K : RimChartLayer sphereW sphereEdgeLayer circ)
    (hK : K.rimChart sphereSouthHandle_CIRCB false = cycleRimChart false false) :
    IsEmpty (LabelledCornerCompatibility Pr sphereEdgeLayer circ K) := by
  refine ⟨fun L => ?_⟩
  have key := L.height_eq sphereSouthHandle_CIRCB false
  rw [hK] at key
  generalize Pr.rows.edge = P at key hP
  subst hP
  exact not_linear_height_cycleRimChart _ key

end GC.GraphManifold.Assembly.FC39P0
