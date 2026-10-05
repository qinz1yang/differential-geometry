import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimParam

/-!
# FC39 GROUP G, RIMBOX route B: consumer of the rim parametrization (the RimProductAt core)

Lane FC39-G-RIMBOX, D62-3 (b). If the handle is the flow of the end disk, `Hm (w, t) = Fl_t (D w)`,
and the end disk agrees with the collar on the inner side, `D w = C w` for `1 − δ < ‖w‖` (POLAR-2's
inner matching), then on the handle quadrant the rim parametrization IS the handle in a product
collar: `F (θ, X, t) = Hm (w, t)` whenever `w = (1 + X/κ) • θ̂` lies in the disk and `−κ δ < X` — the short proof of
`RimProductAt` with `ρ x = 1 + (λ/κ) x`, `A = id` (`rimParam_eq_handle_GRIM`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]

/-- **The rim parametrization is the flow handle on the handle quadrant** (RimProductAt core). -/
theorem rimParam_eq_handle_GRIM {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U)
    (D : ClosedCell 2 → Y) (Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → Y)
    (hHm : ∀ p, ∃ hp : D p.1 ∈ U, Hm p = (Fl (p.2 : ℝ) ⟨D p.1, hp⟩ : Y))
    (C : EuclideanSpace ℝ (Fin 2) → Y) {δ κ : ℝ} (hκ : 0 < κ)
    (hDC : ∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ → D w = C w)
    (θ : Circle) {X : ℝ} (hX : -(κ * δ) < X) (w : ClosedCell 2)
    (hw : (w : EuclideanSpace ℝ (Fin 2)) = (1 + X / κ) • planeOfCircle θ) (t : Icc (0 : ℝ) 1) :
    rimParam_GRIM Fl C κ (θ, (X, (t : ℝ))) = Hm (w, t) := by
  obtain ⟨hp, hHmw⟩ := hHm (w, t)
  have h1 : ‖planeOfCircle θ‖ = 1 := by
    unfold planeOfCircle
    rw [LinearIsometryEquiv.norm_map]
    exact Circle.norm_coe θ
  have hnw : ‖(w : EuclideanSpace ℝ (Fin 2))‖ = |1 + X / κ| := by
    rw [hw, norm_smul, h1, mul_one, Real.norm_eq_abs]
  have hXk : -δ < X / κ := by
    rw [lt_div_iff₀ hκ]
    linarith
  have hnorm : 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ := by
    rw [hnw]
    calc 1 - δ < 1 + X / κ := by linarith
      _ ≤ |1 + X / κ| := le_abs_self _
  have hDw : D w = C (rimPolar_GRIM κ (θ, X)) := by
    rw [hDC w hnorm]
    exact congrArg C hw
  unfold rimParam_GRIM
  rw [hHmw]
  have hU : C (rimPolar_GRIM κ (θ, X)) ∈ U := hDw ▸ hp
  rw [flowExt_of_mem_GRIM Fl hU]
  congr 2
  exact Subtype.ext hDw.symm

end GC.GraphManifold.Assembly.FC39P0
