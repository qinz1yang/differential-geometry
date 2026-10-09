import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {E' E'' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H} {J : ModelWithCorners ℝ E'' H'}
  {Z P : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
  [TopologicalSpace P] [ChartedSpace H' P]

def ballComplementRadialCollar
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) (R : ℝ) (hR : R ≠ 1) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) J
      (sphere (0 : E) 1 × ℝ) P ∞ :=
  (((Diffeomorph.fiberwiseAffine (I := 𝓡 n)
      (fun _ : sphere (0 : E) 1 => R) (fun _ => 1 - R)
      contMDiff_const contMDiff_const
      (fun _ => sub_ne_zero.mpr hR.symm)).toPartialDiffeomorph.trans
      (spherePolarChart (n := n) v)).trans b).trans F

@[simp] theorem ballComplementRadialCollar_apply
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) (R : ℝ) (hR : R ≠ 1)
    (q : sphere (0 : E) 1 × ℝ) :
    ballComplementRadialCollar (n := n) b F v R hR q =
      F (b ((R + (1 - R) * q.2) • (q.1 : E))) := rfl

theorem ballComplementRadialCollar_apply_one
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v z : sphere (0 : E) 1) (R : ℝ) (hR : R ≠ 1) :
    ballComplementRadialCollar (n := n) b F v R hR (z, 1) = F (b z) := by
  simp

private theorem radial_slab_bounds {R t : ℝ} (hR : 1 < R) (ht : t ∈ Icc (0 : ℝ) 1) :
    R + (1 - R) * t ∈ Icc (1 : ℝ) R := by
  constructor <;> nlinarith [ht.1, ht.2]

private theorem radial_slab_mem_complement
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞) {R : ℝ} (hR : 1 < R)
    (hb : closedBall (0 : E) R ⊆ b.source)
    (q : sphere (0 : E) 1 × ℝ) (hq : q.2 ∈ Icc (0 : ℝ) 1) :
    b ((R + (1 - R) * q.2) • (q.1 : E)) ∈ (b '' ball (0 : E) 1)ᶜ := by
  have hr := radial_slab_bounds hR hq
  have hn : ‖(R + (1 - R) * q.2) • (q.1 : E)‖ = R + (1 - R) * q.2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
      norm_eq_of_mem_sphere, mul_one]
  rintro ⟨w, hw, heq⟩
  have hws : w ∈ b.source := hb ((closedBall_subset_closedBall hR.le) (ball_subset_closedBall hw))
  have hqs : (R + (1 - R) * q.2) • (q.1 : E) ∈ b.source := by
    apply hb
    rw [mem_closedBall_zero_iff, hn]
    exact hr.2
  have hwq := b.injOn hws hqs heq
  have hnlt := mem_ball_zero_iff.mp hw
  rw [hwq, hn] at hnlt
  exact not_lt_of_ge hr.1 hnlt

theorem unit_slab_subset_ballComplementRadialCollar_source
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) {R : ℝ} (hR : 1 < R)
    (hb : closedBall (0 : E) R ⊆ b.source)
    (hF : (b '' ball (0 : E) 1)ᶜ ⊆ F.source) :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆
      (ballComplementRadialCollar (n := n) b F v R hR.ne').source := by
  intro q hq
  have hr := radial_slab_bounds hR hq.2
  refine ⟨⟨⟨mem_univ _, ?_⟩, ?_⟩, ?_⟩
  · change 0 < R + (1 - R) * q.2
    linarith [hr.1]
  · apply hb
    change (R + (1 - R) * q.2) • (q.1 : E) ∈ closedBall (0 : E) R
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
      norm_eq_of_mem_sphere, mul_one]
    exact hr.2
  · exact hF (radial_slab_mem_complement b hR hb q hq.2)

theorem ballComplementRadialCollar_image_unit_slab_subset
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) {R : ℝ} (hR : 1 < R)
    (hb : closedBall (0 : E) R ⊆ b.source) :
    ballComplementRadialCollar (n := n) b F v R hR.ne' '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      F '' (b '' ball (0 : E) 1)ᶜ := by
  rintro y ⟨q, hq, rfl⟩
  exact ⟨_, radial_slab_mem_complement b hR hb q hq.2, rfl⟩

end DifferentialGeometry.Topology.Manifold
