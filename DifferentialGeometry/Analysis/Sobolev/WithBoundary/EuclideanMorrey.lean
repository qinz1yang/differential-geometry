import DifferentialGeometry.Analysis.Sobolev.Euclidean.Morrey
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevHalfSpace

/-!
# Morrey-type embedding on Euclidean half-space balls

This is the with-boundary parallel of `Analysis/Sobolev/EuclideanMorrey.lean`. We
deliver Morrey-type embeddings whose conclusions hold on the closed-half-space
portion of a Euclidean ball, `Metric.ball x₀ R ∩ closedHalfSpace`.

## Strategy

For smooth `u : EuclideanSpace ℝ (Fin d) → ℝ` defined on the full ambient space,
the boundaryless smooth Morrey inequalities (`smooth_morrey_pair_bound`,
`smooth_morrey_sup_bound`, `smooth_morrey_holder_modulus`,
`smooth_morrey_pair_bound_uniform`, `smooth_morrey_sup_bound_uniform`) deliver
Hölder/sup bounds on the entire half-radius ball `Metric.ball x₀ (R / 2)`. We
specialise these to the closed-half-space portion
`Metric.ball x₀ (R / 2) ∩ closedHalfSpace` by simple intersection: the
hypotheses of the boundaryless versions are unchanged, and the closed-half-space
points are a subset of the half-radius ball.

For the Dirichlet-variant `MemWkpHalfSpace 1 p u Ω` predicate, we expose a
corollary covering the **interior ball** case where the ball
`Metric.ball x₀ R` is fully contained in the open half-space (equivalently, the
ball does not touch the boundary). In that case, the half-space-Sobolev
membership reduces to the boundaryless `MemW1pWitness` membership and the full
boundaryless Hölder representative on `Metric.ball x₀ (R / 4)` applies, whose
restriction to the closed-half-space portion is automatic.

## Main results

### Smooth-input half-space Morrey bounds
* `smooth_morrey_pair_bound_halfSpace`
* `smooth_morrey_sup_bound_halfSpace`
* `smooth_morrey_holder_modulus_halfSpace`
* `smooth_morrey_pair_bound_uniform_halfSpace`
* `smooth_morrey_sup_bound_uniform_halfSpace`

### `MemWkpHalfSpace` interior-ball Morrey
* `morrey_holder_representative_halfSpace_interior`
* `morrey_sup_bound_halfSpace_interior`
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EuclideanMorrey

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The closed-half-space portion of an open ball is contained in the ball. -/
theorem ball_inter_closedHalfSpace_subset_ball
    {x₀ : E} {r : ℝ} :
    Metric.ball x₀ r ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ⊆
      Metric.ball x₀ r :=
  inter_subset_left

/-- The closed-half-space portion of an open ball is contained in the
closed half-space. -/
theorem ball_inter_closedHalfSpace_subset_closedHalfSpace
    {x₀ : E} {r : ℝ} :
    Metric.ball x₀ r ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
  inter_subset_right

/-- **Smooth pair Hölder bound on the closed-half-space portion of a ball.**

For a smooth function `u : E → ℝ` and any pair `x, y ∈ B(x₀, R/2) ∩ closedHalfSpace`,
the difference `‖u x - u y‖` is bounded by `(dist x y)^{1 - d/p}` times the
gradient `L^p` norm on the larger ball `B(x₀, R)`, with a constant depending
only on `d` and `p`.

This is the boundaryless `smooth_morrey_pair_bound` restricted to the
closed-half-space portion of the half-radius ball. -/
theorem smooth_morrey_pair_bound_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x y : E},
        x ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
        y ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
          ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
            (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ R))).toReal := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_pair_bound (d := d) hp hR hu
  refine ⟨C, hC_nn, ?_⟩
  intro x y hx hy
  exact hbound (ball_inter_closedHalfSpace_subset_ball hx)
    (ball_inter_closedHalfSpace_subset_ball hy)

/-- **Smooth sup bound on the closed-half-space portion of a ball.**

For a smooth function `u : E → ℝ`, every value `u(x)` with
`x ∈ B(x₀, R/2) ∩ closedHalfSpace` is bounded by a constant times the sum of
the `L^p` norms of `u` and its gradient on the larger ball `B(x₀, R)`.

This is the boundaryless `smooth_morrey_sup_bound` restricted to the
closed-half-space portion of the half-radius ball. -/
theorem smooth_morrey_sup_bound_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
        ‖u x‖ ≤ C * (
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
          (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_sup_bound (d := d) hp hR hu
  refine ⟨C, hC_nn, ?_⟩
  intro x hx
  exact hbound x (ball_inter_closedHalfSpace_subset_ball hx)

/-- **Smooth Hölder modulus on the closed-half-space portion of a ball.**

For a smooth function `u : E → ℝ`, the value `‖u x - u y‖` is controlled by
`(dist x y)^{1 - d/p}` times an absolute constant, for `x, y` in the
closed-half-space portion of `B(x₀, R/2)`. The constant depends on `d, p, R`
and the gradient `L^p` norm on `B(x₀, R)`.

This is the boundaryless `smooth_morrey_holder_modulus` restricted to the
closed-half-space portion of the half-radius ball. -/
theorem smooth_morrey_holder_modulus_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x y : E},
        x ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
        y ∈ Metric.ball x₀ (R / 2) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
          ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_holder_modulus (d := d) hp hR hu
  refine ⟨C, hC_nn, ?_⟩
  intro x y hx hy
  exact hbound (ball_inter_closedHalfSpace_subset_ball hx)
    (ball_inter_closedHalfSpace_subset_ball hy)

/-- **Uniform-in-`u` smooth pair Hölder bound on the closed-half-space portion
of a ball.** Strengthens `smooth_morrey_pair_bound_halfSpace` by quantifying the
constant `C` ahead of `u`. -/
theorem smooth_morrey_pair_bound_uniform_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ {x y : E},
          x ∈ Metric.ball x₀ (R / 2) ∩
              DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
          y ∈ Metric.ball x₀ (R / 2) ∩
              DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace →
            ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
              (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_pair_bound_uniform (d := d) hp hR
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x y hx hy
  exact hbound hu (ball_inter_closedHalfSpace_subset_ball hx)
    (ball_inter_closedHalfSpace_subset_ball hy)

/-- **Uniform-in-`u` smooth sup bound on the closed-half-space portion of a
ball.** Strengthens `smooth_morrey_sup_bound_halfSpace` by quantifying the
constant `C` ahead of `u`. -/
theorem smooth_morrey_sup_bound_uniform_halfSpace
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ x ∈ Metric.ball x₀ (R / 2) ∩
              DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
          ‖u x‖ ≤ C *
            ((eLpNorm u (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal +
             (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal) := by
  obtain ⟨C, hC_nn, hbound⟩ := smooth_morrey_sup_bound_uniform (d := d) hp hR
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x hx
  exact hbound hu x (ball_inter_closedHalfSpace_subset_ball hx)

/-- A ball strictly inside the open half-space is half-space-friendly:
`Metric.ball x₀ R ⊆ openHalfSpace ⊆ closedHalfSpace`. -/
theorem ball_subset_openHalfSpace_of_dist_pos
    {x₀ : E} {R : ℝ}
    (hx₀ : R ≤ x₀ 0) :
    Metric.ball x₀ R ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h_proj : |y 0 - x₀ 0| ≤ ‖y - x₀‖ := by
    have h_eq : |y 0 - x₀ 0| = |(y - x₀) 0| := by
      simp [PiLp.sub_apply]
    rw [h_eq]
    have h_eval :
        |(y - x₀) 0| = ‖(y - x₀) 0‖ := by
      rw [Real.norm_eq_abs]
    rw [h_eval]
    exact PiLp.norm_apply_le (y - x₀) 0
  change (0 : ℝ) < y 0
  have h_y0_ge : x₀ 0 - ‖y - x₀‖ ≤ y 0 := by
    have := abs_le.mp h_proj
    linarith [this.1]
  linarith

/-- The closed-half-space portion of an open ball strictly inside the open
half-space is the entire ball. -/
theorem ball_inter_closedHalfSpace_eq_ball_of_dist_pos
    {x₀ : E} {R : ℝ}
    (hx₀ : R ≤ x₀ 0) :
    Metric.ball x₀ R ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace =
      Metric.ball x₀ R := by
  apply Set.Subset.antisymm inter_subset_left
  intro y hy
  refine ⟨hy, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace_subset_closedHalfSpace
    (ball_subset_openHalfSpace_of_dist_pos hx₀ hy)

/-- For a half-space-friendly `Ω` and an open ball strictly inside the open
half-space, if `Metric.ball x₀ R ⊆ Ω`, then the ball is contained in the
interior part `interiorHalfSpace Ω = Ω ∩ openHalfSpace`. -/
theorem ball_subset_interiorHalfSpace_of_dist_pos
    {x₀ : E} {R : ℝ}
    (hx₀ : R ≤ x₀ 0)
    {Ω : Set E}
    (h_ball_sub : Metric.ball x₀ R ⊆ Ω) :
    Metric.ball x₀ R ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω := by
  intro y hy
  refine ⟨h_ball_sub hy, ?_⟩
  exact ball_subset_openHalfSpace_of_dist_pos hx₀ hy

/-- **Interior-ball Morrey Hölder representative for `MemWkpHalfSpace`.**

For `p > d` and `MemWkpHalfSpace 1 p u Ω` on a half-space-friendly `Ω`, with
the ball `Metric.ball x₀ R` lying strictly inside the open half-space
(equivalently, `R ≤ x₀ 0`) and contained in `Ω`, there exists a continuous
representative `ũ` of `u` on `E`, equal to `u` almost everywhere on
`Metric.ball x₀ (R / 4)`, satisfying a Hölder bound with exponent `1 - d/p`
controlled by the witness gradient `L^p` norm on `Metric.ball x₀ R`.

In this interior-ball case the conclusion on
`Metric.ball x₀ (R / 4) ∩ closedHalfSpace` is automatic since the entire ball
already sits in the open half-space. -/
theorem morrey_holder_representative_halfSpace_interior
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hx₀ : R ≤ x₀ 0)
    {Ω : Set E}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen Ω)
    (h_ball_sub : Metric.ball x₀ R ⊆ Ω)
    {u : E → ℝ}
    (hu : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := d) 1 (ENNReal.ofReal p) u Ω) :
    ∃ (ũ : E → ℝ) (C : ℝ) (G : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧ 0 ≤ G ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
       ∀ y ∈ Metric.ball x₀ (R / 4) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
        ‖ũ x - ũ y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) * G) := by
  classical
  have _ := hΩ
  have h_ball_sub_int :
      Metric.ball x₀ R ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω :=
    ball_subset_interiorHalfSpace_of_dist_pos hx₀ h_ball_sub
  have h_memW1p :
      DeGiorgi.MemW1p (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) := by
    have h_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := d) 1 (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
      hu
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp h_unfold
  let hw_int : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
    h_memW1p.someWitness
  have h_ball_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  let hw_ball : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R) :=
    DeGiorgi.MemW1pWitness.restrict h_ball_open h_ball_sub_int hw_int
  obtain ⟨ũ, CHolder, hũ_cont, hC_nn, h_ae, h_holder⟩ :=
    morrey_holder_representative (d := d) hp hR hw_ball
  set G : ℝ := (eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hG_def
  have hG_nn : 0 ≤ G := ENNReal.toReal_nonneg
  refine ⟨ũ, CHolder, G, hũ_cont, hC_nn, hG_nn, h_ae, ?_⟩
  intro x hx y hy
  exact h_holder x hx.1 y hy.1

/-- **Interior-ball Morrey sup bound for `MemWkpHalfSpace`.**

For `p > d` and `MemWkpHalfSpace 1 p u Ω` on a half-space-friendly `Ω`, with
the ball `Metric.ball x₀ R` lying strictly inside the open half-space
(equivalently, `R ≤ x₀ 0`) and contained in `Ω`, there exists a continuous
representative `ũ` of `u` on `E` whose values on
`Metric.ball x₀ (R / 4) ∩ closedHalfSpace` are bounded by a constant times the
sum of the `L^p` norm of `u` and the witness gradient `L^p` norm on
`Metric.ball x₀ R`. -/
theorem morrey_sup_bound_halfSpace_interior
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hx₀ : R ≤ x₀ 0)
    {Ω : Set E}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen Ω)
    (h_ball_sub : Metric.ball x₀ R ⊆ Ω)
    {u : E → ℝ}
    (hu : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := d) 1 (ENNReal.ofReal p) u Ω) :
    ∃ (ũ : E → ℝ) (C : ℝ) (Nu G : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧ 0 ≤ Nu ∧ 0 ≤ G ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4) ∩
            DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
        ‖ũ x‖ ≤ C * (Nu + G)) := by
  classical
  have _ := hΩ
  have h_ball_sub_int :
      Metric.ball x₀ R ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω :=
    ball_subset_interiorHalfSpace_of_dist_pos hx₀ h_ball_sub
  have h_memW1p :
      DeGiorgi.MemW1p (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) := by
    have h_unfold : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := d) 1 (ENNReal.ofReal p) u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
      hu
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp h_unfold
  let hw_int : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
    h_memW1p.someWitness
  have h_ball_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  let hw_ball : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R) :=
    DeGiorgi.MemW1pWitness.restrict h_ball_open h_ball_sub_int hw_int
  obtain ⟨ũ, CSup, hũ_cont, hC_nn, h_ae, h_sup⟩ :=
    morrey_sup_bound (d := d) hp hR hw_ball
  set Nu : ℝ := (eLpNorm u (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hNu_def
  set G : ℝ := (eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hG_def
  have hNu_nn : 0 ≤ Nu := ENNReal.toReal_nonneg
  have hG_nn : 0 ≤ G := ENNReal.toReal_nonneg
  refine ⟨ũ, CSup, Nu, G, hũ_cont, hC_nn, hNu_nn, hG_nn, h_ae, ?_⟩
  intro x hx
  have h_u_finite : eLpNorm u (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := hw_ball.memLp.eLpNorm_ne_top
  have h_grad_finite : eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
    hw_ball.weakGrad_norm_memLp.eLpNorm_ne_top
  have h_sum_eq : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) +
        eLpNorm (fun z => ‖hw_ball.weakGrad z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal = Nu + G :=
    ENNReal.toReal_add h_u_finite h_grad_finite
  have h_initial := h_sup x hx.1
  rw [h_sum_eq] at h_initial
  exact h_initial

end EuclideanMorrey
end Sobolev
end Analysis
end DifferentialGeometry
