/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Operator.Hessian.Positivity
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Geometry.Operator DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace S] [ChartedSpace G S] [CompactSpace S] {e : S → M}

/-- A strict Hessian lower bound on the compact zero section extends uniformly
to a closed signed band of the same collar, metric and scalar function. -/
theorem exists_uniform_hessian_lower_bound_on_closed_band
    (d : SmoothTwoSidedCollar J I e)
    (g : SmoothRiemannianMetric I d.neighborhood) {ρ : d.neighborhood → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (c : ℝ)
    (hboundary : ∀ s : S,
      let q := d.toDiffeomorph (s, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
      ∀ v : TangentSpace I q, v ≠ 0 → c * g.inner q v v < hessFun g ρ q v v) :
    ∃ δ : ℝ, 0 < δ ∧ δ < d.radius ∧
      ∀ q : d.neighborhood, |(d.toDiffeomorph.symm q).2.val| ≤ δ →
        ∀ v : TangentSpace I q, v ≠ 0 → c * g.inner q v v < hessFun g ρ q v v := by
  let z : symmetricOpenInterval d.radius :=
    ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩
  let W : Set d.neighborhood := {q | ∀ v : TangentSpace I q, v ≠ 0 →
    c * g.inner q v v < hessFun g ρ q v v}
  have hW : IsOpen W := isOpen_hessFun_gt_mul_inner g hρ c
  let U : Set (S × symmetricOpenInterval d.radius) := d.toDiffeomorph ⁻¹' W
  have hU : IsOpen U := hW.preimage d.toDiffeomorph.continuous
  have hzero : (univ : Set S) ×ˢ ({z} : Set (symmetricOpenInterval d.radius)) ⊆ U := by
    rintro ⟨s, r⟩ ⟨_, hr⟩
    have hrz : r = z := hr
    subst r
    exact hboundary s
  obtain ⟨A, B, _, hB, hA, hzB, hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hzero
  have hBreal : IsOpen (Subtype.val '' B : Set ℝ) :=
    (symmetricOpenInterval d.radius).isOpen.isOpenMap_subtype_val B hB
  have hzreal : (0 : ℝ) ∈ Subtype.val '' B :=
    ⟨z, hzB (mem_singleton z), rfl⟩
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp hBreal 0 hzreal
  let δ := min (r / 2) (d.radius / 2)
  have hδ : 0 < δ := lt_min (half_pos hr) (half_pos d.radius_pos)
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hδd : δ < d.radius := (min_le_right _ _).trans_lt (half_lt_self d.radius_pos)
  refine ⟨δ, hδ, hδd, ?_⟩
  intro q hq
  have hcoord : (d.toDiffeomorph.symm q).2 ∈ B := by
    obtain ⟨b, hb, hbq⟩ := hrB (show (d.toDiffeomorph.symm q).2.val ∈
        Metric.ball (0 : ℝ) r from by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hq.trans_lt hδr)
    have heq : b = (d.toDiffeomorph.symm q).2 := Subtype.ext hbq
    exact heq ▸ hb
  have hmem : d.toDiffeomorph.symm q ∈ U :=
    hAB ⟨hA (mem_univ (d.toDiffeomorph.symm q).1), hcoord⟩
  change d.toDiffeomorph (d.toDiffeomorph.symm q) ∈ W at hmem
  rw [Diffeomorph.apply_symm_apply] at hmem
  exact hmem

end DifferentialGeometry.Geometry.Operator
