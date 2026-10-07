/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.StratumExtrema

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.ElementaryThickPoint

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful
open HyperbolicConvexity AsymptoticRays BusemannCocycle BoundaryStabilizer
open OrbifoldStrata AxisGeometry

variable {n : ℕ}

theorem eventually_finite_of_displacement_escape (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε) (q : ℝ → HUpper n) (y p : HUpper n)
    (hsub : ∀ᶠ t : ℝ in atTop,
      closedSmallElements hn Γ ε (q t) ⊆ closedSmallElements hn Γ ε y)
    (hescape : ∀ g ∈ closedSmallElements hn Γ ε y,
      (poMulAction hn).smul g p ≠ p →
        Tendsto (fun t : ℝ => Real.cosh (dist ((poMulAction hn).smul g (q t)) (q t)))
          atTop atTop) :
    ∀ᶠ t : ℝ in atTop, q t ∈ finiteLocus hn Γ ε := by
  classical
  let := poMulAction hn
  have hlong : ∀ᶠ t : ℝ in atTop, ∀ g ∈ closedSmallElements hn Γ ε y,
      g • p ≠ p → Real.cosh ε < Real.cosh (dist (g • q t) (q t)) := by
    apply (finite_closedSmallElements hn Γ hΓ ε y).eventually_all.mpr
    intro g hg
    by_cases hp : g • p = p
    · exact Eventually.of_forall (fun _ h => (h hp).elim)
    · filter_upwards [(hescape g hg hp).eventually_gt_atTop (Real.cosh ε)] with t ht
      exact fun _ => ht
  filter_upwards [hsub, hlong] with t ht hlt
  have hfix : closedSmallSubgroup hn Γ ε (q t) ≤ MulAction.stabilizer (PO n 1) p := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change g • p = p
    by_contra hp
    have hl := hlt g (ht hg) hp
    have hu := Real.cosh_strictMonoOn.monotoneOn dist_nonneg hε hg.2
    exact (not_lt_of_ge hu) hl
  exact (fixedLocus_nonempty_iff_finite hn _
    (hΓ.mono (closedSmallSubgroup_le hn Γ ε (q t)))).mp
      ⟨p, fun g => hfix g.property⟩

theorem cosh_displacement_rayTo_neg_tendsto (hn : 1 ≤ n)
    (g : PO n 1) (ξ : BoundaryH n)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (p : HUpper n)
    (hp : (poMulAction hn).smul g p ≠ p) :
    Tendsto (fun t : ℝ => Real.cosh
      (dist ((poMulAction hn).smul g (rayTo p ξ (-t))) (rayTo p ξ (-t))))
      atTop atTop := by
  have hC : 0 < Real.cosh (dist ((poMulAction hn).smul g p) p) - 1 := by
    have h := Real.cosh_strictMonoOn (by norm_num : (0 : ℝ) ∈ Ici 0)
      dist_nonneg (dist_pos.mpr hp)
    simpa only [Real.cosh_zero, sub_pos] using h
  have hE : Tendsto (fun t : ℝ => Real.exp (2 * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have h := tendsto_atTop_add_const_left atTop 1 (hE.const_mul_atTop hC)
  apply h.congr
  intro t
  have he := ParabolicRegions.cosh_displacement_rayTo_sub_one hn g ξ hfix hscale p (-t)
  rw [show -(2 * -t) = 2 * t by ring] at he
  linarith

theorem eventually_finite_horospherical (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε) (ξ : BoundaryH n)
    (hfix : ∀ g : Γ, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧
      poConfFactor hn (g : PO n 1) ξ = 1) (p : HUpper n) :
    ∀ᶠ t : ℝ in atTop, rayTo p ξ (-t) ∈ finiteLocus hn Γ ε := by
  apply eventually_finite_of_displacement_escape hn Γ hΓ hε
    (fun t => rayTo p ξ (-t)) p p
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    intro g hg
    exact ⟨hg.1, (StratumDeformation.displacement_le_rayTo_neg hn g ξ
      (hfix ⟨g, hg.1⟩).1 (hfix ⟨g, hg.1⟩).2 p ht).trans hg.2⟩
  · intro g hg hp
    exact cosh_displacement_rayTo_neg_tendsto hn g ξ
      (hfix ⟨g, hg.1⟩).1 (hfix ⟨g, hg.1⟩).2 p hp

theorem axisRadius_smul (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hp : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (y : HUpper n) :
    axisRadius ξ η ((poMulAction hn).smul g y) = axisRadius ξ η y := by
  let := poMulAction hn
  rw [← cosh_dist_axisFoot ξ η hne, axisFoot_smul hn g ξ η hne hp y]
  exact (congrArg Real.cosh (po_dist_smul hn g y (axisFoot ξ η hne y))).trans
    (cosh_dist_axisFoot ξ η hne y)

theorem normal_coefficient_pos (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hp : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y)
    (hg : (poMulAction hn).smul g (axisFoot ξ η hne y) ≠ axisFoot ξ η hne y) :
    0 < Real.cosh (dist ((poMulAction hn).smul g y) y) -
      Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y))
        (axisFoot ξ η hne y)) := by
  let p := axisFoot ξ η hne y
  let R := axisRadius ξ η y
  let A := Real.cosh (dist ((poMulAction hn).smul g p) p)
  have hR : 1 < R := by
    rw [show R = Real.cosh (dist y p) by
      exact (cosh_dist_axisFoot ξ η hne y).symm]
    have h := Real.cosh_strictMonoOn (by norm_num : (0 : ℝ) ∈ Ici 0)
      dist_nonneg (dist_pos.mpr hy.symm)
    simpa only [Real.cosh_zero] using h
  have hA : 1 < A := by
    have h := Real.cosh_strictMonoOn (by norm_num : (0 : ℝ) ∈ Ici 0)
      dist_nonneg (dist_pos.mpr hg)
    simpa only [Real.cosh_zero, A] using h
  have he := cosh_dist_decomposition ξ η hne ((poMulAction hn).smul g y) y
  have hb := normal_pair_le ξ η hne ((poMulAction hn).smul g y) y
  rw [axisRadius_smul hn g ξ η hne hp y, axisFoot_smul hn g ξ η hne hp y] at he
  rw [axisRadius_smul hn g ξ η hne hp y] at hb
  have hR2 : 0 < R * R - 1 := by nlinarith
  have hprod := mul_pos hR2 (sub_pos.mpr hA)
  change 0 < Real.cosh (dist ((poMulAction hn).smul g y) y) - A
  change Real.cosh (dist ((poMulAction hn).smul g y) y) = R * R * A - _ at he
  change _ ≤ R * R - 1 at hb
  nlinarith

theorem sinh_tendsto_atTop : Tendsto Real.sinh atTop atTop := by
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0 : ℝ)).mono (fun _ ht => ProjectionContraction.half_le_sinh ht))
  exact tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)

theorem cosh_displacement_normal_tendsto (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hp : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y)
    (hg : (poMulAction hn).smul g (axisFoot ξ η hne y) ≠ axisFoot ξ η hne y) :
    Tendsto (fun t : ℝ => Real.cosh (dist ((poMulAction hn).smul g
      (geodFromTo (axisFoot ξ η hne y) y hy t))
        (geodFromTo (axisFoot ξ η hne y) y hy t))) atTop atTop := by
  have hs := Real.sinh_pos_iff.mpr (dist_pos.mpr hy)
  have hpow := (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp
    (sinh_tendsto_atTop.atTop_div_const hs)
  have hmul := hpow.atTop_mul_const (normal_coefficient_pos hn g ξ η hne hp y hy hg)
  exact (tendsto_atTop_add_const_left atTop _ hmul).congr
    (fun t => (cosh_displacement_normal_geod hn g ξ η hne hp y hy t).symm)

theorem eventually_finite_axial (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hp : ∀ g : Γ,
      (poBoundaryMulAction hn).smul (g : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (g : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) :
    ∀ᶠ t : ℝ in atTop,
      geodFromTo (axisFoot ξ η hne y) y hy t ∈ finiteLocus hn Γ ε := by
  apply eventually_finite_of_displacement_escape hn Γ hΓ hε
    (geodFromTo (axisFoot ξ η hne y) y hy) y (axisFoot ξ η hne y)
  · filter_upwards [eventually_ge_atTop (dist (axisFoot ξ η hne y) y)] with t ht
    intro g hg
    exact ⟨hg.1, (displacement_le_normal_geod hn g ξ η hne
      (hp ⟨g, hg.1⟩) y hy ht).trans hg.2⟩
  · intro g hg hgp
    exact cosh_displacement_normal_tendsto hn g ξ η hne (hp ⟨g, hg.1⟩) y hy hgp

theorem finiteLocus_nonempty_of_geometry (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε) (hgeom : ElementaryGeometry hn Γ) :
    (finiteLocus hn Γ ε).Nonempty := by
  let : Nonempty (HUpper n) := ⟨basepointH⟩
  rcases hgeom with ⟨hf, _⟩ | ⟨ξ, η, hne, hp⟩ | ⟨ξ, hξ⟩
  · let := hf
    exact ⟨basepointH, Finite.of_injective
      (Subgroup.inclusion (closedSmallSubgroup_le hn Γ ε basepointH))
        (Subgroup.inclusion_injective _)⟩
  · have hnot : axis ξ η ≠ univ := by
      intro he
      have h := StratumMaximum.interior_axis_eq_empty hdim ξ η
      rw [he, interior_univ] at h
      exact Set.univ_nonempty.ne_empty h
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnot
    have hpy : axisFoot ξ η hne y ≠ y := fun he => hy (he ▸ axisFoot_mem ξ η hne y)
    obtain ⟨t, ht⟩ := (eventually_finite_axial hn Γ hΓ hε ξ η hne hp y hpy).exists
    exact ⟨_, ht⟩
  · obtain ⟨t, ht⟩ := (eventually_finite_horospherical hn Γ hΓ hε ξ hξ basepointH).exists
    exact ⟨_, ht⟩

end DifferentialGeometry.ElementaryThickPoint
