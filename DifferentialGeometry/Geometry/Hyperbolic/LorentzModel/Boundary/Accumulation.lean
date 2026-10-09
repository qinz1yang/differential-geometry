/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.GromovProduct
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.DirichletDomain

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryAccumulation

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open HyperbolicGeometry BoundaryTopology GromovBoundary

variable {n : ℕ}

theorem radial_mem_cube (x : HUpper n) :
    radial x ∈ Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 => Set.Icc (-1 : ℝ) 1) := by
  apply Set.mem_univ_pi.mpr
  intro a
  apply abs_le.mp
  rcases a with i | j
  · change |(tc x.val)⁻¹ * x.val (Sum.inl i)| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr x.future)]
    calc
      (tc x.val)⁻¹ * |x.val (Sum.inl i)| ≤ (tc x.val)⁻¹ * tc x.val :=
        mul_le_mul_of_nonneg_left (abs_inl_le_tc x i) (inv_nonneg.mpr x.future.le)
      _ = 1 := inv_mul_cancel₀ x.future.ne'
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change |tc (radial x)| ≤ 1
    rw [tc_radial, abs_one]

theorem exists_boundary_subsequence {x : ℕ → HUpper n}
    (hx : Tendsto (fun k => dist basepointH (x k)) atTop atTop) :
    ∃ (ξ : BoundaryH n) (r : ℕ → ℕ), StrictMono r ∧
      ConvergesToBoundary (x ∘ r) ξ := by
  have hcube : IsCompact
      (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨v, _, r, hr, hv⟩ := hcube.tendsto_subseq (fun k => radial_mem_cube (x k))
  have htc : tc v = 1 := by
    have hl : Tendsto (fun k => tc (radial (x (r k)))) atTop (𝓝 (tc v)) :=
      (continuous_apply (Sum.inr 0)).tendsto v |>.comp hv
    have hl' : Tendsto (fun k => tc (radial (x (r k)))) atTop (𝓝 (1 : ℝ)) := by
      simp only [tc_radial]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hl hl'
  have hinv : Tendsto (fun k => (tc (x (r k)).val)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ((tendsto_atTop_tc hx).comp hr.tendsto_atTop)
  have heq (k : ℕ) : lorB (radial (x (r k))) (radial (x (r k))) =
      -((tc (x (r k)).val)⁻¹) ^ 2 := by
    simp only [radial, lorB_smul_left, lorB_smul_right, (x (r k)).is_unit]
    ring
  have hnull : lorB v v = 0 := by
    have hl : Tendsto (fun k => lorB (radial (x (r k))) (radial (x (r k))))
        atTop (𝓝 (lorB v v)) := continuous_lorB_self.tendsto v |>.comp hv
    have hl' : Tendsto (fun k => lorB (radial (x (r k))) (radial (x (r k))))
        atTop (𝓝 (0 : ℝ)) := by
      simp only [heq]
      simpa only [zero_pow two_ne_zero, neg_zero] using (hinv.pow 2).neg
    exact tendsto_nhds_unique hl hl'
  exact ⟨⟨v, hnull, htc⟩, r, hr, hv⟩

theorem exists_boundary_orbit_sequence (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) [Infinite Γ] :
    ∃ (γ : ℕ → Γ) (ξ : BoundaryH n),
      ConvergesToBoundary (fun k => (poMulAction hn).smul (γ k : PO n 1) basepointH) ξ := by
  let := poMulAction hn
  have hchoice (k : ℕ) : ∃ γ : Γ,
      (k : ℝ) < dist (basepointH : HUpper n) ((γ : PO n 1) • basepointH) := by
    obtain ⟨γ, hγ⟩ := (DirichletDomain.finite_setOf_coe_le hn Γ hΓ (k : ℝ)).exists_notMem
    exact ⟨γ, by simpa only [Set.mem_ofPred_eq, not_le, dist_comm] using hγ⟩
  choose γ hγ using hchoice
  have hdiv : Tendsto (fun k => dist (basepointH : HUpper n) ((γ k : PO n 1) • basepointH))
      atTop atTop :=
    tendsto_atTop_mono (fun k => (hγ k).le) tendsto_natCast_atTop_atTop
  obtain ⟨ξ, r, _, hr⟩ := exists_boundary_subsequence hdiv
  exact ⟨γ ∘ r, ξ, hr⟩

theorem boundary_fixed_of_bounded_displacement (hn : 1 ≤ n) (g : PO n 1)
    {x : ℕ → HUpper n} {ξ : BoundaryH n} (hx : ConvergesToBoundary x ξ)
    {B : ℝ} (hB : ∀ k, dist (x k) ((poMulAction hn).smul g (x k)) ≤ B) :
    (poBoundaryMulAction hn).smul g ξ = ξ := by
  have hg := convergesToBoundary_smul hn g hx
  have hdiv := tendsto_atTop_dist_basepoint (tendsto_atTop_tc_of_convergesToBoundary hg)
  exact convergesToBoundary_unique hg
    (GromovBoundary.ConvergesToBoundary.of_bounded_dist hx hB hdiv)

theorem exists_boundary_fixed_by_centralizer (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : IsDiscrete (SetLike.coe D)) [Infinite D] :
    ∃ ξ : BoundaryH n, ∀ a ∈ Subgroup.centralizer (D : Set (PO n 1)),
      (poBoundaryMulAction hn).smul a ξ = ξ := by
  let := poMulAction hn
  obtain ⟨d, ξ, hd⟩ := exists_boundary_orbit_sequence hn D hD
  refine ⟨ξ, fun a ha => boundary_fixed_of_bounded_displacement hn a hd
    (B := dist (basepointH : HUpper n) (a • basepointH)) (fun k => ?_)⟩
  have hc : a * (d k : PO n 1) = (d k : PO n 1) * a :=
    (Subgroup.mem_centralizer_iff.mp ha (d k) (d k).property).symm
  calc
    dist ((d k : PO n 1) • (basepointH : HUpper n)) (a • ((d k : PO n 1) • basepointH))
        = dist ((d k : PO n 1) • basepointH) ((d k : PO n 1) • (a • basepointH)) := by
          rw [← mul_smul, hc, mul_smul]
    _ = dist basepointH (a • basepointH) := po_dist_smul hn (d k) _ _
    _ ≤ _ := le_rfl

end DifferentialGeometry.BoundaryAccumulation
