import DifferentialGeometry.Geometry.Metric.CloudGateApplications
import DifferentialGeometry.Geometry.Metric.UniformCutoffConsumer

/-!
# CFS19: threshold gates, fixed-data support stability and the projection tube

Blueprint `master207B.tex`, CFS19 (`prop:fibration-cutoff-gate-stability`, lines 3053–3116).
The first clause (a fixed-data tolerance `κ > 0`: `|f − F| ≤ κρ` keeps `f(M)` in `O` and
`f(p) ∈ supp_O ψ ⇒ p ∈ A`) is X80's `exists_fixedData_gate_support_tolerance`, stated there for
functions on the subtype `O`. This module states the row for `ψ, G : H → ℝ` with the RELATIVE
closed support `closure (support ψ ∩ O) ∩ O`, and proves the second clause: if the original cloud
over `A` satisfies CFS16 (full marker at every point of `A`, scale comparability at every
preimage with a positive marker, a selected preimage of every centre) and `κ ≤ 3σ/10`, then
`f(M) ∩ supp_O ψ ⊆ π⁻¹ N_r(S)` with `S = π F(A)`, `r = σ ρ(sel ·)`
(`cfsProjectedTube`), and CFS18 supplies the smooth adjustment on an open neighbourhood of `f(M)`.

* `mem_tsupport_comp_val_iff`: the relative closed support is the closed support of the
  restriction to the subtype `O`.
* `cfs19_row`: both clauses and the CFS18 neighbourhood.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open scoped ContDiff

namespace GC.MetricGeometry

/-- The relative closed support `closure (support ψ ∩ O)` at a point of `O` is the closed support of
`ψ` restricted to the subtype `O`. -/
theorem mem_tsupport_comp_val_iff {H : Type*} [TopologicalSpace H] {O : Set H} {ψ : H → ℝ}
    {z : H} (hz : z ∈ O) :
    (⟨z, hz⟩ : O) ∈ tsupport (ψ ∘ Subtype.val) ↔ z ∈ closure (support ψ ∩ O) := by
  rw [tsupport, closure_subtype, support_comp_eq_preimage, Subtype.image_preimage_coe,
    inter_comm]

/-- CFS19 (`prop:fibration-cutoff-gate-stability`): a fixed-data tolerance `κ ≤ 3σ/10` such that
every `f` with `|f − F| ≤ κρ` maps into `O`, has its relative closed support of `ψ` only over the
original core `A`, there in the CFS16 half-tube of the original centre, so
`f(M) ∩ supp_O ψ ⊆ π⁻¹ N_r(S)`; and CFS18 gives the smooth adjustment by any field `k` smooth on
`O ∩ π⁻¹ N_r(S)` on an open neighbourhood of `f(M)`. -/
theorem cfs19_row {M H Hq I : Type*} [TopologicalSpace M] [CompactSpace M]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Hq] [NormedSpace ℝ Hq]
    (O : Set H) (hO : IsOpen O) (F : M → H) (hFO : ∀ p, F p ∈ O) (hF : Continuous F)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hρpos : ∀ p, 0 < ρ p) (A : Set M) (hA : IsOpen A)
    (G ψ : H → ℝ) (hG : ContinuousOn G O) (hψ : ContDiffOn ℝ ∞ ψ O)
    (hgate : closure (support ψ ∩ O) ∩ O ⊆ {z | (1 / 2 : ℝ) ≤ G z})
    (houtside : ∀ p ∉ A, G (F p) = 0)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (marker : I → Hq → ℝ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (hsupport : ∀ i p, 0 < marker i (π (F p)) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (hfull : ∀ p ∈ A, ∃ i, marker i (π (F p)) = R i)
    (sel : M → M) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ : ℝ} (hσ : 0 < σ)
    [∀ z, Decidable (z ∈ cfsProjectedTube π F A (fun p => σ * ρ (sel p)))] :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 * σ / 10 ∧ ∀ f : M → H, (∀ p, ‖f p - F p‖ ≤ κ * ρ p) →
      (∀ p, f p ∈ O) ∧
      (∀ p, f p ∈ closure (support ψ ∩ O) → p ∈ A ∧
        ‖π (f p) - π (F p)‖ ≤ σ * ρ (sel p) / 2 ∧
        ball (π (f p)) (σ * ρ (sel p) / 2) ⊆ ball (π (F p)) (σ * ρ (sel p))) ∧
      range f ∩ (closure (support ψ ∩ O) ∩ O) ⊆ cfsProjectedTube π F A (fun p => σ * ρ (sel p)) ∧
      ∀ k : H → H, ContDiffOn ℝ ∞ k (O ∩ cfsProjectedTube π F A (fun p => σ * ρ (sel p))) →
        ∃ V : Set H, IsOpen V ∧ range f ⊆ V ∧ V ⊆ O ∧
          closure (support ψ ∩ V) ∩ V ⊆ cfsProjectedTube π F A (fun p => σ * ρ (sel p)) ∧
          ContDiffOn ℝ ∞ ((cfsProjectedTube π F A (fun p => σ * ρ (sel p))).piecewise
            (fun z => z + ψ z • k z) id) V ∧
          (∀ z ∈ V, z ∉ cfsProjectedTube π F A (fun p => σ * ρ (sel p)) → ψ z = 0) := by
  let F' : M → O := fun p => ⟨F p, hFO p⟩
  have hF' : Continuous F' := hF.subtype_mk hFO
  have hG' : Continuous (G ∘ Subtype.val : O → ℝ) := hG.domRestrict
  have hgate' : tsupport (ψ ∘ Subtype.val : O → ℝ) ⊆ {z | (1 / 2 : ℝ) ≤ (G ∘ Subtype.val) z} := by
    rintro ⟨z, hz⟩ hzs
    exact hgate ⟨(mem_tsupport_comp_val_iff (ψ := ψ) hz).mp hzs, hz⟩
  obtain ⟨κ, hκ, hκc, hprod⟩ := exists_bounded_fixedData_gate_support_tolerance O hO F' hF' ρ hρ
    (fun p => (hρpos p).le) A hA (G ∘ Subtype.val) (ψ ∘ Subtype.val) hG' hgate' houtside
    (by positivity : (0 : ℝ) < 3 * σ / 10)
  refine ⟨κ, hκ, hκc, fun f hf => ?_⟩
  have hfO : ∀ p, f p ∈ O := fun p => (hprod f hf p).1
  have hloc : ∀ p, f p ∈ closure (support ψ ∩ O) → p ∈ A ∧
      ‖π (f p) - π (F p)‖ ≤ σ * ρ (sel p) / 2 ∧
      ball (π (f p)) (σ * ρ (sel p) / 2) ⊆ ball (π (F p)) (σ * ρ (sel p)) := by
    intro p hp
    obtain ⟨hpO, himp⟩ := hprod f hf p
    have hpA : p ∈ A := himp ((mem_tsupport_comp_val_iff (ψ := ψ) hpO).mpr hp)
    obtain ⟨i, hi⟩ := hfull p hpA
    have hbuf := retained_marker_projected_half_buffer π hπ F f ρ marker R hR hsupport p (sel p)
      (hsel p).symm i hi σ κ hσ hκc (hf p)
    exact ⟨hpA, hbuf.2.2.2.1, hbuf.2.2.2.2.1⟩
  have htube : range f ∩ (closure (support ψ ∩ O) ∩ O) ⊆
      cfsProjectedTube π F A (fun p => σ * ρ (sel p)) := by
    rintro _ ⟨⟨p, rfl⟩, hcl, -⟩
    obtain ⟨hpA, hd, -⟩ := hloc p hcl
    have hr : 0 < σ * ρ (sel p) := mul_pos hσ (hρpos (sel p))
    refine ⟨p, hpA, ?_⟩
    rw [mem_ball, dist_eq_norm]
    linarith
  refine ⟨hfO, hloc, htube, fun k hk => ?_⟩
  have hKO : range f ⊆ O := by
    rintro _ ⟨p, rfl⟩
    exact hfO p
  obtain ⟨V, hV, hKV, hVO, hVsupp, hsmooth, hzero, -, -⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_closedSupport_adjustment hO
      (isOpen_cfsProjectedTube π F A _) hKO hψ hk htube
  exact ⟨V, hV, hKV, hVO, hVsupp, hsmooth, hzero⟩

end GC.MetricGeometry
