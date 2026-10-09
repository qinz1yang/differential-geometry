import DifferentialGeometry.Geometry.Fibration.ActualStageMeanShared
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# CFS15's stage output on the register's modulus, with locality and mean on the SAME output

External draft 59 §2.4 (disposition D59-3): the shared modulus `cfs15_shared_modulus_GAFS4` took
the jet-order-`K` kernel for FC39's `Ξ_range` and a SEPARATE jet-order-`0` kernel call for the stage
map and its mean. Here the stage output is extracted from the jet-order-`K` object itself
(`Cfs15ModulusAtV2`, the register's `Ξ_range` form), and GAF03's locality, (SM) and (SMV) are
proved on that one `Cfs15StageOutput`; the `0`-kernel conjunct of the shared theorem is not used.

* `cfs15StageOutput_of_modulusAtV2_C15`: from `Cfs15ModulusAtV2 k K (5/3) Ξ Γ` and CFS12's interior
  condition `Γ((80B + 31)Ξ(Γ)⁻¹ + 2) < 1`, an early `c_w ≥ 0` and, on every cloud with CFS15's
  hypotheses at quality `Γ`, a `Cfs15StageOutput k K (Ξ Γ) c_w S T r P` (all fields from the
  register's own jet-order-`K` selection).
* `exists_cfs15StageOutput_with_mean k K`: the shared modulus `θ₁, Ξ` (same threshold order as
  `cfs15_shared_modulus_GAFS4`) and, for `0 < Γ < θ₁`, the output together with the three levels
  of GAF03's locality, (SM) and (SMV), all on the same output.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **The stage output from the register's jet-order-`K` object.** If `Ξ` carries CFS15's
conclusion at `Γ` (`Cfs15ModulusAtV2 k K (5/3) Ξ Γ`, the register's `Ξ_range` form) and CFS12's
interior condition holds at the buffer `Ξ(Γ)⁻¹`, there is an early weight constant `c_w ≥ 0`
(depending on `k, Ξ(Γ)` only) such that every cloud with CFS15's hypotheses at quality `Γ` has a
`Cfs15StageOutput k K (Ξ Γ) c_w S T r P` built from that object's selection. -/
theorem cfs15StageOutput_of_modulusAtV2_C15 {k K : ℕ} {Ξ : ℝ → ℝ} {Γ : ℝ} (hΓ : 0 < Γ)
    (hat : Cfs15ModulusAtV2 k K (5 / 3) Ξ Γ)
    (hint : Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ Γ)⁻¹ * max (r y) (r x) →
          r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / Γ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / Γ)) ≤
            ENNReal.ofReal (Γ * r x)) →
        Nonempty (Cfs15StageOutput k K (Ξ Γ) cw S T r P) := by
  obtain ⟨⟨m, hm⟩, F, -, C, -, δ₀, -, -, hΓδ, hker⟩ := hat
  have hε : 0 < Ξ Γ := by rw [hm]; positivity
  have hε1 : Ξ Γ ≤ 1 / 10 := by
    rw [hm]
    calc (1 / 2 : ℝ) ^ (m + 4) ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 10 := by norm_num
  have hinv : 1 ≤ (Ξ Γ)⁻¹ := one_le_inv₀ hε |>.mpr (by linarith)
  obtain ⟨cw, hcw, hwb⟩ := exists_selection_weight_deriv_bound_GAFS2.{0} k (Ξ Γ)⁻¹ (5 / 3) hinv
    (by norm_num)
  refine ⟨cw, hcw, ?_⟩
  intro H _ _ _ S T hST htb r P hdim rmin R hrmin hlo hhi hmcb hcloud
  have hr : ∀ x ∈ S, 0 < r x := fun x hx => hrmin.trans_le (hlo x hx)
  obtain ⟨I, hI, hIS, hdisj, hcov, htube, hrest⟩ :=
    hker H S T hST htb r P hdim rmin R Γ hrmin hlo hhi hΓ hΓδ hmcb hcloud
  have hwb' := hwb H S T hST r P hdim hr Γ hΓ hint
    (fun x hx y hy hd => hmcb x (hST hx) y (hST hy) hd) hcloud I hI hIS hdisj htube
  obtain ⟨⟨hprop, cs, hcs⟩, hpo, hnc, hhaus, g, hg⟩ := hrest
  obtain ⟨hman, hemb, p, hsub, hnearest, hval, -, hjets, hretr, hnorm⟩ := hcs
  exact ⟨{
    eps_pos := hε
    eps_le := hε1
    radius_pos := hr
    I := I
    hI := hI
    I_subset := hIS
    disjoint := hdisj
    cover := hcov
    tube := htube
    weight_bound := hwb'
    proper := hprop
    cs := cs
    isManifold := hman
    embedding := hemb
    p := p
    submersion := hsub
    nearest := hnearest
    value_deriv := fun x z hz => hval x ⟨z, hz⟩
    ambient_jets := hjets
    retraction := hretr
    normal_proj := hnorm
    proper_over := hpo
    near_cloud := hnc
    hausdorff := hhaus
    g := g
    graph_smooth := fun x => (hg x).1
    graph_mem := fun x => (hg x).2.1
    graph_unique := fun x t ht n hn => ((hg x).2.2.1 t ht n hn).mp
    graph_eq := fun x => (hg x).2.2.2.2.1
    graph_jets := fun x => (hg x).2.2.2.2.2 }⟩

/-- **CFS15's stage output with locality and mean on ONE construction** (draft 59 §2.4). For the
stage dimension `k` and jet order `K` there are `θ₁ > 0` and `Ξ → 0` (the threshold order of
`cfs15_shared_modulus_GAFS4`) such that for `0 < Γ < θ₁`: `Ξ(Γ)` is dyadic, CFS15's full
conclusion `Cfs15ModulusAtV2 k K (5/3) Ξ Γ` and CFS12's interior condition hold, and there is an
early `c_w ≥ 0` such that every cloud with CFS15's hypotheses at quality `Γ` has an output
`O : Cfs15StageOutput k K (Ξ Γ) c_w S T r P` (from the jet-order-`K` object) on which hold:
GAF03's locality at its three levels (section, zero set, ambient nearest map), (SM) on the zero
set and (SMV) for `a = O.ambient`, each with its hypothesis on the whole closed-support
contributor list of the cloud. -/
theorem exists_cfs15StageOutput_with_mean (k K : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
        Cfs15ModulusAtV2 k K (5 / 3) Ξ Γ ∧
        Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1 ∧
        ∃ cw : ℝ, 0 ≤ cw ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
          (S T : Set H), S ⊆ T → TotallyBounded S →
          ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
          (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
          ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
          (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ Γ)⁻¹ * max (r y) (r x) →
            r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
          (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / Γ))
            ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / Γ)) ≤
              ENNReal.ofReal (Γ * r x)) →
          ∃ O : Cfs15StageOutput k K (Ξ Γ) cw S T r P,
            (∀ x ∈ S, ∀ (Kk : Submodule ℝ H) (c : H),
              (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty →
                Kk.starProjection i = c ∧ P i ≤ Kkᗮ) →
              (∀ z ∈ ball x (8 * (Ξ Γ)⁻¹ * r x),
                Kk.starProjection (cfs15Section_C15 (Ξ Γ) r P O.hI z) =
                  Kk.starProjection z - c) ∧
              (∀ w ∈ O.Z ∩ ball x (8 * (Ξ Γ)⁻¹ * r x), Kk.starProjection w = c) ∧
              (∀ z ∈ ball x (r x), Kk.starProjection (O.ambient z) = c)) ∧
            (∀ x : H, ∀ ℓ : H →L[ℝ] ℝ,
              (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty →
                P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) →
              ∀ w ∈ O.Z ∩ ball x (8 * (Ξ Γ)⁻¹ * r x),
                ℓ w = ∑ i ∈ O.hI.toFinset, cfs15Weight_C15 (Ξ Γ) r O.hI i w * ℓ i) ∧
            (∀ x ∈ S, ∀ ℓ : H →L[ℝ] ℝ,
              (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty →
                P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) →
              ∀ R₀ β : ℝ,
              (∀ i ∈ S, (closedBall i (80 * (Ξ Γ)⁻¹ * r i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * r x)).Nonempty → |ℓ i - R₀| ≤ β) →
              ∀ z ∈ ball x (r x),
                |ℓ (O.ambient z) - R₀| ≤ β ∧
                  ‖ℓ.comp (fderiv ℝ O.ambient z)‖ ≤ 2 * cw * β / r x) := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_shared_modulus_GAFS4 k K
  refine ⟨θ₁, hθ₁, Ξ, hΞ, fun Γ hΓ hΓθ => ?_⟩
  obtain ⟨hm, hat, hint, -⟩ := h Γ hΓ hΓθ
  obtain ⟨cw, hcw, hout⟩ := cfs15StageOutput_of_modulusAtV2_C15 hΓ hat hint
  refine ⟨hm, hat, hint, cw, hcw, ?_⟩
  intro H _ _ _ S T hST htb r P hdim rmin R hrmin hlo hhi hmcb hcloud
  obtain ⟨O⟩ := hout H S T hST htb r P hdim rmin R hrmin hlo hhi hmcb hcloud
  exact ⟨O, fun x hx Kk c hc => O.locality_of_cloud_C15 hx Kk c hc,
    fun x ℓ hpl => O.mean_of_cloud_C15 (x := x) ℓ hpl,
    fun x hx ℓ hpl R₀ β hβ => O.smv_of_cloud_C15 hx ℓ hpl R₀ β hβ⟩

end DifferentialGeometry.Geometry.Collapse
