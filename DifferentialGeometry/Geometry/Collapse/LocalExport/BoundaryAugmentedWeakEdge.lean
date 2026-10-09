import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedOriginalMap

/-!
# BCG03: the weak-edge block (WB) on `edgeB` and its zero extension to `W` (lane BAUG-A, G2)

Draft 61 §2.2, disposition D61-4. On the boundary family (`LocalPacketsOnB` and its extensions) the
`E'` block of the augmented map reads the REVISED edge family `edgeB` only:
`t_B = edgeB.smoothing / ρ`, `z_{E'} = h(t_B/Δ) · χ_{1/2,1}(Σ_{i ∈ I_e^B} ζ_i^B)` with
`h = cgpEdgeH`
and the actual `edgeB` cutoffs `ζ_i^B = edgeB.cutoff_BAUGA i`, and
`F_{∂,E'} = (ρ t_B z_{E'}, ρ z_{E'})` (WB). No additional boundary cutoff is used: on the closed
support of `z_{E'}` the `edgeB` cutoff sum is `≥ 1/2`, so some actual `edgeB` cutoff is nonzero and
the whole block is supported in finitely many closed `edgeB` buffer balls `B̄(j, 14Δρ(j))`.

On a complete carrier (`LocalPacketsOnB.…`):
* `edgeBHeight_BAUGA` (`t_B`), `edgeBSum_BAUGA`, `edgeBMarker_BAUGA` (`z_{E'}`),
  `edgeBDomain_BAUGA`,
  `weakEdgeBlockOn_BAUGA` (WB);
* `contMDiff_edgeBMarker_BAUGA`, `tsupport_edgeBMarker_subset_domain_BAUGA`,
  `tsupport_edgeBMarker_subset_closedBalls_BAUGA`, `tsupport_edgeBMarker_subset_region_BAUGA`
  (inside `U₁` through `edgeB_domain`), `edgeBMarker_mem_Icc_BAUGA`,
  `contMDiff_weakEdgeBlockOn_BAUGA`, `tsupport_weakEdgeBlockOn_subset_BAUGA`,
  `weakEdgeBlockOn_eq_BAUGA` (`ρ t_B z = edgeB.smoothing · z`).
On the original carrier (family on `W°` with `U₁ = {D > 10}`, the T3B regions):
* `contMDiff_weakEdgeBlockW_BAUGA`: the zero extension of (WB) from `W°` to `W` is smooth (the
  closed support lies in `{D ≥ 10}`, compact in `W`);
* `weakEdgeBlockW_edgePrime_formula_BAUGA` (the formula (WB) on `W°`) and
  `weakEdgeBlockW_eq_zero_of_notMem_BAUGA` (zero off `W°`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis DifferentialGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Carrier

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

namespace LocalPacketsOnB

variable (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
  V vs U₁ U₂ Ue₁ Ue₂)

/-- The normalized weak-edge height `t_B = edgeB.smoothing / ρ` of the ONE `edgeB` smoothing. -/
def edgeBHeight_BAUGA (x : X) : ℝ :=
  F.edgeB.smoothing x / ρ x

/-- The sum `Σ_{i ∈ I_e^B} ζ_i^B` of the actual `edgeB` cutoffs. -/
def edgeBSum_BAUGA (x : X) : ℝ :=
  ∑ j : F.edgeB.finite_centres.toFinset, F.edgeB.cutoff_BAUGA j x

/-- The `E'` marker `z_{E'} = h(t_B/Δ) χ_{1/2,1}(Σ_{I_e^B} ζ_i^B)`. -/
def edgeBMarker_BAUGA (x : X) : ℝ :=
  cgpEdgeH (F.edgeBHeight_BAUGA x / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1 (F.edgeBSum_BAUGA x)

/-- The open collar region of the revised edge charts where `t_B` is smooth. -/
def edgeBDomain_BAUGA : Set X :=
  {x | ∃ j ∈ F.edgeB.centres, x ∈ ball j (100 * Δ * ρ j) ∧ |F.edgeB.coord_BAUGA j x| < 10 * Δ ∧
    Δ / 10 < F.edgeBHeight_BAUGA x ∧ F.edgeBHeight_BAUGA x < 10 * Δ}

/-- **The weak-edge block (WB)** `F_{∂,E'} = (ρ t_B z_{E'}, ρ z_{E'})` on the carrier. -/
def weakEdgeBlockOn_BAUGA (x : X) : ℝ × ℝ :=
  (ρ x * F.edgeBHeight_BAUGA x * F.edgeBMarker_BAUGA x, ρ x * F.edgeBMarker_BAUGA x)

/-- `ρ t_B z = edgeB.smoothing · z`. -/
theorem weakEdgeBlockOn_eq_BAUGA (x : X) :
    F.weakEdgeBlockOn_BAUGA x =
      (F.edgeB.smoothing x * F.edgeBMarker_BAUGA x, ρ x * F.edgeBMarker_BAUGA x) := by
  have h := (hρ x).ne'
  unfold weakEdgeBlockOn_BAUGA edgeBHeight_BAUGA
  congr 1
  field_simp

theorem continuous_edgeBHeight_BAUGA : Continuous F.edgeBHeight_BAUGA :=
  F.edgeB.lipschitz_smoothing.continuous.div F.contMDiff_scale.continuous fun x => (hρ x).ne'

theorem isOpen_edgeBDomain_BAUGA : IsOpen F.edgeBDomain_BAUGA := by
  have h : F.edgeBDomain_BAUGA = ⋃ j ∈ F.edgeB.centres, (ball j (100 * Δ * ρ j) ∩
      F.edgeB.coord_BAUGA j ⁻¹' Ioo (-(10 * Δ)) (10 * Δ)) ∩
      F.edgeBHeight_BAUGA ⁻¹' Ioo (Δ / 10) (10 * Δ) := by
    ext x
    simp only [edgeBDomain_BAUGA, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_Ioo,
      abs_lt, exists_prop]
    constructor
    · rintro ⟨j, hj, hx, ⟨h1, h2⟩, h3, h4⟩
      exact ⟨j, hj, ⟨hx, h1, h2⟩, h3, h4⟩
    · rintro ⟨j, hj, ⟨hx, h1, h2⟩, h3, h4⟩
      exact ⟨j, hj, hx, ⟨h1, h2⟩, h3, h4⟩
  rw [h]
  refine isOpen_biUnion fun j hj => IsOpen.inter ?_
    (isOpen_Ioo.preimage F.continuous_edgeBHeight_BAUGA)
  exact (F.edgeB.contMDiffOn_coord_BAUGA hj).continuousOn.isOpen_inter_preimage isOpen_ball
    isOpen_Ioo

theorem contMDiff_edgeBSum_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F.edgeBSum_BAUGA := by
  unfold edgeBSum_BAUGA
  exact contMDiff_finsetSum fun j _ => F.contMDiff_edgeB_cutoff_BAUGA hΛ hΔ hμ hτ hΔΛ j.1

/-- Where the `edgeB` cutoff sum is at least `1/2`, some actual `edgeB` cutoff is nonzero. -/
theorem exists_edgeB_cutoff_ne_zero_of_half_le_BAUGA {x : X} (hx : 1 / 2 ≤ F.edgeBSum_BAUGA x) :
    ∃ j ∈ F.edgeB.centres, F.edgeB.cutoff_BAUGA j x ≠ 0 := by
  have hne : F.edgeBSum_BAUGA x ≠ 0 := by linarith
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨j.1, (Set.Finite.mem_toFinset _).mp j.2, hj⟩

/-- A point with an active `edgeB` cutoff and height in `[Δ/5, 9Δ]` lies in the collar domain. -/
theorem mem_edgeBDomain_of_BAUGA (hΔ : 0 < Δ) {j x : X} (hjx : F.edgeB.cutoff_BAUGA j x ≠ 0)
    (h1 : Δ / 5 ≤ F.edgeBHeight_BAUGA x) (h2 : F.edgeBHeight_BAUGA x ≤ 9 * Δ) :
    x ∈ F.edgeBDomain_BAUGA := by
  obtain ⟨hj, hball, hcoord, -⟩ := F.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hjx
  have hrj := hρ j
  refine ⟨j, hj, ?_, by linarith, by linarith, by linarith⟩
  have h := (inv_mul_lt_iff₀ hrj).mp hball
  rw [mem_ball]
  linarith

/-- The `E'` marker `z_{E'}` is smooth on the carrier. -/
theorem contMDiff_edgeBMarker_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F.edgeBMarker_BAUGA := by
  have hsum := F.contMDiff_edgeBSum_BAUGA hΛ hΔ hμ hτ hΔΛ
  have hht := F.continuous_edgeBHeight_BAUGA
  intro x
  by_cases hx : F.edgeBSum_BAUGA x < 1 / 2
  · have h0 : F.edgeBMarker_BAUGA =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hsum.continuous.continuousAt.eventually (gt_mem_nhds hx)] with y hy
      rw [edgeBMarker_BAUGA, cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy)
        (by norm_num) hy.le, mul_zero]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  rw [not_lt] at hx
  obtain ⟨j, -, hjx⟩ := F.exists_edgeB_cutoff_ne_zero_of_half_le_BAUGA hx
  have hcont : Continuous fun y => F.edgeBHeight_BAUGA y / Δ := hht.div_const Δ
  by_cases hlow : F.edgeBHeight_BAUGA x / Δ < 1 / 5
  · have h0 : F.edgeBMarker_BAUGA =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hlow)] with y hy
      rw [edgeBMarker_BAUGA, cgpEdgeH_eq_zero_of_le hy.le, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  by_cases hhigh : 9 < F.edgeBHeight_BAUGA x / Δ
  · have h0 : F.edgeBMarker_BAUGA =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hhigh)] with y hy
      rw [edgeBMarker_BAUGA, cgpEdgeH_eq_zero_of_ge hy.le, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  rw [not_lt] at hlow hhigh
  have h1 : Δ / 5 ≤ F.edgeBHeight_BAUGA x := by
    rw [le_div_iff₀ hΔ] at hlow
    linarith
  have h2 : F.edgeBHeight_BAUGA x ≤ 9 * Δ := by
    rw [div_le_iff₀ hΔ] at hhigh
    linarith
  obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ := F.mem_edgeBDomain_of_BAUGA hΔ hjx h1 h2
  have hH : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F.edgeBHeight_BAUGA x :=
    F.edgeB.contMDiffAt_height_of_collar_BAUGA hk hxk hck.le hk1.le hk2.le
  have hA : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => cgpEdgeH (F.edgeBHeight_BAUGA y / Δ)) x :=
    (cgpEdgeH_contDiff.comp (contDiff_id.div_const Δ)).contMDiff.contMDiffAt.comp x hH
  have hB : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (F.edgeBSum_BAUGA y)) x :=
    (contDiff_cfsRamp lc87EdgeTransition_contDiff _ _).contMDiff.contMDiffAt.comp x (hsum x)
  exact hA.mul hB

/-- Where `z_{E'}` is nonzero: `Δ/5 ≤ t_B ≤ 9Δ` and the `edgeB` cutoff sum is `≥ 1/2`. -/
theorem edgeBMarker_ne_zero_BAUGA (hΔ : 0 < Δ) {x : X} (hx : F.edgeBMarker_BAUGA x ≠ 0) :
    Δ / 5 ≤ F.edgeBHeight_BAUGA x ∧ F.edgeBHeight_BAUGA x ≤ 9 * Δ ∧
      1 / 2 ≤ F.edgeBSum_BAUGA x := by
  rw [edgeBMarker_BAUGA] at hx
  have hH : cgpEdgeH (F.edgeBHeight_BAUGA x / Δ) ≠ 0 := left_ne_zero_of_mul hx
  have hR : cfsRamp lc87EdgeTransition (1 / 2) 1 (F.edgeBSum_BAUGA x) ≠ 0 :=
    right_ne_zero_of_mul hx
  refine ⟨?_, ?_, ?_⟩
  · by_contra hlt
    apply hH
    refine cgpEdgeH_eq_zero_of_le ?_
    rw [div_le_iff₀ hΔ]
    linarith [not_le.mp hlt]
  · by_contra hlt
    apply hH
    refine cgpEdgeH_eq_zero_of_ge ?_
    rw [le_div_iff₀ hΔ]
    linarith [not_le.mp hlt]
  · by_contra hlt
    exact hR (cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num)
      (not_le.mp hlt).le)

/-- The closed support of `z_{E'}` lies in the open collar domain of the revised edge charts. -/
theorem tsupport_edgeBMarker_subset_domain_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) :
    tsupport F.edgeBMarker_BAUGA ⊆ F.edgeBDomain_BAUGA := by
  have hsum := (F.contMDiff_edgeBSum_BAUGA hΛ hΔ hμ hτ hΔΛ).continuous
  have hht := F.continuous_edgeBHeight_BAUGA
  let S : Set X := {x | Δ / 5 ≤ F.edgeBHeight_BAUGA x ∧ F.edgeBHeight_BAUGA x ≤ 9 * Δ ∧
    1 / 2 ≤ F.edgeBSum_BAUGA x}
  have hS : IsClosed S :=
    (isClosed_le continuous_const hht).inter ((isClosed_le hht continuous_const).inter
      (isClosed_le continuous_const hsum))
  have hsupp : Function.support F.edgeBMarker_BAUGA ⊆ S := fun x hx =>
    F.edgeBMarker_ne_zero_BAUGA hΔ hx
  intro x hx
  obtain ⟨h1, h2, h3⟩ := closure_minimal hsupp hS hx
  obtain ⟨j, -, hjx⟩ := F.exists_edgeB_cutoff_ne_zero_of_half_le_BAUGA h3
  exact F.mem_edgeBDomain_of_BAUGA hΔ hjx h1 h2

/-- **No extra cutoff**: the closed support of `z_{E'}` lies in the finitely many closed `edgeB`
buffer balls `B̄(j, 14Δρ(j))`. -/
theorem tsupport_edgeBMarker_subset_closedBalls_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) :
    tsupport F.edgeBMarker_BAUGA ⊆ ⋃ j ∈ F.edgeB.centres, closedBall j (14 * Δ * ρ j) := by
  have hsum := (F.contMDiff_edgeBSum_BAUGA hΛ hΔ hμ hτ hΔΛ).continuous
  have hclosed : IsClosed (⋃ j ∈ F.edgeB.centres, closedBall j (14 * Δ * ρ j)) :=
    F.edgeB.finite_centres.isClosed_biUnion fun _ _ => isClosed_closedBall
  have hS : IsClosed {x | 1 / 2 ≤ F.edgeBSum_BAUGA x} := isClosed_le continuous_const hsum
  have hsub : tsupport F.edgeBMarker_BAUGA ⊆ {x | 1 / 2 ≤ F.edgeBSum_BAUGA x} :=
    closure_minimal (fun x hx => (F.edgeBMarker_ne_zero_BAUGA hΔ hx).2.2) hS
  intro x hx
  obtain ⟨j, hj, hjx⟩ := F.exists_edgeB_cutoff_ne_zero_of_half_le_BAUGA (hsub hx)
  exact mem_biUnion hj
    ((F.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ hμ hτ hΔΛ hj).1 (subset_tsupport _ hjx))

/-- The closed support of `z_{E'}` lies in the region `U₁` (through `edgeB_domain`). -/
theorem tsupport_edgeBMarker_subset_region_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) :
    tsupport F.edgeBMarker_BAUGA ⊆ U₁ := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp
    (F.tsupport_edgeBMarker_subset_closedBalls_BAUGA hΛ hΔ hμ hτ hΔΛ hx)
  refine F.edgeB_domain j hj (closedBall_subset_ball ?_ hxj)
  have := mul_pos hΔ (hρ j)
  nlinarith

theorem edgeBMarker_mem_Icc_BAUGA (x : X) : F.edgeBMarker_BAUGA x ∈ Icc (0 : ℝ) 1 := by
  have h1 := cgpEdgeH_mem_Icc (F.edgeBHeight_BAUGA x / Δ)
  have h2 := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc (1 / 2) 1 (F.edgeBSum_BAUGA x)
  rw [edgeBMarker_BAUGA]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The weak-edge block (WB) is smooth on the carrier. -/
theorem contMDiff_weakEdgeBlockOn_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) ∞ F.weakEdgeBlockOn_BAUGA := by
  have hz := F.contMDiff_edgeBMarker_BAUGA hΛ hΔ hμ hτ hΔΛ
  have hρs := F.contMDiff_scale
  have hfst : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      fun x => ρ x * F.edgeBHeight_BAUGA x * F.edgeBMarker_BAUGA x := by
    intro x
    by_cases hx : x ∈ tsupport F.edgeBMarker_BAUGA
    · obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ :=
        F.tsupport_edgeBMarker_subset_domain_BAUGA hΛ hΔ hμ hτ hΔΛ hx
      have hH : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F.edgeBHeight_BAUGA x :=
        F.edgeB.contMDiffAt_height_of_collar_BAUGA hk hxk hck.le hk1.le hk2.le
      exact ((hρs x).mul hH).mul (hz x)
    · have h0 : (fun x => ρ x * F.edgeBHeight_BAUGA x * F.edgeBMarker_BAUGA x) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
      exact contMDiffAt_const.congr_of_eventuallyEq h0
  exact hfst.prodMk_space (hρs.mul hz)

/-- The closed support of (WB) lies in that of `z_{E'}`. -/
theorem tsupport_weakEdgeBlockOn_subset_BAUGA :
    tsupport F.weakEdgeBlockOn_BAUGA ⊆ tsupport F.edgeBMarker_BAUGA := by
  refine closure_mono fun x hx => ?_
  rw [mem_support] at hx ⊢
  intro h0
  apply hx
  rw [weakEdgeBlockOn_BAUGA, h0, mul_zero, mul_zero]
  rfl

end LocalPacketsOnB

end Carrier

section Original

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

variable {W : CompactCarrier.{0}} (g : SmoothRiemannianMetric W.model W.Carrier)
  [ConnectedSpace (W.pieceInterior ⊤)] (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤))
  {ρ : W.pieceInterior ⊤ → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤)}

/-- **(WB) on the original carrier**: for a boundary family on `(W°, d_ĝ)` with first region
`U₁ = {D > 10}` (the T3B regions), the zero extension of the weak-edge block from `W°` to `W` is
smooth (its closed support lies in `{D ≥ 10}`, which is compact in `W` and contained in `W°`). -/
theorem contMDiff_weakEdgeBlockW_BAUGA :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) ρ hρ Λ β Δ σs K σc
        μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        {x | ENNReal.ofReal 10 < distanceToBoundary W g x} U₂ Ue₁ Ue₂),
      0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 →
      ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (Subtype.val.extend F.weakEdgeBlockOn_BAUGA 0) := by
  let _ := inducedMetricSpace ĝ
  intro _ F hΛ hΔ hμ hτ hΔΛ
  refine contMDiff_extend_zero_of_tsupport_subset_distanceToBoundary_BAUGA g
    (c := 10) (by norm_num) ?_ (F.contMDiff_weakEdgeBlockOn_BAUGA hΛ hΔ hμ hτ hΔΛ)
  intro x hx
  have h : ENNReal.ofReal 10 < distanceToBoundary W g x :=
    F.tsupport_edgeBMarker_subset_region_BAUGA hΛ hΔ hμ hτ hΔΛ
      (F.tsupport_weakEdgeBlockOn_subset_BAUGA hx)
  exact h.le

/-- **(WB) formula on `W°`**: the zero-extended weak-edge block is `(ρ t_B z_{E'}, ρ z_{E'})` at
every interior point. -/
theorem weakEdgeBlockW_edgePrime_formula_BAUGA :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) ρ hρ Λ β Δ σs K σc
        μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        {x | ENNReal.ofReal 10 < distanceToBoundary W g x} U₂ Ue₁ Ue₂) (x : W.pieceInterior ⊤),
      Subtype.val.extend F.weakEdgeBlockOn_BAUGA 0 x.val =
        (ρ x * F.edgeBHeight_BAUGA x * F.edgeBMarker_BAUGA x, ρ x * F.edgeBMarker_BAUGA x) := by
  intro _ F x
  exact Subtype.val_injective.extend_apply _ _ x

/-- The zero-extended weak-edge block vanishes on the boundary of `W`. -/
theorem weakEdgeBlockW_eq_zero_of_notMem_BAUGA :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) ρ hρ Λ β Δ σs K σc
        μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        {x | ENNReal.ofReal 10 < distanceToBoundary W g x} U₂ Ue₁ Ue₂) {y : W.Carrier},
      y ∉ (W.pieceInterior ⊤ : Set W.Carrier) →
      Subtype.val.extend F.weakEdgeBlockOn_BAUGA 0 y = 0 := by
  intro _ F y hy
  exact extend_apply' _ _ y fun ⟨a, ha⟩ => hy (ha ▸ a.2)

end Original

end DifferentialGeometry.Geometry.Collapse
