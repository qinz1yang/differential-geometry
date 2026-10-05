import DifferentialGeometry.Geometry.Fibration.ActualStageTargets
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudsApplications
import DifferentialGeometry.Geometry.Metric.LargeCloudAffineMarkerLocality
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestFiniteBudget
import DifferentialGeometry.Analysis.Calculus.AdjustmentStepPointwise

/-!
# GAF02's stage nearest maps on the actual clouds (CFS15 / CFS14 (3) with locality)

Blueprint `master207B.tex`, GAF02 (B:5797) with CFS14 (3) / CFS15 (B:2628–2748) and CFS28's
contributor locality (B:3420–3480): at every stage the nearest-point map `p` of CFS15's smoothing
on the actual stage cloud, extended to `H` (`nearestAmbientExtension`), is smooth on
`Ω = ⋃_{x ∈ S} B(x, r_x)`, is `Ξr_x`-close to the affine projection `x + Π_x(z − x)` on each
`B(x, r_x)` with derivative `Ξ`-close to `Π_x`, and keeps every affine block value `K, c` shared
by all contributing cloud centres and their planes (`large_cloud_affine_marker_locality`).

* `exists_nearestAmbientExtension_GAF3`: the ambient extension of a smooth nearest map into a
  smoothly embedded `Z` equals it on `Ω`, is smooth there, and has the manifold derivative.
* `gaf01_row_nearest_abstract_GAF3`: GAF01 (`gaf01_row`) with its FIRST conjunct replaced by these
  nearest maps for every abstract cloud with CFS15's hypotheses at quality `Γ`, and the SECOND
  conjunct (the choice `c, Γ, Σ, e`) verbatim, for the SAME moduli `θ, Ξ`.
* `gaf01_row_nearest_GAF3`: the same on the actual stage clouds of `LocalChartPacketsC14` (FC07's
  ranges, any selection of preimages, `0 < Σ ≤ Ξ_st(Γ)/640`, planes of the stage dimension with the
  (CS) tests at quality `Γ`; CFS14's other hypotheses from `cfs14_stage_inputs_GAF2`).
* `starProjection_comp_mem_GAF3`, `norm_starProjection_comp_sub_affine_le_GAF3`,
  `norm_fderiv_starProjection_comp_sub_le_GAF3`: for `Pst = π_{Q_st} ∘ a` and planes inside
  `Q_st`: values in `Q_st`, the value bound `‖Pst z − (x + Π_x(z − x))‖ ≤ Ξr_x` and the derivative
  bound `‖DPst(z) − Π_x‖ ≤ Ξ` survive (`Q_st` fixes `x + Π_x(z − x)`, `π_{Q_st} ∘ Π_x = Π_x`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Projected

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- `π_Q ∘ a` takes values in `Q`. -/
theorem starProjection_comp_mem_GAF3 (Q : Submodule ℝ H) (a : H → H) (z : H) :
    Q.starProjection (a z) ∈ Q :=
  Q.starProjection_apply_mem _

/-- The value bound survives `π_Q` when `x ∈ Q` and the plane lies in `Q`. -/
theorem norm_starProjection_comp_sub_affine_le_GAF3 (Q W : Submodule ℝ H) (a : H → H)
    {x z : H} (hx : x ∈ Q) (hW : W ≤ Q) {B : ℝ}
    (h : ‖a z - (x + W.starProjection (z - x))‖ ≤ B) :
    ‖Q.starProjection (a z) - (x + W.starProjection (z - x))‖ ≤ B := by
  have hmem : x + W.starProjection (z - x) ∈ Q :=
    Q.add_mem hx (hW (W.starProjection_apply_mem _))
  have hfix : Q.starProjection (x + W.starProjection (z - x)) = x + W.starProjection (z - x) :=
    Q.starProjection_eq_self_iff.mpr hmem
  rw [← hfix, ← map_sub]
  exact (Q.norm_starProjection_apply_le _).trans h

/-- The derivative bound survives `π_Q` when the plane lies in `Q`. -/
theorem norm_fderiv_starProjection_comp_sub_le_GAF3 (Q W : Submodule ℝ H) {a : H → H} {z : H}
    (ha : DifferentiableAt ℝ a z) (hW : W ≤ Q) {B : ℝ}
    (h : ‖fderiv ℝ a z - W.starProjection‖ ≤ B) :
    DifferentiableAt ℝ (fun y => Q.starProjection (a y)) z ∧
      ‖fderiv ℝ (fun y => Q.starProjection (a y)) z - W.starProjection‖ ≤ B := by
  have hd : HasFDerivAt (fun y => Q.starProjection (a y))
      (Q.starProjection.comp (fderiv ℝ a z)) z :=
    Q.starProjection.hasFDerivAt.comp z ha.hasFDerivAt
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  have hQW : Q.starProjection.comp W.starProjection = W.starProjection := by
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    exact Q.starProjection_eq_self_iff.mpr (hW (W.starProjection_apply_mem v))
  have heq : Q.starProjection.comp (fderiv ℝ a z) - W.starProjection =
      Q.starProjection.comp (fderiv ℝ a z - W.starProjection) := by
    rw [ContinuousLinearMap.comp_sub, hQW]
  rw [heq]
  calc _ ≤ ‖Q.starProjection‖ * ‖fderiv ℝ a z - W.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * B := mul_le_mul Q.starProjection_norm_le h (norm_nonneg _) zero_le_one
    _ = B := one_mul B

omit [FiniteDimensional ℝ H] in
/-- The ambient extension of a smooth nearest map into a smoothly embedded `Z`: a map `a : H → H`
equal to `p` on `Ω`, smooth at every point of `Ω`, whose derivative there is the manifold derivative
of `p`. -/
theorem exists_nearestAmbientExtension_GAF3 {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]
    (Ω : TopologicalSpace.Opens H) (p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯)
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H)) :
    ∃ a : H → H, (∀ y (hy : y ∈ Ω), a y = p ⟨y, hy⟩) ∧ (∀ y ∈ Ω, ContDiffAt ℝ ∞ a y) ∧
      ∀ y (hy : y ∈ Ω),
        fderiv ℝ a y = mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun w : Ω => (p w : H)) ⟨y, hy⟩ := by
  classical
  have hext : ∀ z : Ω, nearestAmbientExtension Ω Z p z = p z := fun z => dite_eq_left z.property
  have heq : (fun y : Ω => nearestAmbientExtension Ω Z p y) = (fun y : Ω => (p y : H)) :=
    funext hext
  have hsm : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (fun y : Ω => (p y : H)) :=
    hemb.contMDiff.comp p.contMDiff
  have hcd : ∀ z : Ω, ContDiffAt ℝ ∞ (nearestAmbientExtension Ω Z p) z := by
    intro z
    have h : ContMDiffAt 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (fun y : Ω => nearestAmbientExtension Ω Z p y) z := by
      rw [heq]
      exact hsm z
    exact contMDiffAt_iff_contDiffAt.mp (contMDiffAt_subtype_iff.mp h)
  refine ⟨nearestAmbientExtension Ω Z p, fun y hy => hext ⟨y, hy⟩, fun y hy => hcd ⟨y, hy⟩,
    fun y hy => ?_⟩
  change fderiv ℝ (nearestAmbientExtension Ω Z p) ((⟨y, hy⟩ : Ω) : H) = _
  rw [← heq, DifferentialGeometry.mfderiv_restrict_open, mfderiv_eq_fderiv]
  rfl

end Projected

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF3n {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF3n {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF3n {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF01 with abstract stage nearest maps.** The moduli `θ, Ξ` of `gaf01_row` such that for every
stage `st` and quality `0 < Γ < θ_st` (`0 < Ξ_st(Γ) ≤ 1`), every cloud `S ⊆ T` in a
finite-dimensional inner product space with CFS15's hypotheses at quality `Γ` (bounded radii,
(MCb) at buffer `128Ξ⁻¹` with ratio `5/3`, planes of dimension `k_st`, the (CS) tests) has a map
`a : H → H`
(CFS15's nearest-point map extended to `H`) smooth on `⋃_{x ∈ S} B(x, r_x)` with, on every
`B(x, r_x)`: `‖a z − (x + Π_x(z − x))‖ ≤ Ξr_x`, `‖Da(z) − Π_x‖ ≤ Ξ`, and `π_K(a z) = c` whenever
every contributing centre `i ∈ S` has `π_K i = c` and `P i ⊥ K`; and GAF01's choice clause
verbatim. -/
theorem gaf01_row_nearest_abstract_GAF3 (Kj : ℕ) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ),
      (∀ st : Fin 3, 0 < θ st ∧ Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
        ∀ Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ ∧ Ξ st Γ ≤ 1 ∧
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
            (S T : Set H), S ⊆ T → TotallyBounded S →
            ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
            (∀ x ∈ S, Module.finrank ℝ (P x) = gafStageDim st) →
            ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
            (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ st Γ)⁻¹ * max (r y) (r x) →
              r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
            (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / Γ))
              ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / Γ)) ≤
                ENNReal.ofReal (Γ * r x)) →
            ∃ a : H → H, ContDiffOn ℝ ∞ a (⋃ x ∈ S, ball x (r x)) ∧
              ∀ x ∈ S, ∀ z ∈ ball x (r x),
                ‖a z - (x + (P x).starProjection (z - x))‖ ≤ Ξ st Γ * r x ∧
                DifferentiableAt ℝ a z ∧
                ‖fderiv ℝ a z - (P x).starProjection‖ ≤ Ξ st Γ ∧
                ∀ (Kk : Submodule ℝ H) (c : H),
                  (∀ i ∈ S, (closedBall i (80 * (Ξ st Γ)⁻¹ * r i) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * r x)).Nonempty →
                    Kk.starProjection i = c ∧ P i ≤ Kkᗮ) →
                  Kk.starProjection (a z) = c) ∧
      ∀ (C : Fin 3 → ℝ), (∀ j, 0 < C j) → ∀ cadj : ℝ, 0 < cadj →
      ∃ c Γ S e : Fin 3 → ℝ,
        let Ω : ℝ := max 1 (max (C 0) (max (C 1) (C 2)))
        let α : Fin 3 → ℝ := fun j =>
          min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
            ((1 / 2) / (8 * (1 + gafDerivativeBound)))
        let t : Fin 3 → ℝ := fun j => min (3 * S j / 10) (min (α j) 1)
        (c 2 < cadj ∧ c 2 < 1 / 1000 ∧ c 2 < 1 / 512) ∧
        (c 1 ≤ c 2 ∧ c 1 ≤ t 2 ∧ c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 1 / 1000 ∧ c 1 ≤ 1 / 512) ∧
        (c 0 ≤ c 1 ∧ c 0 ≤ t 1 ∧ c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 1 / 1000 ∧ c 0 ≤ 1 / 512) ∧
        ∀ j, (Γ j < θ j ∧ 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) < 1 / 10 ∧
            Ξ j (Γ j) < α j ∧ Ξ j (Γ j) < 1 / (1000 * (Ω + 1)) ∧
            0 < S j ∧ S j < 1 / 2 ∧ S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧
            S j < Γ j ^ 3 / (100 * C j) ∧
            0 < e j ∧ e j < 1 / 100 ∧ e j < Γ j * S j / 100 ∧ e j < S j / 1000 ∧
            2 * e j < 1 / (48 * Ω)) ∧
          (∀ E H ν σ : ℝ, 0 ≤ E → E ≤ t j → 0 ≤ H → H ≤ t j → ν ≤ Γ j → σ ≤ 1 / 2 →
            let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
            E + a < c j ∧ a * gafCutoffConstant * (gafDerivativeBound + H) +
                Ξ j (Γ j) * (gafDerivativeBound + H) + ν + 2 * H < c j ∧
              Ξ j (Γ j) * (gafDerivativeBound + H) + H < 1 / 2) ∧
          (∀ ν : ℝ, ν ≤ e j → ν + e j ≤ 1 / (48 * Ω)) ∧
          (∀ R rx : ℝ, 0 < R → 9 / 20 * S j * R ≤ rx →
            (2 * e j + 25 / 12 * (1 + Ω) * Ξ j (Γ j) * S j) * R < S j * R / 100 ∧
              S j * R / 100 < rx / 4 ∧ Ξ j (Γ j) < 1 / (2 * Ω)) := by
  obtain ⟨θ, Ξ, hcfs, hchoice⟩ := gaf01_row Kj
  refine ⟨θ, Ξ, fun st => ⟨(hcfs st).1, (hcfs st).2.1, fun Γ hΓ hθΓ => ?_⟩, hchoice⟩
  have hst := (hcfs st).2.2 Γ hΓ hθΓ
  obtain ⟨⟨m, hm⟩, hmain⟩ := hst
  have hΞ : 0 < Ξ st Γ := by
    rw [hm]
    positivity
  have hΞ1 : Ξ st Γ ≤ 1 := by
    rw [hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨hΞ, hΞ1, ?_⟩
  obtain ⟨F, -, Cc, -, δ₀, -, -, hΓδ, hmain'⟩ := hmain
  intro H _ _ _ S T hST htb r plane hdim rmin R hrmin hlo hhi hmcb hcloud
  have happ := hmain' H S T hST htb r plane hdim rmin R Γ hrmin hlo hhi hΓ hΓδ hmcb hcloud
  obtain ⟨I, hI, hIS, -, -, htube, hrest⟩ := happ
  obtain ⟨⟨-, cs, hcs⟩, -⟩ := hrest
  obtain ⟨-, hemb, p, -, -, hval, -⟩ := hcs
  obtain ⟨a, hext, hcd, hfd⟩ := exists_nearestAmbientExtension_GAF3 _ p hemb
  have hΩ : ∀ x ∈ S, ∀ z ∈ ball x (r x), z ∈ ⋃ x : ↥S, ball (x : H) (r x) :=
    fun x hx z hz => mem_iUnion.mpr ⟨⟨x, hx⟩, hz⟩
  refine ⟨a, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    exact (hcd y (hΩ x hx y hyx)).contDiffWithinAt
  · intro x hx z hz
    have hzΩ := hΩ x hx z hz
    have hvx := hval ⟨x, hx⟩ ⟨z, hz⟩
    have haz := hext z hzΩ
    refine ⟨haz ▸ hvx.1, (hcd z hzΩ).differentiableAt (by simp), (hfd z hzΩ) ▸ hvx.2, ?_⟩
    intro Kk c hcontrib
    have hr : ∀ i ∈ I, 0 < r i := fun i hi => lt_of_lt_of_le hrmin (hlo i (hIS hi))
    have htubex : ball x (8 * (Ξ st Γ)⁻¹ * r x) ⊆ ⋃ i ∈ I, ball i (20 * (Ξ st Γ)⁻¹ * r i) :=
      fun y hy => htube (mem_iUnion₂.mpr ⟨x, hx, hy⟩)
    have hloc := large_cloud_affine_marker_locality I hI r plane hΞ hΞ1 hr x htubex Kk c
      (fun i hi hne => hcontrib i (hIS hi) hne)
    have hη := (p ⟨z, hzΩ⟩).2.2
    exact haz ▸ hloc.2.2 z hz _ hη hvx.1

/-- **GAF01 with the actual stage nearest maps.** The moduli `θ, Ξ` of `gaf01_row` such that for
every stage `st`, quality `0 < Γ < θ_st` (`0 < Ξ_st(Γ) ≤ 1`), packets of the final family in FC07's
range, selection `sel` of preimages over `S̃_st`, radius factor `0 < Σ ≤ Ξ_st(Γ)/640` and planes of
the stage dimension with the (CS) tests at quality `Γ`, there is a map `a : H → H` (CFS15's
nearest-point map extended to `H`) which is smooth on `Ω = ⋃_{x ∈ S_st} B(x, r_x)` (`r = Σρ ∘ sel`)
and, on every `B(x, r_x)`: `‖a z − (x + Π_x(z − x))‖ ≤ Ξr_x`, `‖Da(z) − Π_x‖ ≤ Ξ`, and
`π_K(a z) = c` whenever every contributing centre `i ∈ S_st` (`B̄(i, 80Ξ⁻¹r_i)` meets
`B(x, 8Ξ⁻¹r_x)`) has `π_K i = c` and `plane i ⊥ K`; and GAF01's choice clause verbatim. -/
theorem gaf01_row_nearest_GAF3 (Kj : ℕ) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ),
      (∀ st : Fin 3, 0 < θ st ∧ Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
        ∀ Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ ∧ Ξ st Γ ≤ 1 ∧
          ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
            [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
            (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
            (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
            (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
            (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
              εr e T V vs ζ Λz),
            0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
            1000000 * Δ * Λ < 1 / 100000 →
            ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
              cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
                (sel x) = x) →
            ∀ sg : ℝ, 0 < sg → sg ≤ Ξ st Γ / 640 →
            ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
              Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
            (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
              Module.finrank ℝ (plane x) = gafStageDim st) →
            (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
                  ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) →
            ∃ a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
              ContDiffOn ℝ ∞ a (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
                ball x (sg * ρ (sel x))) ∧
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
                ‖a z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ st Γ * (sg * ρ (sel x)) ∧
                DifferentiableAt ℝ a z ∧
                ‖fderiv ℝ a z - (plane x).starProjection‖ ≤ Ξ st Γ ∧
                ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
                  (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                  (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
                    (closedBall i (80 * (Ξ st Γ)⁻¹ * (sg * ρ (sel i))) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * (sg * ρ (sel x)))).Nonempty →
                    Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
                  Kk.starProjection (a z) = c) ∧
      ∀ (C : Fin 3 → ℝ), (∀ j, 0 < C j) → ∀ cadj : ℝ, 0 < cadj →
      ∃ c Γ S e : Fin 3 → ℝ,
        let Ω : ℝ := max 1 (max (C 0) (max (C 1) (C 2)))
        let α : Fin 3 → ℝ := fun j =>
          min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
            ((1 / 2) / (8 * (1 + gafDerivativeBound)))
        let t : Fin 3 → ℝ := fun j => min (3 * S j / 10) (min (α j) 1)
        (c 2 < cadj ∧ c 2 < 1 / 1000 ∧ c 2 < 1 / 512) ∧
        (c 1 ≤ c 2 ∧ c 1 ≤ t 2 ∧ c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 1 / 1000 ∧ c 1 ≤ 1 / 512) ∧
        (c 0 ≤ c 1 ∧ c 0 ≤ t 1 ∧ c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 1 / 1000 ∧ c 0 ≤ 1 / 512) ∧
        ∀ j, (Γ j < θ j ∧ 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) < 1 / 10 ∧
            Ξ j (Γ j) < α j ∧ Ξ j (Γ j) < 1 / (1000 * (Ω + 1)) ∧
            0 < S j ∧ S j < 1 / 2 ∧ S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧
            S j < Γ j ^ 3 / (100 * C j) ∧
            0 < e j ∧ e j < 1 / 100 ∧ e j < Γ j * S j / 100 ∧ e j < S j / 1000 ∧
            2 * e j < 1 / (48 * Ω)) ∧
          (∀ E H ν σ : ℝ, 0 ≤ E → E ≤ t j → 0 ≤ H → H ≤ t j → ν ≤ Γ j → σ ≤ 1 / 2 →
            let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
            E + a < c j ∧ a * gafCutoffConstant * (gafDerivativeBound + H) +
                Ξ j (Γ j) * (gafDerivativeBound + H) + ν + 2 * H < c j ∧
              Ξ j (Γ j) * (gafDerivativeBound + H) + H < 1 / 2) ∧
          (∀ ν : ℝ, ν ≤ e j → ν + e j ≤ 1 / (48 * Ω)) ∧
          (∀ R rx : ℝ, 0 < R → 9 / 20 * S j * R ≤ rx →
            (2 * e j + 25 / 12 * (1 + Ω) * Ξ j (Γ j) * S j) * R < S j * R / 100 ∧
              S j * R / 100 < rx / 4 ∧ Ξ j (Γ j) < 1 / (2 * Ω)) := by
  obtain ⟨θ, Ξ, hnear, hchoice⟩ := gaf01_row_nearest_abstract_GAF3 Kj
  refine ⟨θ, Ξ, fun st => ⟨(hnear st).1, (hnear st).2.1, fun Γ hΓ hθΓ => ?_⟩, hchoice⟩
  have hst := (hnear st).2.2 Γ hΓ hθΓ
  obtain ⟨hΞ, hΞ1, habs⟩ := hst
  refine ⟨hΞ, hΞ1, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hsgΞ plane hdim hcloud
  have hmo : 128 * (Ξ st Γ)⁻¹ * sg ≤ 1 / 5 := by
    have h1 : 128 * (Ξ st Γ)⁻¹ * sg ≤ 128 * (Ξ st Γ)⁻¹ * (Ξ st Γ / 640) :=
      mul_le_mul_of_nonneg_left hsgΞ (by positivity)
    have h2 : 128 * (Ξ st Γ)⁻¹ * (Ξ st Γ / 640) = 1 / 5 := by
      field_simp
      norm_num
    linarith
  obtain ⟨hST, htb, ⟨rmin, R, hrmin, hlo, hhi⟩, hmcb⟩ :=
    cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hΞ hsg hmo
  exact habs (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hST htb (fun x => sg * ρ (sel x)) plane hdim rmin R hrmin hlo hhi hmcb hcloud

end DifferentialGeometry.Geometry.Collapse
