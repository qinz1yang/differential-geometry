import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSelection
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsOn
import DifferentialGeometry.Geometry.Collapse.SelectedZeroPacketsOriginalBuffer
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.BufferedRadialFunctionAtScale

/-!
# Regional zero certificates on a complete carrier (lane BZ-1, G1)

External review 51 (dispositions `docs/geometrization/chapter14/out/dispositions-task51-…`), items
A3 (`zero_local_comparison`), A5 (zero shell splitting + adapted tests), A6 (enlarged zero
curvature). The closed route obtains LC62, X82 and LC73 from ONE selection on a closed manifold
(`exists_selected_zero_packets_of_original_buffer`, `[CompactSpace M]`). Here the same three
certificates on a COMPLETE σ-compact connected Riemannian three-manifold with the distance of its
metric (no compactness), so that they apply to the completed interiors `((W n)°, d_ĝ)`:

* `exists_selected_zero_family_envelope_loc_BZ1`: BDRY-3's selection on a totally bounded candidate
  envelope (`exists_selected_zero_family_envelope_BDRY3`) which ALSO exports LC62's regional local
  comparison `d(i, q) ≤ 10 r_i ⟹ T/20 ≤ r_i / ρ(q)` for the SAME selection (the closed LCP04 keeps
  it, the boundary selection dropped it);
* `ZeroModelFamilyOn.shell_split_BZ1` (X82 / LC70): for ANY regional zero family whose selected
  balls carry the original buffer `sec ≥ -(1/60)² r⁻²` on `B(c, 400 r)`, a radial cone structure
  on the stored cone, the stored cone map with error `δ < δ'`, and the local comparison
  `Λ' ≤ r/ρ(q)` on `B̄(c, 10 r)`: at every point `q` of every closed shell `r/10 ≤ d(c,q) ≤ 10 r`
  an actual Kleiner–Lott `(1, β₁)`-splitting of `(X, ρ(q)⁻¹ d, q)` whose real coordinate is
  EXACTLY `ρ(q)⁻¹ (d(c, ·) − d(c, q))` — the closed field `LocalChartPacketsZ.zero_shell_split`;
* `ZeroModelFamilyOn.adapted_BZ1` (LC73): under the buffer, the cone structure, `δ < δ'` and
  `εr ≤ ε` (the family's radial difference-Lipschitz constant), the prescribed function
  `λ (η_c − η_c(q))` of the STORED radial function `η_c = (F.zero c hc).radial` is `ζ`-adapted at
  every shell point and every ratio `λ ≥ Λ'` — the closed field `LocalChartPacketsZ.zero_adapted`
  (the completeness instance is the carrier's, not `complete_of_compact`);
* `ZeroModelFamilyOn.shell_certificates_BZ1`: both, with common constants chosen before every
  manifold and family.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [local instance] nezero_finrank_euclideanThree_LC87

universe u v

/-! ### The selection with LC62's local comparison -/

section Selection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The zero selection on a complete carrier, with LC62.**
`exists_selected_zero_family_envelope_BDRY3` (LC66 + LC77 on a complete connected Riemannian
three-manifold, candidate centres in a totally bounded envelope) which also exports LC62's
regional local comparison `d(i, q) ≤ 10 r(i) ⟹ T/20 ≤ r(i)/ρ(q)` at every selected centre `i` of
the SAME selection. -/
theorem exists_selected_zero_family_envelope_loc_BZ1 (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I M),
      RiemannianMetricComplete (I := I) g →
      letI m := inducedMetricSpace g
      ∀ (N C : M → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) →
      ∀ (δ : M → ℝ) (r ρ : M → ℝ) (hρpos : ∀ p, 0 < ρ p) {T rmin R : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → ∀ (hlower : ∀ p, T * ρ p ≤ r p), 0 < rmin → (∀ p, rmin ≤ r p) →
      (∀ p, r p ≤ R) →
      ∀ (Z S : Set M), TotallyBounded S →
      Z ⊆ {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} →
      (∀ w, (ball w (r w) ∩ Z).Nonempty → w ∈ S) →
      ∃ J : Set M, J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ J, (ball i (r i) ∩ Z).Nonempty) ∧
        (∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → T / 20 ≤ r i / ρ q) ∧
        ((∀ i ∈ J,
            (∀ y ∈ riemannianBallOf g i (400 * r i),
              SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2))) ∧
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧
            Nonempty (@KleinerLottApprox M (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i))) →
          Z ⊆ ⋃ i ∈ J, ball i (r i / 10) ∧
          ∀ i ∈ J, ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
            connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) := by
  obtain ⟨δ₁, Λ₁, hδ₁, hΛ₁, h66⟩ :=
    exists_zero_stratum_small_core_cover_envelope_BDRY3.{u, v} hβ hβone
  obtain ⟨δ₂, Λ₂, hδ₂, hΛ₂, h77⟩ :=
    exists_selected_model_one_end_parameter.{u, v, v} hβ hβone
  refine ⟨min δ₁ δ₂, max Λ₁ Λ₂, lt_min hδ₁ hδ₂, lt_max_of_lt_left hΛ₁, ?_⟩
  intro M _ _ _ _ _ _ g hg
  let m := inducedMetricSpace g
  have hcomplete : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  intro N C mN _ mC _ n₀ o H δ r ρ hρpos T rmin R hT hTΛ hlower hrmin hrlow hrup Z S hS hZ hSZ
  have hdim : dimH (univ : Set M) ≤ 3 := by
    have h := dimH_univ_le_finrank_of_sigmaCompact_BDRY3 (I := I) g
    rw [hE] at h
    exact_mod_cast h
  have hseg := inducedMetricSpace_segments_of_complete_BDRY3 hg
  have hr : ∀ p, 0 < r p := fun p => (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨J, hfin, hmeet, hdisj, hloc, hcond⟩ :=
    h66 M hseg hdim r ρ hρpos hT ((mul_le_mul_of_nonneg_left (le_max_left _ _)
      (by norm_num)).trans hTΛ) hlower hrmin hrlow hrup Z S hS hZ hSZ
  refine ⟨J, hfin, hdisj, hmeet, hloc, fun hdata => ?_⟩
  have hscale : ∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → max Λ₁ Λ₂ ≤ r i / ρ q := fun i hi q hq => by
    have := hloc i hi q hq
    linarith
  have hsec8 : ∀ i ∈ J, ∀ y ∈ riemannianBallOf g i (8 * (21 * r i)),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2)) := by
    intro i hi y hy
    apply (hdata i hi).1 y
    have hsub : riemannianBallOf g i (8 * (21 * r i)) ⊆ riemannianBallOf g i (400 * r i) := by
      rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
      exact ball_subset_ball (by nlinarith [hr i])
    exact hsub hy
  have hcomp : ∀ i ∈ J, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2) (ball i (21 * r i)) :=
    fun i hi => inducedMetricSpace_fourPointComparison_levels_of_complete_BDRY3 hg i
      (by positivity) (hsec8 i hi) _ le_rfl
  refine ⟨hcond fun i hi => ⟨hcomp i hi, C i, mC i, o i, ⟨H i⟩, δ i,
    ((hdata i hi).2.2.2.2.1).trans_le (min_le_left _ _), (hdata i hi).2.2.2.2.2⟩, ?_⟩
  intro i hi
  obtain ⟨-, hNcomp, hNseg, hcone, hδ, ⟨F⟩⟩ := hdata i hi
  exact h77 M hseg ρ hρpos i (hr i) ((dimH_mono (subset_univ _)).trans hdim) (hcomp i hi)
    (fun q hq => (le_max_right _ _).trans (hscale i hi q (by linarith [hr i]))) (hmeet i hi |>
      fun ⟨z, hz1, hz2⟩ => ⟨z, hz1, hZ hz2⟩)
    (N i) (n₀ i) (C i) (o i) hNcomp hNseg hcone (hδ.trans_le (min_le_right _ _)) ⟨F⟩

end Selection

/-! ### X82 and LC73 for a regional zero family -/

section Helpers

variable {M : Type} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {ι : Type}
  {N C : ι → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [mC : ∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ} {U₁ U₂ : Set M}

/-- The stored cone map of a selected zero-model ball, re-based at its index `c`
(`zero_center`). -/
theorem ZeroModelFamilyOn.nonempty_coneMap_BZ1
    (F : ZeroModelFamilyOn I3 M g ρ hρ β N C o δ εr e T V U₁ U₂) {c : M} (hc : c ∈ F.centres) :
    Nonempty (@KleinerLottApprox M (C (F.zero c hc).model)
      (mM.rescale ((F.zero c hc).radius)⁻¹ (inv_pos.mpr (F.zero c hc).radius_pos)) (mC _) c
      (o (F.zero c hc).model) δ) := by
  have h := (F.zero c hc).coneMap
  rw [F.zero_center c hc] at h
  exact ⟨h⟩

/-- The stored radial function of a selected zero-model ball in LCP04's original form at its index
`c`: smooth on `{3/40 ≤ r⁻¹ d(·, c) ≤ 11}` and `|(η x − r⁻¹ d(c,x)) − (η y − r⁻¹ d(c,y))| ≤
εr r⁻¹ d(x, y)` (the family's OWN constant `εr`). -/
theorem ZeroModelFamilyOn.radial_clauses_BZ1
    (F : ZeroModelFamilyOn I3 M g ρ hρ β N C o δ εr e T V U₁ U₂) {c : M} (hc : c ∈ F.centres) :
    ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ (F.zero c hc).radial
      {x | 3 / 40 ≤ ((F.zero c hc).radius)⁻¹ * dist x c ∧
        ((F.zero c hc).radius)⁻¹ * dist x c ≤ 11} ∧
      ∀ x y, |((F.zero c hc).radial x - ((F.zero c hc).radius)⁻¹ * dist c x) -
        ((F.zero c hc).radial y - ((F.zero c hc).radius)⁻¹ * dist c y)| ≤
          εr * (((F.zero c hc).radius)⁻¹ * dist x y) := by
  have h := radial_original_clauses_of_rescaled (I := I3) (m := mM) (F.zero c hc).radius_pos
    (F.zero c hc).radial_spec.2.1 (F.zero c hc).radial_spec.2.2.2.2.1
  rw [F.zero_center c hc] at h
  exact h

end Helpers

/-- **X82 / LC70 for a regional zero family (zero shell splitting).** Constants first. On a
complete σ-compact connected Riemannian three-manifold with the distance of its metric, for ANY
regional zero family `F` whose selected balls carry the original buffer
`sec ≥ -(1/60)² r_c⁻²` on `B(c, 400 r_c)`, a radial cone structure on the stored cone, cone error
`δ < δ'` and the local comparison `Λ' ≤ r_c/ρ(q)` for `d(c, q) ≤ 10 r_c`: at every point `q` of the
CLOSED shell `r_c/10 ≤ d(c, q) ≤ 10 r_c` an actual Kleiner–Lott `(1, β₁)`-splitting of
`(M, ρ(q)⁻¹ d, q)` whose real coordinate is EXACTLY `ρ(q)⁻¹ (d(c, ·) − d(c, q))`. -/
theorem ZeroModelFamilyOn.shell_split_BZ1 {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I3 M),
      RiemannianMetricComplete (I := I3) g →
      letI mM := inducedMetricSpace g
      ∀ (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) {ι : Type} {N C : ι → Type} [∀ a, MetricSpace (N a)]
        [∀ a, ChartedSpace E3 (N a)] [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
        {δ εr e T V : ℝ} {U₁ U₂ : Set M}
        (F : ZeroModelFamilyOn I3 M g ρ hρ β N C o δ εr e T V U₁ U₂),
      δ < δ' →
      (∀ c (hc : c ∈ F.centres), Nonempty (RadialConeData (o (F.zero c hc).model))) →
      (∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) →
      (∀ c (hc : c ∈ F.centres), ∀ q, dist c q ≤ 10 * (F.zero c hc).radius →
        Λ' ≤ (F.zero c hc).radius / ρ q) →
      ∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
        dist c q ≤ 10 * (F.zero c hc).radius →
        ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
          ∃ (z : Zf) (Fk : @KleinerLottApprox M
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
            (mM.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
            q (WithLp.toLp 2 (0, z)) (β 1)),
            ∀ x : M, (@KleinerLottApprox.toFun M
              (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
              (mM.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
              q (WithLp.toLp 2 (0, z)) (β 1) Fk x).fst = WithLp.toLp 2
              (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q))) := by
  obtain ⟨δ₃, Λ₃, hδ₃, hΛ₃, h82⟩ :=
    original_radial_selected_shell_export.{0, 0} (n := 3) (by norm_num) hβ hβone
  refine ⟨δ₃, Λ₃, hδ₃, hΛ₃, ?_⟩
  intro M _ _ _ _ _ _ g hg ρ hρ ι N C _ _ _ o δ εr e T V U₁ U₂ F hδ hcone hbuf hloc c hc q hq1 hq2
  let mM := inducedMetricSpace g
  have hcomplete : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  have hdim : dimH (univ : Set M) ≤ 3 := by
    have h := dimH_univ_le_finrank_of_sigmaCompact_BDRY3 (I := I3) g
    rw [finrank_euclideanSpace_fin] at h
    exact_mod_cast h
  have hseg := inducedMetricSpace_segments_of_complete_BDRY3 hg
  have hR : 0 < (F.zero c hc).radius := (F.zero c hc).radius_pos
  have hsec8 : ∀ y ∈ riemannianBallOf g c (8 * (21 * (F.zero c hc).radius)),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2)) := by
    intro y hy
    rw [← inducedMetricSpace_ball g] at hy
    exact hbuf c hc y (ball_subset_ball (by nlinarith) hy)
  refine h82 M hseg hdim (fun _ => C (F.zero c hc).model) (fun _ => o (F.zero c hc).model)
    (fun _ => (F.zero c hc).radius) ρ (fun _ => hR) hρ {c} (fun _ _ => hcone c hc) ?_ ?_ ?_ c
    (mem_singleton c) q hq1 hq2
  · intro i hi
    rw [mem_singleton_iff.mp hi]
    exact inducedMetricSpace_fourPointComparison_levels_of_complete_BDRY3 hg c (by positivity)
      hsec8 _ le_rfl
  · intro i hi
    rw [mem_singleton_iff.mp hi]
    exact ⟨δ, hδ, F.nonempty_coneMap_BZ1 hc⟩
  · intro i hi q' hq'
    rw [mem_singleton_iff.mp hi] at hq'
    exact hloc c hc q' hq'

/-- **LC73 for a regional zero family (ζ-adapted tests of the stored radial function).** Constants
first. On a complete σ-compact connected Riemannian three-manifold with the distance of its metric,
for ANY regional zero family `F` with radial difference-Lipschitz constant `εr ≤ ε`, cone error
`δ < δ'`, a radial cone structure on the stored cone and the original buffer on `B(c, 400 r_c)`: at
every point `q` of every closed shell and every ratio `λ ≥ Λ'`, the prescribed function
`λ (η_c − η_c(q))` of the STORED radial function `η_c` is adapted of quality `ζ` (in
`λ² r_c⁻² g`) to an actual splitting with real coordinate `λ (d(c, ·) − d(c, q))` (in `r_c⁻¹ d`):
the closed field `LocalChartPacketsZ.zero_adapted`, with the carrier's completeness. -/
theorem ZeroModelFamilyOn.adapted_BZ1 {β : ℕ → ℝ} (hβ : 0 < β 1) {ζ : ℝ} (hβζ : β 1 < ζ)
    (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I3 M)
        (hg : RiemannianMetricComplete (I := I3) g),
      letI mM := inducedMetricSpace g
      ∀ (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) {ι : Type} {N C : ι → Type} [∀ a, MetricSpace (N a)]
        [∀ a, ChartedSpace E3 (N a)] [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
        {δ εr e T V : ℝ} {U₁ U₂ : Set M}
        (F : ZeroModelFamilyOn I3 M g ρ hρ β N C o δ εr e T V U₁ U₂),
      δ < δ' → εr ≤ ε →
      (∀ c (hc : c ∈ F.centres), Nonempty (RadialConeData (o (F.zero c hc).model))) →
      (∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) →
      ∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
        dist c q ≤ 10 * (F.zero c hc).radius →
        ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
        let R := (F.zero c hc).radius
        let hR : 0 < R := (F.zero c hc).radius_pos
        let η := (F.zero c hc).radial
        let mr := mM.rescale R⁻¹ (inv_pos.mpr hR)
        let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mM) g
          (inducedMetricSpace_hmetric g) hR
        let := mr.rescale lam hlam
        letI := (mr.rescale_completeSpace_iff lam hlam).mpr
          ((mM.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
            (riemannianMetricComplete_iff_inducedMetricSpace.mp hg))
        letI := radialScaledBundle gr lam hlam
        letI := radialScaledContinuous gr lam hlam
        letI := radialScaledManifold (m := mr) gr hmr lam hlam
        let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
        let ψ := fun x => lam * (η x - η q)
        ∃ hEnorm : IsMetricNorm h,
          ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
            ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
            (∀ x, (κ.toFun x).fst = lam *
              (@dist M mr.toDist c x - @dist M mr.toDist c q)) ∧
            ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
            (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
            (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
            (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
            ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
              ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
              intrinsicGeodesic h hEnorm x u (dist x y) = y →
              |mvfderiv (I := I3) ψ x u -
                ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ := by
  obtain ⟨ε, δ₄, Λ₄, hε, hε4, hδ₄, hΛ₄, h73⟩ :=
    selected_center_adapted_coordinate_of_original_buffer.{0, 0} (E := E3) (H := E3) (I := I3)
      hβ hβζ hζone
  refine ⟨ε, δ₄, Λ₄, hε, hε4, hδ₄, hΛ₄, ?_⟩
  intro M _ _ _ _ _ _ g hg ρ hρ ι N C _ _ _ o δ εr e T V U₁ U₂ F hδ hεr hcone hbuf c hc q hq1
    hq2 lam hlam hΛ
  let mM := inducedMetricSpace g
  have hcomplete : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  obtain ⟨hη, herr⟩ := F.radial_clauses_BZ1 hc
  obtain ⟨H⟩ := hcone c hc
  obtain ⟨Fk⟩ := F.nonempty_coneMap_BZ1 hc
  have hR := (F.zero c hc).radius_pos
  exact h73 M g (inducedMetricSpace_hmetric g) c _ hR (hbuf c hc) _ _ H Fk hδ _ hη
    (fun x y => (herr x y).trans (mul_le_mul_of_nonneg_right hεr
      (mul_nonneg (inv_nonneg.mpr hR.le) dist_nonneg))) q hq1 hq2 lam hlam hΛ

end DifferentialGeometry.Geometry.Collapse
