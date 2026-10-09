import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveExit
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveGeneralSteps

/-!
# REL kernel, step (iv): the hinge upper support in the ambient metric (CMS3-REL, G1)

Lane CMS3-REL, sub-lemma SL4 of `build-logs/resume/sheet-CMS3-REL.md`. Setting: a complete metric `g`
of class `C^{r+1}` (`2 ≤ r`, `hnorm`) with `sec ≥ 0`, a closed totally convex `C`, relative interior
`Z`, relative boundary `B`, and the relative orthogonal shift `hshiftZ` (the conclusion of A1-rel
`exists_relative_orthogonal_shift_of_transverseShift` at every point of `Z`).

* `infDist_relBoundaryOfOrder_step_of_shift`: at `x ∈ Z`, for a unit `u ∈ T_x Z` reaching `B` at time
  `d(x, B)` and any unit `e ∈ T_x Z`, `d(exp_x (h e), B) ≤ d(x, B) - h g_x(u, e)` for small `h > 0`.
  The proof is CMS3-SHAVE's `ShaveGeneralSteps.lean` with `∂C → B`, `int C → Z` and the tangency
  bookkeeping: `w = n⁻¹ (e - c u) ∈ T_x Z` (a submodule); the nearest point `τ₀` of the foot segment to
  `z = exp_x (h e)` lies in `Z`, `z ∈ Z` (relative ball), the segment `τ₀ → z` lies in `C` hence its
  direction is tangent; the hinges (`dist_sq_le_hinge_finite`, `inner_eq_zero_of_isLocalMin_dist`) are
  ambient.
* `exists_upper_support_infDist_relBoundaryOfOrder_of_shift`: the linear upper support of
  `t ↦ d(γ_p t, B)` at an interior parameter `s` with `γ_p s ∈ Z` (the velocity is tangent by relative
  openness, SLICE (6)).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The initial direction of a radial arc from a point of `Z` to a point of `C` is tangent to `Z`. -/
theorem mem_sliceTangent_of_expMap_mem
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {x : M}
    (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {W : E} {d : ℝ} (hd : 0 < d)
    (hend : g.expMap (⟨x, d • W⟩ : TangentBundle I M) ∈ C) :
    W ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hflow : ∀ τ : ℝ, g.expMap (⟨x, τ • W⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, W⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 x W τ (by rw [hD]; exact mem_univ _)
  have hZ := hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_start hr hnorm
    (⟨x, W⟩ : TangentBundle I M) hd hx (by rw [← hflow]; exact hend)
  exact snd_mem_sliceTangent_of_eventually g hr1 (⟨x, W⟩ : TangentBundle I M)
    (fun s => by rw [hD]; exact mem_univ _)
    (by filter_upwards [Ioo_mem_nhdsGT hd] with s hs using hZ s ⟨hs.1.le, hs.2⟩)

/-- The velocity at an interior parameter of a geodesic arc of `C`, at a point of `Z`, is tangent to
`Z` (relative openness). -/
theorem snd_mem_sliceTangent_of_mem_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) {ℓ s : ℝ}
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) (hs : s ∈ Ioo 0 ℓ)
    (hsZ : (g.geodesicFlow p s).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    (g.geodesicFlow p s).snd ∈
      sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) (g.geodesicFlow p s).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨U, hU, hsU, hUeq⟩ := maxSliceLocusOfOrder_eq_near g hr hnorm hconv hsZ
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hγc : Continuous (fun t : ℝ => (g.geodesicFlow p t).proj) := by
    refine LipschitzWith.continuous (K := ⟨σ, hσ0⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hγc) s hsU
  have hδ' : 0 < min δ (ℓ - s) := lt_min hδ (by linarith [hs.2])
  refine snd_mem_sliceTangent_of_right g hr hnorm p hδ' fun τ hτ => ?_
  have hτU : (g.geodesicFlow p τ).proj ∈ U := by
    refine hball ?_
    rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith [hτ.1])]
    linarith [hτ.2, min_le_left δ (ℓ - s)]
  have hτC : (g.geodesicFlow p τ).proj ∈ C :=
    hmaps τ ⟨by linarith [hτ.1, hs.1], by linarith [hτ.2, min_le_right δ (ℓ - s)]⟩
  have h : (g.geodesicFlow p τ).proj ∈ U ∩ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
    rw [hUeq]; exact ⟨hτU, hτC⟩
  exact h.2

/-- **The relative step, case `g_x(u, e) ≤ 0`.** -/
theorem infDist_relBoundaryOfOrder_step_of_inner_nonpos [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hshiftZ : ∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ ρ > 0,
      ∀ y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, dist x y < ρ → ∀ u w : E,
      g.inner y u u = 1 → g.inner y w w = 1 → g.inner y u w = 0 →
      u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤ infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))
    {x : M} (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {u : E} (hu : g.inner x u u = 1)
    (huT : u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x)
    (hfoot : g.expMap (⟨x, infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
      relBoundaryOfOrder I (r : ℕ∞ω) C)
    {e : E} (he : g.inner x e e = 1) (heT : e ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x)
    (hc : g.inner x u e ≤ 0) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M))
        (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
      infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) - h * g.inner x u e := by
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  obtain ⟨ρ₀, hρ₀, hshift⟩ := hshiftZ x hx
  obtain ⟨ρ₁, hρ₁, hrad⟩ := exists_radial_dist_eq g hr hnorm x
  set c : ℝ := g.inner x u e with hcdef
  have heu : g.inner x e u = c := by rw [shaveInner_symm]
  have hw2 : g.inner x (e - c • u) (e - c • u) = 1 - c ^ 2 := by
    simp only [shaveInner_sub_left, shaveInner_sub_right, shaveInner_smul_left,
      shaveInner_smul_right, he, hu, heu, ← hcdef]
    ring
  have hnn : 0 ≤ g.inner x (e - c • u) (e - c • u) :=
    DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g x _
  rw [hw2] at hnn
  set n : ℝ := Real.sqrt (1 - c ^ 2) with hndef
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hnsq : n ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hnn
  have hn1 : n ≤ 1 := by nlinarith [sq_nonneg c]
  rcases eq_or_lt_of_le hn0 with hnzero | hnpos
  · have hc1 : c = -1 := by
      have h := hnsq
      rw [← hnzero] at h
      nlinarith
    filter_upwards [Ioo_mem_nhdsGT hρ₁] with h hh
    have hd : dist x (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) = h :=
      hrad e he h ⟨hh.1.le, hh.2⟩
    have htri : infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) B ≤
        infDist x B + dist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) x :=
      infDist_le_infDist_add_dist
    rw [dist_comm, hd] at htri
    refine htri.trans (le_of_eq ?_)
    rw [hc1]
    ring
  · have hne : n ≠ 0 := ne_of_gt hnpos
    have hw : g.inner x (n⁻¹ • (e - c • u)) (n⁻¹ • (e - c • u)) = 1 := by
      rw [shaveInner_smul_left, shaveInner_smul_right, hw2, ← hnsq]
      field_simp
    have huw : g.inner x u (n⁻¹ • (e - c • u)) = 0 := by
      rw [shaveInner_smul_right, shaveInner_sub_right, shaveInner_smul_right, hu, ← hcdef]
      ring
    have hwe : g.inner x (n⁻¹ • (e - c • u)) e = n := by
      rw [shaveInner_smul_left, shaveInner_sub_left, shaveInner_smul_left, he, ← hcdef]
      have h1 : 1 - c * c = n ^ 2 := by rw [hnsq]; ring
      rw [h1]
      field_simp
    have hwT : (n⁻¹ • (e - c • u) : E) ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x :=
      (sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x).smul_mem n⁻¹
        ((sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x).sub_mem heT
          ((sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x).smul_mem c huT))
    have hδ : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    obtain ⟨hh0, hhδ⟩ := hh
    have hhρ₀ : h < ρ₀ := lt_of_lt_of_le hhδ (min_le_left _ _)
    have hhρ₁ : h < ρ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
    have hhn0 : 0 < h * n := mul_pos hh0 hnpos
    have hhnle : h * n ≤ h := by nlinarith
    have hshiftb : infDist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M))
        B ≤ infDist x B :=
      hshift x hx (by rw [dist_self]; exact hρ₀) u (n⁻¹ • (e - c • u)) hu hw huw huT hwT hfoot
        (h * n) ⟨hhn0.le, lt_of_le_of_lt hhnle hhρ₀⟩
    have hminw : dist x (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M)) =
        h * n := hrad _ hw (h * n) ⟨hhn0.le, lt_of_le_of_lt hhnle hhρ₁⟩
    have hmine : dist x (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) = h :=
      hrad e he h ⟨hh0.le, hhρ₁⟩
    have hhinge := dist_sq_le_hinge_finite g hr hnorm hsec x hhn0 hh0 hw he hminw hmine
    rw [hwe] at hhinge
    have hcn : (0 : ℝ) ≤ h * (-c) := mul_nonneg hh0.le (by linarith)
    have hsq : dist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M))
        (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) ^ 2 ≤ (h * (-c)) ^ 2 := by
      have heq : (h * n) ^ 2 + h ^ 2 - 2 * (h * n) * h * n = (h * (-c)) ^ 2 := by
        linear_combination (-h ^ 2) * hnsq
      linarith
    have hdle : dist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M))
        (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) ≤ h * (-c) := by
      have hroot := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq hcn] at hroot
    have hfinal : infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) B ≤
        infDist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M)) B +
          dist (g.expMap (⟨x, h • e⟩ : TangentBundle I M))
            (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M)) :=
      infDist_le_infDist_add_dist
    rw [dist_comm] at hfinal
    refine hfinal.trans ((add_le_add hshiftb hdle).trans (le_of_eq ?_))
    ring

/-- **The relative step, case `g_x(u, e) > 0`** (four hinges and one relative orthogonal shift). -/
theorem infDist_relBoundaryOfOrder_step_of_inner_pos [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hshiftZ : ∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ ρ > 0,
      ∀ y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, dist x y < ρ → ∀ u w : E,
      g.inner y u u = 1 → g.inner y w w = 1 → g.inner y u w = 0 →
      u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤ infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))
    {x : M} (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {u : E} (hu : g.inner x u u = 1)
    (hfoot : g.expMap (⟨x, infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
      relBoundaryOfOrder I (r : ℕ∞ω) C)
    {e : E} (he : g.inner x e e = 1) (heT : e ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x)
    (hc : 0 < g.inner x u e) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M))
        (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
      infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) - h * g.inner x u e := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  obtain ⟨ρ₀, hρ₀, hshift⟩ := hshiftZ x hx
  obtain ⟨ρ₁, hρ₁, hrad⟩ := exists_radial_dist_eq g hr hnorm x
  have hBcl : IsClosed B := isClosed_relBoundaryOfOrder g hr hnorm hCcl hconv
  have hfne : B.Nonempty := ⟨_, hfoot⟩
  have hlpos : 0 < infDist x B := (hBcl.notMem_iff_infDist_pos hfne).1 fun hB => hB.2 hx
  have hxC : x ∈ C := maxSliceLocusOfOrder_subset hx
  obtain ⟨-, hsegZ, -⟩ := foot_segment_relBoundaryOfOrder g hr hnorm hconv hxC hu hfoot
  have hc1 : g.inner x u e ≤ 1 := by
    have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g x u e
    rw [hu, he, Real.sqrt_one, mul_one] at hcs
    exact (abs_le.mp hcs).2
  obtain ⟨hseg, hτ⟩ := dist_infDist_expMap_smul_of_foot g hr hnorm hu hfoot
  set l : ℝ := infDist x B with hldef
  set c : ℝ := g.inner x u e with hcdef
  have hτlip : ∀ s t : ℝ, dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
      (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) ≤ |t - s| := by
    intro s t
    have h := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm (x := x) u s t
    rwa [hu, Real.sqrt_one, one_mul] at h
  have hτc : Continuous (fun t : ℝ => g.expMap (⟨x, t • u⟩ : TangentBundle I M)) := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun s t => ?_)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm]
    exact hτlip s t
  have hτ0 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
    rw [zero_smul]; exact g.expMap_zero hr1 x
  have hflowx : ∀ τ : ℝ, g.expMap (⟨x, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 x u τ (by rw [hD]; exact mem_univ _)
  have hδ : 0 < min (min (ρ₀ / 4) ρ₁) (l / 4) := lt_min (lt_min (by linarith) hρ₁) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  obtain ⟨hh0, hhδ⟩ := hh
  have hhρ₀ : h < ρ₀ / 4 := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_left _ _))
  have hhρ₁ : h < ρ₁ := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_right _ _))
  have hhl : h < l / 4 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hxz : dist x (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) = h := hrad e he h ⟨hh0.le, hhρ₁⟩
  -- `z = exp_x (h e)` lies in `Z` (relative ball)
  have hzZ : g.expMap (⟨x, h • e⟩ : TangentBundle I M) ∈ Z := by
    have hheT : (h • e : E) ∈ sliceTangent I Z x := (sliceTangent I Z x).smul_mem h heT
    refine expMap_mem_maxSliceLocusOfOrder_of_lt_infDist g hr hnorm hCcl hconv hx hheT ?_
    have h1 : g.inner x (h • e) (h • e) = h ^ 2 := by
      rw [shaveInner_smul_left, shaveInner_smul_right, he]; ring
    rw [h1, Real.sqrt_sq hh0.le]
    linarith
  set z : M := g.expMap (⟨x, h • e⟩ : TangentBundle I M) with hzdef
  change infDist z B ≤ l - h * c
  have hzx : dist z x = h := by rw [dist_comm]; exact hxz
  obtain ⟨t₀, ht₀mem, ht₀min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlpos.le)
    ((continuous_const.dist hτc).continuousOn :
      ContinuousOn (fun t => dist z (g.expMap (⟨x, t • u⟩ : TangentBundle I M))) (Icc 0 l))
  have hmin : ∀ t ∈ Icc 0 l, dist z (g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M)) ≤
      dist z (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) := fun t ht => ht₀min ht
  have hxt₀ : dist x (g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M)) = t₀ := (hτ t₀ ht₀mem).1
  have hψt₀ : infDist (g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M)) B = l - t₀ :=
    (hτ t₀ ht₀mem).2
  set τ₀ : M := g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M) with hτ₀def
  have hmin0 : dist z τ₀ ≤ dist z (g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M)) :=
    hmin 0 ⟨le_rfl, hlpos.le⟩
  rw [hτ0, hzx] at hmin0
  set rr : ℝ := dist z τ₀ with hrrdef
  have hrrnn : 0 ≤ rr := dist_nonneg
  have ht₀le : t₀ ≤ 2 * h := by
    have htri : dist x τ₀ ≤ dist x z + dist z τ₀ := dist_triangle _ _ _
    rw [hxt₀, hxz] at htri
    linarith
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀mem.1 with hzero | hposi
    · exfalso
      have hτ₀x : τ₀ = x := by rw [hτ₀def, ← hzero]; exact hτ0
      have hrr_eq : rr = h := by rw [hrrdef, hτ₀x]; exact hzx
      have hspos : 0 < min l (h * c) := lt_min hlpos (mul_pos hh0 hc)
      have hsl : min l (h * c) ≤ l := min_le_left _ _
      have hshc : min l (h * c) ≤ h * c := min_le_right _ _
      have hminu : dist x (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) =
          min l (h * c) := (hτ _ ⟨hspos.le, hsl⟩).1
      have hhinge : dist (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) z ^ 2 ≤
          min l (h * c) ^ 2 + h ^ 2 - 2 * min l (h * c) * h * c :=
        dist_sq_le_hinge_finite g hr hnorm hsec x hspos hh0 hu he hminu hxz
      have hmins : rr ≤ dist z (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) :=
        hmin _ ⟨hspos.le, hsl⟩
      have hge : h ≤ dist (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) z := by
        rw [dist_comm]; linarith
      exact shave_hinge_start_aux hspos hh0 hc hge hshc hhinge
    · exact hposi
  have ht₀l : t₀ < l := by linarith
  have hτ₀Z : τ₀ ∈ Z := by
    rw [hτ₀def, hflowx]; exact hsegZ t₀ ⟨ht₀pos.le, ht₀l⟩
  rcases eq_or_lt_of_le hrrnn with hr0 | hrrpos
  · have hzeq : z = τ₀ := dist_eq_zero.1 (by rw [← hrrdef]; exact hr0.symm)
    have ht₀h : t₀ = h := by rw [← hxt₀, ← hzeq]; exact hxz
    rw [hzeq, hψt₀, ht₀h]
    nlinarith
  · -- the velocity of the segment at `t₀`
    have hPproj : (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t₀).proj = τ₀ :=
      (g.expMap_smul_eq_proj_geodesicFlow hr1 x u t₀ (by rw [hD]; exact mem_univ _)).symm
    obtain ⟨V, hVdef⟩ : ∃ V : E, V = (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t₀).snd :=
      ⟨_, rfl⟩
    have hfwd : ∀ s : ℝ, g.expMap (⟨τ₀, s • V⟩ : TangentBundle I M) =
        g.expMap (⟨x, (t₀ + s) • u⟩ : TangentBundle I M) := by
      intro s
      have h1 := proj_geodesicFlow_add_eq_expMap g hr hnorm (⟨x, u⟩ : TangentBundle I M) t₀ s
      have h2 := g.expMap_smul_eq_proj_geodesicFlow hr1 x u (t₀ + s) (by rw [hD]; exact mem_univ _)
      calc g.expMap (⟨τ₀, s • V⟩ : TangentBundle I M)
          = g.expMap (⟨(g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t₀).proj, s • V⟩ :
              TangentBundle I M) := expMap_mk_congr g hPproj.symm (s • V)
        _ = (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) (t₀ + s)).proj := by
            subst hVdef; exact h1.symm
        _ = g.expMap (⟨x, (t₀ + s) • u⟩ : TangentBundle I M) := h2.symm
    have hVu : g.inner τ₀ V V = 1 := by
      have h3 := g.inner_geodesicFlow_eq hr1 (⟨x, u⟩ : TangentBundle I M) t₀
        (by rw [hD]; exact mem_univ _)
      rw [← hPproj]
      subst hVdef
      exact h3.trans hu
    have hVT : V ∈ sliceTangent I Z τ₀ := by
      have hd : 0 < l - t₀ := by linarith
      refine mem_sliceTangent_of_expMap_mem g hr hnorm hconv hτ₀Z (d := (l - t₀) / 2)
        (by positivity) ?_
      rw [hfwd, hflowx]
      exact maxSliceLocusOfOrder_subset (hsegZ _ ⟨by linarith, by linarith⟩)
    -- the back leg to `x`
    have hback : g.expMap (⟨τ₀, t₀ • ((-1 : ℝ) • V)⟩ : TangentBundle I M) = x := by
      have hv : (t₀ • ((-1 : ℝ) • V) : E) = (-t₀) • V := by rw [smul_smul, mul_neg_one]
      calc g.expMap (⟨τ₀, t₀ • ((-1 : ℝ) • V)⟩ : TangentBundle I M)
          = g.expMap (⟨τ₀, (-t₀) • V⟩ : TangentBundle I M) :=
            congrArg (fun w : E => g.expMap (⟨τ₀, w⟩ : TangentBundle I M)) hv
        _ = g.expMap (⟨x, (t₀ + -t₀) • u⟩ : TangentBundle I M) := hfwd (-t₀)
        _ = x := by rw [add_neg_cancel]; exact hτ0
    have hnegV : g.inner τ₀ ((-1 : ℝ) • V) ((-1 : ℝ) • V) = 1 := by
      rw [shaveInner_smul_left, shaveInner_smul_right, hVu]; norm_num
    have hminback : dist τ₀ (g.expMap (⟨τ₀, t₀ • ((-1 : ℝ) • V)⟩ : TangentBundle I M)) = t₀ := by
      rw [hback, dist_comm]; exact hxt₀
    -- the segment from `τ₀` to `z`
    obtain ⟨W, hW, -, hWend⟩ := g.exists_unit_segment_expMap hr hnorm τ₀ z
    have hτ₀z : dist τ₀ z = rr := by rw [hrrdef, dist_comm]
    have hWend' : g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M) = z := by
      rw [← hτ₀z]; exact hWend
    have hminW : dist τ₀ (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) = rr := by
      rw [hWend']; exact hτ₀z
    have hWT : W ∈ sliceTangent I Z τ₀ :=
      mem_sliceTangent_of_expMap_mem g hr hnorm hconv hτ₀Z hrrpos
        (by rw [hWend']; exact maxSliceLocusOfOrder_subset hzZ)
    have hloc : ∀ᶠ s in 𝓝 (0 : ℝ), dist (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) τ₀ ≤
        dist (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M))
          (g.expMap (⟨τ₀, s • V⟩ : TangentBundle I M)) := by
      filter_upwards [Ioo_mem_nhds (show -t₀ < (0 : ℝ) by linarith)
        (show (0 : ℝ) < l - t₀ by linarith)] with s hs
      have h5 := hmin (t₀ + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [← hfwd s] at h5
      rw [hWend']
      exact h5
    have hperp : g.inner τ₀ W V = 0 :=
      inner_eq_zero_of_isLocalMin_dist g hr hnorm hsec hVu hW hrrpos hminW hloc
    -- hinge at `τ₀`: Pythagoras
    have hinge2 : dist x z ^ 2 ≤ t₀ ^ 2 + rr ^ 2 - 2 * t₀ * rr * g.inner τ₀ ((-1 : ℝ) • V) W := by
      have h4 := dist_sq_le_hinge_finite g hr hnorm hsec τ₀ ht₀pos hrrpos hnegV hW hminback hminW
      rwa [hback, hWend'] at h4
    have hVW : g.inner τ₀ ((-1 : ℝ) • V) W = 0 := by
      rw [shaveInner_smul_left, shaveInner_symm g τ₀ V W, hperp, mul_zero]
    rw [hVW, hxz] at hinge2
    have hpyth : h ^ 2 ≤ t₀ ^ 2 + rr ^ 2 := by linarith
    -- hinge at `x`
    have hinge1 : dist τ₀ z ^ 2 ≤ t₀ ^ 2 + h ^ 2 - 2 * t₀ * h * c :=
      dist_sq_le_hinge_finite g hr hnorm hsec x ht₀pos hh0 hu he hxt₀ hxz
    rw [hτ₀z] at hinge1
    have ht₀ge : h * c ≤ t₀ := shave_hinge_foot_aux ht₀pos hinge1 hpyth
    -- the relative orthogonal shift at `τ₀`
    have hfoot₀ : g.expMap (⟨τ₀, infDist τ₀ B • V⟩ : TangentBundle I M) ∈ B := by
      rw [hψt₀, hfwd (l - t₀), show t₀ + (l - t₀) = l by ring]
      exact hfoot
    have hVW' : g.inner τ₀ V W = 0 := by rw [shaveInner_symm]; exact hperp
    have hsh : infDist (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) B ≤ infDist τ₀ B :=
      hshift τ₀ hτ₀Z (by rw [hxt₀]; linarith) V W hVu hW hVW' hVT hWT hfoot₀ rr ⟨hrrnn, by linarith⟩
    rw [hWend', hψt₀] at hsh
    linarith

/-- **The relative step (SL4)**: the exact linear upper support of `d(·, B)` at `x ∈ Z` along any unit
`e ∈ T_x Z`, with slope `-g_x(u, e)` for a unit tangent direction `u` to a nearest point of `B`. -/
theorem infDist_relBoundaryOfOrder_step_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hshiftZ : ∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ ρ > 0,
      ∀ y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, dist x y < ρ → ∀ u w : E,
      g.inner y u u = 1 → g.inner y w w = 1 → g.inner y u w = 0 →
      u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤ infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))
    {x : M} (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {u : E} (hu : g.inner x u u = 1)
    (huT : u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x)
    (hfoot : g.expMap (⟨x, infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
      relBoundaryOfOrder I (r : ℕ∞ω) C)
    {e : E} (he : g.inner x e e = 1) (heT : e ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M))
        (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
      infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) - h * g.inner x u e := by
  rcases le_or_gt (g.inner x u e) 0 with hc | hc
  · exact infDist_relBoundaryOfOrder_step_of_inner_nonpos g hr hnorm hsec hshiftZ hx hu huT hfoot he
      heT hc
  · exact infDist_relBoundaryOfOrder_step_of_inner_pos g hr hnorm hsec hCcl hconv hshiftZ hx hu
      hfoot he heT hc

/-- **Linear upper support of `d(γ_p ·, B)`** at an interior parameter `s` with `γ_p s ∈ Z` (any
dimension, from the relative orthogonal shift). -/
theorem exists_upper_support_infDist_relBoundaryOfOrder_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hshiftZ : ∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ ρ > 0,
      ∀ y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, dist x y < ρ → ∀ u w : E,
      g.inner y u u = 1 → g.inner y w w = 1 → g.inner y u w = 0 →
      u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤ infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))
    (p : TangentBundle I M) {ℓ s : ℝ} (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C)
    (hs : s ∈ Ioo 0 ℓ) (hsZ : (g.geodesicFlow p s).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∃ c : ℝ, ∀ᶠ y in 𝓝 s, infDist (g.geodesicFlow p y).proj (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
      infDist (g.geodesicFlow p s).proj (relBoundaryOfOrder I (r : ℕ∞ω) C) + c * (y - s) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hlip : ∀ a b : ℝ, dist (g.geodesicFlow p a).proj (g.geodesicFlow p b).proj ≤ σ * |b - a| :=
    fun a b => g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  rcases B.eq_empty_or_nonempty with hB | hB
  · refine ⟨0, Eventually.of_forall fun y => ?_⟩
    rw [hB, infDist_empty, infDist_empty]
    simp
  have hσnn : 0 ≤ σ := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hσnn with hσ0 | hσpos
  · refine ⟨0, Eventually.of_forall fun y => ?_⟩
    have h := hlip s y
    rw [← hσ0, zero_mul] at h
    have heq : (g.geodesicFlow p y).proj = (g.geodesicFlow p s).proj :=
      (dist_le_zero.1 h).symm
    rw [heq]
    simp
  have hBcl : IsClosed B := isClosed_relBoundaryOfOrder g hr hnorm hCcl hconv
  set x : M := (g.geodesicFlow p s).proj with hxdef
  obtain ⟨u, hu, hfoot⟩ := exists_unit_foot_of_isClosed g hr hnorm hBcl hB x
  have hxC : x ∈ C := maxSliceLocusOfOrder_subset hsZ
  have hlx : 0 < infDist x B := (hBcl.notMem_iff_infDist_pos hB).1 fun hxB => hxB.2 hsZ
  obtain ⟨-, hsegZ, -⟩ := foot_segment_relBoundaryOfOrder g hr hnorm hconv hxC hu hfoot
  have huT : u ∈ sliceTangent I Z x :=
    snd_mem_sliceTangent_of_eventually g hr1 (⟨x, u⟩ : TangentBundle I M)
      (fun τ => by rw [hD]; exact mem_univ _)
      (by filter_upwards [Ioo_mem_nhdsGT hlx] with τ hτ using hsegZ τ ⟨hτ.1.le, hτ.2⟩)
  obtain ⟨v, hvdef⟩ : ∃ v : E, v = (g.geodesicFlow p s).snd := ⟨_, rfl⟩
  have hvT : v ∈ sliceTangent I Z x := by
    rw [hvdef]
    exact snd_mem_sliceTangent_of_mem_maxSliceLocusOfOrder g hr hnorm hconv p hmaps hs hsZ
  have hvv : g.inner (g.geodesicFlow p s).proj v v = σ ^ 2 := by
    subst hvdef
    rw [g.inner_geodesicFlow_eq hr1 p s (by rw [hD]; exact mem_univ _), hσ,
      Real.sq_sqrt (DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g _ _)]
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  obtain ⟨e, hedef⟩ : ∃ e : E, e = σ⁻¹ • v := ⟨_, rfl⟩
  have he : g.inner (g.geodesicFlow p s).proj e e = 1 := by
    rw [hedef, shaveInner_smul_left, shaveInner_smul_right, hvv]
    field_simp
  have heT : e ∈ sliceTangent I Z x := by
    rw [hedef]; exact (sliceTangent I Z x).smul_mem σ⁻¹ hvT
  obtain ⟨e', he'def⟩ : ∃ e' : E, e' = (-1 : ℝ) • e := ⟨_, rfl⟩
  have he' : g.inner (g.geodesicFlow p s).proj e' e' = 1 := by
    rw [he'def, shaveInner_smul_left, shaveInner_smul_right, he]
    norm_num
  have he'T : e' ∈ sliceTangent I Z x := by
    rw [he'def]; exact (sliceTangent I Z x).smul_mem (-1 : ℝ) heT
  have hue' : g.inner (g.geodesicFlow p s).proj u e' = -g.inner (g.geodesicFlow p s).proj u e := by
    rw [he'def, shaveInner_smul_right]
    ring
  have hflow : ∀ y : ℝ, (g.geodesicFlow p y).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, (y - s) • v⟩ : TangentBundle I M) := by
    intro y
    have h1 := proj_geodesicFlow_add_eq_expMap g hr hnorm p s (y - s)
    rw [add_sub_cancel] at h1
    subst hvdef
    exact h1
  have hfwd : ∀ y : ℝ, (g.geodesicFlow p y).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (y - s)) • e⟩ : TangentBundle I M) := by
    intro y
    have hv' : ((σ * (y - s)) • (σ⁻¹ • v) : E) = (y - s) • v := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [hflow y, hedef]
    exact (congrArg (fun w : E => g.expMap (⟨(g.geodesicFlow p s).proj, w⟩ : TangentBundle I M))
      hv').symm
  have hbwd : ∀ y : ℝ, (g.geodesicFlow p y).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (s - y)) • e'⟩ : TangentBundle I M) := by
    intro y
    have hv' : ((σ * (s - y)) • ((-1 : ℝ) • (σ⁻¹ • v)) : E) = (y - s) • v := by
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [hflow y, he'def, hedef]
    exact (congrArg (fun w : E => g.expMap (⟨(g.geodesicFlow p s).proj, w⟩ : TangentBundle I M))
      hv').symm
  have hstep1 := infDist_relBoundaryOfOrder_step_of_shift g hr hnorm hsec hCcl hconv hshiftZ hsZ hu
    huT hfoot he heT
  have hstep2 := infDist_relBoundaryOfOrder_step_of_shift g hr hnorm hsec hCcl hconv hshiftZ hsZ hu
    huT hfoot he' he'T
  obtain ⟨δ₁, hδ₁, hP₁⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hstep1)
  obtain ⟨δ₂, hδ₂, hP₂⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hstep2)
  set c : ℝ := g.inner (g.geodesicFlow p s).proj u e with hcdef
  refine ⟨-(σ * c), ?_⟩
  have hε : 0 < min δ₁ δ₂ / σ := div_pos (lt_min hδ₁ hδ₂) hσpos
  filter_upwards [Ioo_mem_nhds (show s - min δ₁ δ₂ / σ < s by linarith)
    (show s < s + min δ₁ δ₂ / σ by linarith)] with y hy
  have hσδ : ∀ a : ℝ, 0 < a → a < min δ₁ δ₂ / σ → σ * a < min δ₁ δ₂ := by
    intro a ha hlt
    have h := mul_lt_mul_of_pos_left hlt hσpos
    rwa [mul_div_cancel₀ _ hσne] at h
  rcases lt_trichotomy y s with hlt | hyeq | hgt
  · have hh0 : 0 < σ * (s - y) := mul_pos hσpos (by linarith)
    have hlt2 := hσδ (s - y) (by linarith) (by linarith [hy.1])
    have hres : infDist (g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (s - y)) • e'⟩ :
        TangentBundle I M)) B ≤ infDist (g.geodesicFlow p s).proj B -
          σ * (s - y) * g.inner (g.geodesicFlow p s).proj u e' :=
      hP₂ (by rw [Real.dist_eq, sub_zero, abs_of_pos hh0]; exact lt_of_lt_of_le hlt2 (min_le_right _ _))
        hh0
    rw [← hbwd y, hue'] at hres
    refine hres.trans (le_of_eq ?_)
    ring
  · rw [hyeq, sub_self, mul_zero, add_zero]
  · have hh0 : 0 < σ * (y - s) := mul_pos hσpos (by linarith)
    have hlt2 := hσδ (y - s) (by linarith) (by linarith [hy.2])
    have hres : infDist (g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (y - s)) • e⟩ :
        TangentBundle I M)) B ≤ infDist (g.geodesicFlow p s).proj B - σ * (y - s) * c :=
      hP₁ (by rw [Real.dist_eq, sub_zero, abs_of_pos hh0]; exact lt_of_lt_of_le hlt2 (min_le_left _ _))
        hh0
    rw [← hfwd y] at hres
    refine hres.trans (le_of_eq ?_)
    ring

end DifferentialGeometry.Geometry.FiniteSoul

end
