import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeInteriorApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicSlice
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveHinge
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveFootPoint

/-!
# REL kernel, step (i): the relative ball by first boundary hit and length bound (CMS3-REL, G1)

Lane CMS3-REL, sub-lemmas SL0–SL1 of `build-logs/resume/sheet-CMS3-REL.md` (review
`out/review-finite-soul-three.md` item 7: the relative ball is proved by a first boundary hit plus a
length bound). Setting: a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`), a closed totally
convex `C`, its relative interior `Z = maxSliceLocusOfOrder I r C` and relative boundary
`B = relBoundaryOfOrder I r C = C \ Z`. Everything is AMBIENT: ambient geodesics and distances only.

* `snd_mem_sliceTangent_of_right`, `snd_mem_sliceTangent_of_left`: the velocity of a geodesic lying in
  a set on one side of a time is tangent to the set there (reversal of the flow for the left side).
* `IsTotallyConvexFinite.proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_end` / `_of_start`: an arc of
  `C` ending (starting) in `Z` lies in `Z` except possibly at its other end (SLICE (7)).
* `proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_forall_notMem` (no escape): a geodesic starting in `Z`
  tangent to `Z` that avoids `B` on `[0, T]` stays in `Z` on `[0, T]`. Proof: the prefix set
  `{t | γ [0, t] ⊆ Z}` is closed in `[0, T]` (`closure Z ⊆ C`, `C \ B ⊆ Z`) and open to the right (the
  velocity at a prefix end is tangent, `Z` is totally geodesic); `IsClosed.Icc_subset_of_forall_mem_nhdsWithin`.
* `proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_mul_lt`, `expMap_mem_maxSliceLocusOfOrder_of_lt_infDist`
  (relative ball): `exp_y v ∈ Z` for `v ∈ T_y Z` with `|v| < d(y, B)` (length bound `d(y, γ t) ≤ t |v|`).
* `exists_unit_foot_of_isClosed`, `foot_segment_relBoundaryOfOrder`: nearest points of a closed set and
  the foot segment to `B` (in `C`, in `Z` before the foot, `d(γ t, B) = d(y, B) - t`).
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

/-- The velocity at time `t` of a geodesic lying in `S` on `(t, t + δ)` is tangent to `S`. -/
theorem snd_mem_sliceTangent_of_right
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (p : TangentBundle I M) {t δ : ℝ} (hδ : 0 < δ)
    (h : ∀ τ ∈ Ioo t (t + δ), (g.geodesicFlow p τ).proj ∈ S) :
    (g.geodesicFlow p t).snd ∈ sliceTangent I S (g.geodesicFlow p t).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  refine snd_mem_sliceTangent_of_eventually g hr1 (g.geodesicFlow p t)
    (fun s => by rw [hD]; exact mem_univ _) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
  rw [← geodesicFlow_add_of_complete g hr hnorm]
  exact h _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The velocity at time `t` of a geodesic lying in `S` on `(t - δ, t)` is tangent to `S`. -/
theorem snd_mem_sliceTangent_of_left
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (p : TangentBundle I M) {t δ : ℝ} (hδ : 0 < δ)
    (h : ∀ τ ∈ Ioo (t - δ) t, (g.geodesicFlow p τ).proj ∈ S) :
    (g.geodesicFlow p t).snd ∈ sliceTangent I S (g.geodesicFlow p t).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set P := g.geodesicFlow p t with hP
  have hneg : ((-1 : ℝ) • P.snd : TangentSpace I P.proj) ∈ sliceTangent I S P.proj := by
    refine snd_mem_sliceTangent_of_eventually g hr1
      (⟨P.proj, (-1 : ℝ) • P.snd⟩ : TangentBundle I M) (fun s => by rw [hD]; exact mem_univ _) ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    rw [proj_geodesicFlow_neg_snd g hr hnorm P s, hP, ← geodesicFlow_add_of_complete g hr hnorm]
    exact h _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h2 := (sliceTangent I S P.proj).smul_mem (-1 : ℝ) hneg
  rwa [smul_smul, show (-1 : ℝ) * (-1) = 1 by norm_num, one_smul] at h2

/-- An arc of the totally convex `C` that ends in the relative interior lies in it except possibly at
its start (total convexity + relative open-core propagation). -/
theorem IsTotallyConvexFinite.proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_end
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : p.proj ∈ C) (hend : (g.geodesicFlow p ℓ).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∀ t ∈ Ioc 0 ℓ, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C :=
    hconv p ℓ hℓ.le hp (maxSliceLocusOfOrder_subset hend)
  intro t ht
  rcases eq_or_lt_of_le ht.2 with htℓ | htℓ
  · rw [htℓ]; exact hend
  · exact hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm p hmaps ⟨hℓ.le, le_rfl⟩ hend t
      ⟨ht.1, htℓ⟩

/-- An arc of the totally convex `C` that starts in the relative interior lies in it except possibly
at its end. -/
theorem IsTotallyConvexFinite.proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_start
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : p.proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) (hend : (g.geodesicFlow p ℓ).proj ∈ C) :
    ∀ t ∈ Ico 0 ℓ, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hp0 : (g.geodesicFlow p 0).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
    rw [g.geodesicFlow_zero hr1]; exact hp
  have hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C :=
    hconv p ℓ hℓ.le (maxSliceLocusOfOrder_subset hp) hend
  intro t ht
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · rw [← ht0]; exact hp0
  · exact hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm p hmaps ⟨le_rfl, hℓ.le⟩ hp0 t
      ⟨ht0, ht.2⟩

/-- **No escape (SL1).** A geodesic starting in the relative interior `Z` of the closed totally convex
`C`, tangent to `Z`, that avoids the relative boundary `B` on `[0, T]`, stays in `Z` on `[0, T]`. -/
theorem proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_forall_notMem
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M)
    (hp : p.proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C)
    (hv : p.snd ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) p.proj) {T : ℝ}
    (hstay : ∀ t ∈ Icc 0 T, (g.geodesicFlow p t).proj ∉ relBoundaryOfOrder I (r : ℕ∞ω) C) :
    ∀ t ∈ Icc 0 T, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγdef
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hγc : Continuous γ := by
    refine LipschitzWith.continuous (K := ⟨σ, hσ0⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  have htg : IsTotallyGeodesicFinite g Z := isTotallyGeodesicFinite_maxSliceLocusOfOrder g hr hnorm hconv
  have hclZ : closure Z ⊆ C := closure_minimal maxSliceLocusOfOrder_subset hCcl
  have hmemZ : ∀ t ∈ Icc 0 T, γ t ∈ C → γ t ∈ Z := fun t ht hC => by
    by_contra hZ
    exact hstay t ht ⟨hC, hZ⟩
  set s : Set ℝ := {t | ∀ τ ∈ Icc 0 t, γ τ ∈ Z} with hsdef
  have h0 : γ 0 ∈ Z := by
    change (g.geodesicFlow p 0).proj ∈ Z
    rw [g.geodesicFlow_zero hr1]; exact hp
  have hsub : Icc 0 T ⊆ s := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · refine isClosed_of_closure_subset fun x hx => ?_
      have hxI : x ∈ Icc 0 T :=
        isClosed_Icc.closure_subset (closure_mono inter_subset_right hx)
      refine ⟨fun τ hτ => ?_, hxI⟩
      rcases eq_or_lt_of_le hτ.2 with hτx | hτx
      · have hcl : γ x ∈ closure Z := by
          refine map_mem_closure hγc hx fun y hy => ?_
          exact hy.1 y ⟨hy.2.1, le_rfl⟩
        rw [hτx]
        exact hmemZ x hxI (hclZ hcl)
      · obtain ⟨y, hyU, hys⟩ := mem_closure_iff.1 hx (Ioi τ) isOpen_Ioi hτx
        exact hys.1 τ ⟨hτ.1, le_of_lt hyU⟩
    · intro τ hτ
      have hτ0 : τ = 0 := le_antisymm hτ.2 hτ.1
      rw [hτ0]; exact h0
    · rintro x ⟨hxs, hxI⟩
      have hxZ : γ x ∈ Z := hxs x ⟨hxI.1, le_rfl⟩
      have hvx : (g.geodesicFlow p x).snd ∈ sliceTangent I Z (g.geodesicFlow p x).proj := by
        rcases eq_or_lt_of_le hxI.1 with hx0 | hx0
        · have hflow0 : g.geodesicFlow p x = p := by rw [← hx0]; exact g.geodesicFlow_zero hr1 p
          rw [hflow0]; exact hv
        · exact snd_mem_sliceTangent_of_left g hr hnorm p hx0 fun τ hτ =>
            hxs τ ⟨by linarith [hτ.1], hτ.2.le⟩
      obtain ⟨δ, hδ, hδZ⟩ := htg _ hxZ _ hvx
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show x < x + δ by linarith)) ?_
      intro y hy τ hτ
      rcases le_or_gt τ x with hτx | hτx
      · exact hxs τ ⟨hτ.1, hτx⟩
      · have h1 := hδZ (τ - x) ⟨by linarith, by linarith [hy.2, hτ.2]⟩
        change (g.geodesicFlow p τ).proj ∈ Z
        rw [show τ = x + (τ - x) by ring, geodesicFlow_add_of_complete g hr hnorm]
        exact h1
  intro t ht
  exact hsub ht t ⟨ht.1, le_rfl⟩

/-- **Relative ball, flow form.** If `T |v| < d(y, B)` with `y ∈ Z`, `v ∈ T_y Z`, the geodesic from
`(y, v)` lies in `Z` on `[0, T]`. -/
theorem proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_mul_lt
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {y : M}
    (hy : y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {v : E}
    (hv : v ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y) {T : ℝ}
    (hlt : T * Real.sqrt (g.inner y v v) < infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)) :
    ∀ t ∈ Icc 0 T, (g.geodesicFlow (⟨y, v⟩ : TangentBundle I M) t).proj ∈
      maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  refine proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_forall_notMem g hr hnorm hCcl hconv
    (⟨y, v⟩ : TangentBundle I M) hy hv fun t ht hB => ?_
  have hd := g.dist_proj_geodesicFlow_le hr1 hnorm (p := (⟨y, v⟩ : TangentBundle I M)) (s := 0)
    (t := t) (fun τ _ => by rw [hD]; exact mem_univ _)
  rw [g.geodesicFlow_zero hr1] at hd
  change dist y _ ≤ Real.sqrt (g.inner y v v) * |t - 0| at hd
  rw [sub_zero, abs_of_nonneg ht.1] at hd
  have h1 := infDist_le_dist_of_mem (x := y) hB
  have h2 : Real.sqrt (g.inner y v v) * t ≤ T * Real.sqrt (g.inner y v v) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg _)
  linarith

/-- **Relative ball (SL1).** `exp_y v ∈ Z` for `y ∈ Z`, `v ∈ T_y Z`, `|v| < d(y, B)`. -/
theorem expMap_mem_maxSliceLocusOfOrder_of_lt_infDist
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {y : M}
    (hy : y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {v : E}
    (hv : v ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y)
    (hlt : Real.sqrt (g.inner y v v) < infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)) :
    g.expMap (⟨y, v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have h := proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_mul_lt g hr hnorm hCcl hconv hy hv
    (by rw [one_mul]; exact hlt) 1 ⟨zero_le_one, le_rfl⟩
  have he : g.expMap (⟨y, v⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, v⟩ : TangentBundle I M) 1).proj := by
    rw [← g.expMap_smul_eq_proj_geodesicFlow hr1 y v 1 (by rw [hD]; exact mem_univ _)]
    exact congrArg (fun w : E => g.expMap (⟨y, w⟩ : TangentBundle I M)) (one_smul ℝ v).symm
  rw [he]
  exact h

/-- A unit direction to a nearest point of a closed nonempty set. -/
theorem exists_unit_foot_of_isClosed [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {B : Set M} (hBcl : IsClosed B) (hB : B.Nonempty) (x : M) :
    ∃ u : E, g.inner x u u = 1 ∧ g.expMap (⟨x, infDist x B • u⟩ : TangentBundle I M) ∈ B := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨z, hz, hdist⟩ := hBcl.exists_infDist_eq_dist hB x
  obtain ⟨u, hu, -, hend⟩ := g.exists_unit_segment_expMap hr hnorm x z
  refine ⟨u, hu, ?_⟩
  rw [hdist, hend]
  exact hz

/-- **The foot segment to the relative boundary.** If `y ∈ C` and the unit geodesic from `y` in
direction `u` reaches `B` at time `l = d(y, B) > 0`, then it lies in `C` on `[0, l]`, in `Z` on
`[0, l)`, and `d(γ t, B) = l - t`. -/
theorem foot_segment_relBoundaryOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {y : M} (hy : y ∈ C) {u : E}
    (hu : g.inner y u u = 1)
    (hfoot : g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
      relBoundaryOfOrder I (r : ℕ∞ω) C) :
    (∀ t ∈ Icc 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
        (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj ∈ C) ∧
      (∀ t ∈ Ico 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
        (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      ∀ t ∈ Icc 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
        infDist (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj
            (relBoundaryOfOrder I (r : ℕ∞ω) C) =
          infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) - t := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  set l := infDist y B with hl
  have hl0 : 0 ≤ l := infDist_nonneg
  have hflow : ∀ τ : ℝ, g.expMap (⟨y, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 y u τ (by rw [hD]; exact mem_univ _)
  have hC : ∀ t ∈ Icc 0 l, (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj ∈ C :=
    hconv _ l hl0 hy (by rw [← hflow]; exact relBoundaryOfOrder_subset hfoot)
  obtain ⟨-, hτ⟩ := dist_infDist_expMap_smul_of_foot g hr hnorm hu hfoot
  have hdist : ∀ t ∈ Icc 0 l,
      infDist (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj B = l - t := fun t ht => by
    rw [← hflow]; exact (hτ t ht).2
  refine ⟨hC, fun t ht => ?_, hdist⟩
  by_contra hZ
  have hB : (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj ∈ B :=
    ⟨hC t ⟨ht.1, ht.2.le⟩, hZ⟩
  have h0 := hdist t ⟨ht.1, ht.2.le⟩
  rw [infDist_zero_of_mem hB] at h0
  linarith [ht.2]

end DifferentialGeometry.Geometry.FiniteSoul

end
