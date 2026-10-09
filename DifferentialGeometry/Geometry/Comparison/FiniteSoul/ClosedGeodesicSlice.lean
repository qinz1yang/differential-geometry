import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderImage
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteNormalChart
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShapeTwo
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulArc

/-!
# BASE-1a: a compact connected one-dimensional totally geodesic slice is a simple closed geodesic

Lane CMS3-SLICE (group G4), design `design-finite-soul-three-20261004.md` §4 BASE-1a. For a complete
metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`) and a compact connected `S` which is a `1`-slice of
order `r` and totally geodesic (`IsTotallyGeodesicFinite`):
`exists_closedGeodesic_of_slice_dim_one` gives a unit `p` and `ℓ > 0` with `Φ_ℓ p = p`,
`t ↦ π Φ_t p` injective on `[0, ℓ)` and `S` its range. Any dimension of the carrier.

Route (re-encounter argument of CMS-S/S-SHAPE2, transported to a slice):
* `eq_or_eq_neg_of_mem_sliceTangent_dim_one`: unit vectors of the one-dimensional tangent space are `±`;
* `snd_mem_sliceTangent_of_eventually`: the velocity of a geodesic running in `S` is tangent to `S`;
* `exists_local_geodesic_dim_one` (local structure): near `y ∈ S`, `S` is the geodesic arc
  `s ↦ π Φ_s (y, w)`, `|s| < δ` (the arc is a `1`-slice inside the `1`-slice `S`, hence relatively open
  in it: `IsEmbeddedSliceOfOrder.exists_open_inter_subset`);
* a unit geodesic tangent to `S` stays in `S` with tangent velocity forever (clopen set of times), its
  range is open and closed in `S` (matching with the local arcs), hence all of `S`; compactness forces a
  re-encounter, which is a phase-space period (opposite velocities would stop the geodesic at the
  midpoint, `geodesicFlow_ne_neg_of_unit`); the least period is `≥ ρ > 0`.
The frozen statement's instance `[NeZero (Module.finrank ℝ E)]` is not used and is dropped
(linter-forced); the verbatim statement is an `example` in `ClosedGeodesicSliceApplications.lean`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric Function
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- **Unit tangent vectors of a one-dimensional slice are `±` each other.** -/
theorem eq_or_eq_neg_of_mem_sliceTangent_dim_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {k : WithTop ℕ∞} (hk : k ≠ 0) {S : Set M} (hS : IsEmbeddedSliceOfOrder I k 1 S) {y : M}
    (hy : y ∈ S) {v w : E} (hv : v ∈ sliceTangent I S y) (hw : w ∈ sliceTangent I S y)
    (hv1 : g.inner y v v = 1) (hw1 : g.inner y w w = 1) : v = w ∨ v = (-1 : ℝ) • w := by
  have hfr : Module.finrank ℝ (sliceTangent I S y) = 1 := finrank_sliceTangent_ofOrder hk hS hy
  have hw0 : (⟨w, hw⟩ : sliceTangent I S y) ≠ 0 := by
    intro h
    exact ne_zero_of_inner_self_eq_one g hw1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw0).1 hfr ⟨v, hv⟩
  have hcv : c • w = v := congrArg Subtype.val hc
  have hc2 : c ^ 2 = 1 := by
    have h1 : g.inner y (c • w) (c • w) = c ^ 2 * g.inner y w w :=
      inner_smul_smul_self_finite g y c w
    rw [hcv, hv1, hw1, mul_one] at h1
    exact h1.symm
  have hc' : c = 1 ∨ c = -1 := by
    have h3 : (c - 1) * (c + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 h3 with h | h
    · left; linarith
    · right; linarith
  rcases hc' with rfl | rfl
  · left; rw [← hcv, one_smul]
  · right; exact hcv.symm

omit [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
/-- **The velocity of a geodesic running into `S` is tangent to `S`.** -/
theorem snd_mem_sliceTangent_of_eventually
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) {S : Set M} (q : TangentBundle I M) (hq : ∀ s, (q, s) ∈ g.geodesicFlowDomain)
    (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), (g.geodesicFlow q s).proj ∈ S) :
    q.snd ∈ sliceTangent I S q.proj := by
  have hd := g.hasMFDerivAt_geodesicFlow_proj hr (hq 0)
  refine Submodule.subset_span ⟨fun s => (g.geodesicFlow q s).proj, ?_, h, hd.mdifferentiableAt, ?_⟩
  · change (g.geodesicFlow q 0).proj = q.proj
    rw [g.geodesicFlow_zero hr]
  · rw [hd.mfderiv]
    change (1 : ℝ) • (g.geodesicFlow q 0).snd = q.snd
    rw [one_smul]
    exact congrArg (fun z : TangentBundle I M => (z.snd : E)) (g.geodesicFlow_zero hr q)

/-- **Local structure of a one-dimensional totally geodesic slice.** Near `y ∈ S`, `S` is the geodesic
arc `s ↦ π Φ_s (y, w)`, `|s| < δ`, with `w` a unit tangent vector; along it `d(y, ·) = |s|`. -/
theorem exists_local_geodesic_dim_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 S) (htg : IsTotallyGeodesicFinite g S)
    {y : M} (hy : y ∈ S) :
    ∃ w : E, w ∈ sliceTangent I S y ∧ g.inner y w w = 1 ∧ ∃ δ > 0,
      (∀ s ∈ Ioo (-δ) δ, (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj ∈ S) ∧
      (∀ s ∈ Ioo (-δ) δ, dist y (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj = |s|) ∧
      ∃ U : Set M, IsOpen U ∧ y ∈ U ∧
        ∀ x ∈ U ∩ S, ∃ s ∈ Ioo (-δ) δ, (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj = x := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk0 : (r : ℕ∞ω) ≠ 0 := by
    have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr1
    exact (zero_lt_one.trans_le h').ne'
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  -- a unit tangent vector
  have hfr : Module.finrank ℝ (sliceTangent I S y) = 1 := finrank_sliceTangent_ofOrder hk0 hS hy
  obtain ⟨⟨w₂, hw₂T⟩, hw₂⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by rw [hfr]; exact one_pos)
  obtain ⟨w₀, rfl⟩ : ∃ w₀ : E, w₀ = w₂ := ⟨w₂, rfl⟩
  have hw₀ne : w₀ ≠ 0 := fun h => hw₂ (Subtype.ext h)
  have hpos : 0 < g.inner y w₀ w₀ := g.pos y w₀ hw₀ne
  set c : ℝ := (Real.sqrt (g.inner y w₀ w₀))⁻¹ with hcdef
  set w : E := c • w₀ with hwdef
  have hwT : w ∈ sliceTangent I S y := (sliceTangent I S y).smul_mem c hw₂T
  have hw1 : g.inner y w w = 1 := by
    have h1 : g.inner y w w = c ^ 2 * g.inner y w₀ w₀ :=
      DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g y c w₀
    rw [h1, hcdef, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hwne : w ≠ 0 := ne_zero_of_inner_self_eq_one g hw1
  refine ⟨w, hwT, hw1, ?_⟩
  -- the normal chart and the geodesic arc
  obtain ⟨ρ, hρ, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm
    (isCompact_singleton (x := y))
  obtain ⟨e, hsrc, -, hexp, hdist, -, -, he0, -⟩ := hch y rfl
  obtain ⟨δ₀, hδ₀, hδ₀S⟩ := htg y hy w hwT
  set δ : ℝ := min δ₀ ρ with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hρ
  have hflow : ∀ s : ℝ, g.expMap (⟨y, s • w⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj := fun s =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 y w s (by rw [hD]; exact mem_univ _)
  have hnormsw : ∀ s : ℝ, g.inner y (s • w) (s • w) = s ^ 2 := fun s => by
    rw [inner_smul_smul_self_finite g y s w, hw1, mul_one]
  have hswsrc : ∀ s ∈ Ioo (-δ) δ, s • w ∈ e.source := by
    intro s hs
    rw [hsrc]
    change g.inner y (s • w) (s • w) < ρ ^ 2
    rw [hnormsw]
    have h1 : |s| < ρ := lt_of_lt_of_le (abs_lt.2 hs) (min_le_right _ _)
    have h2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    rw [h2]
    exact pow_lt_pow_left₀ h1 (abs_nonneg s) (by norm_num)
  have harcS : ∀ s ∈ Ioo (-δ) δ, (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj ∈ S :=
    fun s hs => hδ₀S s ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have harcdist : ∀ s ∈ Ioo (-δ) δ,
      dist y (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj = |s| := by
    intro s hs
    rw [← hflow, ← hexp _ (hswsrc s hs), hdist _ (hswsrc s hs), hnormsw, Real.sqrt_sq_eq_abs]
  refine ⟨δ, hδ, harcS, harcdist, ?_⟩
  -- the arc is a `1`-slice inside `S`
  set L : Submodule ℝ E := ℝ ∙ w with hLdef
  set B : Set E := {v : E | g.inner y v v < δ ^ 2} with hBdef
  have hBopen : IsOpen B :=
    isOpen_lt ((g.inner y : E →L[ℝ] E →L[ℝ] ℝ).continuous₂.comp (continuous_id.prodMk continuous_id))
      continuous_const
  set P : Set E := (L.toAffineSubspace : Set E) ∩ B with hPdef
  have hP : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (r : ℕ∞ω) 1 P := by
    have h := (IsEmbeddedSliceOfOrder.of_affineSubspace (k := (r : ℕ∞ω))
      L.toAffineSubspace).inter_open hBopen
    rwa [Submodule.toAffineSubspace_direction, finrank_span_singleton hwne] at h
  have hPmem : ∀ v ∈ P, ∃ s ∈ Ioo (-δ) δ, s • w = v := by
    rintro v ⟨hvL, hvB⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 (Submodule.mem_toAffineSubspace.1 hvL)
    refine ⟨s, ?_, rfl⟩
    have hvB' : g.inner y (s • w) (s • w) < δ ^ 2 := hvB
    rw [hnormsw] at hvB'
    exact abs_lt.1 (abs_lt_of_sq_lt_sq hvB' hδ.le)
  have hPsrc : P ⊆ e.source := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := hPmem v hv
    exact hswsrc s hs
  set T : Set M := e '' P with hTdef
  have hT : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 T := hP.image e hPsrc
  have hTarc : ∀ x ∈ T, ∃ s ∈ Ioo (-δ) δ,
      (g.geodesicFlow (⟨y, w⟩ : TangentBundle I M) s).proj = x := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hPmem v hv
    exact ⟨s, hs, by rw [← hflow, hexp _ (hswsrc s hs)]⟩
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hTarc x hx
    exact harcS s hs
  have h0P : (0 : E) ∈ P := by
    refine ⟨Submodule.mem_toAffineSubspace.2 L.zero_mem, ?_⟩
    change g.inner y 0 0 < δ ^ 2
    simp only [map_zero]
    positivity
  have hyT : y ∈ T := ⟨0, h0P, he0⟩
  obtain ⟨U, hU, hyU, hUS⟩ := hT.exists_open_inter_subset hk0 hS hTS hyT
  exact ⟨U, hU, hyU, fun x hx => hTarc x (hUS hx)⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- **Matching of unit tangent states.** Two unit states over the same point of a one-dimensional
slice, both tangent to it, are equal or opposite. -/
theorem eq_or_eq_rev_of_mem_sliceTangent_dim_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {k : WithTop ℕ∞} (hk : k ≠ 0) {S : Set M} (hS : IsEmbeddedSliceOfOrder I k 1 S)
    {q₁ q₂ : TangentBundle I M} (hproj : q₁.proj = q₂.proj) (hq₂ : q₂.proj ∈ S)
    (h₁ : q₁.snd ∈ sliceTangent I S q₁.proj) (h₂ : q₂.snd ∈ sliceTangent I S q₂.proj)
    (hu₁ : g.inner q₁.proj q₁.snd q₁.snd = 1) (hu₂ : g.inner q₂.proj q₂.snd q₂.snd = 1) :
    q₁ = q₂ ∨ q₁ = ⟨q₂.proj, (-1 : ℝ) • q₂.snd⟩ := by
  obtain ⟨x₁, v₁⟩ := q₁
  obtain ⟨x₂, v₂⟩ := q₂
  change x₁ = x₂ at hproj
  subst hproj
  rcases eq_or_eq_neg_of_mem_sliceTangent_dim_one g hk hS hq₂ h₁ h₂ hu₁ hu₂ with h | h
  · left
    change v₁ = v₂ at h
    rw [h]
  · right
    change v₁ = (-1 : ℝ) • v₂ at h
    rw [h]

/-- **BASE-1a** (`2 ≤ r`). A compact connected one-dimensional totally geodesic `C^r` slice is a simple
closed geodesic. (Frozen statement minus the unused instance `[NeZero (Module.finrank ℝ E)]`.) -/
theorem exists_closedGeodesic_of_slice_dim_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hconn : IsConnected S)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 S) (htg : IsTotallyGeodesicFinite g S) :
    ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
      g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
      S = range (fun t => (g.geodesicFlow p t).proj) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk0 : (r : ℕ∞ω) ≠ 0 := by
    have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr1
    exact (zero_lt_one.trans_le h').ne'
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  have hadd : ∀ (Q : TangentBundle I M) (s t : ℝ),
      g.geodesicFlow (g.geodesicFlow Q s) t = g.geodesicFlow Q (s + t) := fun Q s t =>
    (g.geodesicFlow_add hr1 (hmem Q s) (hmem Q (s + t))).symm
  have hrev : ∀ (Q : TangentBundle I M) (τ : ℝ),
      g.geodesicFlow ⟨Q.proj, (-1 : ℝ) • Q.snd⟩ τ =
        ⟨(g.geodesicFlow Q (-τ)).proj, (-1 : ℝ) • (g.geodesicFlow Q (-τ)).snd⟩ := by
    intro Q τ
    have h := g.geodesicFlow_smul_eq hr1 Q (-1) τ (hmem Q _)
    rwa [neg_one_mul] at h
  have hSclosed : IsClosed S := hSc.isClosed
  -- local structure at every point of `S`
  choose! W hWT hW1 Δ hΔ harcS harcdist U hUo hyU hUS using
    fun y (hy : y ∈ S) => exists_local_geodesic_dim_one g hr hnorm hS htg hy
  have hσ0 : ∀ y : M, (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) 0).proj = y := fun y => by
    rw [g.geodesicFlow_zero hr1]
  have hσvel : ∀ y ∈ S, ∀ s ∈ Ioo (-Δ y) (Δ y),
      (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).snd ∈
        sliceTangent I S (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).proj := by
    intro y hy s hs
    apply snd_mem_sliceTangent_of_eventually g hr1 _ (fun τ => hmem _ τ)
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), s + τ ∈ Ioo (-Δ y) (Δ y) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
        (by simpa using isOpen_Ioo.mem_nhds hs)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with τ hτ
    rw [hadd]
    exact harcS y hy (s + τ) hτ
  -- matching a unit tangent state with the local arc
  have hmatch : ∀ y ∈ S, ∀ Q : TangentBundle I M, Q.proj ∈ U y → Q.proj ∈ S →
      Q.snd ∈ sliceTangent I S Q.proj → g.inner Q.proj Q.snd Q.snd = 1 →
      ∃ s ∈ Ioo (-Δ y) (Δ y), ∃ ε : ℝ, ε * ε = 1 ∧ ∀ τ : ℝ, (g.geodesicFlow Q τ).proj =
        (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) (s + ε * τ)).proj := by
    intro y hy Q hQU hQS hQT hQ1
    obtain ⟨s, hs, hσs⟩ := hUS y hy Q.proj ⟨hQU, hQS⟩
    refine ⟨s, hs, ?_⟩
    have hu₂ : g.inner (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).proj
        (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).snd
        (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).snd = 1 :=
      (g.inner_geodesicFlow_eq hr1 _ s (hmem _ s)).trans (hW1 y hy)
    rcases eq_or_eq_rev_of_mem_sliceTangent_dim_one g hk0 hS hσs.symm (harcS y hy s hs) hQT
        (hσvel y hy s hs) hQ1 hu₂ with h | h
    · refine ⟨1, one_mul 1, fun τ => ?_⟩
      rw [h, hadd, one_mul]
    · refine ⟨-1, by norm_num, fun τ => ?_⟩
      rw [h, hrev, hadd, neg_one_mul, ← sub_eq_add_neg]
  -- the geodesic
  obtain ⟨x, hx⟩ := hconn.nonempty
  set p : TangentBundle I M := ⟨x, W x⟩ with hpdef
  have hp1 : g.inner p.proj p.snd p.snd = 1 := hW1 x hx
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγdef
  have hunit : ∀ t, g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd
      (g.geodesicFlow p t).snd = 1 := fun t =>
    (g.inner_geodesicFlow_eq hr1 p t (hmem p t)).trans hp1
  have hlip : ∀ s t : ℝ, dist (γ s) (γ t) ≤ |t - s| := by
    intro s t
    have h := g.dist_proj_geodesicFlow_le hr1 hnorm (p := p) (s := s) (t := t)
      (fun τ _ => hmem p τ)
    rwa [hp1, Real.sqrt_one, one_mul] at h
  have hγc : Continuous γ := by
    refine Metric.continuous_iff.2 fun t ε hε => ⟨ε, hε, fun z hz => ?_⟩
    refine (hlip z t).trans_lt ?_
    rw [Real.dist_eq] at hz
    rwa [abs_sub_comm]
  have hshift : ∀ t a : ℝ, (g.geodesicFlow (g.geodesicFlow p t) a).proj = γ (t + a) := fun t a => by
    rw [hadd]
  /- Claim 1: the geodesic stays in `S` with tangent velocity -/
  set A : Set ℝ := {t | γ t ∈ S ∧ (g.geodesicFlow p t).snd ∈ sliceTangent I S (γ t)} with hAdef
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨δ', hδ', hδ'S⟩ := htg (γ t) ht.1 (g.geodesicFlow p t).snd ht.2
    have hS' : ∀ τ ∈ Ioo (-δ') δ', γ (t + τ) ∈ S := fun τ hτ => by
      rw [← hshift]; exact hδ'S τ hτ
    refine ⟨δ' / 2, half_pos hδ', fun t' ht' => ?_⟩
    rw [mem_ball, Real.dist_eq] at ht'
    have ht'S : γ t' ∈ S := by
      have h := hS' (t' - t) ⟨by linarith [(abs_lt.1 ht').1], by linarith [(abs_lt.1 ht').2]⟩
      rwa [add_sub_cancel] at h
    refine ⟨ht'S, ?_⟩
    apply snd_mem_sliceTangent_of_eventually g hr1 _ (fun τ => hmem _ τ)
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ')] with τ hτ
    rw [hshift]
    have h := hS' (t' - t + τ) ⟨by linarith [(abs_lt.1 ht').1, hτ.1],
      by linarith [(abs_lt.1 ht').2, hτ.2]⟩
    rwa [show t + (t' - t + τ) = t' + τ by ring] at h
  have hAclosed : IsClosed A := by
    apply isClosed_of_closure_subset
    intro t₁ ht₁
    have hy₁ : γ t₁ ∈ S :=
      closure_minimal (image_subset_iff.2 fun t ht => ht.1) hSclosed
        (mem_closure_image hγc.continuousAt ht₁)
    set y := γ t₁ with hydef
    have hN : γ ⁻¹' U y ∩ ball t₁ (Δ y / 2) ∈ 𝓝 t₁ :=
      inter_mem (hγc.continuousAt.preimage_mem_nhds ((hUo y hy₁).mem_nhds (hyU y hy₁)))
        (ball_mem_nhds t₁ (half_pos (hΔ y hy₁)))
    obtain ⟨t, ⟨htU, htball⟩, htA⟩ := mem_closure_iff_nhds.1 ht₁ _ hN
    rw [mem_ball, Real.dist_eq] at htball
    obtain ⟨s, hs, ε, hε, hγσ⟩ := hmatch y hy₁ (g.geodesicFlow p t) htU htA.1 htA.2 (hunit t)
    -- `|s| < Δ / 2`
    have hσs : (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).proj = γ t := by
      have h := hγσ 0
      rw [mul_zero, add_zero] at h
      rw [← h]
      change (g.geodesicFlow (g.geodesicFlow p t) 0).proj = γ t
      rw [g.geodesicFlow_zero hr1]
    have hsabs : |s| < Δ y / 2 := by
      rw [← harcdist y hy₁ s hs, hσs]
      calc dist y (γ t) ≤ |t - t₁| := hlip t₁ t
        _ < Δ y / 2 := htball
    have hε1 : |ε| = 1 := by
      have h := congrArg abs hε
      rw [abs_mul, abs_one] at h
      nlinarith [abs_nonneg ε]
    refine ⟨hy₁, ?_⟩
    apply snd_mem_sliceTangent_of_eventually g hr1 _ (fun τ => hmem _ τ)
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), s + ε * (t₁ - t + τ) ∈ Ioo (-Δ y) (Δ y) := by
      have hc : Continuous fun τ : ℝ => s + ε * (t₁ - t + τ) := by continuity
      apply hc.continuousAt.preimage_mem_nhds
      apply isOpen_Ioo.mem_nhds
      have h1 : |ε * (t₁ - t + 0)| < Δ y / 2 := by
        rw [abs_mul, hε1, one_mul, add_zero, abs_sub_comm]; exact htball
      constructor <;> linarith [abs_lt.1 hsabs, abs_lt.1 h1]
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with τ hτ
    rw [hshift, show t₁ + τ = t + (t₁ - t + τ) by ring, ← hshift, hγσ]
    exact harcS y hy₁ _ hτ
  have h0A : (0 : ℝ) ∈ A := by
    change (g.geodesicFlow p 0).proj ∈ S ∧
      (g.geodesicFlow p 0).snd ∈ sliceTangent I S (g.geodesicFlow p 0).proj
    rw [g.geodesicFlow_zero hr1]
    exact ⟨hx, hWT x hx⟩
  have hAuniv : A = univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ ⟨0, h0A⟩
  have hA : ∀ t, γ t ∈ S ∧ (g.geodesicFlow p t).snd ∈ sliceTangent I S (γ t) := fun t => by
    have h : t ∈ A := by rw [hAuniv]; exact mem_univ t
    exact h
  /- the local arcs are reparametrizations of `γ` -/
  have hreparam : ∀ t : ℝ, ∀ y ∈ S, γ t ∈ U y → ∃ s₀ ∈ Ioo (-Δ y) (Δ y), ∀ s ∈ Ioo (-Δ y) (Δ y),
      ∃ t', |t' - t| < 2 * Δ y ∧
        γ t' = (g.geodesicFlow (⟨y, W y⟩ : TangentBundle I M) s).proj := by
    intro t y hy htU
    obtain ⟨s₀, hs₀, ε, hε, hγσ⟩ := hmatch y hy (g.geodesicFlow p t) htU (hA t).1 (hA t).2 (hunit t)
    refine ⟨s₀, hs₀, fun s hs => ⟨t + ε * (s - s₀), ?_, ?_⟩⟩
    · have hε1 : |ε| = 1 := by
        have h := congrArg abs hε
        rw [abs_mul, abs_one] at h
        nlinarith [abs_nonneg ε]
      rw [add_sub_cancel_left, abs_mul, hε1, one_mul]
      have h1 := abs_lt.1 (show |s| < Δ y from abs_lt.2 hs)
      have h2 := abs_lt.1 (show |s₀| < Δ y from abs_lt.2 hs₀)
      rw [abs_lt]
      constructor <;> linarith
    · rw [← hshift, hγσ, ← mul_assoc, hε, one_mul, add_sub_cancel]
  /- Claim 2: `S` is the range of `γ` -/
  have hloc_range : ∀ t : ℝ, ∀ z ∈ U (γ t) ∩ S, ∃ t', |t' - t| < 2 * Δ (γ t) ∧ γ t' = z := by
    intro t z hz
    obtain ⟨-, -, hrep⟩ := hreparam t (γ t) (hA t).1 (hyU (γ t) (hA t).1)
    obtain ⟨s, hs, hσs⟩ := hUS (γ t) (hA t).1 z hz
    obtain ⟨t', ht', hγt'⟩ := hrep s hs
    exact ⟨t', ht', hγt'.trans hσs⟩
  have hrange : S = range γ := by
    apply Subset.antisymm _ (by rintro _ ⟨t, rfl⟩; exact (hA t).1)
    set u : Set M := ⋃ t : ℝ, U (γ t) with hudef
    set v : Set M := (closure (range γ))ᶜ with hvdef
    have hu : IsOpen u := isOpen_iUnion fun t => hUo (γ t) (hA t).1
    have hv : IsOpen v := isClosed_closure.isOpen_compl
    have hcover : S ⊆ u ∪ v := by
      intro y hy
      by_cases hyc : y ∈ closure (range γ)
      · obtain ⟨_, hzU, ⟨t, rfl⟩⟩ :=
          mem_closure_iff.1 hyc (U y) (hUo y hy) (hyU y hy)
        obtain ⟨s₀, -, hrep⟩ := hreparam t y hy hzU
        obtain ⟨t', -, hγt'⟩ := hrep 0 ⟨neg_lt_zero.2 (hΔ y hy), hΔ y hy⟩
        rw [hσ0] at hγt'
        left
        refine mem_iUnion.2 ⟨t', ?_⟩
        rw [hγt']
        exact hyU y hy
      · exact Or.inr hyc
    have hdisj : S ∩ (u ∩ v) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hy hyu hyv
      obtain ⟨t, hyt⟩ := mem_iUnion.1 hyu
      obtain ⟨t', -, hγt'⟩ := hloc_range t y ⟨hyt, hy⟩
      exact hyv (subset_closure ⟨t', hγt'⟩)
    rcases (isPreconnected_iff_subset_of_disjoint.1 hconn.isPreconnected) u v hu hv hcover hdisj
      with hsub | hsub
    · intro y hy
      obtain ⟨t, hyt⟩ := mem_iUnion.1 (hsub hy)
      obtain ⟨t', -, hγt'⟩ := hloc_range t y ⟨hyt, hy⟩
      exact ⟨t', hγt'⟩
    · exfalso
      have hx0 : γ 0 = x := by
        change (g.geodesicFlow p 0).proj = x
        rw [g.geodesicFlow_zero hr1]
      exact hsub hx (subset_closure ⟨0, hx0⟩)
  /- re-encounters are phase-space periods -/
  have hRE : ∀ t₁ t₂ : ℝ, γ t₁ = γ t₂ → g.geodesicFlow p t₁ = g.geodesicFlow p t₂ := by
    intro t₁ t₂ heq
    rcases eq_or_eq_rev_of_mem_sliceTangent_dim_one g hk0 hS (q₁ := g.geodesicFlow p t₁)
        (q₂ := g.geodesicFlow p t₂) heq (hA t₂).1 (hA t₁).2 (hA t₂).2 (hunit t₁) (hunit t₂)
      with h | h
    · exact h
    · exact absurd h (geodesicFlow_ne_neg_of_unit g hr hnorm hp1 t₂ t₁)
  /- Claim 3: a period, by compactness -/
  obtain ⟨F, hF⟩ := hSc.elim_finite_subcover (fun t : ℝ => U (γ t))
    (fun t => hUo (γ t) (hA t).1) (fun y hy => by
      rw [hrange] at hy
      obtain ⟨t, rfl⟩ := hy
      exact mem_iUnion.2 ⟨t, hyU (γ t) (hA t).1⟩)
  set N : ℝ := ∑ t ∈ F, (|t| + 2 * Δ (γ t)) + 1 with hNdef
  have hterm : ∀ t ∈ F, |t| + 2 * Δ (γ t) ≤ N - 1 := by
    intro t ht
    rw [hNdef, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun t => |t| + 2 * Δ (γ t))
      (fun i _ => add_nonneg (abs_nonneg i) (mul_nonneg zero_le_two (hΔ _ (hA i).1).le)) ht
  obtain ⟨t₀, ht₀F, hNU⟩ := mem_iUnion₂.1 (hF (hA N).1)
  obtain ⟨t', ht', hγt'⟩ := hloc_range t₀ (γ N) ⟨hNU, (hA N).1⟩
  have ht'N : t' < N := by
    have h1 := hterm t₀ ht₀F
    have h2 := abs_lt.1 ht'
    have h3 := le_abs_self t₀
    linarith
  set T₀ : ℝ := N - t' with hT₀def
  have hT₀ : 0 < T₀ := sub_pos.2 ht'N
  have hγT₀ : γ T₀ = γ 0 := by
    have hP := hRE t' N hγt'
    change (g.geodesicFlow p (N - t')).proj = (g.geodesicFlow p 0).proj
    have h1 : g.geodesicFlow p (N - t') = g.geodesicFlow (g.geodesicFlow p N) (-t') := by
      rw [hadd, sub_eq_add_neg]
    rw [h1, ← hP, hadd, add_neg_cancel]
  /- Claim 4: the least period -/
  obtain ⟨ρ₀, hρ₀, hinj⟩ := exists_pos_injOn_proj_geodesicFlow g hr hnorm hp1 0
  have hlow : ∀ τ : ℝ, 0 < τ → τ < ρ₀ → γ τ ≠ γ 0 := by
    intro τ hτ0 hτρ heq
    have h := hinj ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ heq
    linarith
  set Tset : Set ℝ := {τ | ρ₀ ≤ τ ∧ γ τ = γ 0} with hTsetdef
  have hTcl : IsClosed Tset :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_eq hγc continuous_const)
  have hT₀ρ : ρ₀ ≤ T₀ := by
    by_contra hlt
    push Not at hlt
    exact hlow T₀ hT₀ hlt hγT₀
  have hTne : Tset.Nonempty := ⟨T₀, hT₀ρ, hγT₀⟩
  have hTbdd : BddBelow Tset := ⟨ρ₀, fun τ hτ => hτ.1⟩
  set ℓ : ℝ := sInf Tset with hℓdef
  have hℓT : ℓ ∈ Tset := hTcl.csInf_mem hTne hTbdd
  have hℓpos : 0 < ℓ := hρ₀.trans_le hℓT.1
  have hΦℓ : g.geodesicFlow p ℓ = p := by
    rw [hRE ℓ 0 hℓT.2, g.geodesicFlow_zero hr1]
  refine ⟨p, ℓ, hℓpos, hp1, hΦℓ, ?_, hrange⟩
  have hno : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ < ℓ → γ t₁ = γ t₂ → False := by
    intro t₁ t₂ h0 h12 h2ℓ heq
    have hP := hRE t₁ t₂ heq
    have hT'0 : 0 < t₂ - t₁ := sub_pos.2 h12
    have hγT' : γ (t₂ - t₁) = γ 0 := by
      change (g.geodesicFlow p (t₂ - t₁)).proj = (g.geodesicFlow p 0).proj
      have h1 : g.geodesicFlow p (t₂ - t₁) = g.geodesicFlow (g.geodesicFlow p t₂) (-t₁) := by
        rw [hadd, sub_eq_add_neg]
      rw [h1, ← hP, hadd, add_neg_cancel]
    rcases lt_or_ge (t₂ - t₁) ρ₀ with hρ' | hρ'
    · exact hlow _ hT'0 hρ' hγT'
    · have h3 := csInf_le hTbdd (show t₂ - t₁ ∈ Tset from ⟨hρ', hγT'⟩)
      rw [← hℓdef] at h3
      linarith
  intro t₁ ht₁ t₂ ht₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hno t₁ t₂ ht₁.1 h ht₂.2 heq
  · exact hno t₂ t₁ ht₂.1 h ht₁.2 heq.symm

end DifferentialGeometry.Geometry.FiniteSoul
