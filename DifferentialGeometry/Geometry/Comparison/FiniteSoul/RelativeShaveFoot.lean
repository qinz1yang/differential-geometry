import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveBall
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteNormalChart
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderImage

/-!
# REL kernel, step (ii): the relative foot point (CMS3-REL, G1)

Lane CMS3-REL, sub-lemma SL2 of `build-logs/resume/sheet-CMS3-REL.md` (review item 7: the relative foot
point needs a finite-order first-variation / local propagation statement). Setting: a complete metric
`g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`, `sec ≥ 0` for the hinge), a closed totally convex `C`, its
relative interior `Z` and relative boundary `B = C \ Z`. A vector `v` at `p` is called inner (written
inline everywhere, never as a definition) when `exp_p (s v) ∈ Z` for all small `s > 0`.

* `mem_maxSliceLocusOfOrder_of_inner_neg` (LOCAL PROPAGATION): if `v` and `-v` are inner at `p ∈ C`, the
  geodesic arc through `p` has both ends in `Z`, so `p ∈ Z` (total convexity + SLICE (7)).
* `symm_mem_sliceTangent_of_mem`, `mfderiv_symm_mem_sliceTangent_of_inner`: for `q ∈ Z` and a normal chart
  `e_q` (`e_q = exp_q` on its source), `e_q⁻¹ (Z ∩ target) ⊆ T_q Z` (radial segments from `q` into `Z` lie
  in `Z`), hence `d(e_q⁻¹)_p` maps every inner vector at `p ∈ target` into `T_q Z`.
* `exists_inner_sub_smul` (OPENNESS): inner `a`, `b` at `p` give an inner `a - ε b`: in a normal chart at
  `p` the relative interior is a `d`-slice inside the `d`-dimensional `d(e_q⁻¹)_p⁻¹ (T_q Z)`.
* `inner_of_acute` (FIRST VARIATION): with `q = exp_p (r₀ w)`, `d(q, B) = d(q, p) = r₀`, every `z` with
  `d(e_q⁻¹)_p z ∈ T_q Z` and `g_p(w, z) > 0` is inner: the curve `e_q (e_q⁻¹ p + s d(e_q⁻¹)_p z)` enters the
  relative ball of `q` (finite first variation), the directions from `p` to it are inner and tend to `z`,
  the hinge keeps the corresponding geodesics in `ball q r₀` (so away from `B`) on a uniform interval,
  no escape keeps them in `Z`, and `C` is closed.
* `eventually_expMap_notMem_maxSliceLocusOfOrder_of_foot` (RELATIVE FOOT POINT): at the foot `P` of a
  segment realising `d(y, B) > 0`, no `ξ` with `g(ξ, P.snd) ≥ 0` is inner.
* `expMap_notMem_maxSliceLocusOfOrder_of_foot`: the same for every `ξ` of length `< ρ` (uniform on a
  compact set of feet), by SLICE's relative radial cone.
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
theorem coe_ne_zero_of_two_le_CMS3REL (hr : 2 ≤ r) : (r : ℕ∞ω) ≠ 0 := by
  have h : (1 : ℕ∞) ≤ r := one_le_two.trans hr
  have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast h
  exact (zero_lt_one.trans_le h').ne'

/-- The radial curve `s ↦ exp_p (s v)` has velocity `v` at `0`. -/
theorem hasMFDerivAt_expMap_smul_zero
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : E) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => g.expMap (⟨p, s • v⟩ : TangentBundle I M)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have h := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := (⟨p, v⟩ : TangentBundle I M)) (t := 0)
    (by rw [hD]; exact mem_univ _)
  have hX0 : (g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) 0).snd = v := by
    rw [g.geodesicFlow_zero hr1]
  rw [hX0] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  exact g.expMap_smul_eq_proj_geodesicFlow hr1 p v s (by rw [hD]; exact mem_univ _)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
/-- Chain rule for a curve followed by a map into the model space, read as an ordinary derivative. -/
theorem hasDerivAt_comp_of_hasMFDerivAt_CMS3REL {f : M → E} {γ : ℝ → M} {X : E}
    (hf : MDifferentiableAt I 𝓘(ℝ, E) f (γ 0))
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) :
    HasDerivAt (fun t => f (γ t)) (mfderiv I 𝓘(ℝ, E) f (γ 0) X) 0 := by
  have h3 : HasFDerivAt (fun t => f (γ t))
      (show ℝ →L[ℝ] E from (mfderiv I 𝓘(ℝ, E) f (γ 0)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight X)) 0 :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hf.hasMFDerivAt.comp 0 hγ)
  refine h3.hasDerivAt.congr_deriv ?_
  change (mfderiv I 𝓘(ℝ, E) f (γ 0)) (((1 : ℝ →L[ℝ] ℝ).smulRight X) 1) =
    (mfderiv I 𝓘(ℝ, E) f (γ 0)) X
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
/-- `dc⁻¹ ∘ dc = id` at a point of the source of a partial diffeomorphism `E → M` of order `k ≠ 0`. -/
theorem mfderiv_symm_apply_mfderiv_of_source_CMS3REL {k : WithTop ℕ∞} (hk : k ≠ 0)
    {c : PartialDiffeomorph 𝓘(ℝ, E) I E M k} {X : E} (hX : X ∈ c.source) (w : E) :
    mfderiv I 𝓘(ℝ, E) c.symm (c X) (mfderiv 𝓘(ℝ, E) I c X w) = w := by
  have hcdiff : MDifferentiableAt 𝓘(ℝ, E) I c X := c.mdifferentiableAt hk hX
  have hcx : c X ∈ c.target := c.toPartialEquiv.map_source hX
  have hsymm : MDifferentiableAt I 𝓘(ℝ, E) c.symm (c X) := c.symm.mdifferentiableAt hk hcx
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => c.symm (c y)) X =
      (mfderiv I 𝓘(ℝ, E) c.symm (c X)).comp (mfderiv 𝓘(ℝ, E) I c X) :=
    mfderiv_comp X hsymm hcdiff
  have heq : (fun y : E => c.symm (c y)) =ᶠ[𝓝 X] id := by
    filter_upwards [c.open_source.mem_nhds hX] with y hy
    exact c.toPartialEquiv.left_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact congrArg (fun L : TangentSpace 𝓘(ℝ, E) X →L[ℝ] TangentSpace 𝓘(ℝ, E) X => L w) hcomp.symm

/-- One time in `Z` on a radial arc from `p ∈ C` gives all smaller positive times. -/
theorem expMap_smul_mem_maxSliceLocusOfOrder_of_mem
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {p : M} (hp : p ∈ C) {v : E} {s₀ : ℝ}
    (hs₀ : 0 < s₀)
    (h : g.expMap (⟨p, s₀ • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∀ s ∈ Ioc 0 s₀, g.expMap (⟨p, s • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hflow : ∀ τ : ℝ, g.expMap (⟨p, τ • v⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 p v τ (by rw [hD]; exact mem_univ _)
  intro s hs
  rw [hflow] at h ⊢
  exact hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_end hr hnorm _ hs₀ hp h s hs

/-- Frequently inner implies inner (`p ∈ C`). -/
theorem eventually_expMap_smul_mem_of_frequently
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {p : M} (hp : p ∈ C) {v : E}
    (h : ∃ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  obtain ⟨s₀, hs₀, hs₀pos⟩ := (h.and_eventually self_mem_nhdsWithin).exists
  have hs₀pos' : (0 : ℝ) < s₀ := hs₀pos
  filter_upwards [Ioo_mem_nhdsGT hs₀pos'] with s hs
  exact expMap_smul_mem_maxSliceLocusOfOrder_of_mem g hr hnorm hconv hp hs₀pos' hs₀ s
    ⟨hs.1, hs.2.le⟩

/-- **Local propagation.** If `v` and `-v` are both inner at `p ∈ C`, then `p ∈ Z`. -/
theorem mem_maxSliceLocusOfOrder_of_inner_neg
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {p : M} {v : E}
    (h₁ : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C)
    (h₂ : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • ((-1 : ℝ) • v)⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    p ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set P0 : TangentBundle I M := ⟨p, v⟩ with hP0
  obtain ⟨a, ha, hapos⟩ := (h₁.and self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hbpos⟩ := (h₂.and self_mem_nhdsWithin).exists
  have hapos' : (0 : ℝ) < a := hapos
  have hbpos' : (0 : ℝ) < b := hbpos
  have hA : (g.geodesicFlow P0 a).proj ∈ Z := by
    rw [← g.expMap_smul_eq_proj_geodesicFlow hr1 p v a (by rw [hD]; exact mem_univ _)]
    exact ha
  have hB : (g.geodesicFlow P0 (-b)).proj ∈ Z := by
    have h1 := g.expMap_smul_eq_proj_geodesicFlow hr1 p ((-1 : ℝ) • v) b
      (by rw [hD]; exact mem_univ _)
    have h2 := proj_geodesicFlow_neg_snd g hr hnorm P0 b
    rw [← h2]
    change (g.geodesicFlow (⟨p, (-1 : ℝ) • v⟩ : TangentBundle I M) b).proj ∈ Z
    rw [← h1]
    exact hb
  set Q := g.geodesicFlow P0 (-b) with hQ
  have hQt : ∀ τ : ℝ, (g.geodesicFlow Q τ).proj = (g.geodesicFlow P0 (-b + τ)).proj := fun τ => by
    rw [hQ, ← geodesicFlow_add_of_complete g hr hnorm]
  have hQ0 : (g.geodesicFlow Q 0).proj ∈ Z := by rw [hQt, add_zero]; exact hB
  have hQend : (g.geodesicFlow Q (a + b)).proj ∈ C := by
    rw [hQt, show -b + (a + b) = a by ring]
    exact maxSliceLocusOfOrder_subset hA
  have hmaps : ∀ t ∈ Icc 0 (a + b), (g.geodesicFlow Q t).proj ∈ C :=
    hconv Q (a + b) (by linarith)
      (by have h0 := maxSliceLocusOfOrder_subset hQ0; rwa [g.geodesicFlow_zero hr1] at h0) hQend
  have h := hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm Q hmaps
    ⟨le_rfl, by linarith⟩ hQ0 b ⟨hbpos', by linarith⟩
  rw [hQt, show -b + b = 0 by ring, g.geodesicFlow_zero hr1] at h
  exact h

/-- **Radial segments from a point of `Z` into `Z`.** For `q ∈ Z` and a chart `e` equal to `exp_q` on
its source, `e⁻¹ a ∈ T_q Z` for every `a ∈ Z ∩ e.target`. -/
theorem symm_mem_sliceTangent_of_mem
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {q : M}
    (hq : q ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {e : PartialDiffeomorph 𝓘(ℝ, E) I E M (r : ℕ∞ω)}
    (hexp : ∀ v ∈ e.source, e v = g.expMap (⟨q, v⟩ : TangentBundle I M)) {a : M}
    (haZ : a ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) (haT : a ∈ e.target) :
    e.symm a ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) q := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set u : E := e.symm a with hu
  have husrc : u ∈ e.source := e.toPartialEquiv.map_target haT
  have heu : e u = a := e.toPartialEquiv.right_inv haT
  have hend : (g.geodesicFlow (⟨q, u⟩ : TangentBundle I M) 1).proj ∈
      maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
    have h2 : (g.geodesicFlow (⟨q, u⟩ : TangentBundle I M) 1).proj =
        g.expMap (⟨q, u⟩ : TangentBundle I M) := by
      rw [← g.expMap_smul_eq_proj_geodesicFlow hr1 q u 1 (by rw [hD]; exact mem_univ _)]
      exact congrArg (fun w : E => g.expMap (⟨q, w⟩ : TangentBundle I M)) (one_smul ℝ u)
    rw [h2, ← hexp u husrc, heu]
    exact haZ
  have hseg := hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_end hr hnorm
    (⟨q, u⟩ : TangentBundle I M) one_pos (maxSliceLocusOfOrder_subset hq) hend
  have h := snd_mem_sliceTangent_of_eventually g hr1 (⟨q, u⟩ : TangentBundle I M)
    (fun s => by rw [hD]; exact mem_univ _)
    (by filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs using hseg s ⟨hs.1, hs.2.le⟩)
  exact h

/-- **Inner vectors at `p` map into `T_q Z`.** For `q ∈ Z`, a chart `e` equal to `exp_q` on its source
and `p ∈ e.target`, an inner vector `v` at `p` satisfies `e⁻¹ p ∈ T_q Z` and `d(e⁻¹)_p v ∈ T_q Z`. -/
theorem mfderiv_symm_mem_sliceTangent_of_inner
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {q : M}
    (hq : q ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {e : PartialDiffeomorph 𝓘(ℝ, E) I E M (r : ℕ∞ω)}
    (hexp : ∀ v ∈ e.source, e v = g.expMap (⟨q, v⟩ : TangentBundle I M)) {p : M} (hpT : p ∈ e.target)
    {v : E} (hv : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    e.symm p ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) q ∧
      (mfderiv I 𝓘(ℝ, E) e.symm p v : E) ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) q := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk : (r : ℕ∞ω) ≠ 0 := coe_ne_zero_of_two_le_CMS3REL hr
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  have hZ : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) Z :=
    isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr hnorm hconv
  set K : Submodule ℝ E := sliceTangent I Z q with hKdef
  have hKcl : IsClosed (K : Set E) := by
    have : FiniteDimensional ℝ K := finiteDimensional_sliceTangent_ofOrder hk hZ hq
    exact K.closed_of_finiteDimensional
  set γv : ℝ → M := fun s => g.expMap (⟨p, s • v⟩ : TangentBundle I M) with hγvdef
  have hγ0 : γv 0 = p := by
    simp only [hγvdef, zero_smul]
    exact g.expMap_zero hr1 p
  have hγd := hasMFDerivAt_expMap_smul_zero g hr hnorm p v
  have hderiv : HasDerivAt (fun s => e.symm (γv s)) (mfderiv I 𝓘(ℝ, E) e.symm p v) 0 := by
    have h := hasDerivAt_comp_of_hasMFDerivAt_CMS3REL (f := e.symm) (γ := γv)
      (by rw [hγ0]; exact e.symm.mdifferentiableAt hk hpT) hγd
    rw [hγ0] at h
    exact h
  have hcont : ContinuousAt (fun s => e.symm (γv s)) 0 := hderiv.continuousAt
  have hγc : ContinuousAt γv 0 := hγd.continuousAt
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), e.symm (γv s) ∈ K := by
    have hT : ∀ᶠ s in 𝓝 (0 : ℝ), γv s ∈ e.target :=
      hγc.preimage_mem_nhds (by rw [hγ0]; exact e.open_target.mem_nhds hpT)
    filter_upwards [hv, hT.filter_mono nhdsWithin_le_nhds] with s hs hsT
    exact symm_mem_sliceTangent_of_mem g hr hnorm hconv hq hexp hs hsT
  have h0 : e.symm p ∈ K := by
    have h := hKcl.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
    rw [hγ0] at h
    exact h
  refine ⟨h0, ?_⟩
  refine mem_of_hasDerivAt_of_eventually_sub_mem hKcl hderiv ?_
  filter_upwards [hev] with s hs
  have h0' : e.symm (γv 0) ∈ K := by rw [hγ0]; exact h0
  exact K.sub_mem hs h0'

/-- **Openness of inner vectors.** If `a` and `b` are inner at `p ∈ C`, so is `a - ε b` for some
`ε > 0` (normal chart at `p`: the relative interior is a `d`-slice of `E` inside the `d`-dimensional
`d(e_q⁻¹)_p⁻¹ (T_q Z)`, hence relatively open in it). -/
theorem exists_inner_sub_smul
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {q : M}
    (hq : q ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {e : PartialDiffeomorph 𝓘(ℝ, E) I E M (r : ℕ∞ω)}
    (hexp : ∀ v ∈ e.source, e v = g.expMap (⟨q, v⟩ : TangentBundle I M)) {p : M} (hpT : p ∈ e.target)
    (hpC : p ∈ C) {a b : E}
    (ha : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • a⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C)
    (hb : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • b⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • (a - ε • b)⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hk : (r : ℕ∞ω) ≠ 0 := coe_ne_zero_of_two_le_CMS3REL hr
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set d := maxSliceDimOfOrder I (r : ℕ∞ω) C with hddef
  have hZ : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d Z :=
    isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr hnorm hconv
  obtain ⟨ρp, hρp, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm
    (isCompact_singleton (x := p))
  obtain ⟨ep, hsrc, htgt, hexpp, -, hbal, h0p, he0, -⟩ := hch p rfl
  -- the subspace `L`
  set K : Submodule ℝ E := sliceTangent I Z q with hKdef
  set Aₗ : E →ₗ[ℝ] E := (mfderiv I 𝓘(ℝ, E) e.symm p).toLinearMap with hAdef
  set Bₗ : E →ₗ[ℝ] E := (mfderiv 𝓘(ℝ, E) I e (e.symm p)).toLinearMap with hBdef
  have hpsrc : e.symm p ∈ e.source := e.toPartialEquiv.map_target hpT
  have hBA : ∀ u : E, Bₗ (Aₗ u) = u := fun u =>
    mfderiv_symm_apply_mfderiv_ofOrder hk (c := e.symm) hpT u
  have hAB : ∀ w : E, Aₗ (Bₗ w) = w := by
    intro w
    have h := mfderiv_symm_apply_mfderiv_of_source_CMS3REL hk hpsrc w
    have hep : e (e.symm p) = p := e.toPartialEquiv.right_inv hpT
    rw [hep] at h
    exact h
  set Aeq : E ≃ₗ[ℝ] E := LinearEquiv.ofLinearMap Aₗ Bₗ (LinearMap.ext hAB) (LinearMap.ext hBA)
    with hAeqdef
  set L : Submodule ℝ E := Submodule.comap Aeq.toLinearMap K with hLdef
  have hmemL : ∀ u : E, u ∈ L ↔ (mfderiv I 𝓘(ℝ, E) e.symm p u : E) ∈ K := fun u => Iff.rfl
  have hLdim : Module.finrank ℝ L = d := by
    rw [hLdef, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact finrank_sliceTangent_ofOrder hk hZ hq
  have hinnerL : ∀ u : E, (∀ᶠ s in 𝓝[>] (0 : ℝ), g.expMap (⟨p, s • u⟩ : TangentBundle I M) ∈ Z) →
      u ∈ L := fun u hu =>
    (hmemL u).2 (mfderiv_symm_mem_sliceTangent_of_inner g hr hnorm hconv hq hexp hpT hu).2
  -- the slice `V` of `E`
  set V : Set E := ep.symm '' (Z ∩ ep.target) with hVdef
  have hV : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (r : ℕ∞ω) d V :=
    (hZ.inter_open ep.open_target).image ep.symm fun y hy => hy.2
  have hVsrc : ∀ u ∈ V, u ∈ ep.source ∧ ep u ∈ Z := by
    rintro _ ⟨y, hy, rfl⟩
    have h3 : ep (ep.symm y) = y := ep.toPartialEquiv.right_inv hy.2
    refine ⟨ep.toPartialEquiv.map_target hy.2, ?_⟩
    show ep (ep.symm y) ∈ Z
    rw [h3]; exact hy.1
  have hinner_of_mem : ∀ u ∈ ep.source, ep u ∈ Z → ∀ t ∈ Ioc (0 : ℝ) 1,
      g.expMap (⟨p, t • u⟩ : TangentBundle I M) ∈ Z := by
    intro u hu hZu
    have h1 : g.expMap (⟨p, (1 : ℝ) • u⟩ : TangentBundle I M) ∈ Z := by
      have h2 : g.expMap (⟨p, (1 : ℝ) • u⟩ : TangentBundle I M) = ep u := by
        rw [hexpp u hu]
        exact congrArg (fun w : E => g.expMap (⟨p, w⟩ : TangentBundle I M)) (one_smul ℝ u)
      rw [h2]; exact hZu
    exact expMap_smul_mem_maxSliceLocusOfOrder_of_mem g hr hnorm hconv hpC one_pos h1
  have hVL : V ⊆ (L.toAffineSubspace : Set E) := by
    intro u hu
    obtain ⟨husrc, hZu⟩ := hVsrc u hu
    refine hinnerL u ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    exact hinner_of_mem u husrc hZu t ⟨ht.1, ht.2.le⟩
  have hdimA : Module.finrank ℝ L.toAffineSubspace.direction = d := by
    rw [Submodule.toAffineSubspace_direction]; exact hLdim
  have haL : a ∈ L := hinnerL a ha
  have hbL : b ∈ L := hinnerL b hb
  -- a point `t • a ∈ V`
  have hsrcev : ∀ᶠ s in 𝓝 (0 : ℝ), s • a ∈ ep.source := by
    have hc : ContinuousAt (fun s : ℝ => s • a) 0 := (continuous_id.smul continuous_const).continuousAt
    exact hc.preimage_mem_nhds (by simpa using ep.open_source.mem_nhds h0p)
  have htgtev : ∀ᶠ s in 𝓝 (0 : ℝ), g.expMap (⟨p, s • a⟩ : TangentBundle I M) ∈ ep.target := by
    have hc : ContinuousAt (fun s : ℝ => g.expMap (⟨p, s • a⟩ : TangentBundle I M)) 0 :=
      (hasMFDerivAt_expMap_smul_zero g hr hnorm p a).continuousAt
    refine hc.preimage_mem_nhds ?_
    have h00 : g.expMap (⟨p, (0 : ℝ) • a⟩ : TangentBundle I M) = p := by
      rw [zero_smul]; exact g.expMap_zero (one_le_two.trans hr) p
    rw [h00]
    exact ep.open_target.mem_nhds (by rw [htgt]; exact mem_ball_self hρp)
  obtain ⟨t, ⟨htZ, htsrc, httgt⟩, htpos⟩ := ((ha.and ((hsrcev.and htgtev).filter_mono
    nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  have htpos' : (0 : ℝ) < t := htpos
  have hepta : ep (t • a) = g.expMap (⟨p, t • a⟩ : TangentBundle I M) := hexpp _ htsrc
  have htaV : t • a ∈ V := ⟨ep (t • a), ⟨by rw [hepta]; exact htZ, by rw [hepta]; exact httgt⟩,
    ep.toPartialEquiv.left_inv htsrc⟩
  obtain ⟨ε₀, hε₀, hball⟩ := hV.exists_ball_affine_subset hk hVL hdimA htaV
  set ε : ℝ := ε₀ / (2 * t * (‖b‖ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, ?_⟩
  have hxL : t • (a - ε • b) ∈ L := L.smul_mem t (L.sub_mem haL (L.smul_mem ε hbL))
  have hxd : dist (t • (a - ε • b)) (t • a) < ε₀ := by
    rw [dist_eq_norm, smul_sub, sub_sub_cancel_left, norm_neg, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos', abs_of_pos hε]
    have h1 : t * (ε * ‖b‖) ≤ t * ε * (‖b‖ + 1) := by nlinarith [norm_nonneg b]
    have h2 : t * ε * (‖b‖ + 1) = ε₀ / 2 := by
      rw [hεdef]; field_simp
    linarith
  have hxV : t • (a - ε • b) ∈ V := hball _ (Submodule.mem_toAffineSubspace.2 hxL) hxd
  obtain ⟨hxsrc, hxZ⟩ := hVsrc _ hxV
  have hx : g.expMap (⟨p, t • (a - ε • b)⟩ : TangentBundle I M) ∈ Z := by
    rw [← hexpp _ hxsrc]; exact hxZ
  filter_upwards [Ioo_mem_nhdsGT htpos'] with s hs
  exact expMap_smul_mem_maxSliceLocusOfOrder_of_mem g hr hnorm hconv hpC htpos' hx s
    ⟨hs.1, hs.2.le⟩

/-- **Continuation of an inner geodesic** while it avoids the relative boundary (no escape, SL1). -/
theorem expMap_smul_mem_maxSliceLocusOfOrder_of_notMem
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {p : M} {e : E} {n T : ℝ}
    (hn : 0 < n)
    (hin : ∀ τ ∈ Ioc 0 n, g.expMap (⟨p, τ • e⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C)
    (hav : ∀ τ ∈ Ioo 0 T, g.expMap (⟨p, τ • e⟩ : TangentBundle I M) ∉ relBoundaryOfOrder I (r : ℕ∞ω) C) :
    ∀ τ ∈ Ioo 0 T, g.expMap (⟨p, τ • e⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hflow : ∀ τ : ℝ, g.expMap (⟨p, τ • e⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨p, e⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 p e τ (by rw [hD]; exact mem_univ _)
  intro τ hτ
  rcases le_or_gt τ n with hτn | hτn
  · exact hin τ ⟨hτ.1, hτn⟩
  · set τ₁ : ℝ := n / 2 with hτ₁def
    have hτ₁ : 0 < τ₁ := by positivity
    set P₁ := g.geodesicFlow (⟨p, e⟩ : TangentBundle I M) τ₁ with hP₁
    have hP₁Z : P₁.proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
      rw [hP₁, ← hflow]; exact hin τ₁ ⟨hτ₁, by linarith⟩
    have hv : P₁.snd ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) P₁.proj :=
      snd_mem_sliceTangent_of_left g hr hnorm _ hτ₁ fun σ hσ => by
        rw [← hflow]; exact hin σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have h := proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_forall_notMem g hr hnorm hCcl hconv P₁
      hP₁Z hv (T := τ - τ₁) (fun t ht => by
        rw [hP₁, ← geodesicFlow_add_of_complete g hr hnorm, ← hflow]
        exact hav _ ⟨by linarith [ht.1], by linarith [ht.2, hτ.2]⟩) (τ - τ₁) ⟨by linarith, le_rfl⟩
    rw [hP₁, ← geodesicFlow_add_of_complete g hr hnorm, show τ₁ + (τ - τ₁) = τ by ring,
      ← hflow] at h
    exact h

/-- **Hinge at `p`**: if `exp_p (r₀ w)` realises the distance `r₀` and `e` is a unit vector with
`g_p(w, e) ≥ c₀`, then `exp_p (τ e)` is strictly closer than `r₀` to `exp_p (r₀ w)` for
`0 < τ < min ρ₁ (2 r₀ c₀)`. -/
theorem dist_expMap_lt_of_hinge_CMS3REL [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {p : M} {w : E} (hw : g.inner p w w = 1) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hmin : dist p (g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M)) = r₀) {ρ₁ : ℝ}
    (hrad : ∀ e : E, g.inner p e e = 1 → ∀ s ∈ Ico 0 ρ₁,
      dist p (g.expMap (⟨p, s • e⟩ : TangentBundle I M)) = s)
    {c₀ : ℝ} {e : E} (he : g.inner p e e = 1) (hwe : c₀ ≤ g.inner p w e) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < ρ₁) (hτ2 : τ < 2 * r₀ * c₀) :
    dist (g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M)) (g.expMap (⟨p, τ • e⟩ : TangentBundle I M)) <
      r₀ := by
  have hh := dist_sq_le_hinge_finite g hr hnorm hsec p hr₀ hτ0 hw he hmin (hrad e he τ ⟨hτ0.le, hτ1⟩)
  have h1 : 2 * r₀ * τ * c₀ ≤ 2 * r₀ * τ * g.inner p w e :=
    mul_le_mul_of_nonneg_left hwe (by positivity)
  have h2 : τ ^ 2 < 2 * r₀ * τ * c₀ := by nlinarith
  by_contra hge
  push Not at hge
  have h3 : r₀ ^ 2 ≤ dist (g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M))
      (g.expMap (⟨p, τ • e⟩ : TangentBundle I M)) ^ 2 := pow_le_pow_left₀ hr₀.le hge 2
  nlinarith

/-- **Acute vectors are inner** (finite first variation + relative ball + hinge + closedness). Let
`q = exp_p (r₀ w) ∈ Z` with `d(p, q) = d(q, B) = r₀`, `w` inner at `p ∈ C`, and `e` a normal chart at `q`
with `p ∈ e.target`. Then every `z` with `d(e⁻¹)_p z ∈ T_q Z` and `g_p(w, z) > 0` is inner at `p`. -/
theorem inner_of_acute [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {q : M}
    (hq : q ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {e : PartialDiffeomorph 𝓘(ℝ, E) I E M (r : ℕ∞ω)}
    (hexp : ∀ v ∈ e.source, e v = g.expMap (⟨q, v⟩ : TangentBundle I M))
    (hdist : ∀ v ∈ e.source, dist q (e v) = Real.sqrt (g.inner q v v)) {p : M} (hpT : p ∈ e.target)
    (hpC : p ∈ C) {w : E} (hw : g.inner p w w = 1) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hqw : g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M) = q) (hpq : dist p q = r₀)
    (hqB : infDist q (relBoundaryOfOrder I (r : ℕ∞ω) C) = r₀)
    (hwin : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • w⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C)
    {z : E} (hzK : (mfderiv I 𝓘(ℝ, E) e.symm p z : E) ∈
      sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) q)
    (hzw : 0 < g.inner p w z) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨p, s • z⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk : (r : ℕ∞ω) ≠ 0 := coe_ne_zero_of_two_le_CMS3REL hr
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  have hclZ : closure Z ⊆ C := closure_minimal maxSliceLocusOfOrder_subset hCcl
  have hnotB : ∀ x : M, dist q x < r₀ → x ∉ B := fun x hx hxB => by
    have h := infDist_le_dist_of_mem (x := q) hxB
    linarith
  -- the curve `cur` through `p` with velocity `z`, inside the relative ball of `q`
  set X : E := e.symm p with hXdef
  have hXsrc : X ∈ e.source := e.toPartialEquiv.map_target hpT
  have heX : e X = p := e.toPartialEquiv.right_inv hpT
  have hXK : X ∈ sliceTangent I Z q :=
    (mfderiv_symm_mem_sliceTangent_of_inner g hr hnorm hconv hq hexp hpT hwin).1
  set W : E := mfderiv I 𝓘(ℝ, E) e.symm p z with hWdef
  have hBW : (mfderiv 𝓘(ℝ, E) I e X W : E) = z :=
    mfderiv_symm_apply_mfderiv_ofOrder hk (c := e.symm) hpT z
  set cur : ℝ → M := fun s => e (X + s • W) with hcurdef
  have hcur0 : cur 0 = p := by
    simp only [hcurdef, zero_smul, add_zero]
    exact heX
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => X + s • W) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight W) := by
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const W).const_add X).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have hX0 : (fun s : ℝ => X + s • W) 0 = X := by
    change X + (0 : ℝ) • W = X
    rw [zero_smul, add_zero]
  have he' : HasMFDerivAt 𝓘(ℝ, E) I e ((fun s : ℝ => X + s • W) 0) (mfderiv 𝓘(ℝ, E) I e X) := by
    rw [hX0]
    exact (e.mdifferentiableAt hk hXsrc).hasMFDerivAt
  have hcurd : HasMFDerivAt 𝓘(ℝ, ℝ) I cur 0 ((1 : ℝ →L[ℝ] ℝ).smulRight z) := by
    refine (he'.comp (0 : ℝ) hlin).congr_mfderiv ?_
    refine ContinuousLinearMap.ext_ring ?_
    change mfderiv 𝓘(ℝ, E) I e X ((1 : ℝ) • W) = (1 : ℝ) • z
    rw [one_smul, one_smul]
    exact hBW
  -- first variation from `p` towards `q`
  have hpnq : p ∉ ({q} : Set M) := by
    intro h
    rw [mem_singleton_iff] at h
    rw [h, dist_self] at hpq
    linarith
  have hu : (w : TangentSpace I p) ∈ g.finiteMinimizingDirectionsTo {q} p := by
    refine ⟨hw, ?_⟩
    rw [infDist_singleton, hpq]
    exact (show g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M) ∈ ({q} : Set M) by
      rw [hqw]; exact mem_singleton q)
  have hfv := g.eventually_infDist_sub_le_finite_of_eq hr hnorm isClosed_singleton
    (singleton_nonempty q) hcur0 hcurd hpnq hu (c := -(g.inner p w z) / 2) (by linarith)
  have hsrcev : ∀ᶠ s in 𝓝 (0 : ℝ), X + s • W ∈ e.source := by
    have hc : ContinuousAt (fun s : ℝ => X + s • W) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    exact hc.preimage_mem_nhds (by simpa using e.open_source.mem_nhds hXsrc)
  have hcurZ : ∀ᶠ s in 𝓝[>] (0 : ℝ), cur s ∈ Z := by
    filter_upwards [hfv, hsrcev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsrc
      hspos
    have hspos' : (0 : ℝ) < s := hspos
    have hd : dist q (cur s) < r₀ := by
      rw [infDist_singleton, infDist_singleton, hpq] at hs
      rw [dist_comm]
      have h1 : s * (-(g.inner p w z) / 2) < 0 := by
        have := mul_pos hspos' hzw
        nlinarith
      linarith
    have hmemK : X + s • W ∈ sliceTangent I Z q :=
      (sliceTangent I Z q).add_mem hXK ((sliceTangent I Z q).smul_mem s hzK)
    have hlen : Real.sqrt (g.inner q (X + s • W) (X + s • W)) < infDist q B := by
      rw [← hdist _ hsrc, hqB]
      exact hd
    have h := expMap_mem_maxSliceLocusOfOrder_of_lt_infDist g hr hnorm hCcl hconv hq hmemK hlen
    change e (X + s • W) ∈ Z
    rw [hexp _ hsrc]
    exact h
  -- the normal chart at `p` and the directions `U s` from `p` to `cur s`
  obtain ⟨ρp, hρp, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm
    (isCompact_singleton (x := p))
  obtain ⟨ep, -, htgtp, hexpp, -, -, h0p, he0p, hderivp⟩ := hch p rfl
  have hpTp : p ∈ ep.target := by rw [htgtp]; exact mem_ball_self hρp
  have hsymm0 : ep.symm p = 0 := by
    rw [← he0p]
    exact ep.toPartialEquiv.left_inv h0p
  set U : ℝ → E := fun s => ep.symm (cur s) with hUdef
  have hU0 : U 0 = 0 := by
    change ep.symm (cur 0) = 0
    rw [hcur0]
    exact hsymm0
  have hUd : HasDerivAt U z 0 := by
    have h := hasDerivAt_comp_of_hasMFDerivAt_CMS3REL (f := ep.symm) (γ := cur)
      (by rw [hcur0]; exact ep.symm.mdifferentiableAt hk hpTp) hcurd
    rw [hcur0] at h
    have hid : (mfderiv I 𝓘(ℝ, E) ep.symm p z : E) = z := by
      have h2 := mfderiv_symm_apply_mfderiv_ofOrder hk (c := ep.symm) hpTp z
      have hd' : HasMFDerivAt 𝓘(ℝ, E) I ep (ep.symm p) (ContinuousLinearMap.id ℝ E) := by
        rw [hsymm0]; exact hderivp
      change mfderiv 𝓘(ℝ, E) I ep (ep.symm p) (mfderiv I 𝓘(ℝ, E) ep.symm p z) = z at h2
      rw [hd'.mfderiv] at h2
      exact h2
    rw [hid] at h
    exact h
  have hslope : Tendsto (fun s : ℝ => s⁻¹ • U s) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have h := hUd.tendsto_slope.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ne_of_gt ht)
    refine h.congr' (Eventually.of_forall fun s => ?_)
    rw [slope_def_module, hU0, sub_zero, sub_zero]
  -- normalisation
  set N : E → ℝ := fun v => Real.sqrt (g.inner p v v) with hNdef
  have hNc : Continuous N := by
    refine Real.continuous_sqrt.comp ?_
    exact (g.inner p).continuous₂.comp (continuous_id.prodMk continuous_id)
  have hz0 : z ≠ 0 := by
    intro hz
    have h0 : g.inner p w z = 0 := by rw [hz]; exact (g.inner p w).map_zero
    linarith
  have hNz : 0 < N z := Real.sqrt_pos.2 (g.pos p z hz0)
  set F : E → E := fun v => (N v)⁻¹ • v with hFdef
  have hFc : ContinuousAt F z := ((hNc.continuousAt).inv₀ hNz.ne').smul continuousAt_id
  have hNsmul : ∀ c : ℝ, 0 ≤ c → ∀ v : E, N (c • v) = c * N v := by
    intro c hc v
    change Real.sqrt (g.inner p (c • v) (c • v)) = c * Real.sqrt (g.inner p v v)
    have h1 : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
      rw [shaveInner_smul_left, shaveInner_smul_right]; ring
    rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have hFscale : ∀ c : ℝ, 0 < c → ∀ v : E, F (c • v) = F v := by
    intro c hc v
    change (N (c • v))⁻¹ • (c • v) = (N v)⁻¹ • v
    rw [hNsmul c hc.le, smul_smul, mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne',
      mul_one]
  have hunitF : ∀ v : E, v ≠ 0 → g.inner p (F v) (F v) = 1 := by
    intro v hv
    have hpos := g.pos p v hv
    change g.inner p ((N v)⁻¹ • v) ((N v)⁻¹ • v) = 1
    rw [shaveInner_smul_left, shaveInner_smul_right]
    have hsq : N v ^ 2 = g.inner p v v := Real.sq_sqrt hpos.le
    have hN0 : N v ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    field_simp
    linarith
  have hÛ : Tendsto (fun s => F (U s)) (𝓝[>] (0 : ℝ)) (𝓝 (F z)) := by
    have h := hFc.tendsto.comp hslope
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hFscale s⁻¹ (inv_pos.2 hs) (U s)
  set c₀ : ℝ := g.inner p w (F z) / 2 with hc₀def
  have hwFz : g.inner p w (F z) = (N z)⁻¹ * g.inner p w z := by
    change g.inner p w ((N z)⁻¹ • z) = _
    rw [shaveInner_smul_right]
  have hc₀ : 0 < c₀ := by
    rw [hc₀def, hwFz]
    have := mul_pos (inv_pos.2 hNz) hzw
    linarith
  have hc₀ev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c₀ < g.inner p w (F (U s)) := by
    have hcw : Continuous (fun v : E => g.inner p w v) := (g.inner p w).continuous
    have h := (hcw.tendsto (F z)).comp hÛ
    exact h.eventually (lt_mem_nhds (by rw [hc₀def]; linarith))
  have hUne : ∀ᶠ s in 𝓝[>] (0 : ℝ), U s ≠ 0 := by
    have h := hslope.eventually (isOpen_ne.mem_nhds hz0)
    filter_upwards [h, self_mem_nhdsWithin] with s hs hspos
    intro hU
    apply hs
    rw [hU, smul_zero]
  have hcurT : ∀ᶠ s in 𝓝[>] (0 : ℝ), cur s ∈ ep.target := by
    have hc : ContinuousAt cur 0 := hcurd.continuousAt
    have h : ∀ᶠ s in 𝓝 (0 : ℝ), cur s ∈ ep.target :=
      hc.preimage_mem_nhds (by rw [hcur0]; exact ep.open_target.mem_nhds hpTp)
    exact h.filter_mono nhdsWithin_le_nhds
  -- the uniform interval
  obtain ⟨ρ₁, hρ₁, hrad⟩ := exists_radial_dist_eq g hr hnorm p
  set τ₀ : ℝ := min ρ₁ (2 * r₀ * c₀) with hτ₀def
  have hτ₀ : 0 < τ₀ := lt_min hρ₁ (by positivity)
  have hmin : dist p (g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M)) = r₀ := by rw [hqw]; exact hpq
  have havoid : ∀ e' : E, g.inner p e' e' = 1 → c₀ ≤ g.inner p w e' → ∀ τ ∈ Ioo 0 τ₀,
      g.expMap (⟨p, τ • e'⟩ : TangentBundle I M) ∉ B := by
    intro e' he' hwe' τ hτ
    apply hnotB
    have h := dist_expMap_lt_of_hinge_CMS3REL g hr hnorm hsec hw hr₀ hmin hrad he' hwe' hτ.1
      (lt_of_lt_of_le hτ.2 (min_le_left _ _)) (lt_of_lt_of_le hτ.2 (min_le_right _ _))
    rwa [hqw] at h
  -- the approximating geodesics stay in `Z` on the uniform interval
  have hgood : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ τ ∈ Ioo 0 τ₀,
      g.expMap (⟨p, τ • F (U s)⟩ : TangentBundle I M) ∈ Z := by
    filter_upwards [hcurZ, hcurT, hUne, hc₀ev] with s hsZ hsT hsne hsc
    set u : E := U s with hudef
    have husrc : u ∈ ep.source := ep.toPartialEquiv.map_target hsT
    have hepu : ep u = cur s := ep.toPartialEquiv.right_inv hsT
    have hNu : 0 < N u := Real.sqrt_pos.2 (g.pos p u hsne)
    have h1 : g.expMap (⟨p, (1 : ℝ) • u⟩ : TangentBundle I M) ∈ Z := by
      have h2 : g.expMap (⟨p, (1 : ℝ) • u⟩ : TangentBundle I M) = ep u := by
        rw [hexpp u husrc]
        exact congrArg (fun v : E => g.expMap (⟨p, v⟩ : TangentBundle I M)) (one_smul ℝ u)
      rw [h2, hepu]
      exact hsZ
    have hseg := expMap_smul_mem_maxSliceLocusOfOrder_of_mem g hr hnorm hconv hpC one_pos h1
    have hin : ∀ τ ∈ Ioc 0 (N u), g.expMap (⟨p, τ • F u⟩ : TangentBundle I M) ∈ Z := by
      intro τ hτ
      have hv : (τ • F u : E) = (τ / N u) • u := by
        change τ • ((N u)⁻¹ • u) = (τ / N u) • u
        rw [smul_smul, div_eq_mul_inv]
      have heq : g.expMap (⟨p, τ • F u⟩ : TangentBundle I M) =
          g.expMap (⟨p, (τ / N u) • u⟩ : TangentBundle I M) :=
        congrArg (fun v : E => g.expMap (⟨p, v⟩ : TangentBundle I M)) hv
      rw [heq]
      exact hseg (τ / N u) ⟨div_pos hτ.1 hNu, (div_le_one hNu).2 hτ.2⟩
    exact expMap_smul_mem_maxSliceLocusOfOrder_of_notMem g hr hnorm hCcl hconv hNu hin
      fun τ hτ => havoid (F u) (hunitF u hsne) hsc.le τ hτ
  -- the limit direction
  have hlimZ : ∀ τ ∈ Ioo 0 τ₀, g.expMap (⟨p, τ • F z⟩ : TangentBundle I M) ∈ Z := by
    intro τ hτ
    have hsm : Continuous (fun v : E => τ • v) := continuous_const.smul continuous_id
    have hcont : Continuous (fun v : E => g.expMap (⟨p, τ • v⟩ : TangentBundle I M)) :=
      (g.continuous_expMap_of_completeSpace hr hnorm).comp
        ((FiberBundle.totalSpaceMk_isInducing E (TangentSpace I) p).continuous.comp hsm)
    have htend : Tendsto (fun s => g.expMap (⟨p, τ • F (U s)⟩ : TangentBundle I M)) (𝓝[>] (0 : ℝ))
        (𝓝 (g.expMap (⟨p, τ • F z⟩ : TangentBundle I M))) := (hcont.tendsto _).comp hÛ
    have hmemC : g.expMap (⟨p, τ • F z⟩ : TangentBundle I M) ∈ C :=
      hclZ (mem_closure_of_tendsto htend (hgood.mono fun s hs => hs τ hτ))
    by_contra hZ
    exact havoid (F z) (hunitF z hz0) (by rw [hc₀def]; linarith) τ hτ ⟨hmemC, hZ⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < τ₀ / N z by positivity)] with s hs
  have hv : (s • z : E) = (s * N z) • F z := by
    change s • z = (s * N z) • ((N z)⁻¹ • z)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hNz.ne', mul_one]
  have heq : g.expMap (⟨p, s • z⟩ : TangentBundle I M) =
      g.expMap (⟨p, (s * N z) • F z⟩ : TangentBundle I M) :=
    congrArg (fun v : E => g.expMap (⟨p, v⟩ : TangentBundle I M)) hv
  have h1 := hs.2
  rw [lt_div_iff₀ hNz] at h1
  have key := hlimZ _ ⟨mul_pos hs.1 hNz, h1⟩
  rw [← heq] at key
  exact key

/-- **Relative foot point (SL2, local form).** Let the unit geodesic from `y ∈ C` in direction `u`
reach the relative boundary at time `l = d(y, B) > 0` in the foot `P = φ_l (y, u)`. Then no `ξ` with
`g(ξ, P.snd) ≥ 0` is inner at the foot: `exp_{π P} (s ξ) ∉ Z` for all small `s > 0`. -/
theorem eventually_expMap_notMem_maxSliceLocusOfOrder_of_foot [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {y : M} (hy : y ∈ C) {u : E}
    (hu : g.inner y u u = 1) (hl : 0 < infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))
    (hfoot : (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
      (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj ∈ relBoundaryOfOrder I (r : ℕ∞ω) C)
    (ξ : E)
    (hξ : 0 ≤ g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
      (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj ξ
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).snd) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
      (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj, s • ξ⟩ : TangentBundle I M) ∉
        maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  set l := infDist y B with hldef
  set P := g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l with hP
  set p : M := P.proj with hpdef
  have hflow : ∀ τ : ℝ, g.expMap (⟨y, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 y u τ (by rw [hD]; exact mem_univ _)
  have hfoot' : g.expMap (⟨y, l • u⟩ : TangentBundle I M) ∈ B := by rw [hflow]; exact hfoot
  obtain ⟨-, hsegZ, hsegd⟩ := foot_segment_relBoundaryOfOrder g hr hnorm hconv hy hu hfoot'
  obtain ⟨hseg, -⟩ := dist_infDist_expMap_smul_of_foot g hr hnorm hu hfoot'
  have hpC : p ∈ C := relBoundaryOfOrder_subset hfoot
  have hpZ : p ∉ Z := hfoot.2
  have hPunit : g.inner p P.snd P.snd = 1 := by
    rw [hpdef, hP, g.inner_geodesicFlow_eq hr1 _ l (by rw [hD]; exact mem_univ _)]
    exact hu
  set vP : E := P.snd with hvPdef
  set w : E := (-1 : ℝ) • vP with hwdef
  have hw : g.inner p w w = 1 := by
    rw [hwdef, shaveInner_smul_left, shaveInner_smul_right, hPunit]; norm_num
  have hwflow : ∀ s : ℝ, g.expMap (⟨p, s • w⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (l - s)).proj := by
    intro s
    have h1 := g.expMap_smul_eq_proj_geodesicFlow hr1 p w s (by rw [hD]; exact mem_univ _)
    have h2 := proj_geodesicFlow_neg_snd g hr hnorm P s
    calc g.expMap (⟨p, s • w⟩ : TangentBundle I M)
        = (g.geodesicFlow (⟨p, w⟩ : TangentBundle I M) s).proj := h1
      _ = (g.geodesicFlow P (-s)).proj := h2
      _ = (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (l - s)).proj := by
          rw [hP, ← geodesicFlow_add_of_complete g hr hnorm, ← sub_eq_add_neg]
  have hwin : ∀ᶠ s in 𝓝[>] (0 : ℝ), g.expMap (⟨p, s • w⟩ : TangentBundle I M) ∈ Z := by
    filter_upwards [Ioo_mem_nhdsGT hl] with s hs
    have h := hsegZ (l - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [← hwflow] at h
    exact h
  -- the auxiliary point `q` on the foot segment, close to `p`
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨ρ, hρ, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm
    (isCompact_closedBall p l)
  set r₀ : ℝ := min (l / 2) (ρ / 2) with hr₀def
  have hr₀ : 0 < r₀ := lt_min (by linarith) (by linarith)
  have hr₀l : r₀ ≤ l / 2 := min_le_left _ _
  have hr₀ρ : r₀ ≤ ρ / 2 := min_le_right _ _
  set q : M := (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (l - r₀)).proj with hqdef
  have hqZ : q ∈ Z := hsegZ (l - r₀) ⟨by linarith, by linarith⟩
  have hqB : infDist q B = r₀ := by
    rw [hqdef, hsegd (l - r₀) ⟨by linarith, by linarith⟩]; ring
  have hpq : dist p q = r₀ := by
    have h := hseg l ⟨hl.le, le_rfl⟩ (l - r₀) ⟨by linarith, by linarith⟩
    rw [hflow, hflow] at h
    rw [hpdef, hP, hqdef, h, show l - (l - r₀) = r₀ by ring, abs_of_pos hr₀]
  have hqw : g.expMap (⟨p, r₀ • w⟩ : TangentBundle I M) = q := hwflow r₀
  have hqK : q ∈ closedBall p l := by
    rw [mem_closedBall, dist_comm, hpq]; linarith
  obtain ⟨e, -, htgt, hexp, hdist, -, -, -, -⟩ := hch q hqK
  have hpT : p ∈ e.target := by
    rw [htgt, mem_ball, hpq]; linarith
  -- if `ξ` were inner: openness, acuteness and local propagation put the foot in `Z`
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_not] at hcon
  have hξin := eventually_expMap_smul_mem_of_frequently g hr hnorm hconv hpC hcon
  obtain ⟨ε, hε, hvin⟩ := exists_inner_sub_smul g hr hnorm hconv hqZ hexp hpT hpC hξin hwin
  set v : E := ξ - ε • w with hvdef
  have hvK := (mfderiv_symm_mem_sliceTangent_of_inner g hr hnorm hconv hqZ hexp hpT hvin).2
  set z : E := (-1 : ℝ) • v with hzdef
  have hzK : (mfderiv I 𝓘(ℝ, E) e.symm p z : E) ∈ sliceTangent I Z q := by
    have h := (sliceTangent I Z q).smul_mem (-1 : ℝ) hvK
    have hlin : (mfderiv I 𝓘(ℝ, E) e.symm p z : E) =
        (-1 : ℝ) • (mfderiv I 𝓘(ℝ, E) e.symm p v : E) :=
      (mfderiv I 𝓘(ℝ, E) e.symm p).map_smul (-1) v
    rw [hlin]
    exact h
  have hzw : 0 < g.inner p w z := by
    have h1 : g.inner p w z = -(g.inner p w ξ) + ε := by
      rw [hzdef, hvdef, shaveInner_smul_right, shaveInner_sub_right, shaveInner_smul_right, hw]
      ring
    have h2 : g.inner p w ξ = -(g.inner p ξ vP) := by
      rw [hwdef, shaveInner_smul_left, shaveInner_symm]
      ring
    rw [h1, h2]
    linarith
  have hzin := inner_of_acute g hr hnorm hsec hCcl hconv hqZ hexp hdist hpT hpC hw hr₀ hqw hpq hqB
    hwin hzK hzw
  exact hpZ (mem_maxSliceLocusOfOrder_of_inner_neg g hr hnorm hconv hvin hzin)

/-- **Relative foot point (SL2, finite form).** Uniformly for feet in a compact `K`: no vector `ξ` of
length `< ρ` with `g(ξ, P.snd) ≥ 0` at the foot has `exp_{π P} ξ ∈ Z` (local form + SLICE's relative
radial cone). -/
theorem expMap_notMem_maxSliceLocusOfOrder_of_foot [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {K : Set M}
    (hK : IsCompact K) :
    ∃ ρ > 0, ∀ y ∈ C, ∀ u : E, g.inner y u u = 1 →
      0 < infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) →
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
        (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj ∈ relBoundaryOfOrder I (r : ℕ∞ω) C →
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
        (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj ∈ K →
      ∀ ξ : E, 0 ≤ g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
          (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj ξ
          (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
            (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).snd →
        g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
          (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj ξ ξ < ρ ^ 2 →
        g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
          (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj, ξ⟩ : TangentBundle I M) ∉
            maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  obtain ⟨ρ, hρ, hcone⟩ := exists_expMap_smul_mem_maxSliceLocusOfOrder g hr hnorm hK
  refine ⟨ρ, hρ, fun y hy u hu hl hfoot hPK ξ hξ hlen hmem => ?_⟩
  have hev := eventually_expMap_notMem_maxSliceLocusOfOrder_of_foot g hr hnorm hsec hCcl hconv hy hu
    hl hfoot ξ hξ
  have hall := hcone hconv _ hPK (relBoundaryOfOrder_subset hfoot) ξ hlen hmem
  obtain ⟨s, hs, hsI⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
  exact hs (hall s ⟨hsI.1, hsI.2.le⟩)

end DifferentialGeometry.Geometry.FiniteSoul

end
