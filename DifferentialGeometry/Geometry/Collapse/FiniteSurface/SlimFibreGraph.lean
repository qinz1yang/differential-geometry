import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimGraph
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrame
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections

/-!
# LFR20 step 4: the ENTIRE zero fibre is the graph over the factor

Blueprint LFR20 (master207A:26358), steps 3–4 ("the whole fiber is the graph over `Z` … this gives
connectedness as well as its type").

* `nonempty_homeomorph_zeroLevel_of_graph` (topological kernel): let `P : ℝ × Z → X` be continuous
  and injective on the cylinder `[-b, b] × Z`, `Z` compact, `X` Hausdorff, and let `η` be continuous
  with `t ↦ η(P(t, z))` strictly increasing on `[-b, b]` and `|η(P(t, z)) - t| < c ≤ b`. If every
  point of a set `S` with `η = 0` is `P` of a cylinder point, and the cylinder's zero points lie in
  `S`, then `{x ∈ S | η x = 0} ≃ₜ Z` (by `z ↦ P(T(0, z), z)`, `T` the root of `exists_continuousOn_root`).
* `hasDerivAt_comp_splitting_line` (the line velocity): on a complete finite-order Riemannian
  manifold with an exact splitting `Φ : N ≃ᵢ ℓ²(ℝ × W)` and LFR18's vertical field `V` (the unique
  minimizing direction to the shifted point), every coordinate line `s ↦ Φ⁻¹(s, w)` has velocity `V`:
  `d/ds f(Φ⁻¹(s, w)) = df(V)` for every `f` differentiable on the line. This turns (LFR20.1) into
  the strict monotonicity used by the kernel.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- **LFR20 step 4, topological kernel.** The zero level of `η` in `S` is homeomorphic to `Z`
through the graph of the root `T(0, ·)`. -/
theorem nonempty_homeomorph_zeroLevel_of_graph {Z X : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [TopologicalSpace X] [T2Space X] {P : ℝ × Z → X} {b c : ℝ}
    (hP : ContinuousOn P (Icc (-b) b ×ˢ univ)) (hPinj : InjOn P (Icc (-b) b ×ˢ univ))
    {η : X → ℝ} (hη : Continuous η)
    (hmono : ∀ z, StrictMonoOn (fun t => η (P (t, z))) (Icc (-b) b))
    (hval : ∀ t ∈ Icc (-b) b, ∀ z, |η (P (t, z)) - t| < c) (hc : 0 < c) (hcb : c ≤ b)
    {S : Set X} (hS : ∀ t ∈ Ioo (-b) b, ∀ z, η (P (t, z)) = 0 → P (t, z) ∈ S)
    (hencl : ∀ x ∈ S, η x = 0 → ∃ t ∈ Icc (-b) b, ∃ z, P (t, z) = x) :
    Nonempty ({x // x ∈ S ∧ η x = 0} ≃ₜ Z) := by
  have hb : -b ≤ b := by linarith
  let ρ : ℝ × Z → ℝ × Z := fun q => (max (-b) (min b q.1), q.2)
  have hρc : Continuous ρ :=
    ((continuous_const.max (continuous_const.min continuous_fst))).prodMk continuous_snd
  have hρmem : ∀ q, ρ q ∈ Icc (-b) b ×ˢ (univ : Set Z) := fun q =>
    ⟨⟨le_max_left _ _, max_le hb (min_le_left _ _)⟩, mem_univ _⟩
  have hρid : ∀ t ∈ Icc (-b) b, ∀ z, ρ (t, z) = (t, z) := by
    intro t ht z
    simp only [ρ, min_eq_right ht.2, max_eq_right ht.1]
  let f : ℝ × Z → ℝ := fun q => η (P (ρ q))
  have hf : Continuous f := hη.comp (hP.comp_continuous hρc hρmem)
  have hfeq : ∀ t ∈ Icc (-b) b, ∀ z, f (t, z) = η (P (t, z)) := by
    intro t ht z
    simp only [f, hρid t ht z]
  have hfmono : ∀ z, StrictMonoOn (fun t => f (t, z)) (Icc (-b) b) := by
    intro z s hs t ht hst
    simp only [hfeq s hs z, hfeq t ht z]
    exact hmono z hs ht hst
  have hfval : ∀ t ∈ Icc (-b) b, ∀ z, |f (t, z) - t| < c := by
    intro t ht z
    rw [hfeq t ht z]
    exact hval t ht z
  obtain ⟨T, hTc, hT⟩ := exists_continuousOn_root (a := 0) hf hfmono hfval hc (by linarith)
  have h0 : (0 : ℝ) ∈ Icc (-0 : ℝ) 0 := ⟨by norm_num, le_rfl⟩
  have hTmem : ∀ z, T (0, z) ∈ Icc (-b) b := fun z => Ioo_subset_Icc_self (hT 0 h0 z).1
  have hTroot : ∀ z, η (P (T (0, z), z)) = 0 := fun z => by
    rw [← hfeq _ (hTmem z) z]
    exact (hT 0 h0 z).2.1
  let G : Z → {x // x ∈ S ∧ η x = 0} := fun z =>
    ⟨P (T (0, z), z), hS _ (hT 0 h0 z).1 z (hTroot z), hTroot z⟩
  have hT0c : Continuous fun z : Z => T (0, z) :=
    hTc.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨h0, mem_univ _⟩
  have hGc : Continuous G :=
    (hP.comp_continuous (hT0c.prodMk continuous_id) fun z => ⟨hTmem z, mem_univ _⟩).subtype_mk _
  have hGinj : Injective G := by
    intro z z' h
    have h' := hPinj ⟨hTmem z, mem_univ _⟩ ⟨hTmem z', mem_univ _⟩ (congrArg Subtype.val h)
    exact congrArg Prod.snd h'
  have hGsurj : Surjective G := by
    rintro ⟨x, hxS, hx0⟩
    obtain ⟨t, ht, z, rfl⟩ := hencl x hxS hx0
    have htT : t = T (0, z) := (hT 0 h0 z).2.2.2 t ht (by rw [hfeq t ht z]; exact hx0)
    exact ⟨z, Subtype.ext (by simp only [G, ← htT])⟩
  exact ⟨(hGc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G ⟨hGinj, hGsurj⟩)).symm⟩

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Geometry.ExactSplitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] {r : ℕ∞} {W : Type*} [MetricSpace W]

omit [CompleteSpace N] in
/-- The shifted point of a coordinate line is at distance `ℓ`. -/
theorem dist_splitting_shift (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (x : N) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    dist x (Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))) = ℓ := by
  rw [← Φ.dist_eq, Φ.apply_symm_apply]
  have h := WithLp.prod_dist_sq_eq_add_sq (Φ x) (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq] at h
  have h2 : |(Φ x).fst - ((Φ x).fst + ℓ)| = ℓ := by
    rw [show (Φ x).fst - ((Φ x).fst + ℓ) = -ℓ by ring, abs_neg, abs_of_nonneg hℓ]
  rw [h2] at h
  have := dist_nonneg (x := Φ x) (y := toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))
  nlinarith

/-- **The coordinate lines have velocity `V`.** With LFR18's vertical field `V` (the unique
minimizing direction to the `ℓ`-shifted point), the line `s ↦ Φ⁻¹(s, w)` satisfies
`d/ds f(Φ⁻¹(s, w)) = df(V)` at every `t` where `f` is differentiable. -/
theorem hasDerivAt_comp_splitting_line
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    {f : N → ℝ} (w₀ : W) (t : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ.symm (toLp 2 (t, w₀)))) :
    HasDerivAt (fun s => f (Φ.symm (toLp 2 (s, w₀))))
      (mvfderiv I f (Φ.symm (toLp 2 (t, w₀))) (V (Φ.symm (toLp 2 (t, w₀))))) t := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set x : N := Φ.symm (toLp 2 (t, w₀)) with hx
  have hΦx : Φ x = toLp 2 (t, w₀) := Φ.apply_symm_apply _
  have hfst : (Φ x).fst = t := by rw [hΦx]; rfl
  have hsnd : (Φ x).snd = w₀ := by rw [hΦx]; rfl
  -- the forward line vector is `V x`
  obtain ⟨w, hw1, hdw, hline⟩ := exists_unit_line_expMap_forall G hr hnorm Φ x
    (u := (1 : ℝ)) (by simp)
  have hwV : w = V x := by
    have hmem : (w : TangentSpace I x) ∈ G.finiteMinimizingDirectionsTo
        {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x := by
      refine ⟨hw1, ?_⟩
      rw [infDist_singleton, dist_splitting_shift Φ x hℓ.le]
      erw [hline ℓ hℓ.le]
      rw [smul_eq_mul, mul_one]
      exact mem_singleton _
    rw [hVdir x] at hmem
    exact hmem
  -- the backward line vector is `-V x`
  obtain ⟨w', hw'1, hdw', hline'⟩ := exists_unit_line_expMap_forall G hr hnorm Φ x
    (u := (-1 : ℝ)) (by simp)
  have hw'V : w' = -w := by
    refine eq_of_mvfderiv_splitting_fst_eq G hr hnorm Φ x (u := (-1 : ℝ)) (by simp) hw'1 ?_ hdw' ?_
    · set W' : TangentSpace I x := w
      change G.inner x (-W') (-W') = 1
      simp only [map_neg, neg_apply, neg_neg]
      exact hw1
    · have hneg := (mvfderiv I (fun x => (Φ x).fst) x).map_neg (w : TangentSpace I x)
      erw [hneg, hdw]
  have hD : ∀ s : ℝ, ((⟨x, V x⟩ : TangentBundle I N), s) ∈ G.geodesicFlowDomain := by
    rw [G.geodesicFlowDomain_eq_univ hr hnorm]
    exact fun _ => mem_univ _
  -- the geodesic from `x` in direction `V x` is the line
  have hγ : ∀ s : ℝ, (G.geodesicFlow (⟨x, V x⟩ : TangentBundle I N) s).proj =
      Φ.symm (toLp 2 (t + s, w₀)) := by
    intro s
    rw [← G.expMap_smul_eq_proj_geodesicFlow hr1 x (V x) s (hD s)]
    rcases le_total 0 s with hs | hs
    · rw [← hwV]
      erw [hline s hs]
      rw [hfst, hsnd, smul_eq_mul, mul_one]
    · set W'' : TangentSpace I x := w' with hW''
      have hw'V' : W'' = -(V x) := by
        rw [← hwV]
        exact hw'V
      have hsv : s • V x = (-s) • W'' := by
        rw [hw'V']
        simp only [smul_neg, neg_smul, neg_neg]
      rw [hsv]
      erw [hline' (-s) (by linarith)]
      rw [hfst, hsnd, smul_eq_mul, mul_neg, mul_one, neg_neg]
  have hvel := G.hasMFDerivAt_geodesicFlow_proj hr1 (hD 0)
  rw [G.geodesicFlow_zero hr1] at hvel
  have h0 : (G.geodesicFlow (⟨x, V x⟩ : TangentBundle I N) 0).proj = x := by
    rw [G.geodesicFlow_zero hr1]
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f
      (G.geodesicFlow (⟨x, V x⟩ : TangentBundle I N) 0).proj := by
    rw [h0]; exact hf
  have hder0 := TauCeti.Manifold.hasDerivAt_comp_curve hfd hvel
  rw [h0] at hder0
  have hcomp : (f ∘ fun s => (G.geodesicFlow (⟨x, V x⟩ : TangentBundle I N) s).proj) =
      fun s => f (Φ.symm (toLp 2 (s + t, w₀))) := by
    funext s
    simp only [Function.comp_apply, hγ s, add_comm t s]
  rw [hcomp] at hder0
  have hder0' : HasDerivAt (fun s => f (Φ.symm (toLp 2 (s + t, w₀))))
      (mvfderiv I f x (V x)) (t + -t) := by
    rw [add_neg_cancel]
    exact hder0
  have h := hder0'.comp_add_const t (-t)
  simp only [neg_add_cancel_right] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
