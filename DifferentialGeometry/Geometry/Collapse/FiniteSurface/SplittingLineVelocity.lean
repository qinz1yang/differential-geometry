import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreGraph

/-!
# The coordinate lines of an exact splitting have manifold velocity `V`

On a complete finite-order Riemannian manifold `N` with an exact splitting
`Φ : N ≃ᵢ ℓ²(ℝ × W)` and LFR18's vertical field `V` (the unique minimizing direction to the
`ℓ`-shifted point):

* `hasMFDerivAt_splitting_line`: the line `s ↦ Φ⁻¹(t + s, w₀)` has manifold derivative
  `1 ↦ V(Φ⁻¹(t, w₀))` at `s = 0` (the manifold-valued form of `hasDerivAt_comp_splitting_line`,
  same route: the line is the geodesic in direction `V`);
* `mfderiv_vertical_eq_zero_of_const_on_lines`: a map to any manifold that is constant along the
  coordinate lines and differentiable at `x` kills `V x`.

Lane LFR20-CMP (smooth fibre type: the differential of the projection to the factor vanishes on
the vertical direction).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Geometry.ExactSplitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] {r : ℕ∞} {W : Type*} [MetricSpace W]

/-- **The coordinate lines have manifold velocity `V`.** -/
theorem hasMFDerivAt_splitting_line
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    (w₀ : W) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ.symm (toLp 2 (t + s, w₀))) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ.symm (toLp 2 (t, w₀))))) := by
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
  have hcurve : (fun s => (G.geodesicFlow (⟨x, V x⟩ : TangentBundle I N) s).proj) =
      fun s => Φ.symm (toLp 2 (t + s, w₀)) := funext hγ
  rw [hcurve] at hvel
  exact hvel

/-- **A map constant along the coordinate lines kills the vertical field.** -/
theorem mfderiv_vertical_eq_zero_of_const_on_lines
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    {F' H' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F' H'} {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
    {pr : N → X} {x : N} (hpr : MDifferentiableAt I J pr x)
    (hconst : ∀ s : ℝ, pr (Φ.symm (toLp 2 (s, (Φ x).snd))) = pr x) :
    mfderiv I J pr x (V x) = 0 := by
  have hx : Φ.symm (toLp 2 ((Φ x).fst, (Φ x).snd)) = x := Φ.symm_apply_apply x
  have hline := hasMFDerivAt_splitting_line G hr hnorm Φ hℓ V hVdir (Φ x).snd (Φ x).fst
  rw [hx] at hline
  have h0x : Φ.symm (toLp 2 ((Φ x).fst + 0, (Φ x).snd)) = x := by rw [add_zero, hx]
  have hpr' : MDifferentiableAt I J pr
      ((fun s => Φ.symm (toLp 2 ((Φ x).fst + s, (Φ x).snd))) 0) := by
    simp only [h0x]
    exact hpr
  have hcomp := hpr'.hasMFDerivAt.comp 0 hline
  have hfun : (pr ∘ fun s => Φ.symm (toLp 2 ((Φ x).fst + s, (Φ x).snd))) = fun _ => pr x :=
    funext fun s => hconst _
  rw [hfun] at hcomp
  have h0 := hcomp.mfderiv.symm.trans (hasMFDerivAt_const (pr x) (0 : ℝ)).mfderiv
  have h1 : mfderiv I J pr (Φ.symm (toLp 2 ((Φ x).fst + 0, (Φ x).snd))) (V x) = 0 := by
    have h2 := congrArg (fun L => L (1 : ℝ)) h0
    have h3 : (1 : ℝ →L[ℝ] ℝ).smulRight (V x) (1 : ℝ) = V x := by simp
    change mfderiv I J pr (Φ.symm (toLp 2 ((Φ x).fst + 0, (Φ x).snd)))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V x) (1 : ℝ)) = 0 at h2
    rw [h3] at h2
    exact h2
  have key : ∀ p : N, p = x → mfderiv I J pr p (V x) = 0 → mfderiv I J pr x (V x) = 0 := by
    intro p hp h
    rw [hp] at h
    exact h
  exact key _ h0x h1

end DifferentialGeometry.Geometry.Collapse
