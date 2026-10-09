import DifferentialGeometry.Topology.Manifold.SmoothApproximation.NoncompactSource
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.ChartConvergence
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Topology.Manifold.CompactCoreEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth partial diffeomorphisms near a `C^s` partial diffeomorphism (LFR48, tier T2)

LFR48 (A:29037) replaces the `C^s` comparison embeddings of LFR14 by SMOOTH ones. Tier T1
(`exists_smooth_seq_chart_tendsto_near_isCompact`) produces smooth maps `hs n` near a compact set
of a noncompact source, `C^k` close to a given map in charts. This file shows that maps which are
chartwise `C¹` close to a `C^s` partial diffeomorphism `j` (`1 ≤ s`) on an open `W ⊆ j.source` are
eventually SMOOTH partial diffeomorphisms on any open `O` with compact closure in `W`.

* `contDiffOn_one_chartRep_of_contMDiffOn`, `isInvertible_fderiv_chartRep_iff_of_mdifferentiableAt`:
  local forms (maps defined on an open set only) of the chart lemmas of W2
  (`SmoothApproximation/ChartConvergence.lean`).
* `exists_isOpen_eventually_injOn_isInvertible_mfderiv_of_contMDiffOn`: local step. Near a point
  of `W` where `mfderiv h` is invertible, one fixed open neighbourhood inside `W` on which
  eventually every `hs n` is injective with invertible `mfderiv`.
* `eventually_exists_smooth_partialDiffeomorph_of_chart_tendsto` (T2 kernel): `hs n` smooth on `W`,
  locally uniformly convergent to `j` on `W` and chartwise `C^m` convergent (`1 ≤ m`) on compact chart
  pieces over `W` ⇒ eventually `hs n` is a smooth `PartialDiffeomorph` with source `O`.
* `exists_smooth_partialDiffeomorph_seq_near_isCompact` (T1 + T2): a `C^k` partial diffeomorphism
  (`1 ≤ k`), a compact `C ⊆ j.source` and `x₀ ∈ C` give an open `O ⊇ C` with compact closure in
  `j.source` and pointed smooth maps, `C^k` close to `j` in charts over `O`, eventually smooth
  partial diffeomorphisms with source `O`.

Route: the local step is W2's (`exists_isOpen_eventually_injOn_isInvertible_mfderiv`) on the open
chart domain cut by `W`; the inverse function theorem
`ContMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv` (order `∞`); global injectivity on the
compact `closure O` from local injectivity and the uniform limit `j`, injective on its source
(`Topology.Manifold.eventually_exists_partialDiffeomorph_of_local_diffeomorphs`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]

section Local

variable {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- The coordinate expression of a map that is `C¹` on an open set `W` is `C¹` on the (open)
chart domain cut by `W`. -/
theorem contDiffOn_one_chartRep_of_contMDiffOn {f : A → B} {W : Set A}
    (hf : ContMDiffOn I J 1 f W) (p : A) (q : B) :
    ContDiffOn ℝ 1 (fun y => extChartAt J q (f ((extChartAt I p).symm y)))
      ((extChartAt I p).target ∩
        (extChartAt I p).symm ⁻¹' (W ∩ f ⁻¹' (extChartAt J q).source)) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) J 1 (f ∘ (extChartAt I p).symm)
      ((extChartAt I p).target ∩
        (extChartAt I p).symm ⁻¹' (W ∩ f ⁻¹' (extChartAt J q).source)) :=
    hf.comp ((contMDiffOn_extChartAt_symm p).mono inter_subset_left) fun y hy => hy.2.1
  refine contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_extChartAt (n := 1) (x := q)).comp h1 ?_)
  intro y hy
  have h := hy.2.2
  simp only [mem_preimage, extChartAt_source] at h ⊢
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- Invertibility of the derivative of a coordinate expression is invertibility of `mfderiv`, for
a map that is only differentiable at the point (local form of `isInvertible_fderiv_chartRep_iff`). -/
theorem isInvertible_fderiv_chartRep_iff_of_mdifferentiableAt {f : A → B} {p : A} {q : B}
    {y : E} (hf : MDifferentiableAt I J f ((extChartAt I p).symm y))
    (hy : y ∈ (extChartAt I p).target)
    (hfy : f ((extChartAt I p).symm y) ∈ (extChartAt J q).source) :
    (fderiv ℝ (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y).IsInvertible ↔
      (mfderiv I J f ((extChartAt I p).symm y)).IsInvertible := by
  set x := (extChartAt I p).symm y with hx
  have h1 : MDifferentiableAt J 𝓘(ℝ, E') (extChartAt J q) (f x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hfy)
  have h3 : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm y := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) hy
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y =
      (mfderiv J 𝓘(ℝ, E') (extChartAt J q) (f x)).comp
        ((mfderiv I J f x).comp (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y)) := by
    rw [show (fun y => extChartAt J q (f ((extChartAt I p).symm y))) =
        (extChartAt J q) ∘ (f ∘ (extChartAt I p).symm) from rfl,
      mfderiv_comp y h1 (hf.comp y h3), mfderiv_comp y hf h3]
    rfl
  obtain ⟨eA, heA⟩ := isInvertible_mfderiv_extChartAt (I := J) (x := q) hfy
  have hC : (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := p) hy
    rwa [I.range_eq_univ, mfderivWithin_univ] at h
  obtain ⟨eC, heC⟩ := hC
  have hiff1 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E')
      (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y).IsInvertible ↔
      (fderiv ℝ (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y).IsInvertible := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv]
  have hiff2 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E')
      (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y).IsInvertible ↔
      (mfderiv I J f x).IsInvertible := by
    rw [hc, ← heA, ← heC, ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv]
  exact hiff1.symm.trans hiff2

omit [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- **Local step of T2.** Let `h` and every `hs n` be `C¹` on an open set `W`, with chartwise
`C^m` convergence `hs n → h` (`1 ≤ m`) on compact chart pieces over `W`. If `mfderiv h a` is
invertible at `a ∈ W`, there is an open `N`, `a ∈ N ⊆ W`, on which eventually every `hs n` is
injective with invertible `mfderiv`. -/
theorem exists_isOpen_eventually_injOn_isInvertible_mfderiv_of_contMDiffOn {m : ℕ}
    (hm : 1 ≤ m) {W : Set A} (hW : IsOpen W) {h : A → B} (hh : ContMDiffOn I J 1 h W)
    {hs : ℕ → A → B} (hsm : ∀ n, ContMDiffOn I J 1 (hs n) W)
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K →
        K ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' W →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ n in atTop, MapsTo (fun y => hs n ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun n y => extChartAt J q (hs n ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))))
    {a : A} (haW : a ∈ W) (ha : (mfderiv I J h a).IsInvertible) :
    ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ N ⊆ W ∧ ∀ᶠ n in atTop,
      InjOn (hs n) N ∧ ∀ x ∈ N, (mfderiv I J (hs n) x).IsInvertible := by
  let rep : E → E' := fun y => extChartAt J (h a) (h ((extChartAt I a).symm y))
  let O : Set E := (extChartAt I a).target ∩
    (extChartAt I a).symm ⁻¹' (W ∩ h ⁻¹' (extChartAt J (h a)).source)
  have hO : IsOpen O := (continuousOn_extChartAt_symm a).isOpen_inter_preimage
    (isOpen_extChartAt_target a)
    (hh.continuousOn.isOpen_inter_preimage hW (isOpen_extChartAt_source (h a)))
  have hsrc₀ : h ((extChartAt I a).symm (extChartAt I a a)) ∈ (extChartAt J (h a)).source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source (h a)
  have hy₀ : extChartAt I a a ∈ O := by
    refine ⟨mem_extChartAt_target a, ?_⟩
    change (extChartAt I a).symm (extChartAt I a a) ∈ W ∩ h ⁻¹' (extChartAt J (h a)).source
    rw [extChartAt_to_inv]
    exact ⟨haW, mem_extChartAt_source (h a)⟩
  have hrep : ContDiffOn ℝ 1 rep O := contDiffOn_one_chartRep_of_contMDiffOn hh a (h a)
  have hmd₀ : MDifferentiableAt I J h ((extChartAt I a).symm (extChartAt I a a)) := by
    rw [extChartAt_to_inv]
    exact (hh.contMDiffAt (hW.mem_nhds haW)).mdifferentiableAt one_ne_zero
  have hinv₀ : (fderiv ℝ rep (extChartAt I a a)).IsInvertible := by
    refine (isInvertible_fderiv_chartRep_iff_of_mdifferentiableAt hmd₀
      (mem_extChartAt_target a) hsrc₀).mpr ?_
    rw [extChartAt_to_inv]
    exact ha
  obtain ⟨L, hL⟩ := hinv₀
  set ε : ℝ := (4 * (‖(L.symm : E' →L[ℝ] E)‖ + 1))⁻¹ with hεdef
  have hε : 0 < ε := by positivity
  have hDc : ContinuousOn (fderiv ℝ rep) O := hrep.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨ρ₁, hρ₁, hρ₁O⟩ := Metric.isOpen_iff.mp hO _ hy₀
  obtain ⟨ρ₂, hρ₂, hρ₂c⟩ :=
    Metric.continuousAt_iff.mp (hDc.continuousAt (hO.mem_nhds hy₀)) ε hε
  set ρ : ℝ := min ρ₁ ρ₂ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ₁' : ρ < ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hρ₂' : ρ < ρ₂ := by rw [hρdef]; linarith [min_le_right ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hKO : closedBall (extChartAt I a a) ρ ⊆ O := fun y hy =>
    hρ₁O (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hρ₁'))
  have hLK : ∀ y ∈ closedBall (extChartAt I a a) ρ,
      ‖fderiv ℝ rep y - (L : E →L[ℝ] E')‖ ≤ ε := fun y hy => by
    rw [hL, ← dist_eq_norm]
    exact (hρ₂c ((mem_closedBall.mp hy).trans_lt hρ₂')).le
  have hdiff₀ : ∀ y ∈ closedBall (extChartAt I a a) ρ, DifferentiableAt ℝ rep y := fun y hy =>
    (hrep.differentiableOn one_ne_zero y (hKO hy)).differentiableAt (hO.mem_nhds (hKO hy))
  obtain ⟨hev, hcv⟩ := hconv a (h a) (closedBall (extChartAt I a a) ρ)
    (isCompact_closedBall _ _) (fun y hy => ⟨(hKO hy).1, (hKO hy).2.1⟩)
    (fun y hy => (hKO hy).2.2)
  have hGd : ∀ᶠ n in atTop, ∀ y ∈ closedBall (extChartAt I a a) ρ,
      DifferentiableAt ℝ (fun y => extChartAt J (h a) (hs n ((extChartAt I a).symm y))) y := by
    filter_upwards [hev] with n hn y hy
    have hOn : IsOpen ((extChartAt I a).target ∩
        (extChartAt I a).symm ⁻¹' (W ∩ hs n ⁻¹' (extChartAt J (h a)).source)) :=
      (continuousOn_extChartAt_symm a).isOpen_inter_preimage (isOpen_extChartAt_target a)
        ((hsm n).continuousOn.isOpen_inter_preimage hW (isOpen_extChartAt_source (h a)))
    have hyO : y ∈ (extChartAt I a).target ∩
        (extChartAt I a).symm ⁻¹' (W ∩ hs n ⁻¹' (extChartAt J (h a)).source) :=
      ⟨(hKO hy).1, (hKO hy).2.1, hn hy⟩
    exact ((contDiffOn_one_chartRep_of_contMDiffOn (hsm n) a (h a)).differentiableOn
      one_ne_zero y hyO).differentiableAt (hOn.mem_nhds hyO)
  have hker := eventually_injOn_isInvertible_fderiv_of_mapCPConvergenceOn
    (convex_closedBall _ ρ) L hdiff₀ hLK hGd (hcv.mono_order hm)
  have hNW : (extChartAt I a).source ∩ extChartAt I a ⁻¹' ball (extChartAt I a a) ρ ⊆ W := by
    intro x hx
    have h1 := (hKO (ball_subset_closedBall hx.2)).2.1
    rwa [(extChartAt I a).left_inv hx.1] at h1
  refine ⟨(extChartAt I a).source ∩ extChartAt I a ⁻¹' ball (extChartAt I a a) ρ,
    (continuousOn_extChartAt a).isOpen_inter_preimage (isOpen_extChartAt_source a) isOpen_ball,
    ⟨mem_extChartAt_source a, mem_ball_self hρ⟩, hNW, ?_⟩
  filter_upwards [hker, hev] with n hn hnmap
  refine ⟨fun x hx x' hx' hxx' => ?_, fun x hx => ?_⟩
  · refine (extChartAt I a).injOn hx.1 hx'.1 ?_
    refine hn.1 (ball_subset_closedBall hx.2) (ball_subset_closedBall hx'.2) ?_
    change extChartAt J (h a) (hs n ((extChartAt I a).symm (extChartAt I a x))) =
      extChartAt J (h a) (hs n ((extChartAt I a).symm (extChartAt I a x')))
    rw [(extChartAt I a).left_inv hx.1, (extChartAt I a).left_inv hx'.1, hxx']
  · have hyK : extChartAt I a x ∈ closedBall (extChartAt I a a) ρ := ball_subset_closedBall hx.2
    have hmd : MDifferentiableAt I J (hs n) ((extChartAt I a).symm (extChartAt I a x)) := by
      rw [(extChartAt I a).left_inv hx.1]
      exact ((hsm n).contMDiffAt (hW.mem_nhds (hNW hx))).mdifferentiableAt one_ne_zero
    have h1 := (isInvertible_fderiv_chartRep_iff_of_mdifferentiableAt hmd (hKO hyK).1
      (hnmap hyK)).mp (hn.2 _ hyK)
    rwa [(extChartAt I a).left_inv hx.1] at h1

end Local

variable {B : Type*} [MetricSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

omit [FiniteDimensional ℝ E'] in
/-- **LFR48 T2: smooth partial diffeomorphisms near a `C^s` partial diffeomorphism.** Let
`j : A → B` be a `C^s` partial diffeomorphism (`1 ≤ s`), `W ⊆ j.source` open, and `hs n` smooth on
`W`, converging to `j` locally uniformly on `W` and chartwise in `C^m` (`1 ≤ m`) on every compact
chart piece over `W` (the conclusion of T1, `exists_smooth_seq_chart_tendsto_near_isCompact`). For
every open `O` with compact closure inside `W`, eventually `hs n` is a SMOOTH partial
diffeomorphism with source `O` and target `hs n '' O`. -/
theorem eventually_exists_smooth_partialDiffeomorph_of_chart_tendsto [Nonempty A] {s : ℕ∞ω}
    (hs1 : 1 ≤ s) (j : PartialDiffeomorph I J A B s) {m : ℕ} (hm : 1 ≤ m) {W : Set A}
    (hW : IsOpen W) (hWj : W ⊆ j.source) {hs : ℕ → A → B}
    (hsm : ∀ n, ContMDiffOn I J ∞ (hs n) W) (hunif : TendstoLocallyUniformlyOn hs j atTop W)
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K →
        K ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' W →
        MapsTo (fun y => j ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ n in atTop, MapsTo (fun y => hs n ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun n y => extChartAt J q (hs n ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (j ((extChartAt I p).symm y))))
    {O : Set A} (hO : IsOpen O) (hOc : IsCompact (closure O)) (hOW : closure O ⊆ W) :
    ∀ᶠ n in atTop, ∃ d : PartialDiffeomorph I J A B ∞,
      d.source = O ∧ d.target = hs n '' O ∧ (d : A → B) = hs n := by
  have hs0 : s ≠ 0 := (zero_lt_one.trans_le hs1).ne'
  have hinf : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hj1 : ContMDiffOn I J 1 j W := (j.contMDiffOn.of_le hs1).mono hWj
  have hsm1 : ∀ n, ContMDiffOn I J 1 (hs n) W := fun n => (hsm n).of_le hinf
  refine Topology.Manifold.eventually_exists_partialDiffeomorph_of_local_diffeomorphs
    (M := fun _ => B) hOc hO subset_closure hs (fun _ => id) ∞ ?_ (g := j) ?_ ?_ ?_
  · intro x hx
    have hxW : x ∈ W := hOW hx
    have hinvx : (mfderiv I J j x).IsInvertible :=
      (j.isLocalDiffeomorphAt I J s (hWj hxW)).isInvertible_mfderiv hs0
    obtain ⟨N, hN, hxN, hNW, hev⟩ :=
      exists_isOpen_eventually_injOn_isInvertible_mfderiv_of_contMDiffOn hm hW hj1 hsm1 hconv
        hxW hinvx
    refine ⟨N, hN.mem_nhds hxN, hev.mono fun n hn => ⟨?_, hn.1⟩⟩
    exact ((hsm n).mono hNW).isLocalDiffeomorphOn_of_isInvertible_mfderiv hN hinf hn.2
  · exact hunif.mono hOW
  · exact j.contMDiffOn.continuousOn.mono (hOW.trans hWj)
  · exact j.toPartialEquiv.injOn.mono (hOW.trans hWj)

/-- **LFR48 T1 + T2: pointed smooth partial diffeomorphisms near a compact set.** Let `j` be a
`C^k` partial diffeomorphism (`1 ≤ k`) of boundaryless manifolds, `A` Hausdorff (no compactness),
`B` metric, `C ⊆ j.source` compact and `x₀ ∈ C`. There are an open `O ⊇ C` with compact closure in
`j.source` and maps `hs n : A → B`, smooth on `O`, with `hs n x₀ = j x₀`, `hs n → j` uniformly on
`closure O`, chartwise `C^k` convergence (with eventual chart capture) on every compact chart piece
over `closure O`, and eventually every `hs n` is a smooth partial diffeomorphism with source `O`. -/
theorem exists_smooth_partialDiffeomorph_seq_near_isCompact [T2Space A] {k : ℕ} (hk : 1 ≤ k)
    (j : PartialDiffeomorph I J A B k) {C : Set A} (hC : IsCompact C) (hCj : C ⊆ j.source)
    {x₀ : A} (hx₀ : x₀ ∈ C) :
    ∃ O : Set A, IsOpen O ∧ C ⊆ O ∧ IsCompact (closure O) ∧ closure O ⊆ j.source ∧
      ∃ hs : ℕ → A → B, (∀ n, ContMDiffOn I J ∞ (hs n) O) ∧ (∀ n, hs n x₀ = j x₀) ∧
        TendstoUniformlyOn hs j atTop (closure O) ∧
        (∀ (p : A) (q : B) (K : Set E), IsCompact K →
          K ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' closure O →
          MapsTo (fun y => j ((extChartAt I p).symm y)) K (extChartAt J q).source →
          (∀ᶠ n in atTop, MapsTo (fun y => hs n ((extChartAt I p).symm y)) K
              (extChartAt J q).source) ∧
            MapCPConvergenceOn K k (fun n y => extChartAt J q (hs n ((extChartAt I p).symm y)))
              (fun y => extChartAt J q (j ((extChartAt I p).symm y)))) ∧
        ∀ᶠ n in atTop, ∃ d : PartialDiffeomorph I J A B ∞,
          d.source = O ∧ d.target = hs n '' O ∧ (d : A → B) = hs n := by
  obtain ⟨W, hW, hCW, hWU, hs, hsm, hpt, hunif, hconv⟩ :=
    exists_smooth_seq_chart_tendsto_near_isCompact k j.open_source j.contMDiffOn hC hCj hx₀
  have : Nonempty A := ⟨x₀⟩
  have : LocallyCompactSpace A := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨O, hO, hCO, hOW, hOc⟩ := exists_open_between_and_isCompact_closure hC hW hCW
  refine ⟨O, hO, hCO, hOc, hOW.trans hWU, hs, fun n => (hsm n).mono (subset_closure.trans hOW),
    hpt, hunif.mono hOW, ?_, ?_⟩
  · intro p q K hK hKO hKm
    exact hconv p q K hK (fun y hy => ⟨(hKO hy).1, hOW (hKO hy).2⟩) hKm
  · exact eventually_exists_smooth_partialDiffeomorph_of_chart_tendsto (by exact_mod_cast hk) j hk
      hW hWU hsm hunif.tendstoLocallyUniformlyOn hconv hO hOc hOW

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
