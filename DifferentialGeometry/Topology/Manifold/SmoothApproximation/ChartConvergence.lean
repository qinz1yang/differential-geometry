import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Chart-wise convergence of maps between manifolds: local consequences

The chart-wise `C^m` convergence `hs j → h` of maps `A → B` used by W1 and W2 is the clause
```
∀ p q K, IsCompact K → K ⊆ (extChartAt I p).target →
  MapsTo (h ∘ (extChartAt I p).symm) K (extChartAt J q).source →
  (∀ᶠ j in atTop, MapsTo (hs j ∘ (extChartAt I p).symm) K (extChartAt J q).source) ∧
  MapCPConvergenceOn K m (ψ_q ∘ hs j ∘ φ_p⁻¹) (ψ_q ∘ h ∘ φ_p⁻¹)
```
This file proves its local consequences:
* `eventually_injOn_isInvertible_fderiv_of_mapCPConvergenceOn` (Euclidean kernel): `C¹`
  convergence on a convex set to a map whose derivative is close to a fixed isomorphism gives,
  eventually, injectivity and invertible derivatives;
* `isInvertible_fderiv_chartRep_iff`: invertibility of the derivative of a coordinate
  expression in arbitrary charts is invertibility of `mfderiv`;
* `eventually_mapsTo_of_chart_tendsto` (LU): local uniform `C⁰` convergence;
* `exists_isOpen_eventually_injOn_isInvertible_mfderiv`: near a point where `mfderiv h` is
  invertible, eventually every `hs j` is injective with invertible `mfderiv` on one fixed open
  neighbourhood.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Euclidean kernel of W2.** If `G i → G₀` in `C¹` on a convex set `s` and the derivative of
`G₀` is within `(4 (‖L⁻¹‖ + 1))⁻¹` of a fixed isomorphism `L` on `s`, then eventually every `G i`
is injective on `s` with invertible derivatives there. -/
theorem eventually_injOn_isInvertible_fderiv_of_mapCPConvergenceOn
    {G : ℕ → E → F} {G₀ : E → F} {s : Set E} (hs : Convex ℝ s) (L : E ≃L[ℝ] F)
    (hG₀ : ∀ y ∈ s, DifferentiableAt ℝ G₀ y)
    (hL : ∀ y ∈ s, ‖fderiv ℝ G₀ y - (L : E →L[ℝ] F)‖ ≤
      (4 * (‖(L.symm : F →L[ℝ] E)‖ + 1))⁻¹)
    (hGd : ∀ᶠ i in atTop, ∀ y ∈ s, DifferentiableAt ℝ (G i) y)
    (hconv : MapCPConvergenceOn s 1 G G₀) :
    ∀ᶠ i in atTop, InjOn (G i) s ∧ ∀ y ∈ s, (fderiv ℝ (G i) y).IsInvertible := by
  set c : ℝ := ‖(L.symm : F →L[ℝ] E)‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set ε : ℝ := (4 * (c + 1))⁻¹ with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨k0, hk0⟩ := hconv ε hεpos
  filter_upwards [hGd, eventually_ge_atTop k0] with i hdi hi
  have hD : ∀ y ∈ s, ‖fderiv ℝ (G i) y - (L : E →L[ℝ] F)‖ ≤ 2 * ε := by
    intro y hy
    have h1 := hk0 i hi 1 le_rfl y hy
    rw [mapDerivNorm, norm_iteratedFDeriv_one, fderiv_fun_sub (hdi y hy) (hG₀ y hy)] at h1
    calc ‖fderiv ℝ (G i) y - (L : E →L[ℝ] F)‖
        = ‖(fderiv ℝ (G i) y - fderiv ℝ G₀ y) + (fderiv ℝ G₀ y - (L : E →L[ℝ] F))‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖fderiv ℝ (G i) y - fderiv ℝ G₀ y‖ + ‖fderiv ℝ G₀ y - (L : E →L[ℝ] F)‖ :=
          norm_add_le _ _
      _ ≤ ε + ε := add_le_add h1 (hL y hy)
      _ = 2 * ε := by ring
  have hT : ∀ y ∈ s, ‖ContinuousLinearMap.id ℝ E -
      (L.symm : F →L[ℝ] E).comp (fderiv ℝ (G i) y)‖ ≤ 1 / 2 := by
    intro y hy
    have heq : ContinuousLinearMap.id ℝ E - (L.symm : F →L[ℝ] E).comp (fderiv ℝ (G i) y) =
        (L.symm : F →L[ℝ] E).comp ((L : E →L[ℝ] F) - fderiv ℝ (G i) y) := by
      ext v
      simp
    rw [heq]
    have hcε : c * (2 * ε) ≤ 1 / 2 := by
      rw [hε, ← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ c * ‖(L : E →L[ℝ] F) - fderiv ℝ (G i) y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ c * (2 * ε) := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hD y hy) hc0
      _ ≤ 1 / 2 := hcε
  have hdiff' : ∀ y ∈ s, DifferentiableAt ℝ (fun z => L.symm (G i z)) y := fun y hy =>
    L.symm.differentiableAt.comp y (hdi y hy)
  have hfd' : ∀ y ∈ s, fderiv ℝ (fun z => L.symm (G i z)) y =
      (L.symm : F →L[ℝ] E).comp (fderiv ℝ (G i) y) := fun y hy =>
    ((L.symm : F →L[ℝ] E).hasFDerivAt.comp y (hdi y hy).hasFDerivAt).fderiv
  refine ⟨?_, fun y hy => ?_⟩
  · have hinj := DifferentialGeometry.Coordinates.injOn_of_fderiv_near_id hs
      (G := fun z => L.symm (G i z)) (ε := 1 / 2) (by norm_num) hdiff'
      (fun y hy => by rw [hfd' y hy]; exact hT y hy)
    exact InjOn.of_comp (f := G i) (g := L.symm) hinj
  · have hTinv := DifferentialGeometry.Coordinates.isInvertible_of_norm_id_sub_lt
      ((hT y hy).trans_lt (by norm_num))
    exact (ContinuousLinearMap.isInvertible_equiv_comp (e := L.symm)).mp hTinv

end Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- The coordinate expression of a `C¹` map in arbitrary extended charts is `C¹` on the open set
where it is defined. -/
theorem contDiffOn_one_chartRep {f : A → B} (hf : ContMDiff I J 1 f) (p : A) (q : B) :
    ContDiffOn ℝ 1 (fun y => extChartAt J q (f ((extChartAt I p).symm y)))
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt J q).source)) :=
  contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_extChartAt (n := 1) (x := q)).comp
    ((hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).mono inter_subset_left)
    (fun y hy => by
      have h := hy.2
      simp only [mem_preimage, extChartAt_source] at h ⊢
      exact h))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ A] [FiniteDimensional ℝ E'] [J.Boundaryless]
  [IsManifold J ∞ B] in
theorem isOpen_chartRep_domain {f : A → B} (hf : Continuous f) (p : A) (q : B) :
    IsOpen ((extChartAt I p).target ∩
      (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt J q).source)) :=
  (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p)
    ((isOpen_extChartAt_source q).preimage hf)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- Invertibility of the derivative of the coordinate expression of `f` in arbitrary extended
charts is invertibility of `mfderiv f`. -/
theorem isInvertible_fderiv_chartRep_iff {f : A → B} (hf : ContMDiff I J 1 f) {p : A} {q : B}
    {y : E} (hy : y ∈ (extChartAt I p).target)
    (hfy : f ((extChartAt I p).symm y) ∈ (extChartAt J q).source) :
    (fderiv ℝ (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y).IsInvertible ↔
      (mfderiv I J f ((extChartAt I p).symm y)).IsInvertible := by
  set x := (extChartAt I p).symm y with hx
  have h1 : MDifferentiableAt J 𝓘(ℝ, E') (extChartAt J q) (f x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hfy)
  have h2 : MDifferentiableAt I J f x := hf.mdifferentiableAt one_ne_zero
  have h3 : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm y := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) hy
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') (fun y => extChartAt J q (f ((extChartAt I p).symm y))) y =
      (mfderiv J 𝓘(ℝ, E') (extChartAt J q) (f x)).comp
        ((mfderiv I J f x).comp (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y)) := by
    rw [show (fun y => extChartAt J q (f ((extChartAt I p).symm y))) =
        (extChartAt J q) ∘ (f ∘ (extChartAt I p).symm) from rfl,
      mfderiv_comp y h1 (h2.comp y h3), mfderiv_comp y h2 h3]
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

omit [IsManifold I ∞ A] [FiniteDimensional ℝ E'] [IsManifold J ∞ B] in
/-- **LU (local uniform `C⁰` convergence).** Chart-wise convergence `hs j → h` (any order `m`)
implies: for every `a` and every open `V ∋ h a`, some neighbourhood of `a` is eventually mapped
into `V` by every `hs j`. -/
theorem eventually_mapsTo_of_chart_tendsto {m : ℕ} {h : A → B} (hh : Continuous h)
    {hs : ℕ → A → B}
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))))
    (a : A) {V : Set B} (hV : IsOpen V) (haV : h a ∈ V) :
    ∃ N ∈ 𝓝 a, ∀ᶠ j in atTop, MapsTo (hs j) N V := by
  let rep : E → E' := fun y => extChartAt J (h a) (h ((extChartAt I a).symm y))
  let O : Set E := (extChartAt I a).target ∩
    (extChartAt I a).symm ⁻¹' (h ⁻¹' ((extChartAt J (h a)).source ∩ V))
  have hO : IsOpen O := (continuousOn_extChartAt_symm a).isOpen_inter_preimage
    (isOpen_extChartAt_target a) (((isOpen_extChartAt_source (h a)).inter hV).preimage hh)
  have hy₀ : extChartAt I a a ∈ O := by
    refine ⟨mem_extChartAt_target a, ?_⟩
    change h ((extChartAt I a).symm (extChartAt I a a)) ∈ (extChartAt J (h a)).source ∩ V
    rw [extChartAt_to_inv]
    exact ⟨mem_extChartAt_source (h a), haV⟩
  have hrepc : ContinuousOn rep O :=
    (continuousOn_extChartAt (h a)).comp
      ((hh.comp_continuousOn (continuousOn_extChartAt_symm a)).mono inter_subset_left)
      (fun y hy => hy.2.1)
  have hrepat : ContinuousAt rep (extChartAt I a a) := hrepc.continuousAt (hO.mem_nhds hy₀)
  let T : Set E' := (extChartAt J (h a)).target ∩ (extChartAt J (h a)).symm ⁻¹' V
  have hT : IsOpen T := (continuousOn_extChartAt_symm (h a)).isOpen_inter_preimage
    (isOpen_extChartAt_target (h a)) hV
  have hrep₀ : rep (extChartAt I a a) = extChartAt J (h a) (h a) := by
    simp only [rep, extChartAt_to_inv]
  have hrepT : rep (extChartAt I a a) ∈ T := by
    rw [hrep₀]
    refine ⟨mem_extChartAt_target (h a), ?_⟩
    change (extChartAt J (h a)).symm (extChartAt J (h a) (h a)) ∈ V
    rw [extChartAt_to_inv]
    exact haV
  obtain ⟨δ, hδ, hδT⟩ := Metric.isOpen_iff.mp hT _ hrepT
  obtain ⟨ρ₁, hρ₁, hρ₁O⟩ := Metric.isOpen_iff.mp hO _ hy₀
  obtain ⟨ρ₂, hρ₂, hρ₂c⟩ := Metric.continuousAt_iff.mp hrepat (δ / 2) (half_pos hδ)
  set ρ : ℝ := min ρ₁ ρ₂ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ₁' : ρ < ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hρ₂' : ρ < ρ₂ := by rw [hρdef]; linarith [min_le_right ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hKO : closedBall (extChartAt I a a) ρ ⊆ O := fun y hy =>
    hρ₁O (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hρ₁'))
  obtain ⟨hev, hcv⟩ := hconv a (h a) (closedBall (extChartAt I a a) ρ)
    (isCompact_closedBall _ _) (fun y hy => (hKO hy).1) (fun y hy => (hKO hy).2.1)
  have hunif := tendstoUniformlyOn_of_cPConvergence (hcv.mono_order (Nat.zero_le m))
  refine ⟨(extChartAt I a).source ∩ extChartAt I a ⁻¹' ball (extChartAt I a a) ρ,
    inter_mem (extChartAt_source_mem_nhds a)
      ((continuousAt_extChartAt a).preimage_mem_nhds (ball_mem_nhds _ hρ)), ?_⟩
  filter_upwards [hev, Metric.tendstoUniformlyOn_iff.mp hunif (δ / 2) (half_pos hδ)]
    with j hj1 hj2 x hx
  have hyK : extChartAt I a x ∈ closedBall (extChartAt I a a) ρ := ball_subset_closedBall hx.2
  have hxx : (extChartAt I a).symm (extChartAt I a x) = x := (extChartAt I a).left_inv hx.1
  have hsrc : hs j x ∈ (extChartAt J (h a)).source := by
    have := hj1 hyK
    simp only [hxx] at this
    exact this
  have hd1 := hj2 _ hyK
  simp only [hxx] at hd1
  have hrepx : rep (extChartAt I a x) = extChartAt J (h a) (h x) := by simp only [rep, hxx]
  have hd2 : dist (extChartAt J (h a) (h x)) (rep (extChartAt I a a)) < δ / 2 := by
    rw [← hrepx]
    exact hρ₂c ((mem_closedBall.mp hyK).trans_lt hρ₂')
  have hin : extChartAt J (h a) (hs j x) ∈ ball (rep (extChartAt I a a)) δ := by
    rw [mem_ball]
    calc dist (extChartAt J (h a) (hs j x)) (rep (extChartAt I a a))
        ≤ dist (extChartAt J (h a) (hs j x)) (extChartAt J (h a) (h x)) +
          dist (extChartAt J (h a) (h x)) (rep (extChartAt I a a)) := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by
          rw [dist_comm] at hd1
          exact add_lt_add hd1 hd2
      _ = δ := by ring
  have hV' := (hδT hin).2
  change (extChartAt J (h a)).symm (extChartAt J (h a) (hs j x)) ∈ V at hV'
  rwa [(extChartAt J (h a)).left_inv hsrc] at hV'

omit [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- **Local step of W2.** If `hs j → h` chart-wise in `C^m`, `1 ≤ m`, all maps are `C¹` and
`mfderiv h a` is invertible, then on one open neighbourhood `N` of `a` eventually every `hs j` is
injective with invertible `mfderiv`. -/
theorem exists_isOpen_eventually_injOn_isInvertible_mfderiv {m : ℕ} (hm : 1 ≤ m) {h : A → B}
    (hh : ContMDiff I J 1 h) {hs : ℕ → A → B} (hsm : ∀ j, ContMDiff I J 1 (hs j))
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))))
    {a : A} (ha : (mfderiv I J h a).IsInvertible) :
    ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∀ᶠ j in atTop,
      InjOn (hs j) N ∧ ∀ x ∈ N, (mfderiv I J (hs j) x).IsInvertible := by
  let rep : E → E' := fun y => extChartAt J (h a) (h ((extChartAt I a).symm y))
  let O : Set E := (extChartAt I a).target ∩
    (extChartAt I a).symm ⁻¹' (h ⁻¹' (extChartAt J (h a)).source)
  have hO : IsOpen O := isOpen_chartRep_domain (I := I) (J := J) hh.continuous a (h a)
  have hsrc₀ : h ((extChartAt I a).symm (extChartAt I a a)) ∈ (extChartAt J (h a)).source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source (h a)
  have hy₀ : extChartAt I a a ∈ O := ⟨mem_extChartAt_target a, hsrc₀⟩
  have hrep : ContDiffOn ℝ 1 rep O := contDiffOn_one_chartRep hh a (h a)
  have hinv₀ : (fderiv ℝ rep (extChartAt I a a)).IsInvertible := by
    refine (isInvertible_fderiv_chartRep_iff hh (mem_extChartAt_target a) hsrc₀).mpr ?_
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
    (isCompact_closedBall _ _) (fun y hy => (hKO hy).1) (fun y hy => (hKO hy).2)
  have hGd : ∀ᶠ j in atTop, ∀ y ∈ closedBall (extChartAt I a a) ρ,
      DifferentiableAt ℝ (fun y => extChartAt J (h a) (hs j ((extChartAt I a).symm y))) y := by
    filter_upwards [hev] with j hj y hy
    have hOj := isOpen_chartRep_domain (I := I) (J := J) (hsm j).continuous a (h a)
    have hyO : y ∈ (extChartAt I a).target ∩
        (extChartAt I a).symm ⁻¹' (hs j ⁻¹' (extChartAt J (h a)).source) :=
      ⟨(hKO hy).1, hj hy⟩
    exact ((contDiffOn_one_chartRep (hsm j) a (h a)).differentiableOn one_ne_zero y hyO).differentiableAt
      (hOj.mem_nhds hyO)
  have hker := eventually_injOn_isInvertible_fderiv_of_mapCPConvergenceOn
    (convex_closedBall _ ρ) L hdiff₀ hLK hGd (hcv.mono_order hm)
  refine ⟨(extChartAt I a).source ∩ extChartAt I a ⁻¹' ball (extChartAt I a a) ρ,
    (continuousOn_extChartAt a).isOpen_inter_preimage (isOpen_extChartAt_source a) isOpen_ball,
    ⟨mem_extChartAt_source a, mem_ball_self hρ⟩, ?_⟩
  filter_upwards [hker, hev] with j hj hjmap
  refine ⟨fun x hx x' hx' hxx' => ?_, fun x hx => ?_⟩
  · refine (extChartAt I a).injOn hx.1 hx'.1 ?_
    refine hj.1 (ball_subset_closedBall hx.2) (ball_subset_closedBall hx'.2) ?_
    change extChartAt J (h a) (hs j ((extChartAt I a).symm (extChartAt I a x))) =
      extChartAt J (h a) (hs j ((extChartAt I a).symm (extChartAt I a x')))
    rw [(extChartAt I a).left_inv hx.1, (extChartAt I a).left_inv hx'.1, hxx']
  · have hyK : extChartAt I a x ∈ closedBall (extChartAt I a a) ρ := ball_subset_closedBall hx.2
    have h1 := (isInvertible_fderiv_chartRep_iff (hsm j) (hKO hyK).1 (hjmap hyK)).mp (hj.2 _ hyK)
    rwa [(extChartAt I a).left_inv hx.1] at h1

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
