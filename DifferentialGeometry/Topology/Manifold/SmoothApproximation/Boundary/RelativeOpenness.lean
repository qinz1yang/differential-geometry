import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.InverseSmooth
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.RelativeManifoldValued
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.ChartConvergence
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.InteriorChart
import Mathlib.Topology.Connected.Clopen

/-!
# Openness of diffeomorphisms relative to the boundary (W2 with boundary)

`eventually_exists_diffeomorph_of_rel_chart_tendsto`: let `h : A ≃ₘ^n⟮I, J⟯ B` be a `C^n`
diffeomorphism (`1 ≤ n`) of manifolds whose models may have boundary, `A` compact Hausdorff, `h`
smooth on an open `O ⊇ ∂A`. If smooth maps `hs j` agree with `h` on `O`, converge to `h` locally
uniformly, and converge chart-wise in `C^m` (`1 ≤ m`) on compact subsets of chart targets inside
the interior of the model range, then eventually every `hs j` is a smooth diffeomorphism of
manifolds with boundary.

Local step at interior points (`exists_isOpen_eventually_injOn_isLocalDiffeomorphAt`): the
Euclidean kernel `eventually_injOn_isInvertible_fderiv_of_mapCPConvergenceOn` on a small ball of
the interior chart, the interior charts `interiorChart` as coordinates, and
`DifferentiableAt.mem_interior_convex_of_surjective_fderiv` to keep the images interior. On `O`
the maps equal `h`, a smooth local diffeomorphism there by `isLocalDiffeomorphAt_of_eqOn_diffeomorph`.
The global step is W-1's: separation off the pieces, clopen range, components.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ A] in
/-- The interior of an extended chart target is its part in the interior of the model range. -/
theorem interior_extChartAt_target (p : A) :
    interior (extChartAt I p).target = (extChartAt I p).target ∩ interior (range I) := by
  apply Subset.antisymm
  · exact subset_inter interior_subset (interior_mono (extChartAt_target_subset_range p))
  · exact interior_maximal inter_subset_left (isOpen_extChartAt_target_inter_interior p)

omit [FiniteDimensional ℝ E'] in
/-- **Local step at an interior point.** -/
theorem exists_isOpen_eventually_injOn_isLocalDiffeomorphAt {m : ℕ} (hm : 1 ≤ m)
    {h : A → B} (hh : ContMDiff I J 1 h) {hs : ℕ → A → B} (hsm : ∀ j, ContMDiff I J ∞ (hs j))
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        K ⊆ interior (range I) →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))))
    {a : A} (ha : I.IsInteriorPoint a) (hinv : (mfderiv I J h a).IsInvertible) :
    ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∀ᶠ j in atTop,
      InjOn (hs j) N ∧ ∀ x ∈ N, IsLocalDiffeomorphAt I J ∞ (hs j) x := by
  have : IsManifold J 1 B := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold I 1 A := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  set φ := extChartAt I a with hφ
  set ψ := extChartAt J (h a) with hψ
  let rep : E → E' := fun y => ψ (h (φ.symm y))
  have hcontφ : ContinuousOn φ.symm (interior φ.target) :=
    (continuousOn_extChartAt_symm a).mono interior_subset
  set Ob : Set E := interior φ.target ∩ φ.symm ⁻¹' (h ⁻¹' ψ.source) with hObdef
  have hOb : IsOpen Ob := hcontφ.isOpen_inter_preimage isOpen_interior
    ((isOpen_extChartAt_source (h a)).preimage hh.continuous)
  have hy₀int : φ a ∈ interior φ.target := I.isInteriorPoint_iff.mp ha
  have hy₀ : φ a ∈ Ob := by
    refine ⟨hy₀int, ?_⟩
    change h (φ.symm (φ a)) ∈ ψ.source
    rw [hφ, extChartAt_to_inv]
    exact mem_extChartAt_source (h a)
  have hrepOn : ∀ {g : A → B} {k : ℕ∞}, ContMDiff I J k g →
      ContDiffOn ℝ k (fun y => ψ (g (φ.symm y)))
        (interior φ.target ∩ φ.symm ⁻¹' (g ⁻¹' ψ.source)) := by
    intro g k hg
    apply contMDiffOn_iff_contDiffOn.mp
    refine ((contMDiffOn_extChartAt (n := ∞) (x := h a)).of_le (by exact_mod_cast le_top)).comp
      (hg.comp_contMDiffOn
        (((contMDiffOn_extChartAt_symm (n := ∞) a).of_le (by exact_mod_cast le_top)).mono
          fun y hy => interior_subset hy.1)) ?_
    intro y hy
    have := hy.2
    rw [mem_preimage, mem_preimage, hψ, extChartAt_source] at this
    exact this
  have hrep : ContDiffOn ℝ 1 rep Ob := hrepOn hh
  have hinv₀ : (fderiv ℝ rep (φ a)).IsInvertible := by
    have hmd : MDifferentiableAt I J h a := hh.mdifferentiableAt one_ne_zero
    have hrange : range I ∈ 𝓝 (φ a) :=
      mem_interior_iff_mem_nhds.mp (interior_mono (extChartAt_target_subset_range a) hy₀int)
    have heq : mfderiv I J h a = fderiv ℝ rep (φ a) := by
      rw [hmd.mfderiv, fderivWithin_of_mem_nhds hrange]
      rfl
    rw [← heq]
    exact hinv
  obtain ⟨L, hL⟩ := hinv₀
  set ε : ℝ := (4 * (‖(L.symm : E' →L[ℝ] E)‖ + 1))⁻¹ with hεdef
  have hε : 0 < ε := by positivity
  have hDc : ContinuousOn (fderiv ℝ rep) Ob := hrep.continuousOn_fderiv_of_isOpen hOb le_rfl
  obtain ⟨ρ₁, hρ₁, hρ₁O⟩ := Metric.isOpen_iff.mp hOb _ hy₀
  obtain ⟨ρ₂, hρ₂, hρ₂c⟩ :=
    Metric.continuousAt_iff.mp (hDc.continuousAt (hOb.mem_nhds hy₀)) ε hε
  set ρ : ℝ := min ρ₁ ρ₂ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ₁' : ρ < ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hρ₂' : ρ < ρ₂ := by rw [hρdef]; linarith [min_le_right ρ₁ ρ₂, lt_min hρ₁ hρ₂]
  have hKO : closedBall (φ a) ρ ⊆ Ob := fun y hy =>
    hρ₁O (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hρ₁'))
  have hLK : ∀ y ∈ closedBall (φ a) ρ, ‖fderiv ℝ rep y - (L : E →L[ℝ] E')‖ ≤ ε := fun y hy => by
    rw [hL, ← dist_eq_norm]
    exact (hρ₂c ((mem_closedBall.mp hy).trans_lt hρ₂')).le
  have hdiff₀ : ∀ y ∈ closedBall (φ a) ρ, DifferentiableAt ℝ rep y := fun y hy =>
    (hrep.differentiableOn one_ne_zero y (hKO hy)).differentiableAt (hOb.mem_nhds (hKO hy))
  have hKt : closedBall (φ a) ρ ⊆ φ.target := fun y hy => interior_subset (hKO hy).1
  have hKi : closedBall (φ a) ρ ⊆ interior (range I) := fun y hy => by
    have := (hKO hy).1
    rw [interior_extChartAt_target] at this
    exact this.2
  obtain ⟨hev, hcv⟩ := hconv a (h a) (closedBall (φ a) ρ) (isCompact_closedBall _ _) hKt hKi
    (fun y hy => (hKO hy).2)
  have hObj : ∀ j, IsOpen (interior φ.target ∩ φ.symm ⁻¹' (hs j ⁻¹' ψ.source)) := fun j =>
    hcontφ.isOpen_inter_preimage isOpen_interior
      ((isOpen_extChartAt_source (h a)).preimage (hsm j).continuous)
  have hGd : ∀ᶠ j in atTop, ∀ y ∈ closedBall (φ a) ρ,
      DifferentiableAt ℝ (fun y => ψ (hs j (φ.symm y))) y := by
    filter_upwards [hev] with j hj y hy
    have hyO : y ∈ interior φ.target ∩ φ.symm ⁻¹' (hs j ⁻¹' ψ.source) := ⟨(hKO hy).1, hj hy⟩
    exact (((hrepOn (k := 1) ((hsm j).of_le (by exact_mod_cast le_top))).differentiableOn
      one_ne_zero) y hyO).differentiableAt ((hObj j).mem_nhds hyO)
  have hker := eventually_injOn_isInvertible_fderiv_of_mapCPConvergenceOn
    (convex_closedBall _ ρ) L hdiff₀ hLK hGd (hcv.mono_order hm)
  refine ⟨φ.source ∩ φ ⁻¹' (interior φ.target ∩ ball (φ a) ρ),
    (continuousOn_extChartAt a).isOpen_inter_preimage (isOpen_extChartAt_source a)
      (isOpen_interior.inter isOpen_ball),
    ⟨mem_extChartAt_source a, hy₀int, mem_ball_self hρ⟩, ?_⟩
  filter_upwards [hker, hev] with j hj hjmap
  refine ⟨fun x hx x' hx' hxx' => ?_, fun x hx => ?_⟩
  · refine φ.injOn hx.1 hx'.1 ?_
    refine hj.1 (ball_subset_closedBall hx.2.2) (ball_subset_closedBall hx'.2.2) ?_
    change ψ (hs j (φ.symm (φ x))) = ψ (hs j (φ.symm (φ x')))
    rw [φ.left_inv hx.1, φ.left_inv hx'.1, hxx']
  · -- coordinates: interior charts at `a` and `h a`
    let c := interiorChart I ∞ a
    let d := interiorChart J ∞ (h a)
    have hxc : x ∈ c.source := by
      refine ⟨?_, hx.2.1⟩
      have := hx.1
      rwa [hφ, extChartAt_source] at this
    have hballOb : ball (φ a) ρ ⊆ interior φ.target ∩ φ.symm ⁻¹' (hs j ⁻¹' ψ.source) :=
      fun y hy => ⟨(hKO (ball_subset_closedBall hy)).1, hjmap (ball_subset_closedBall hy)⟩
    have hsmball : ContDiffOn ℝ ∞ (fun y => ψ (hs j (φ.symm y))) (ball (φ a) ρ) :=
      (hrepOn (k := ⊤) (hsm j)).mono hballOb
    refine DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_coordinates c d isOpen_ball
      hxc hx.2.2 ?_ (by exact hsmball) fun z hz => by exact hj.2 z (ball_subset_closedBall hz)
    intro z hz
    have hsrc : hs j (φ.symm z) ∈ ψ.source := hjmap (ball_subset_closedBall hz)
    change hs j (φ.symm z) ∈ (chartAt H' (h a)).source ∩ ψ ⁻¹' interior ψ.target
    refine ⟨?_, ?_⟩
    · rw [hψ, extChartAt_source] at hsrc
      exact hsrc
    · change ψ (hs j (φ.symm z)) ∈ interior ψ.target
      rw [hψ, interior_extChartAt_target, ← hψ]
      refine ⟨ψ.map_source hsrc, ?_⟩
      have hdz : DifferentiableAt ℝ (fun y => ψ (hs j (φ.symm y))) z :=
        (hsmball.differentiableOn (by simp) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
      refine hdz.mem_interior_convex_of_surjective_fderiv (isOpen_ball.mem_nhds hz)
        J.convex_range J.isClosed_range J.nonempty_interior ?_
        (hj.2 z (ball_subset_closedBall hz)).surjective
      intro w hw
      exact extChartAt_target_subset_range (h a)
        (ψ.map_source (hjmap (ball_subset_closedBall hw)))

variable [T2Space A] [CompactSpace A]

omit [FiniteDimensional ℝ E'] in
/-- **W2 relative to the boundary.** Smooth maps that agree with a `C^n` diffeomorphism `h`
(`1 ≤ n`) on an open `O ⊇ ∂A` where `h` is smooth, converge to it locally uniformly and
chart-wise in `C^m` (`1 ≤ m`) on interior compacta, are eventually smooth diffeomorphisms of
manifolds with boundary. -/
theorem eventually_exists_diffeomorph_of_rel_chart_tendsto {n : ℕ∞ω} (hn : 1 ≤ n)
    (h : A ≃ₘ^n⟮I, J⟯ B) {m : ℕ} (hm : 1 ≤ m) {O : Set A} (hO : IsOpen O)
    (hbO : I.boundary A ⊆ O) (hsmO : ContMDiffOn I J ∞ h O)
    {hs : ℕ → A → B} (hsm : ∀ j, ContMDiff I J ∞ (hs j)) (heq : ∀ j, EqOn (hs j) h O)
    (hLU : ∀ (a : A) (V : Set B), IsOpen V → h a ∈ V →
      ∃ N ∈ 𝓝 a, ∀ᶠ j in atTop, MapsTo (hs j) N V)
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        K ⊆ interior (range I) →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y)))) :
    ∀ᶠ j in atTop, ∃ Φ : A ≃ₘ⟮I, J⟯ B, ⇑Φ = hs j := by
  have hh1 : ContMDiff I J 1 h := h.contMDiff.of_le hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have hinv : ∀ a, (mfderiv I J h a).IsInvertible := fun a => h.isInvertible_mfderiv hn0
  have : T2Space B := h.toHomeomorph.symm.isEmbedding.t2Space
  have : CompactSpace B := h.toHomeomorph.compactSpace
  have : LocallyPathConnectedSpace (range J) := J.convex_range.locallyPathConnectedSpace
  have : LocallyConnectedSpace H' :=
    J.isClosedEmbedding.isEmbedding.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  have : LocallyConnectedSpace B := ChartedSpace.locallyConnectedSpace H' B
  -- local pieces
  have hpiece : ∀ a : A, ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∀ᶠ j in atTop,
      InjOn (hs j) N ∧ ∀ x ∈ N, IsLocalDiffeomorphAt I J ∞ (hs j) x := by
    intro a
    by_cases haO : a ∈ O
    · refine ⟨O, hO, haO, Eventually.of_forall fun j => ⟨?_, fun x hx =>
        isLocalDiffeomorphAt_of_eqOn_diffeomorph hn h hO hsmO (heq j) hx⟩⟩
      intro x hx x' hx' hxx'
      rw [heq j hx, heq j hx'] at hxx'
      exact h.injective hxx'
    · have ha : I.IsInteriorPoint a := by
        rw [I.isInteriorPoint_iff_not_isBoundaryPoint]
        exact fun hb => haO (hbO hb)
      exact exists_isOpen_eventually_injOn_isLocalDiffeomorphAt hm hh1 hsm hconv ha (hinv a)
  choose N hNo haN hNev using hpiece
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.2 ⟨x, haN x⟩)
  have hpieces : ∀ᶠ j in atTop, ∀ a ∈ t,
      InjOn (hs j) (N a) ∧ ∀ x ∈ N a, IsLocalDiffeomorphAt I J ∞ (hs j) x :=
    (eventually_all_finset t).2 fun a _ => hNev a
  -- separation off the pieces
  set Z : Set (A × A) := univ \ ⋃ a ∈ t, N a ×ˢ N a with hZdef
  have hZ : IsCompact Z :=
    isCompact_univ.diff (isOpen_biUnion fun a _ => (hNo a).prod (hNo a))
  have hsep : ∀ᶠ j in atTop, ∀ z ∈ Z, hs j z.1 ≠ hs j z.2 := by
    refine eventually_forall_mem_of_isCompact_nhdsWithin hZ ?_
    rintro ⟨x, x'⟩ hz
    have hne : x ≠ x' := by
      rintro rfl
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact hz.2 (mem_iUnion₂.2 ⟨a, ha, ⟨hxa, hxa⟩⟩)
    obtain ⟨V₁, V₂, hV₁, hV₂, hx₁, hx₂, hdisj⟩ := t2_separation (h.injective.ne hne)
    obtain ⟨N₁, hN₁, hev₁⟩ := hLU x V₁ hV₁ hx₁
    obtain ⟨N₂, hN₂, hev₂⟩ := hLU x' V₂ hV₂ hx₂
    refine ⟨N₁ ×ˢ N₂, prod_mem_nhds hN₁ hN₂, ?_⟩
    filter_upwards [hev₁, hev₂] with j hj₁ hj₂ z hz'
    exact hdisj.ne_of_mem (hj₁ hz'.2.1) (hj₂ hz'.2.2)
  -- every connected component of `B` is eventually met
  obtain ⟨t', ht'⟩ := isCompact_univ.elim_finite_subcover (fun b : B => connectedComponent b)
    (fun _ => isOpen_connectedComponent) (fun b _ => mem_iUnion.2 ⟨b, mem_connectedComponent⟩)
  have hcomp : ∀ᶠ j in atTop, ∀ b ∈ t', hs j (h.symm b) ∈ connectedComponent b := by
    refine (eventually_all_finset t').2 fun b _ => ?_
    have hb : h (h.symm b) ∈ connectedComponent b := by
      rw [h.apply_symm_apply]
      exact mem_connectedComponent
    obtain ⟨N', hN', hev⟩ := hLU (h.symm b) _ isOpen_connectedComponent hb
    exact hev.mono fun j hj => hj (mem_of_mem_nhds hN')
  filter_upwards [hpieces, hsep, hcomp] with j hpj hsj hcj
  have hloc : IsLocalDiffeomorph I J ∞ (hs j) := by
    intro x
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact (hpj a ha).2 x hxa
  have hinj : Injective (hs j) := by
    intro x x' hxx
    by_contra hne
    by_cases hz : (x, x') ∈ Z
    · exact hsj _ hz hxx
    · have hmem : (x, x') ∈ ⋃ a ∈ t, N a ×ˢ N a := by
        by_contra hc
        exact hz ⟨mem_univ _, hc⟩
      obtain ⟨a, ha, hxa, hxa'⟩ := mem_iUnion₂.1 hmem
      exact hne ((hpj a ha).1 hxa hxa' hxx)
  have hsurj : Surjective (hs j) := by
    have hclopen : IsClopen (range (hs j)) :=
      ⟨(isCompact_range (hsm j).continuous).isClosed, hloc.isOpenMap.isOpen_range⟩
    intro y
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 (ht' (mem_univ y))
    exact isPreconnected_connectedComponent.subset_isClopen hclopen
      ⟨_, hcj b hb, mem_range_self _⟩ hyb
  exact ⟨hloc.diffeomorphOfBijective ⟨hinj, hsurj⟩, rfl⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
