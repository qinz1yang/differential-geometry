import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.RelativeEuclidean
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.EventualCongruence
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteLocality

/-!
# Relative smooth approximation of maps between manifolds with boundary

`exists_smooth_seq_rel_chart_tendsto`: let `A`, `B` be compact Hausdorff manifolds whose models may
have boundary, `h : A → B` a `C^k` map, smooth on an open `O ⊇ ∂A`, sending interior points to
interior points. Then there are an open `O' ⊇ ∂A`, `O' ⊆ O`, and smooth maps `hs j : A → B` with
`hs j = h` on `O'` for every `j`, converging to `h` locally uniformly and chart-wise in `C^k` on
every compact subset of a chart target lying in the interior of the model range.

Route: `h(A ∖ O')` is a compact subset of `int B`; a Whitney embedding `e` of `B` and a smooth
retraction `r` near `e '' h(A ∖ O')` (`exists_smooth_retraction_near_interior_compact`); the
relative Euclidean approximants `us j` of `e ∘ h` (equal to `e ∘ h` on `O'`); then
`hs j x = r (us j x)` where `us j x ∈ U` and `h x` otherwise. On `O'` both formulas give `h`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

theorem eventually_forall_mem_of_isCompact_nhdsWithin {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {P : ℕ → X → Prop}
    (hP : ∀ x ∈ S, ∃ N ∈ 𝓝 x, ∀ᶠ j in atTop, ∀ z ∈ S ∩ N, P j z) :
    ∀ᶠ j in atTop, ∀ z ∈ S, P j z := by
  refine hS.induction_on (p := fun T => ∀ᶠ j in atTop, ∀ z ∈ T, P j z) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun _ _ hz => hz.elim
  · intro s t hst ht
    exact ht.mono fun j hj z hz => hj z (hst hz)
  · intro s t hs ht
    filter_upwards [hs, ht] with j hj1 hj2 z hz
    exact hz.elim (hj1 z) (hj2 z)
  · intro x hx
    obtain ⟨N, hN, hev⟩ := hP x hx
    refine ⟨S ∩ N, inter_mem_nhdsWithin S hN, hev⟩

theorem eventually_mem_of_tendstoUniformly_of_isCompact {α X : Type*} [PseudoMetricSpace X]
    {fs : ℕ → α → X} {f : α → X} (hu : TendstoUniformly fs f atTop) {C V : Set X}
    (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) :
    ∀ᶠ j in atTop, ∀ x, f x ∈ C → fs j x ∈ V := by
  obtain ⟨δ, hδ, hsub⟩ := hC.exists_thickening_subset_open hV hCV
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with j hj x hx
  exact hsub (Metric.mem_thickening_iff.mpr ⟨f x, hx, by rw [dist_comm]; exact hj x⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B] [CompactSpace B]

/-- **Relative smooth approximation (manifold values, boundary allowed).** -/
theorem exists_smooth_seq_rel_chart_tendsto (k : ℕ) {h : A → B} (hh : ContMDiff I J k h)
    {O : Set A} (hO : IsOpen O) (hbO : I.boundary A ⊆ O) (hsm : ContMDiffOn I J ∞ h O)
    (hint : ∀ x, I.IsInteriorPoint x → J.IsInteriorPoint (h x)) :
    ∃ (O' : Set A) (hs : ℕ → A → B), IsOpen O' ∧ I.boundary A ⊆ O' ∧ O' ⊆ O ∧
      (∀ j, ContMDiff I J ∞ (hs j)) ∧ (∀ j, EqOn (hs j) h O') ∧
      (∀ (a : A) (V : Set B), IsOpen V → h a ∈ V →
        ∃ N ∈ 𝓝 a, ∀ᶠ j in atTop, MapsTo (hs j) N V) ∧
      ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        K ⊆ interior (range I) →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K k (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))) := by
  classical
  have h0 : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨O', hO', hbO', hO'O⟩ :=
    normal_exists_closure_subset (I.isClosed_boundary h0) hO hbO
  have hO'O₀ : O' ⊆ O := subset_closure.trans hO'O
  have hCc : IsCompact (h '' O'ᶜ) := (hO'.isClosed_compl.isCompact).image hh.continuous
  have hCi : h '' O'ᶜ ⊆ J.interior B := by
    rintro _ ⟨x, hx, rfl⟩
    refine hint x ?_
    rw [I.isInteriorPoint_iff_not_isBoundaryPoint]
    exact fun hb => hx (hbO' hb)
  rcases (h '' O'ᶜ).eq_empty_or_nonempty with hempty | hne
  · -- `O' = univ`: `h` itself is smooth
    have hO'u : ∀ x, x ∈ O' := fun x => by
      by_contra hx
      exact (hempty ▸ (mem_image_of_mem h hx) : h x ∈ (∅ : Set B))
    have hhs : ContMDiff I J ∞ h := fun x => hsm.contMDiffAt (hO.mem_nhds (hO'O₀ (hO'u x)))
    refine ⟨O', fun _ => h, hO', hbO', hO'O₀, fun _ => hhs, fun _ => eqOn_refl _ _,
      fun a V hV ha => ⟨h ⁻¹' V, hh.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds ha),
        Eventually.of_forall fun _ _ hx => hx⟩, ?_⟩
    intro p q K _ _ _ hKmap
    exact ⟨Eventually.of_forall fun _ => hKmap, MapCPConvergenceOn.const_seq _⟩
  obtain ⟨N, e, he, hemb, hi⟩ := exists_embedding_euclidean_of_compact (I := J) (M := B)
  obtain ⟨r, U, hU, hCU, hr, -, hleft⟩ :=
    exists_smooth_retraction_near_interior_compact he hemb.isEmbedding (fun x _ => hi x)
      hCc hCi hne
  set u : A → EuclideanSpace ℝ (Fin N) := fun x => e (h x) with hudef
  have hu : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) k u :=
    (he.of_le (by exact_mod_cast le_top)).comp hh
  have husm : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ u O :=
    he.comp_contMDiffOn hsm
  obtain ⟨us, hus, husO', hunif, hchart⟩ :=
    exists_smooth_seq_rel_chart_tendsto_normedSpace k hu hO hbO' hO'O husm
  have huC : IsCompact (e '' (h '' O'ᶜ)) := hCc.image he.continuous
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (eventually_mem_of_tendstoUniformly_of_isCompact hunif huC hU hCU)
  have husU : ∀ j x, x ∉ O' → us (j + j₀) x ∈ U := fun j x hx =>
    hj₀ (j + j₀) (Nat.le_add_left j₀ j) x ⟨h x, ⟨x, hx, rfl⟩, rfl⟩
  have hshift : StrictMono fun j : ℕ => j + j₀ := fun a b hab => Nat.add_lt_add_right hab j₀
  set hs : ℕ → A → B := fun j x => if us (j + j₀) x ∈ U then r (us (j + j₀) x) else h x
    with hsdef
  have hsO' : ∀ j, EqOn (hs j) h O' := by
    intro j x hx
    simp only [hsdef]
    split_ifs with hU'
    · have hux : us (j + j₀) x = e (h x) := husO' (j + j₀) hx
      rw [hux] at hU' ⊢
      exact hleft (h x) hU'
    · rfl
  have hsU : ∀ j x, us (j + j₀) x ∈ U → hs j x = r (us (j + j₀) x) := by
    intro j x hx
    simp only [hsdef, hx, ↓reduceIte]
  have hssm : ∀ j, ContMDiff I J ∞ (hs j) := by
    intro j x
    by_cases hx : us (j + j₀) x ∈ U
    · have hev : ∀ᶠ y in 𝓝 x, us (j + j₀) y ∈ U :=
        (hus (j + j₀)).continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      have hcomp : ContMDiffAt I J ∞ (fun y => r (us (j + j₀) y)) x :=
        (hr.contMDiffAt (hU.mem_nhds hx)).comp x ((hus (j + j₀)) x)
      exact hcomp.congr_of_eventuallyEq (hev.mono fun y hy => hsU j y hy)
    · have hxO' : x ∈ O' := by
        by_contra hc
        exact hx (husU j x hc)
      have hcomp : ContMDiffAt I J ∞ h x := hsm.contMDiffAt (hO.mem_nhds (hO'O₀ hxO'))
      exact hcomp.congr_of_eventuallyEq
        (Filter.eventually_of_mem (hO'.mem_nhds hxO') fun y hy => hsO' j hy)
  refine ⟨O', hs, hO', hbO', hO'O₀, hssm, hsO', ?_, ?_⟩
  · -- local uniform convergence
    intro a V hV ha
    by_cases haO' : a ∈ O'
    · refine ⟨O' ∩ h ⁻¹' V, inter_mem (hO'.mem_nhds haO')
        (hh.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds ha)), ?_⟩
      exact Eventually.of_forall fun j x hx => by rw [hsO' j hx.1]; exact hx.2
    · have huaU : u a ∈ U := hCU ⟨h a, ⟨a, haO', rfl⟩, rfl⟩
      have hra : r (u a) = h a := hleft (h a) huaU
      have hW : U ∩ r ⁻¹' V ∈ 𝓝 (u a) :=
        inter_mem (hU.mem_nhds huaU)
          ((hr.continuousOn.continuousAt (hU.mem_nhds huaU)).preimage_mem_nhds
            (hV.mem_nhds (by rw [hra]; exact ha)))
      obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
      refine ⟨u ⁻¹' ball (u a) (δ / 2),
        hu.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (by positivity)), ?_⟩
      have hev := (tendsto_add_atTop_nat j₀).eventually
        (Metric.tendstoUniformly_iff.mp hunif (δ / 2) (by positivity))
      filter_upwards [hev] with j hj x hx
      have hx' : dist (u x) (u a) < δ / 2 := hx
      have hmem : us (j + j₀) x ∈ ball (u a) δ := by
        rw [mem_ball]
        calc dist (us (j + j₀) x) (u a)
            ≤ dist (us (j + j₀) x) (u x) + dist (u x) (u a) := dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := by
            refine add_lt_add ?_ hx'
            rw [dist_comm]
            exact hj x
          _ = δ := add_halves δ
      have h2 := hδW hmem
      rw [hsU j x h2.1]
      exact h2.2
  · intro p q K hK hKt hKi hKmap
    set φ := extChartAt I p with hφ
    set ψ := extChartAt J q with hψ
    have hU₀ : IsOpen (φ.target ∩ interior (range I)) :=
      isOpen_extChartAt_target_inter_interior p
    have hcont : ContinuousOn φ.symm (φ.target ∩ interior (range I)) :=
      (continuousOn_extChartAt_symm p).mono inter_subset_left
    have hBinf : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun y => u (φ.symm y)) φ.target :=
      contMDiffOn_iff_contDiffOn.mp (hu.comp_contMDiffOn
        ((contMDiffOn_extChartAt_symm (n := ∞) p).of_le (by exact_mod_cast le_top)))
    have hBj : ∀ j, ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞)
        (fun y => us (j + j₀) (φ.symm y)) φ.target := fun j =>
      (contMDiffOn_iff_contDiffOn.mp ((hus (j + j₀)).comp_contMDiffOn
        (contMDiffOn_extChartAt_symm p))).of_le (by exact_mod_cast le_top)
    set Vt : Set (EuclideanSpace ℝ (Fin N)) := U ∩ r ⁻¹' ψ.source with hVtdef
    have hVt : IsOpen Vt :=
      hr.continuousOn.isOpen_inter_preimage hU (isOpen_extChartAt_source q)
    have hΨ : ContDiffOn ℝ ∞ (fun z => ψ (r z)) Vt := by
      apply contMDiffOn_iff_contDiffOn.mp
      refine (contMDiffOn_extChartAt (x := q)).comp (hr.mono inter_subset_left) ?_
      intro z hz
      have hz2 := hz.2
      rw [mem_preimage, hψ, extChartAt_source] at hz2
      exact hz2
    -- local statement at each point of `K`
    have hloc : ∀ y ∈ K, ∃ Vy ∈ 𝓝 y,
        (∀ᶠ j in atTop, ∀ z ∈ K ∩ Vy, hs j (φ.symm z) ∈ ψ.source) ∧
        MapCPConvergenceOn (K ∩ Vy) k (fun j z => ψ (hs j (φ.symm z)))
          (fun z => ψ (h (φ.symm z))) := by
      intro y hy
      have hyU₀ : y ∈ φ.target ∩ interior (range I) := ⟨hKt hy, hKi hy⟩
      by_cases hxO' : φ.symm y ∈ O'
      · set W : Set E := (φ.target ∩ interior (range I)) ∩ φ.symm ⁻¹' O' with hWdef
        have hWo : IsOpen W := hcont.isOpen_inter_preimage hU₀ hO'
        refine ⟨W, hWo.mem_nhds ⟨hyU₀, hxO'⟩, Eventually.of_forall fun j z hz => ?_, ?_⟩
        · rw [hsO' j hz.2.2]
          exact hKmap hz.1
        · refine (MapCPConvergenceOn.const_seq (fun z => ψ (h (φ.symm z)))).congr_eventually
            hWo (fun z hz => hz.2) (Eventually.of_forall fun j z hz => ?_) (fun _ _ => rfl)
          change ψ (hs j (φ.symm z)) = ψ (h (φ.symm z))
          rw [hsO' j hz.2]
      · set W : Set E := (φ.target ∩ interior (range I)) ∩
          φ.symm ⁻¹' (h ⁻¹' ψ.source ∩ u ⁻¹' U) with hWdef
        have hWo : IsOpen W := hcont.isOpen_inter_preimage hU₀
          ((isOpen_extChartAt_source q).preimage hh.continuous |>.inter
            (hU.preimage hu.continuous))
        have hyW : y ∈ W := ⟨hyU₀, hKmap hy, hCU ⟨h (φ.symm y), ⟨φ.symm y, hxO', rfl⟩, rfl⟩⟩
        obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo y hyW
        have hcb : closedBall y (ε / 2) ⊆ W := fun z hz =>
          hεW (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by linarith)))
        have hBinfW : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun z => u (φ.symm z)) W :=
          hBinf.mono fun z hz => hz.1.1
        have hmapW : MapsTo (fun z => u (φ.symm z)) W Vt := by
          intro z hz
          refine ⟨hz.2.2, ?_⟩
          change r (e (h (φ.symm z))) ∈ ψ.source
          rw [hleft _ hz.2.2]
          exact hz.2.1
        have hL : IsCompact ((fun z => u (φ.symm z)) '' closedBall y (ε / 2)) :=
          (isCompact_closedBall y (ε / 2)).image_of_continuousOn
            (hBinfW.continuousOn.mono hcb)
        have hLV : (fun z => u (φ.symm z)) '' closedBall y (ε / 2) ⊆ Vt :=
          (hmapW.mono_left hcb).image_subset
        have hev := (tendsto_add_atTop_nat j₀).eventually
          (eventually_mem_of_tendstoUniformly_of_isCompact hunif hL hVt hLV)
        have hevV : ∀ᶠ j in atTop, ∀ z ∈ closedBall y (ε / 2), us (j + j₀) (φ.symm z) ∈ Vt := by
          filter_upwards [hev] with j hj z hz
          exact hj (φ.symm z) ⟨z, hz, rfl⟩
        refine ⟨closedBall y (ε / 2), closedBall_mem_nhds y (by positivity), ?_, ?_⟩
        · filter_upwards [hevV] with j hj z hz
          rw [hsU j _ (hj z hz.2).1]
          exact (hj z hz.2).2
        · have hconvW := mapCPConvergenceOn_comp_of_eventually_contDiffOn
            (B := fun j z => us (j + j₀) (φ.symm z)) (Binf := fun z => u (φ.symm z))
            (A := fun _ w => ψ (r w)) (Ainf := fun w => ψ (r w))
            hWo hVt
            (fun L hL hLW => (hchart p L hL (fun z hz => (hLW hz).1.1)
              (fun z hz => (hLW hz).1.2)).comp_subseq hshift)
            (fun S _ _ => MapCPConvergenceOn.const_seq _)
            (fun L _ hLW => Eventually.of_forall fun j => (hBj j).mono fun z hz => (hLW hz).1.1)
            hBinfW
            (fun S _ hSV => Eventually.of_forall fun _ =>
              (hΨ.of_le (by exact_mod_cast le_top)).mono hSV)
            (hΨ.of_le (by exact_mod_cast le_top)) hmapW
            ((hK.inter_right isClosed_closedBall)) (inter_subset_right.trans hcb)
          refine hconvW.congr_eventually isOpen_ball (U := ball y (ε / 2 + ε / 4)) ?_ ?_ ?_
          · intro z hz
            exact mem_ball.mpr ((mem_closedBall.mp hz.2).trans_lt (by linarith))
          · -- eventually `hs j = r ∘ us` near the closed ball
            have hcb' : closedBall y (ε / 2 + ε / 4) ⊆ W := fun z hz =>
              hεW (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by linarith)))
            have hL' : IsCompact ((fun z => u (φ.symm z)) '' closedBall y (ε / 2 + ε / 4)) :=
              (isCompact_closedBall y _).image_of_continuousOn (hBinfW.continuousOn.mono hcb')
            have hLU' : (fun z => u (φ.symm z)) '' closedBall y (ε / 2 + ε / 4) ⊆ U :=
              fun w hw => ((hmapW.mono_left hcb').image_subset hw).1
            have hev' := (tendsto_add_atTop_nat j₀).eventually
              (eventually_mem_of_tendstoUniformly_of_isCompact hunif hL' hU hLU')
            filter_upwards [hev'] with j hj z hz
            change ψ (hs j (φ.symm z)) = ψ (r (us (j + j₀) (φ.symm z)))
            rw [hsU j _ (hj (φ.symm z) ⟨z, ball_subset_closedBall hz, rfl⟩)]
          · intro z hz
            have hzW : z ∈ W := hεW (mem_ball.mpr ((mem_ball.mp hz).trans (by linarith)))
            change ψ (h (φ.symm z)) = ψ (r (e (h (φ.symm z))))
            rw [hleft _ hzW.2.2]
    choose Vy hVy hVyev hVyconv using hloc
    refine ⟨?_, ?_⟩
    · exact eventually_forall_mem_of_isCompact_nhdsWithin hK fun y hy =>
        ⟨Vy y hy, hVy y hy, hVyev y hy⟩
    · exact MapCPConvergenceOn.of_nhds hK fun y hy => ⟨Vy y hy, hVy y hy, hVyconv y hy⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
