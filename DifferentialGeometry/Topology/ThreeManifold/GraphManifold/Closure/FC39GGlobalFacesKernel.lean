import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesOne

/-!
# FC39 GROUP G, global face functions (F5–F6 kernel): all faces at once, the final shrinking

Lane FC39-G-GFF(b), external draft 58 §二 F5, disposition D58-3. On a boundaryless Hausdorff
surface `M`: a compact `K`, finitely many closed face traces `B f ⊆ K` (`K \ ⋃ B f ⊆ int K`),
finitely many corners `p e` (injective) with two distinct labels `a e`, `b e` and a corner chart
`(X_e, Y_e)` on an open `V e` (`K = {X_e ≥ 0, Y_e ≥ 0}`, `B (a e) = K ∩ {X_e = 0}`,
`B (b e) = K ∩ {Y_e = 0}`, the other traces off `V e`, `dX_e`, `dY_e ≠ 0`, `(dX_e, dY_e)` onto at
`p e`, `X_e = Y_e = 0` only at `p e`), every point of two traces a corner, and a regular local
defining function at every point of exactly one trace. Then
`exists_globalFaceFunctions_kernel_GGFF` gives an open `base ⊇ K` and smooth functions `fn f` with
every field of `GlobalFaceFunctionsV2` (regular zeros on `base`, `K = {∀ f, fn f ≤ 0}` exactly on
`base`, zeros on `K` = the traces, depth `≤ 2`, double zeros only at the corners with their two labels
and independent differentials, all other functions negative there, and `fn (a e) = −X_e`,
`fn (b e) = −Y_e` on an open neighbourhood of `p e` inside `base ∩ V e`).

Proof: one face function per label (`exists_faceFunction_GGFF`), then `base := int {c | Good c}`
where `Good` collects the pointwise fields; `Good` holds near every point of `K`: near a corner by
the protected germs, near a single-label trace point by the sign and regularity outputs, near an
interior point because every function is negative there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M]

/-- **F5 kernel: global face functions on a shrunk base.** See the module docstring. -/
theorem exists_globalFaceFunctions_kernel_GGFF {ι ε : Type*} [Finite ι] [Finite ε]
    {K : Set M} (hK : IsCompact K) (B : ι → Set M) (hBc : ∀ f, IsClosed (B f))
    (hBK : ∀ f, B f ⊆ K) (hint : ∀ c ∈ K, (∀ f, c ∉ B f) → c ∈ interior K)
    (p : ε → M) (hp : Injective p) (a b : ε → ι) (hab : ∀ e, a e ≠ b e)
    (V : ε → Set M) (hV : ∀ e, IsOpen (V e)) (hpV : ∀ e, p e ∈ V e)
    (X Y : ε → M → ℝ) (hX : ∀ e, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (X e) (V e))
    (hY : ∀ e, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (Y e) (V e))
    (hX0 : ∀ e, X e (p e) = 0) (hY0 : ∀ e, Y e (p e) = 0)
    (hXr : ∀ e, ∀ c ∈ V e, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (X e) c ≠ 0)
    (hYr : ∀ e, ∀ c ∈ V e, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Y e) c ≠ 0)
    (hXY : ∀ e, Surjective fun w : TangentSpace (𝓡 2) (p e) =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (X e) (p e) w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Y e) (p e) w))
    (hXY0 : ∀ e, ∀ c ∈ V e, X e c = 0 → Y e c = 0 → c = p e)
    (hKV : ∀ e, ∀ c ∈ V e, c ∈ K ↔ 0 ≤ X e c ∧ 0 ≤ Y e c)
    (hBa : ∀ e, ∀ c ∈ V e, c ∈ B (a e) ↔ c ∈ K ∧ X e c = 0)
    (hBb : ∀ e, ∀ c ∈ V e, c ∈ B (b e) ↔ c ∈ K ∧ Y e c = 0)
    (hBo : ∀ e g, g ≠ a e → g ≠ b e → Disjoint (B g) (V e))
    (htwo : ∀ c f g, f ≠ g → c ∈ B f → c ∈ B g → c ∈ range p)
    (hloc : ∀ f, ∀ c ∈ B f, (∀ g, g ≠ f → c ∉ B g) → ∃ U : Set M, IsOpen U ∧ c ∈ U ∧
      ∃ φ : M → ℝ, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ U ∧ mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
        (∀ y ∈ U, y ∈ K ↔ φ y ≤ 0) ∧ (∀ y ∈ U, y ∈ K → (φ y = 0 ↔ y ∈ B f))) :
    ∃ (base : TopologicalSpace.Opens M) (fn : ι → M → ℝ),
      K ⊆ base ∧ (∀ f, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fn f) base) ∧
      (∀ f, ∀ c ∈ base, fn f c = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f) c ≠ 0) ∧
      K = {c | c ∈ base ∧ ∀ f, fn f c ≤ 0} ∧
      (∀ f, {c | c ∈ K ∧ fn f c = 0} = B f) ∧
      (∀ c ∈ base, Set.ncard {f | fn f c = 0} ≤ 2) ∧
      (∀ c ∈ base, ∀ f f', f ≠ f' → fn f c = 0 → fn f' c = 0 →
        Surjective fun w : TangentSpace (𝓡 2) c =>
          (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f) c w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f') c w)) ∧
      (∀ c ∈ base, ∀ f f', f ≠ f' → fn f c = 0 → fn f' c = 0 →
        ∃ e, c = p e ∧ ((f = a e ∧ f' = b e) ∨ (f = b e ∧ f' = a e)) ∧
          ∀ f'', f'' ≠ f → f'' ≠ f' → fn f'' c < 0) ∧
      (∀ e, ∃ O : TopologicalSpace.Opens M, p e ∈ O ∧ (O : Set M) ⊆ (base : Set M) ∩ V e ∧
        ∀ c ∈ O, fn (a e) c = -X e c ∧ fn (b e) c = -Y e c) := by
  classical
  have hpK : ∀ e, p e ∈ K := fun e => (hKV e (p e) (hpV e)).2 ⟨(hX0 e).ge, (hY0 e).ge⟩
  -- one face function per label
  have hFex : ∀ f, ∃ F : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ F ∧ (∀ c ∈ K, F c ≤ 0) ∧
      (∀ c ∈ K, F c = 0 ↔ c ∈ B f) ∧
      (∀ c ∈ B f, c ∉ range p → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) F c ≠ 0) ∧
      (∀ c ∈ B f, c ∉ range p → ∀ᶠ u in 𝓝 c, u ∉ K → 0 < F u) ∧
      (∀ e, a e = f → F =ᶠ[𝓝 (p e)] fun u => -X e u) ∧
      (∀ e, b e = f → F =ᶠ[𝓝 (p e)] fun u => -Y e u) := fun f =>
    exists_faceFunction_GGFF hK (hBc f) (hBK f) f p hp a b hab V hV hpV X Y hX hY hX0 hY0 hXr hYr
      hXY0 hKV (fun e he => he ▸ hBa e) (fun e he => he ▸ hBb e)
      (fun e hpe => by
        by_contra h
        push Not at h
        exact Set.disjoint_left.1 (hBo e f (Ne.symm h.1) (Ne.symm h.2)) hpe (hpV e))
      (fun c hc hcP => hloc f c hc fun g hg hcg => hcP (htwo c f g (Ne.symm hg) hc hcg))
  choose F hFsm hFnp hFz hFr hFpos hFa hFb using hFex
  have hFneg : ∀ f, ∀ c ∈ K, c ∉ B f → F f c < 0 := fun f c hcK hcB =>
    lt_of_le_of_ne (hFnp f c hcK) fun h => hcB ((hFz f c hcK).1 h)
  -- the corner germs on open sets
  have hOa : ∀ e, ∃ O : Set M, IsOpen O ∧ p e ∈ O ∧ O ⊆ V e ∧ ∀ u ∈ O,
      F (a e) u = -X e u ∧ F (b e) u = -Y e u := by
    intro e
    obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.1 (((hFa (a e) e rfl).and (hFb (b e) e rfl)).and
      ((hV e).mem_nhds (hpV e)))
    exact ⟨O, hOo, hpO, fun u hu => (hO u hu).2, fun u hu => (hO u hu).1⟩
  choose O hOo hpO hOV hOF using hOa
  have hderX : ∀ e, ∀ c ∈ O e, HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (F (a e)) c
      (-mderivR_GTR (𝓡 2) (X e) c) := by
    intro e c hc
    have hXd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (X e) c :=
      ((hX e c (hOV e hc)).contMDiffAt ((hV e).mem_nhds (hOV e hc))).mdifferentiableAt (by simp)
    have h : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (-(X e)) c (-mderivR_GTR (𝓡 2) (X e) c) :=
      hXd.hasMFDerivAt.neg
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [(hOo e).mem_nhds hc] with u hu using (hOF e u hu).1
  have hderY : ∀ e, ∀ c ∈ O e, HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (F (b e)) c
      (-mderivR_GTR (𝓡 2) (Y e) c) := by
    intro e c hc
    have hYd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (Y e) c :=
      ((hY e c (hOV e hc)).contMDiffAt ((hV e).mem_nhds (hOV e hc))).mdifferentiableAt (by simp)
    have h : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (-(Y e)) c (-mderivR_GTR (𝓡 2) (Y e) c) :=
      hYd.hasMFDerivAt.neg
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [(hOo e).mem_nhds hc] with u hu using (hOF e u hu).2
  -- the pointwise fields
  let Good : M → Prop := fun c =>
    (∀ f, F f c = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (F f) c ≠ 0) ∧ (c ∉ K → ∃ f, 0 < F f c) ∧
      Set.ncard {f | F f c = 0} ≤ 2 ∧
      (∀ f f', f ≠ f' → F f c = 0 → F f' c = 0 →
        Surjective fun w : TangentSpace (𝓡 2) c =>
          (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (F f) c w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (F f') c w)) ∧
      (∀ f f', f ≠ f' → F f c = 0 → F f' c = 0 →
        ∃ e, c = p e ∧ ((f = a e ∧ f' = b e) ∨ (f = b e ∧ f' = a e)) ∧
          ∀ f'', f'' ≠ f → f'' ≠ f' → F f'' c < 0)
  have hgood : ∀ c₀ ∈ K, ∀ᶠ c in 𝓝 c₀, Good c := by
    intro c₀ hc₀
    by_cases hcP : c₀ ∈ range p
    · -- near a corner: the protected germs
      obtain ⟨e, rfl⟩ := hcP
      have hothers : ∀ᶠ c in 𝓝 (p e), ∀ g, g ≠ a e → g ≠ b e → F g c < 0 := by
        rw [Filter.eventually_all]
        intro g
        by_cases hg : g ≠ a e ∧ g ≠ b e
        · have hlt : F g (p e) < 0 := hFneg g (p e) (hpK e)
            fun h => Set.disjoint_left.1 (hBo e g hg.1 hg.2) h (hpV e)
          filter_upwards [(hFsm g).continuous.continuousAt.eventually (gt_mem_nhds hlt)] with c hc
            _ _ using hc
        · push Not at hg
          exact Filter.Eventually.of_forall fun c h1 h2 => absurd (hg h1) h2
      filter_upwards [hothers, (hOo e).mem_nhds (hpO e)] with c hc hcO
      have hcV := hOV e hcO
      have hzero : ∀ f, F f c = 0 → f = a e ∨ f = b e := by
        intro f hf
        by_contra h
        push Not at h
        exact (hc f h.1 h.2).ne hf
      have hXz : F (a e) c = 0 → X e c = 0 := fun h => by
        rw [(hOF e c hcO).1] at h
        linarith
      have hYz : F (b e) c = 0 → Y e c = 0 := fun h => by
        rw [(hOF e c hcO).2] at h
        linarith
      refine ⟨fun f hf => ?_, fun hcK => ?_, ?_, fun f f' hff' hf hf' => ?_,
        fun f f' hff' hf hf' => ?_⟩
      · rcases hzero f hf with rfl | rfl
        · rw [(hderX e c hcO).mfderiv]
          exact neg_ne_zero.2 (hXr e c hcV)
        · rw [(hderY e c hcO).mfderiv]
          exact neg_ne_zero.2 (hYr e c hcV)
      · have h : ¬ (0 ≤ X e c ∧ 0 ≤ Y e c) := fun h => hcK ((hKV e c hcV).2 h)
        by_cases hXc : 0 ≤ X e c
        · refine ⟨b e, ?_⟩
          rw [(hOF e c hcO).2]
          have : Y e c < 0 := lt_of_not_ge fun hY' => h ⟨hXc, hY'⟩
          linarith
        · refine ⟨a e, ?_⟩
          rw [(hOF e c hcO).1]
          linarith
      · have hsub : {f | F f c = 0} ⊆ {a e, b e} := fun f hf => hzero f hf
        exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
          ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
      · have hpc : c = p e := by
          rcases hzero f hf with rfl | rfl <;> rcases hzero f' hf' with h' | h'
          · exact absurd h'.symm hff'
          · subst h'
            exact hXY0 e c hcV (hXz hf) (hYz hf')
          · subst h'
            exact hXY0 e c hcV (hXz hf') (hYz hf)
          · exact absurd h'.symm hff'
        subst hpc
        rcases hzero f hf with rfl | rfl <;> rcases hzero f' hf' with h' | h'
        · exact absurd h'.symm hff'
        · subst h'
          rw [(hderX e (p e) hcO).mfderiv, (hderY e (p e) hcO).mfderiv]
          intro r
          obtain ⟨w, hw⟩ := hXY e (-r.1, -r.2)
          refine ⟨w, ?_⟩
          have h1 := congrArg Prod.fst hw
          have h2 := congrArg Prod.snd hw
          simp only at h1 h2
          have h1' : mderivR_GTR (𝓡 2) (X e) (p e) w = -r.1 := h1
          have h2' : mderivR_GTR (𝓡 2) (Y e) (p e) w = -r.2 := h2
          refine Prod.ext ?_ ?_
          · change -(mderivR_GTR (𝓡 2) (X e) (p e) w) = r.1
            rw [h1']
            exact neg_neg _
          · change -(mderivR_GTR (𝓡 2) (Y e) (p e) w) = r.2
            rw [h2']
            exact neg_neg _
        · subst h'
          rw [(hderY e (p e) hcO).mfderiv, (hderX e (p e) hcO).mfderiv]
          intro r
          obtain ⟨w, hw⟩ := hXY e (-r.2, -r.1)
          refine ⟨w, ?_⟩
          have h1 := congrArg Prod.fst hw
          have h2 := congrArg Prod.snd hw
          simp only at h1 h2
          have h1' : mderivR_GTR (𝓡 2) (X e) (p e) w = -r.2 := h1
          have h2' : mderivR_GTR (𝓡 2) (Y e) (p e) w = -r.1 := h2
          refine Prod.ext ?_ ?_
          · change -(mderivR_GTR (𝓡 2) (Y e) (p e) w) = r.1
            rw [h2']
            exact neg_neg _
          · change -(mderivR_GTR (𝓡 2) (X e) (p e) w) = r.2
            rw [h1']
            exact neg_neg _
        · exact absurd h'.symm hff'
      · have hpc : c = p e := by
          rcases hzero f hf with rfl | rfl <;> rcases hzero f' hf' with h' | h'
          · exact absurd h'.symm hff'
          · subst h'
            exact hXY0 e c hcV (hXz hf) (hYz hf')
          · subst h'
            exact hXY0 e c hcV (hXz hf') (hYz hf)
          · exact absurd h'.symm hff'
        refine ⟨e, hpc, ?_, ?_⟩
        · rcases hzero f hf with rfl | rfl <;> rcases hzero f' hf' with h' | h'
          · exact absurd h'.symm hff'
          · exact Or.inl ⟨rfl, h'⟩
          · exact Or.inr ⟨rfl, h'⟩
          · exact absurd h'.symm hff'
        · intro f'' h1 h2
          refine hc f'' ?_ ?_
          · rintro rfl
            rcases hzero f hf with h3 | h3 <;> rcases hzero f' hf' with h4 | h4
            · exact hff' (h3.trans h4.symm)
            · exact h1 h3.symm
            · exact h2 h4.symm
            · exact hff' (h3.trans h4.symm)
          · rintro rfl
            rcases hzero f hf with h3 | h3 <;> rcases hzero f' hf' with h4 | h4
            · exact hff' (h3.trans h4.symm)
            · exact h2 h4.symm
            · exact h1 h3.symm
            · exact hff' (h3.trans h4.symm)
    · by_cases hcB : ∃ f, c₀ ∈ B f
      · -- near a single-label trace point
        obtain ⟨f, hf⟩ := hcB
        have hsing : ∀ g, g ≠ f → c₀ ∉ B g := fun g hg hcg => hcP (htwo c₀ f g (Ne.symm hg) hf hcg)
        have hothers : ∀ᶠ c in 𝓝 c₀, ∀ g, g ≠ f → F g c < 0 := by
          rw [Filter.eventually_all]
          intro g
          by_cases hg : g = f
          · exact Filter.Eventually.of_forall fun c h => absurd hg h
          · have hlt := hFneg g c₀ hc₀ (hsing g hg)
            filter_upwards [(hFsm g).continuous.continuousAt.eventually (gt_mem_nhds hlt)] with c hc
              _ using hc
        filter_upwards [hothers, hFpos f c₀ hf hcP,
          (Set.finite_range p).isClosed.isOpen_compl.mem_nhds hcP] with c hc hcpos hcP'
        have hzero : ∀ g, F g c = 0 → g = f := fun g hg => by
          by_contra h
          exact (hc g h).ne hg
        have hcK : F f c = 0 → c ∈ K := fun h => by
          by_contra hK'
          exact (hcpos hK').ne' h
        refine ⟨fun g hg => ?_, fun hK' => ⟨f, hcpos hK'⟩, ?_, fun g g' hgg' hg hg' => ?_,
          fun g g' hgg' hg hg' => ?_⟩
        · obtain rfl := hzero g hg
          exact hFr g c ((hFz g c (hcK hg)).1 hg) hcP'
        · have hsub : {g | F g c = 0} ⊆ {f} := fun g hg => hzero g hg
          exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by rw [Set.ncard_singleton]; omega)
        · exact absurd ((hzero g hg).trans (hzero g' hg').symm) hgg'
        · exact absurd ((hzero g hg).trans (hzero g' hg').symm) hgg'
      · -- near an interior point
        push Not at hcB
        have hall : ∀ᶠ c in 𝓝 c₀, ∀ g, F g c < 0 := by
          rw [Filter.eventually_all]
          intro g
          exact (hFsm g).continuous.continuousAt.eventually (gt_mem_nhds (hFneg g c₀ hc₀ (hcB g)))
        filter_upwards [hall, isOpen_interior.mem_nhds (hint c₀ hc₀ hcB)] with c hc hcK
        refine ⟨fun g hg => absurd hg (hc g).ne, fun h => absurd (interior_subset hcK) h, ?_,
          fun g _ _ hg _ => absurd hg (hc g).ne, fun g _ _ hg _ => absurd hg (hc g).ne⟩
        have hemp : {g | F g c = 0} = ∅ := Set.eq_empty_of_forall_notMem fun g hg => (hc g).ne hg
        rw [hemp, Set.ncard_empty]
        omega
  -- the final base
  have hKb : K ⊆ interior {c | Good c} := fun c hc =>
    mem_interior_iff_mem_nhds.2 (hgood c hc)
  have hG : ∀ c ∈ interior {c | Good c}, Good c := fun c hc =>
    (interior_subset hc : c ∈ {c | Good c})
  refine ⟨⟨interior {c | Good c}, isOpen_interior⟩, F, hKb, fun f => (hFsm f).contMDiffOn,
    fun f c hc => (hG c hc).1 f, ?_, fun f => ?_, fun c hc => (hG c hc).2.2.1,
    fun c hc => (hG c hc).2.2.2.1, fun c hc => (hG c hc).2.2.2.2, fun e => ?_⟩
  · ext c
    constructor
    · intro hc
      exact ⟨hKb hc, fun f => hFnp f c hc⟩
    · rintro ⟨hcb, hle⟩
      by_contra hcK
      obtain ⟨f, hf⟩ := (hG c hcb).2.1 hcK
      linarith [hle f]
  · ext c
    constructor
    · rintro ⟨hcK, h0⟩
      exact (hFz f c hcK).1 h0
    · intro hc
      exact ⟨hBK f hc, (hFz f c (hBK f hc)).2 hc⟩
  · refine ⟨⟨interior {c | Good c} ∩ O e, isOpen_interior.inter (hOo e)⟩, ⟨hKb (hpK e), hpO e⟩,
      fun c hc => ⟨hc.1, hOV e hc.2⟩, fun c hc => hOF e c hc.2⟩

end GC.GraphManifold.Assembly.FC39P0
