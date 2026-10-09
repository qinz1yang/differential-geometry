import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesPatch

/-!
# FC39 GROUP G, global face functions (F3–F4): ONE face function with protected corner germs

Lane FC39-G-GFF(b), external draft 58 §二 F3–F4, disposition D58-3. Generic statement on a
boundaryless Hausdorff surface `M`:

* `cornerPatch_GGFF` — the corner germ `−Z` of a corner chart `(Z, W)` (`K = {Z ≥ 0, W ≥ 0}` and
  the face trace `= K ∩ {Z = 0}` on the chart domain): non-positive on `K` with zeros exactly the
  trace, regular, and a one-face defining function of `K` near every non-corner trace point;
* `exists_faceFunction_GGFF` — **one face function**: corner bumps times `−X_e` / `−Y_e`, bumps at
  the non-corner points of the trace times regular local defining functions, minus a non-negative
  background sum of bumps supported off the trace. The output is smooth on `M`, `≤ 0` on `K` with
  zeros on `K` exactly the trace, regular and positive just outside `K` at every non-corner trace
  point, and EQUAL to `−X_e` (resp. `−Y_e`) near every corner `p e` of the face (F3: the protected
  canonical germs; the bumps of the other patches avoid the corner points).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- **The corner germ** `−Z` of a corner chart `(Z, W)` on an open `U ⊆ V`: on `K` it is `≤ 0` with
zeros exactly the trace; it is regular; near every trace point other than the corner it cuts out
`K` as `{−Z ≤ 0}` (there `W > 0`). -/
theorem cornerPatch_GGFF {K Bf V U : Set M} {Z W : M → ℝ} {p : M} (hV : IsOpen V) (hUV : U ⊆ V)
    (hW : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ W V)
    (hZr : ∀ c ∈ V, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Z c ≠ 0)
    (hZW0 : ∀ c ∈ V, Z c = 0 → W c = 0 → c = p)
    (hKV : ∀ c ∈ V, c ∈ K ↔ 0 ≤ Z c ∧ 0 ≤ W c) (hBV : ∀ c ∈ V, c ∈ Bf ↔ c ∈ K ∧ Z c = 0) :
    (∀ c ∈ U, c ∈ K → -Z c ≤ 0) ∧ (∀ c ∈ U, c ∈ K → (-Z c = 0 ↔ c ∈ Bf)) ∧
      (∀ c ∈ U, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun u => -Z u) c ≠ 0) ∧
      (∀ c ∈ U, c ∈ Bf → c ≠ p → ∀ᶠ u in 𝓝 c, u ∈ K ↔ -Z u ≤ 0) := by
  refine ⟨fun c hc hcK => ?_, fun c hc hcK => ?_, fun c hc => ?_, fun c hc hcB hcp => ?_⟩
  · have := ((hKV c (hUV hc)).1 hcK).1
    linarith
  · rw [hBV c (hUV hc), neg_eq_zero]
    exact ⟨fun h => ⟨hcK, h⟩, fun h => h.2⟩
  · change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (-Z) c ≠ 0
    rw [mfderiv_neg]
    exact neg_ne_zero.2 (hZr c (hUV hc))
  · have hcV := hUV hc
    obtain ⟨hcK, hZ0⟩ := (hBV c hcV).1 hcB
    have hW0 : 0 < W c := by
      rcases ((hKV c hcV).1 hcK).2.eq_or_lt with h | h
      · exact absurd (hZW0 c hcV hZ0 h.symm) hcp
      · exact h
    have hWc : ContinuousAt W c := ((hW c hcV).contMDiffAt (hV.mem_nhds hcV)).continuousAt
    filter_upwards [hWc.eventually (lt_mem_nhds hW0), hV.mem_nhds hcV] with u hu huV
    rw [hKV u huV]
    constructor
    · rintro ⟨h1, -⟩
      linarith
    · intro h
      exact ⟨by linarith, hu.le⟩

variable [IsManifold (𝓡 2) ∞ M] [T2Space M]

/-- **One face function (F3–F4).** See the module docstring. -/
theorem exists_faceFunction_GGFF {ι ε : Type*} [Finite ε] {K : Set M} (hK : IsCompact K)
    {Bf : Set M} (hBc : IsClosed Bf) (hBK : Bf ⊆ K) (f : ι)
    (p : ε → M) (hp : Injective p) (a b : ε → ι) (hab : ∀ e, a e ≠ b e)
    (V : ε → Set M) (hV : ∀ e, IsOpen (V e)) (hpV : ∀ e, p e ∈ V e)
    (X Y : ε → M → ℝ) (hX : ∀ e, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (X e) (V e))
    (hY : ∀ e, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (Y e) (V e))
    (hX0 : ∀ e, X e (p e) = 0) (hY0 : ∀ e, Y e (p e) = 0)
    (hXr : ∀ e, ∀ c ∈ V e, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (X e) c ≠ 0)
    (hYr : ∀ e, ∀ c ∈ V e, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Y e) c ≠ 0)
    (hXY0 : ∀ e, ∀ c ∈ V e, X e c = 0 → Y e c = 0 → c = p e)
    (hKV : ∀ e, ∀ c ∈ V e, c ∈ K ↔ 0 ≤ X e c ∧ 0 ≤ Y e c)
    (hBa : ∀ e, a e = f → ∀ c ∈ V e, c ∈ Bf ↔ c ∈ K ∧ X e c = 0)
    (hBb : ∀ e, b e = f → ∀ c ∈ V e, c ∈ Bf ↔ c ∈ K ∧ Y e c = 0)
    (hpB : ∀ e, p e ∈ Bf → a e = f ∨ b e = f)
    (hloc : ∀ c ∈ Bf, c ∉ range p → ∃ U : Set M, IsOpen U ∧ c ∈ U ∧ ∃ φ : M → ℝ,
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ U ∧ mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
      (∀ y ∈ U, y ∈ K ↔ φ y ≤ 0) ∧ (∀ y ∈ U, y ∈ K → (φ y = 0 ↔ y ∈ Bf))) :
    ∃ F : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ F ∧ (∀ c ∈ K, F c ≤ 0) ∧
      (∀ c ∈ K, F c = 0 ↔ c ∈ Bf) ∧
      (∀ c ∈ Bf, c ∉ range p → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) F c ≠ 0) ∧
      (∀ c ∈ Bf, c ∉ range p → ∀ᶠ u in 𝓝 c, u ∉ K → 0 < F u) ∧
      (∀ e, a e = f → F =ᶠ[𝓝 (p e)] fun u => -X e u) ∧
      (∀ e, b e = f → F =ᶠ[𝓝 (p e)] fun u => -Y e u) := by
  classical
  have : Fintype ε := Fintype.ofFinite ε
  -- the corner points
  have hPc : IsClosed (range p) := (Set.finite_range p).isClosed
  have hpK : ∀ e, p e ∈ K := fun e => (hKV e (p e) (hpV e)).2 ⟨(hX0 e).ge, (hY0 e).ge⟩
  -- corner domains: `V e` minus the other corner points
  let Uc : ε → Set M := fun e => V e ∩ (p '' {e' | e' ≠ e})ᶜ
  have hUc : ∀ e, IsOpen (Uc e) := fun e =>
    (hV e).inter ((Set.toFinite _).image p).isClosed.isOpen_compl
  have hpUc : ∀ e, p e ∈ Uc e := fun e => ⟨hpV e, by
    rintro ⟨e', he', hpe⟩
    exact he' (hp hpe)⟩
  have hUcV : ∀ e, Uc e ⊆ V e := fun e => inter_subset_left
  have hnotUc : ∀ e e', e' ≠ e → p e ∉ Uc e' := fun e e' hne h => h.2 ⟨e, hne.symm, rfl⟩
  -- corner bumps
  have hbc : ∀ e, ∃ g : SmoothBumpFunction (𝓡 2) (p e), tsupport g ⊆ Uc e := fun e =>
    (SmoothBumpFunction.nhds_basis_support (I := 𝓡 2) ((hUc e).mem_nhds (hpUc e))).ex_mem
  choose bc hbc using hbc
  -- the corner germs
  have hcpa : ∀ e, a e = f → _ := fun e he => cornerPatch_GGFF (K := K) (Bf := Bf) (hV e)
    (hUcV e) (hY e) (hXr e) (hXY0 e) (hKV e) (hBa e he)
  have hcpb : ∀ e, b e = f → _ := fun e he => cornerPatch_GGFF (K := K) (Bf := Bf) (hV e)
    (hUcV e) (hX e) (hYr e) (fun c hc h1 h2 => hXY0 e c hc h2 h1)
    (fun c hc => (hKV e c hc).trans and_comm) (hBb e he)
  -- the non-corner part of the trace
  let Sc : Set M := (⋃ e ∈ {e | a e = f}, support (bc e)) ∪ ⋃ e ∈ {e | b e = f}, support (bc e)
  have hSc : IsOpen Sc := (isOpen_biUnion fun e _ => (bc e).isOpen_support).union
    (isOpen_biUnion fun e _ => (bc e).isOpen_support)
  let Q : Set M := Bf \ Sc
  have hQ : IsCompact Q := (hK.of_isClosed_subset hBc hBK).diff hSc
  have hQP : ∀ y ∈ Q, y ∉ range p := by
    rintro y ⟨hyB, hyS⟩ ⟨e, rfl⟩
    rcases hpB e hyB with h | h
    · exact hyS (Or.inl (mem_biUnion h (bc e).c_mem_support))
    · exact hyS (Or.inr (mem_biUnion h (bc e).c_mem_support))
  have hsing : ∀ y ∈ Q, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ U ⊆ (range p)ᶜ ∧ ∃ φ : M → ℝ,
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ U ∧ (∀ z ∈ U, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ z ≠ 0) ∧
      (∀ z ∈ U, z ∈ K ↔ φ z ≤ 0) ∧ (∀ z ∈ U, z ∈ K → (φ z = 0 ↔ z ∈ Bf)) := by
    intro y hy
    obtain ⟨U, hU, hyU, φ, hφ, hr, hφK, hφB⟩ := hloc y hy.1 (hQP y hy)
    obtain ⟨U', hU', hyU', hU'U, hr'⟩ := exists_regular_open_GGFF (hU.inter hPc.isOpen_compl)
      (hφ.mono inter_subset_left) ⟨hyU, hQP y hy⟩ hr
    exact ⟨U', hU', hyU', fun z hz => (hU'U hz).2, φ, hφ.mono (hU'U.trans inter_subset_left),
      hr', fun z hz => hφK z (hU'U hz).1, fun z hz => hφB z (hU'U hz).1⟩
  choose! Us hUs hyUs hUsP φs hφs hφsr hφsK hφsB using hsing
  obtain ⟨t, βs, hβs, hβsnn, hβsU, htQ, hQcov⟩ :=
    exists_bump_cover_GGFF hQ Us fun y hy => (hUs y hy).mem_nhds (hyUs y hy)
  -- the patches
  let J := {e // a e = f} ⊕ {e // b e = f} ⊕ {y // y ∈ t}
  let β : J → M → ℝ := Sum.elim (fun e => (bc e.1 : M → ℝ))
    (Sum.elim (fun e => (bc e.1 : M → ℝ)) fun y => βs y.1)
  let ψ : J → M → ℝ := Sum.elim (fun e u => -X e.1 u)
    (Sum.elim (fun e u => -Y e.1 u) fun y => φs y.1)
  let U : J → Set M := Sum.elim (fun e => Uc e.1) (Sum.elim (fun e => Uc e.1) fun y => Us y.1)
  have hU : ∀ j, IsOpen (U j) := by
    rintro (e | e | y)
    · exact hUc e.1
    · exact hUc e.1
    · exact hUs y.1 (htQ y.1 y.2)
  have hβU : ∀ j, tsupport (β j) ⊆ U j := by
    rintro (e | e | y)
    · exact hbc e.1
    · exact hbc e.1
    · exact hβsU y.1 (htQ y.1 y.2)
  have hβ : ∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (β j) := by
    rintro (e | e | y)
    · exact (bc e.1).contMDiff
    · exact (bc e.1).contMDiff
    · exact hβs y.1
  have hβnn : ∀ j u, 0 ≤ β j u := by
    rintro (e | e | y) u
    · exact (bc e.1).nonneg
    · exact (bc e.1).nonneg
    · exact hβsnn y.1 u
  have hψ : ∀ j, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (ψ j) (U j) := by
    rintro (e | e | y)
    · exact ((hX e.1).neg).mono (hUcV e.1)
    · exact ((hY e.1).neg).mono (hUcV e.1)
    · exact hφs y.1 (htQ y.1 y.2)
  have hψK : ∀ j, ∀ c ∈ U j, c ∈ K → ψ j c ≤ 0 := by
    rintro (e | e | y)
    · exact (hcpa e.1 e.2).1
    · exact (hcpb e.1 e.2).1
    · exact fun c hc hcK => (hφsK y.1 (htQ y.1 y.2) c hc).1 hcK
  have hψ0 : ∀ j, ∀ c ∈ U j, c ∈ K → (ψ j c = 0 ↔ c ∈ Bf) := by
    rintro (e | e | y)
    · exact (hcpa e.1 e.2).2.1
    · exact (hcpb e.1 e.2).2.1
    · exact hφsB y.1 (htQ y.1 y.2)
  have hψr : ∀ j, ∀ c ∈ U j, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (ψ j) c ≠ 0 := by
    rintro (e | e | y)
    · exact (hcpa e.1 e.2).2.2.1
    · exact (hcpb e.1 e.2).2.2.1
    · exact hφsr y.1 (htQ y.1 y.2)
  have hψs : ∀ j, ∀ c ∈ U j, c ∈ Bf → c ∉ range p → ∀ᶠ u in 𝓝 c, u ∈ K ↔ ψ j u ≤ 0 := by
    rintro (e | e | y)
    · exact fun c hc hcB hcP => (hcpa e.1 e.2).2.2.2 c hc hcB fun h => hcP ⟨e.1, h.symm⟩
    · exact fun c hc hcB hcP => (hcpb e.1 e.2).2.2.2 c hc hcB fun h => hcP ⟨e.1, h.symm⟩
    · intro c hc _ _
      filter_upwards [(hUs y.1 (htQ y.1 y.2)).mem_nhds hc] with u hu
      exact hφsK y.1 (htQ y.1 y.2) u hu
  have hcov : Bf ⊆ ⋃ j, support (β j) := by
    intro c hcB
    by_cases hcS : c ∈ Sc
    · rcases hcS with hcS | hcS
      · obtain ⟨e, he, hce⟩ := mem_iUnion₂.1 hcS
        exact mem_iUnion.2 ⟨Sum.inl ⟨e, he⟩, hce⟩
      · obtain ⟨e, he, hce⟩ := mem_iUnion₂.1 hcS
        exact mem_iUnion.2 ⟨Sum.inr (Sum.inl ⟨e, he⟩), hce⟩
    · obtain ⟨y, hyt, hcy⟩ := mem_iUnion₂.1 (hQcov ⟨hcB, hcS⟩)
      exact mem_iUnion.2 ⟨Sum.inr (Sum.inr ⟨y, hyt⟩), hcy⟩
  -- the background
  let R : Set M := K \ ⋃ j, support (β j)
  have hR : IsCompact R :=
    hK.diff (isOpen_iUnion fun j => (hβ j).continuous.isOpen_support)
  obtain ⟨t', γ, hγ, hγnn, hγU, ht'R, hRcov⟩ := exists_bump_cover_GGFF hR (fun _ => Bfᶜ)
    fun y hy => hBc.isOpen_compl.mem_nhds fun hyB => hy.2 (hcov hyB)
  let G : M → ℝ := fun u => ∑ y ∈ t', γ y u
  have hGsm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ G := contMDiff_finsetSum fun y _ => hγ y
  have hGnn : ∀ u, 0 ≤ G u := fun u => Finset.sum_nonneg fun y _ => hγnn y u
  have hG0 : ∀ c ∈ Bf, G =ᶠ[𝓝 c] 0 := by
    intro c hcB
    have h : ∀ᶠ u in 𝓝 c, ∀ y ∈ t', γ y u = 0 := by
      rw [Filter.eventually_all_finset]
      intro y hy
      have hc : c ∉ tsupport (γ y) := fun h => hγU y (ht'R y hy) h hcB
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hc] with u hu
      exact hu
    filter_upwards [h] with u hu
    exact Finset.sum_eq_zero hu
  have hGpos : ∀ c ∈ R, 0 < G c := by
    intro c hc
    obtain ⟨y, hyt, hcy⟩ := mem_iUnion₂.1 (hRcov hc)
    exact Finset.sum_pos' (fun y _ => hγnn y c) ⟨y, hyt, lt_of_le_of_ne (hγnn y c) (Ne.symm hcy)⟩
  -- the face function
  refine ⟨fun u => ∑ j, β j u * ψ j u - G u, ?_, fun c hcK => ?_, fun c hcK => ?_,
    fun c hcB hcP => ?_, fun c hcB hcP => ?_, fun e he => ?_, fun e he => ?_⟩
  · exact (contMDiff_finsetSum fun j _ =>
      contMDiff_mul_of_tsupport_GGFF (hU j) (hβU j) (hβ j) (hψ j)).sub hGsm
  · exact sum_mul_sub_nonpos_GGFF β ψ U hβU hβnn hψK hGnn hcK
  · constructor
    · intro h0
      by_contra hcB
      have hneg : (∃ j, 0 < β j c ∧ ψ j c < 0) ∨ 0 < G c := by
        by_cases hcS : c ∈ ⋃ j, support (β j)
        · obtain ⟨j, hj⟩ := mem_iUnion.1 hcS
          have hjU : c ∈ U j := hβU j (subset_tsupport _ hj)
          refine Or.inl ⟨j, lt_of_le_of_ne (hβnn j c) (Ne.symm hj), ?_⟩
          exact lt_of_le_of_ne (hψK j c hjU hcK) fun h => hcB ((hψ0 j c hjU hcK).1 h)
        · exact Or.inr (hGpos c ⟨hcK, hcS⟩)
      have := sum_mul_sub_neg_GGFF β ψ U hβU hβnn hψK hGnn hcK hneg
      linarith
    · intro hcB
      exact sum_mul_sub_eq_zero_GGFF β ψ U hβU (fun j hj => (hψ0 j c hj hcK).2 hcB)
        (hG0 c hcB).eq_of_nhds
  · obtain ⟨j₀, hj₀⟩ := mem_iUnion.1 (hcov hcB)
    exact mfderiv_sum_mul_sub_ne_zero_GGFF β ψ U hU hβU hβ hψ hβnn (hG0 c hcB)
      (fun j hj => (hψ0 j c hj (hBK hcB)).2 hcB) (fun j hj => hψr j c hj)
      (fun j hj => hψs j c hj hcB hcP) (j₀ := j₀) (lt_of_le_of_ne (hβnn j₀ c) (Ne.symm hj₀))
  · obtain ⟨j₀, hj₀⟩ := mem_iUnion.1 (hcov hcB)
    have hact : ∀ j, ∀ᶠ u in 𝓝 c, u ∉ K → 0 < β j u → 0 < ψ j u := by
      intro j
      by_cases hj : c ∈ tsupport (β j)
      · filter_upwards [hψs j c (hβU j hj) hcB hcP] with u hu huK _
        exact lt_of_not_ge fun h => huK (hu.2 h)
      · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hj] with u hu _ hpos
        exact absurd hu (ne_of_gt hpos)
    have hβ₀ : ∀ᶠ u in 𝓝 c, 0 < β j₀ u :=
      Filter.mem_of_superset ((hβ j₀).continuous.isOpen_support.mem_nhds hj₀) fun u hu =>
        lt_of_le_of_ne (hβnn j₀ u) (Ne.symm hu)
    filter_upwards [Filter.eventually_all.2 hact, hβ₀, hG0 c hcB] with u hu hu₀ hGu huK
    have hGu' : G u = 0 := hGu
    rw [hGu', sub_zero]
    exact sum_mul_pos_GGFF β ψ hβnn (fun j hj => hu j huK hj) hu₀
  · -- the protected germ `−X_e`
    have hpB' : p e ∈ Bf := (hBa e he (p e) (hpV e)).2 ⟨hpK e, hX0 e⟩
    have hoff : ∀ j, j ≠ Sum.inl ⟨e, he⟩ → ∀ᶠ u in 𝓝 (p e), β j u = 0 := by
      rintro (⟨e', he'⟩ | ⟨e', he'⟩ | ⟨y, hy⟩) hj
      · have hne : e' ≠ e := fun h => hj (by subst h; rfl)
        exact notMem_tsupport_iff_eventuallyEq.1 fun h => hnotUc e e' hne (hbc e' h)
      · have hne : e' ≠ e := fun h => hab e (by subst h; exact he.trans he'.symm)
        exact notMem_tsupport_iff_eventuallyEq.1 fun h => hnotUc e e' hne (hbc e' h)
      · exact notMem_tsupport_iff_eventuallyEq.1 fun h =>
          hUsP y (htQ y hy) (hβsU y (htQ y hy) h) ⟨e, rfl⟩
    have hall : ∀ᶠ u in 𝓝 (p e), ∀ j, j ≠ Sum.inl ⟨e, he⟩ → β j u = 0 := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = Sum.inl ⟨e, he⟩
      · exact Filter.Eventually.of_forall fun u h => absurd hj h
      · filter_upwards [hoff j hj] with u hu _ using hu
    filter_upwards [hall, (bc e).eventuallyEq_one, hG0 (p e) hpB'] with u hu h1 hGu
    have hGu' : G u = 0 := hGu
    have h1' : (bc e : M → ℝ) u = 1 := h1
    rw [hGu', sub_zero, Finset.sum_eq_single (Sum.inl ⟨e, he⟩)
      (fun j _ hj => by rw [hu j hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
    change (bc e : M → ℝ) u * -X e u = -X e u
    rw [h1', one_mul]
  · -- the protected germ `−Y_e`
    have hpB' : p e ∈ Bf := (hBb e he (p e) (hpV e)).2 ⟨hpK e, hY0 e⟩
    have hoff : ∀ j, j ≠ Sum.inr (Sum.inl ⟨e, he⟩) → ∀ᶠ u in 𝓝 (p e), β j u = 0 := by
      rintro (⟨e', he'⟩ | ⟨e', he'⟩ | ⟨y, hy⟩) hj
      · have hne : e' ≠ e := fun h => hab e (by subst h; exact he'.trans he.symm)
        exact notMem_tsupport_iff_eventuallyEq.1 fun h => hnotUc e e' hne (hbc e' h)
      · have hne : e' ≠ e := fun h => hj (by subst h; rfl)
        exact notMem_tsupport_iff_eventuallyEq.1 fun h => hnotUc e e' hne (hbc e' h)
      · exact notMem_tsupport_iff_eventuallyEq.1 fun h =>
          hUsP y (htQ y hy) (hβsU y (htQ y hy) h) ⟨e, rfl⟩
    have hall : ∀ᶠ u in 𝓝 (p e), ∀ j, j ≠ Sum.inr (Sum.inl ⟨e, he⟩) → β j u = 0 := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = Sum.inr (Sum.inl ⟨e, he⟩)
      · exact Filter.Eventually.of_forall fun u h => absurd hj h
      · filter_upwards [hoff j hj] with u hu _ using hu
    filter_upwards [hall, (bc e).eventuallyEq_one, hG0 (p e) hpB'] with u hu h1 hGu
    have hGu' : G u = 0 := hGu
    have h1' : (bc e : M → ℝ) u = 1 := h1
    rw [hGu', sub_zero, Finset.sum_eq_single (Sum.inr (Sum.inl ⟨e, he⟩))
      (fun j _ hj => by rw [hu j hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
    change (bc e : M → ℝ) u * -Y e u = -Y e u
    rw [h1', one_mul]

end GC.GraphManifold.Assembly.FC39P0
