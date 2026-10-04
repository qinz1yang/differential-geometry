import DifferentialGeometry.Geometry.Collapse.SublevelCore.Globalization
import DifferentialGeometry.Geometry.Collapse.SublevelCore.GraphIsotopy

/-!
# LC35: smooth radial graph isotopy

Blueprint LC35 (master207A:21535). Let `Φ` be the product flow of LC46 (LC33) on the band
`K = f⁻¹[a,b]` of `f`, with base level `Σ = f⁻¹(c)`, and let `h` be smooth near `Σ` with
`a < h < b` on `Σ`. For `ρ ∈ (a,b)` the domain
`D_h = {f ≤ a} ∪ {Φ (u - c) x : x ∈ Σ, a ≤ u ≤ h x}` is carried onto the sublevel `{f ≤ ρ}` by a
smooth ambient isotopy whose support is one compact subset of `f⁻¹(a,b)`.

The isotopy moves each point along its own flow line: with `R y = Φ (c - f y) y ∈ Σ` and the
one-dimensional flow `φ` of `exists_real_flow_translating` (W3-F5b, `GraphIsotopy.lean`),
`G t y = Φ (φ (t (ρ - h (R y))) (f y) - f y) y`. In product coordinates this is the graph-to-level
isotopy `(x, u) ↦ (x, φ_{t(ρ - h x)} u)`.

* `exists_band_graph_isotopy`: kernel form (globally smooth `f`, supplied product flow `Φ`).
* `exists_band_graph_isotopy_of_contMDiffOn`: binding form for a function smooth only near its
  band (the LC30 radial function), with the product flow of LC46/LC33.
* `exists_band_sublevel_isotopy`: constant heights; all `{f ≤ ρ}`, `ρ ∈ (a,b)`, are smoothly
  ambient isotopic.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- A strictly monotone map of `ℝ` fixing every point outside `[a', b']` maps `[a', b']` into
itself. -/
private theorem mem_Icc_of_strictMono_fix {ψ : ℝ → ℝ} (hψ : StrictMono ψ) {a' b' : ℝ}
    (hfix : ∀ u, u ∉ Icc a' b' → ψ u = u) {u : ℝ} (hu : u ∈ Icc a' b') : ψ u ∈ Icc a' b' := by
  constructor
  · by_contra hlt
    push Not at hlt
    set v := (ψ u + a') / 2 with hvdef
    have hv : v < a' := by rw [hvdef]; linarith
    have h1 : ψ v = v := hfix v (fun h => absurd h.1 (not_le.mpr hv))
    have h2 : ψ v < ψ u := hψ (lt_of_lt_of_le hv hu.1)
    have h3 : ψ u < v := by rw [hvdef]; linarith
    linarith
  · by_contra hlt
    push Not at hlt
    set v := (ψ u + b') / 2 with hvdef
    have hv : b' < v := by rw [hvdef]; linarith
    have h1 : ψ v = v := hfix v (fun h => absurd h.2 (not_le.mpr hv))
    have h2 : ψ u < ψ v := hψ (lt_of_le_of_lt hu.2 hv)
    have h3 : v < ψ u := by rw [hvdef]; linarith
    linarith

/-- The translation region of the one-dimensional flow lies in its support interval. -/
private theorem Icc_subset_of_translating {φ : ℝ → ℝ → ℝ} {a' b' m₁ m₂ : ℝ} (hm : m₁ < m₂)
    (hfix : ∀ s u, u ∉ Icc a' b' → φ s u = u)
    (htr : ∀ s u, u ∈ Icc m₁ m₂ → u + s ∈ Icc m₁ m₂ → φ s u = u + s) :
    Icc m₁ m₂ ⊆ Icc a' b' := by
  intro u hu
  by_contra hout
  set d := (m₂ - m₁) / 2 with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  by_cases hmid : u ≤ (m₁ + m₂) / 2
  · have h1 := htr d u hu ⟨by linarith [hu.1], by rw [hddef]; linarith⟩
    have h2 := hfix d u hout
    linarith
  · have h1 := htr (-d) u hu ⟨by rw [hddef]; linarith, by linarith [hu.2]⟩
    have h2 := hfix (-d) u hout
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- LC35, kernel form. -/
theorem exists_band_graph_isotopy {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b c ρ : ℝ}
    (hc : c ∈ Icc a b) (hρ : ρ ∈ Ioo a b) (hB : IsCompact (f ⁻¹' Icc a b))
    (Φ : ℝ → Diffeomorph I I M M ∞)
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s)
    {h : M → ℝ} {V : Set M} (hV : IsOpen V) (hSV : ∀ x, f x = c → x ∈ V)
    (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h V) (hah : ∀ x, f x = c → a < h x)
    (hhb : ∀ x, f x = c → h x < b) :
    ∃ G : ℝ → Diffeomorph I I M M ∞,
      G 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (G q.1).symm q.2) ∧
      (∃ T : Set M, IsCompact T ∧ T ⊆ f ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ T → G t x = x ∧ (G t).symm x = x) ∧
      G 1 '' ({x | f x ≤ a} ∪ {y | ∃ x, f x = c ∧ ∃ u ∈ Icc a (h x), y = Φ (u - c) x}) =
        {x | f x ≤ ρ} := by
  classical
  -- The level `Σ = f⁻¹(c)` and the range of the heights.
  set Sg : Set M := f ⁻¹' {c} with hSgdef
  have hSgB : Sg ⊆ f ⁻¹' Icc a b := by
    intro x hx
    rw [hSgdef, mem_preimage, mem_singleton_iff] at hx
    rw [mem_preimage, hx]
    exact hc
  have hSg : IsCompact Sg :=
    hB.of_isClosed_subset (isClosed_singleton.preimage hf.continuous) hSgB
  set Kset : Set ℝ := insert ρ (h '' Sg) with hKdef
  have hK : IsCompact Kset :=
    (hSg.image_of_continuousOn (hh.continuousOn.mono fun x hx => hSV x hx)).insert ρ
  have hKne : Kset.Nonempty := ⟨ρ, mem_insert ρ _⟩
  have hKab : Kset ⊆ Ioo a b := by
    rintro u (rfl | ⟨x, hx, rfl⟩)
    · exact hρ
    · exact ⟨hah x hx, hhb x hx⟩
  set m₁ := sInf Kset with hm₁def
  set m₂ := sSup Kset with hm₂def
  have hmem : ∀ u ∈ Kset, u ∈ Icc m₁ m₂ := fun u hu =>
    ⟨csInf_le hK.bddBelow hu, le_csSup hK.bddAbove hu⟩
  have hm₁ab := hKab (hK.sInf_mem hKne)
  have hm₂ab := hKab (hK.sSup_mem hKne)
  have hm₁₂ : m₁ ≤ m₂ := (hmem ρ (mem_insert ρ _)).1.trans (hmem ρ (mem_insert ρ _)).2
  set ε := min (m₁ - a) (b - m₂) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (lt_min (by linarith [hm₁ab.1]) (by linarith [hm₂ab.2])) (by norm_num)
  have hεa : ε < m₁ - a := by
    have := min_le_left (m₁ - a) (b - m₂)
    have : 0 < m₁ - a := by linarith [hm₁ab.1]
    rw [hεdef]; linarith
  have hεb : ε < b - m₂ := by
    have := min_le_right (m₁ - a) (b - m₂)
    have : 0 < b - m₂ := by linarith [hm₂ab.2]
    rw [hεdef]; linarith
  obtain ⟨a', b', ha', hab', hb', φ, hφ, hφ0, hφadd, hφfix, hφmono, hφtr⟩ :=
    exists_real_flow_translating (a := a) (b := b) (m₁ := m₁ - ε) (m₂ := m₂ + ε)
      (by linarith) (by linarith) (by linarith)
  have hsub := Icc_subset_of_translating (by linarith) hφfix hφtr
  have ha'm : a' ≤ m₁ - ε := (hsub ⟨le_rfl, by linarith⟩).1
  have hb'm : m₂ + ε ≤ b' := (hsub ⟨by linarith, le_rfl⟩).2
  have hρm : ρ ∈ Icc (m₁ - ε) (m₂ + ε) := by
    have := hmem ρ (mem_insert ρ _)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hhm : ∀ x, f x = c → h x ∈ Icc (m₁ - ε) (m₂ + ε) := by
    intro x hx
    have := hmem (h x) (mem_insert_of_mem ρ ⟨x, hx, rfl⟩)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- Flow-line bookkeeping on the band.
  let R : M → M := fun y => Φ (c - f y) y
  have hshift : ∀ y, f y ∈ Icc a b → ∀ s, f y + s ∈ Icc a b → f (Φ s y) = f y + s := by
    intro y hy s hs
    have h1 := hval y hy (f y + s) hs
    rwa [add_sub_cancel_left] at h1
  have hRlev : ∀ y, f y ∈ Icc a b → f (R y) = c := fun y hy => hval y hy c hc
  have hRflow : ∀ y, f y ∈ Icc a b → ∀ s, f y + s ∈ Icc a b → R (Φ s y) = R y := by
    intro y hy s hs
    change Φ (c - f (Φ s y)) (Φ s y) = Φ (c - f y) y
    rw [hshift y hy s hs, ← hΦadd]
    congr 2
    ring
  have hrecon : ∀ y, Φ (f y - c) (R y) = y := by
    intro y
    change Φ (f y - c) (Φ (c - f y) y) = y
    rw [← hΦadd, show c - f y + (f y - c) = 0 by ring, hΦ0]
  have hIcc'ab : Icc a' b' ⊆ Icc a b := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  let δ : M → ℝ := fun y => ρ - h (R y)
  let G0 : ℝ → M → M := fun t y => Φ (φ (t * δ y) (f y) - f y) y
  let G1 : ℝ → M → M := fun t y => Φ (φ (-(t * δ y)) (f y) - f y) y
  have hout0 : ∀ t y, f y ∉ Icc a' b' → G0 t y = y := by
    intro t y hy
    change Φ (φ (t * δ y) (f y) - f y) y = y
    rw [hφfix _ _ hy, sub_self, hΦ0]
  have hout1 : ∀ t y, f y ∉ Icc a' b' → G1 t y = y := by
    intro t y hy
    change Φ (φ (-(t * δ y)) (f y) - f y) y = y
    rw [hφfix _ _ hy, sub_self, hΦ0]
  -- Inside the support interval: values and flow lines.
  have hin : ∀ s y, f y ∈ Icc a' b' →
      f (Φ (φ s (f y) - f y) y) = φ s (f y) ∧ R (Φ (φ s (f y) - f y) y) = R y ∧
        φ s (f y) ∈ Icc a' b' := by
    intro s y hy
    have hφy := mem_Icc_of_strictMono_fix (hφmono s) (hφfix s) hy
    have hs : f y + (φ s (f y) - f y) ∈ Icc a b := by
      rw [add_sub_cancel]; exact hIcc'ab hφy
    refine ⟨?_, hRflow y (hIcc'ab hy) _ hs, hφy⟩
    rw [hshift y (hIcc'ab hy) _ hs, add_sub_cancel]
  have hinv : ∀ s y, φ (-s) (φ s y) = y := by
    intro s y
    rw [← hφadd, add_neg_cancel, hφ0]
  have hG10 : ∀ t y, G1 t (G0 t y) = y := by
    intro t y
    by_cases hy : f y ∈ Icc a' b'
    · obtain ⟨hf1, hR1, hmem1⟩ := hin (t * δ y) y hy
      have hδ : δ (G0 t y) = δ y := by
        change ρ - h (R (G0 t y)) = ρ - h (R y)
        rw [show G0 t y = Φ (φ (t * δ y) (f y) - f y) y from rfl, hR1]
      change Φ (φ (-(t * δ (G0 t y))) (f (G0 t y)) - f (G0 t y)) (G0 t y) = y
      rw [hδ, show G0 t y = Φ (φ (t * δ y) (f y) - f y) y from rfl, hf1, hinv, ← hΦadd,
        show φ (t * δ y) (f y) - f y + (f y - φ (t * δ y) (f y)) = 0 by ring, hΦ0]
    · rw [hout0 t y hy, hout1 t y hy]
  have hG01 : ∀ t y, G0 t (G1 t y) = y := by
    intro t y
    by_cases hy : f y ∈ Icc a' b'
    · obtain ⟨hf1, hR1, hmem1⟩ := hin (-(t * δ y)) y hy
      have hδ : δ (G1 t y) = δ y := by
        change ρ - h (R (G1 t y)) = ρ - h (R y)
        rw [show G1 t y = Φ (φ (-(t * δ y)) (f y) - f y) y from rfl, hR1]
      change Φ (φ (t * δ (G1 t y)) (f (G1 t y)) - f (G1 t y)) (G1 t y) = y
      rw [hδ, show G1 t y = Φ (φ (-(t * δ y)) (f y) - f y) y from rfl, hf1]
      have hinv' : φ (t * δ y) (φ (-(t * δ y)) (f y)) = f y := by
        have := hinv (-(t * δ y)) (f y)
        rwa [neg_neg] at this
      rw [hinv', ← hΦadd,
        show φ (-(t * δ y)) (f y) - f y + (f y - φ (-(t * δ y)) (f y)) = 0 by ring, hΦ0]
    · rw [hout1 t y hy, hout0 t y hy]
  -- Smoothness.
  have hR : ContMDiff I I ∞ R :=
    hΦc.comp ((contMDiff_const.sub hf).prodMk contMDiff_id)
  have hφm : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => φ p.1 p.2) := hφ.contMDiff
  have hjoint : ∀ σ : ℝ → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ →
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Φ (φ (σ q.1 * δ q.2) (f q.2) - f q.2) q.2) := by
    intro σ hσ q
    by_cases hq : f q.2 ∈ Icc a' b'
    · have hqV : R q.2 ∈ V := hSV _ (hRlev _ (hIcc'ab hq))
      have hhR : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => h (R y)) q.2 :=
        (hh.contMDiffAt (hV.mem_nhds hqV)).comp q.2 (hR q.2)
      have hδq : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => σ q.1 * δ q.2) q :=
        ((hσ q.1).comp q contMDiffAt_fst).mul
          ((contMDiffAt_const.sub hhR).comp q contMDiffAt_snd)
      have hfq : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.2) q :=
        (hf q.2).comp q contMDiffAt_snd
      have hτ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => φ (σ q.1 * δ q.2) (f q.2) - f q.2) q :=
        ((hφm _).comp q (hδq.prodMk_space hfq)).sub hfq
      exact (hΦc _).comp q (hτ.prodMk contMDiffAt_snd)
    · have hopen : IsOpen {y : M | f y ∉ Icc a' b'} :=
        (isClosed_Icc.preimage hf.continuous).isOpen_compl
      apply (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := I)).congr_of_eventuallyEq
      filter_upwards [(hopen.preimage continuous_snd).mem_nhds hq] with r hr
      rw [hφfix _ _ hr, sub_self, hΦ0]
  have hG0c : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G0 q.1 q.2) :=
    hjoint id contMDiff_id
  have hG1c : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G1 q.1 q.2) := by
    have h1 := hjoint (fun t => -t) contMDiff_id.neg
    refine h1.congr fun q => ?_
    change Φ (φ (-(q.1 * δ q.2)) (f q.2) - f q.2) q.2 =
      Φ (φ (-q.1 * δ q.2) (f q.2) - f q.2) q.2
    rw [neg_mul]
  let G : ℝ → Diffeomorph I I M M ∞ := fun t =>
    { toFun := G0 t
      invFun := G1 t
      left_inv := hG10 t
      right_inv := hG01 t
      contMDiff_toFun := hG0c.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hG1c.comp (contMDiff_const.prodMk contMDiff_id) }
  -- Membership in `D_h`.
  set D : Set M := {x | f x ≤ a} ∪ {y | ∃ x, f x = c ∧ ∃ u ∈ Icc a (h x), y = Φ (u - c) x}
    with hDdef
  have hD : ∀ y, y ∈ D ↔ f y ≤ a ∨ (f y ∈ Icc a b ∧ f y ≤ h (R y)) := by
    intro y
    constructor
    · rintro (hy | ⟨x, hx, u, hu, rfl⟩)
      · exact Or.inl hy
      · have hxB : f x ∈ Icc a b := by rw [hx]; exact hc
        have huB : u ∈ Icc a b := ⟨hu.1, hu.2.trans (hhb x hx).le⟩
        have hfu : f (Φ (u - c) x) = u := by
          have := hval x hxB u huB
          rwa [hx] at this
        have hRu : R (Φ (u - c) x) = x := by
          change Φ (c - f (Φ (u - c) x)) (Φ (u - c) x) = x
          rw [hfu, ← hΦadd, show u - c + (c - u) = 0 by ring, hΦ0]
        right
        rw [hfu, hRu]
        exact ⟨huB, hu.2⟩
    · rintro (hy | ⟨hyB, hyh⟩)
      · exact Or.inl hy
      · by_cases hya : f y ≤ a
        · exact Or.inl hya
        · right
          exact ⟨R y, hRlev y hyB, f y, ⟨hyB.1, hyh⟩, (hrecon y).symm⟩
  have hkey : ∀ y, y ∈ D ↔ f (G0 1 y) ≤ ρ := by
    intro y
    rw [hD y]
    by_cases hy : f y ∈ Icc a' b'
    · obtain ⟨hf1, -, -⟩ := hin (1 * δ y) y hy
      change _ ↔ f (Φ (φ (1 * δ y) (f y) - f y) y) ≤ ρ
      rw [hf1, one_mul]
      have hyB := hIcc'ab hy
      have hRy := hRlev y hyB
      have htrans : φ (δ y) (h (R y)) = ρ := by
        rw [hφtr (δ y) (h (R y)) (hhm _ hRy) (by
          change h (R y) + (ρ - h (R y)) ∈ _
          rw [add_sub_cancel]
          exact hρm)]
        change h (R y) + (ρ - h (R y)) = ρ
        ring
      rw [← htrans, (hφmono (δ y)).le_iff_le]
      have hya : ¬ f y ≤ a := not_le.mpr (by linarith [hy.1])
      constructor
      · rintro (h1 | ⟨-, h2⟩)
        · exact absurd h1 hya
        · exact h2
      · intro h2
        exact Or.inr ⟨hyB, h2⟩
    · rw [hout0 1 y hy]
      rcases not_and_or.mp hy with hlo | hhi
      · have hlt : f y < a' := lt_of_not_ge hlo
        constructor
        · intro _
          linarith [hρm.1]
        · intro _
          by_cases hya : f y ≤ a
          · exact Or.inl hya
          · have hyB : f y ∈ Icc a b := ⟨(not_le.mp hya).le, by linarith⟩
            have hRy := hRlev y hyB
            exact Or.inr ⟨hyB, by linarith [(hhm _ hRy).1]⟩
      · have hgt : b' < f y := lt_of_not_ge hhi
        constructor
        · rintro (h1 | ⟨hyB, h2⟩)
          · linarith
          · have hRy := hRlev y hyB
            linarith [(hhm _ hRy).2]
        · intro h1
          linarith [hρm.2]
  refine ⟨G, ?_, hG0c, hG1c, ⟨f ⁻¹' Icc a' b',
    hB.of_isClosed_subset (isClosed_Icc.preimage hf.continuous) (fun y hy => hIcc'ab hy),
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩,
    fun t x hx => ⟨hout0 t x hx, hout1 t x hx⟩⟩, ?_⟩
  · apply Diffeomorph.ext
    intro y
    change Φ (φ (0 * δ y) (f y) - f y) y = y
    rw [zero_mul, hφ0, sub_self, hΦ0]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hkey y).mp hy
    · intro hz
      refine ⟨G1 1 z, (hkey _).mpr ?_, hG01 1 z⟩
      rw [hG01]
      exact hz

/-- LC35, last assertion: all sublevels `{f ≤ ρ}`, `ρ ∈ (a,b)`, are smoothly ambient isotopic
(constant heights). -/
theorem exists_band_sublevel_isotopy {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b c ρ ρ' : ℝ}
    (hc : c ∈ Icc a b) (hρ : ρ ∈ Ioo a b) (hρ' : ρ' ∈ Ioo a b)
    (hB : IsCompact (f ⁻¹' Icc a b)) (Φ : ℝ → Diffeomorph I I M M ∞)
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s) :
    ∃ G : ℝ → Diffeomorph I I M M ∞,
      G 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (G q.1).symm q.2) ∧
      (∃ T : Set M, IsCompact T ∧ T ⊆ f ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ T → G t x = x ∧ (G t).symm x = x) ∧
      G 1 '' {x | f x ≤ ρ'} = {x | f x ≤ ρ} := by
  obtain ⟨G, hG0, hGc, hGs, hT, himg⟩ := exists_band_graph_isotopy hf hc hρ hB Φ hΦc hΦadd hΦ0
    hval (h := fun _ => ρ') isOpen_univ (fun _ _ => mem_univ _) contMDiffOn_const
    (fun _ _ => hρ'.1) (fun _ _ => hρ'.2)
  refine ⟨G, hG0, hGc, hGs, hT, ?_⟩
  rw [← himg]
  congr 1
  ext y
  constructor
  · intro hy
    by_cases hya : f y ≤ a
    · exact Or.inl hya
    · have hyB : f y ∈ Icc a b := ⟨(not_le.mp hya).le, hy.trans hρ'.2.le⟩
      refine Or.inr ⟨Φ (c - f y) y, hval y hyB c hc, f y, ⟨hyB.1, hy⟩, ?_⟩
      rw [← hΦadd, show c - f y + (f y - c) = 0 by ring, hΦ0]
  · rintro (hy | ⟨x, hx, u, hu, rfl⟩)
    · exact hy.trans hρ'.1.le
    · have hxB : f x ∈ Icc a b := by rw [hx]; exact hc
      have := hval x hxB u ⟨hu.1, hu.2.trans hρ'.2.le⟩
      rw [hx] at this
      change f (Φ (u - c) x) ≤ ρ'
      rw [this]
      exact hu.2

section Binding

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- LC35, binding form: `η` smooth only on an open `W ⊇ η⁻¹[a,b]` (the LC30 radial function),
`Φ` a product flow for `η` as produced by LC46/LC33. The domain
`D_h = {η ≤ a} ∪ {Φ (u - c) x : η x = c, a ≤ u ≤ h x}` is smoothly ambient isotopic to
`{η ≤ ρ}` through diffeomorphisms supported in one compact subset of `η⁻¹(a,b)`. -/
theorem exists_band_graph_isotopy_of_contMDiffOn {η : M → ℝ} (hη : Continuous η) {W : Set M}
    (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b c ρ : ℝ} (hab : a < b)
    (hc : c ∈ Icc a b) (hρ : ρ ∈ Ioo a b) (hK : IsCompact (η ⁻¹' Icc a b))
    (hKW : η ⁻¹' Icc a b ⊆ W) (Φ : ℝ → Diffeomorph I I M M ∞)
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s)
    {h : M → ℝ} {V : Set M} (hV : IsOpen V) (hSV : ∀ x, η x = c → x ∈ V)
    (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h V) (hah : ∀ x, η x = c → a < h x)
    (hhb : ∀ x, η x = c → h x < b) :
    ∃ G : ℝ → Diffeomorph I I M M ∞,
      G 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (G q.1).symm q.2) ∧
      (∃ T : Set M, IsCompact T ∧ T ⊆ η ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ T → G t x = x ∧ (G t).symm x = x) ∧
      G 1 '' ({x | η x ≤ a} ∪ {y | ∃ x, η x = c ∧ ∃ u ∈ Icc a (h x), y = Φ (u - c) x}) =
        {x | η x ≤ ρ} := by
  obtain ⟨f, hf, ⟨O, -, hKO, -, hEq⟩, hlo, hhi⟩ := exists_contMDiff_eqOn_band hη hW hηW hab hK hKW
  have hband : ∀ x, f x ∈ Icc a b ↔ η x ∈ Icc a b := fun x => band_mem_Icc_iff hEq hKO hlo hhi
  have hfK : f ⁻¹' Icc a b = η ⁻¹' Icc a b := Set.ext hband
  have hfval : ∀ x, η x ∈ Icc a b → f x = η x := fun x hx => hEq (hKO hx)
  have hlev : ∀ x, f x = c ↔ η x = c := fun x => band_eq_iff hEq hKO hlo hhi hc
  have hle : ∀ t ∈ Icc a b, ∀ x, f x ≤ t ↔ η x ≤ t := fun t ht x => band_le_iff hEq hKO hlo hhi ht
  have hvalf : ∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s := by
    intro x hx s hs
    have hxη := (hband x).mp hx
    rw [hfval x hxη]
    have h1 := hval x hxη s hs
    rw [hfval _ (by rw [h1]; exact hs), h1]
  obtain ⟨G, hG0, hGc, hGs, ⟨T, hT, hTab, hTfix⟩, himg⟩ :=
    exists_band_graph_isotopy hf hc hρ (hfK ▸ hK) Φ hΦc hΦadd hΦ0 hvalf hV
      (fun x hx => hSV x ((hlev x).mp hx)) hh (fun x hx => hah x ((hlev x).mp hx))
      (fun x hx => hhb x ((hlev x).mp hx))
  refine ⟨G, hG0, hGc, hGs, ⟨T, hT, fun x hx => ?_, hTfix⟩, ?_⟩
  · have hxf := hTab hx
    have hxη : η x ∈ Icc a b := (hband x).mp (Ioo_subset_Icc_self hxf)
    rw [mem_preimage, ← hfval x hxη]
    exact hxf
  · have hD : ({x | η x ≤ a} ∪ {y | ∃ x, η x = c ∧ ∃ u ∈ Icc a (h x), y = Φ (u - c) x}) =
        ({x | f x ≤ a} ∪ {y | ∃ x, f x = c ∧ ∃ u ∈ Icc a (h x), y = Φ (u - c) x}) := by
      ext y
      simp only [mem_union, mem_ofPred_eq, hle a ⟨le_rfl, hab.le⟩, hlev]
    rw [hD, himg]
    ext y
    exact hle ρ (Ioo_subset_Icc_self hρ) y

/-- LC35, last assertion, binding form: the sublevels `{η ≤ ρ}`, `ρ ∈ (a,b)`, of a radial
function are smoothly ambient isotopic to one another. -/
theorem exists_band_sublevel_isotopy_of_contMDiffOn {η : M → ℝ} (hη : Continuous η)
    {W : Set M} (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b c ρ ρ' : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b) (hρ : ρ ∈ Ioo a b) (hρ' : ρ' ∈ Ioo a b)
    (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W) (Φ : ℝ → Diffeomorph I I M M ∞)
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s) :
    ∃ G : ℝ → Diffeomorph I I M M ∞,
      G 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (G q.1).symm q.2) ∧
      (∃ T : Set M, IsCompact T ∧ T ⊆ η ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ T → G t x = x ∧ (G t).symm x = x) ∧
      G 1 '' {x | η x ≤ ρ'} = {x | η x ≤ ρ} := by
  obtain ⟨G, hG0, hGc, hGs, hT, himg⟩ := exists_band_graph_isotopy_of_contMDiffOn hη hW hηW
    hab hc hρ hK hKW Φ hΦc hΦadd hΦ0 hval (h := fun _ => ρ') isOpen_univ
    (fun _ _ => mem_univ _) contMDiffOn_const (fun _ _ => hρ'.1) (fun _ _ => hρ'.2)
  refine ⟨G, hG0, hGc, hGs, hT, ?_⟩
  rw [← himg]
  congr 1
  ext y
  constructor
  · intro hy
    by_cases hya : η y ≤ a
    · exact Or.inl hya
    · have hyB : η y ∈ Icc a b := ⟨(not_le.mp hya).le, hy.trans hρ'.2.le⟩
      refine Or.inr ⟨Φ (c - η y) y, hval y hyB c hc, η y, ⟨hyB.1, hy⟩, ?_⟩
      rw [← hΦadd, show c - η y + (η y - c) = 0 by ring, hΦ0]
  · rintro (hy | ⟨x, hx, u, hu, rfl⟩)
    · exact hy.trans hρ'.1.le
    · have hxB : η x ∈ Icc a b := by rw [hx]; exact hc
      have := hval x hxB u ⟨hu.1, hu.2.trans hρ'.2.le⟩
      rw [hx] at this
      change η (Φ (u - c) x) ≤ ρ'
      rw [this]
      exact hu.2

end Binding

end DifferentialGeometry.Geometry.Collapse
