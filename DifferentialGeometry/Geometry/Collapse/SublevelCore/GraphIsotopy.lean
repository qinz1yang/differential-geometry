import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue

/-!
# Moving a graph to a constant level in product coordinates

Shared kernel of the sublevel-and-core family (chapter 13): the vertical isotopy used in the proofs
of LC35 (`lem:collapse-smooth-graph-isotopy`, master207A 21535–21571), LC47
(`lem:collapse-common-field-isotopy`, 22289–22347) and LC55
(`thm:collapse-point-distance-model-core`, 22905–23003).

Let `Σ` be a compact manifold (any model, no boundary assumption), `a < b`, `ρ ∈ (a, b)` and
`h : Σ → (a, b)` of class `C^n`. We build `Φ : ℝ → Σ × ℝ ≃ Σ × ℝ`, each `Φ t` a `C^n`
diffeomorphism, with `Φ 0 = id`, `(t, z) ↦ Φ t z` and `(t, z) ↦ (Φ t)⁻¹ z` jointly `C^n`,
preserving the `Σ`-coordinate, strictly increasing on every fibre, equal to the identity off the
compact slab `Σ × [a', b']` for some `a < a' < b' < b`, and with `Φ 1` carrying the closed subgraph
`{u ≤ h x}`, the graph and the open subgraph onto `{u ≤ ρ}`, `{u = ρ}` and `{u < ρ}`.

The construction uses ONE autonomous compactly supported field `β(u) ∂_u` on `ℝ` with `β = 1` near
`[min (h ∪ ρ), max (h ∪ ρ)]` and its smooth global flow `φ` (`Analysis/ODE/Flow/CompactSupport`):
`Φ t (x, u) = (x, φ (t (ρ - h x)) u)`. On the region where `β = 1` the flow is a unit-speed
translation, so `φ (ρ - h x) (h x) = ρ`. No time-dependent ODE is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis.ODE

/-- **One-dimensional compactly supported flow.** For `a < m₁ ≤ m₂ < b` there are
`a < a' < b' < b` and a jointly smooth flow `φ` on `ℝ` that fixes every point outside `[a', b']`,
consists of strictly increasing maps, and translates at unit speed inside `[m₁, m₂]`. -/
theorem exists_real_flow_translating {a b m₁ m₂ : ℝ} (ha : a < m₁) (hm : m₁ ≤ m₂) (hb : m₂ < b) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ ∃ φ : ℝ → ℝ → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) ∧
      (∀ u, φ 0 u = u) ∧ (∀ s t u, φ (s + t) u = φ t (φ s u)) ∧
      (∀ s u, u ∉ Icc a' b' → φ s u = u) ∧ (∀ s, StrictMono (φ s)) ∧
      ∀ s u, u ∈ Icc m₁ m₂ → u + s ∈ Icc m₁ m₂ → φ s u = u + s := by
  classical
  -- The bump `β`: equal to one on `[m₁ - ε, m₂ + ε]`, supported in `[m₁ - 2ε, m₂ + 2ε]`.
  set ε : ℝ := min (m₁ - a) (b - m₂) / 3 with hεdef
  have hε : 0 < ε := by
    simp only [hεdef]; exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hεa : 3 * ε ≤ m₁ - a := by
    simp only [hεdef]; linarith [min_le_left (m₁ - a) (b - m₂)]
  have hεb : 3 * ε ≤ b - m₂ := by
    simp only [hεdef]; linarith [min_le_right (m₁ - a) (b - m₂)]
  set c : ℝ := (m₁ + m₂) / 2 with hcdef
  set rIn : ℝ := (m₂ - m₁) / 2 + ε with hrIndef
  let β : ContDiffBump c := ⟨rIn, rIn + ε, by simp only [hrIndef]; linarith, by linarith⟩
  have hβ1 : ∀ u ∈ Icc (m₁ - ε) (m₂ + ε), β u = 1 := by
    intro u hu
    apply β.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -rIn ≤ u - c ∧ u - c ≤ rIn
    simp only [hrIndef, hcdef]
    constructor <;> linarith [hu.1, hu.2]
  set a' : ℝ := m₁ - 2 * ε with ha'def
  set b' : ℝ := m₂ + 2 * ε with hb'def
  have hβsupp : tsupport (β : ℝ → ℝ) ⊆ Icc a' b' := by
    rw [β.tsupport_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hu
    change -(rIn + ε) ≤ u - c ∧ u - c ≤ rIn + ε at hu
    simp only [hrIndef, hcdef] at hu
    constructor <;> linarith [hu.1, hu.2]
  -- The field on the manifold `ℝ`.
  let v : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun x => β x
  have hv : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : ℝ => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr β.contDiff
  have hvsupp : IsCompact (tsupport v) := β.hasCompactSupport.isCompact
  set hcomplete := exists_globalIntegralCurve_of_compactSupport v hv hvsupp with hcompdef
  let φ : ℝ → ℝ → ℝ := fun s u => curveAt v hcomplete u s
  have hv1 : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (1 : WithTop ℕ∞)
      (fun x : ℝ => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    hv.of_le (by norm_num)
  have hjoint : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => φ p.1 p.2) :=
    contMDiff_globalFlow_joint_of_compactSupport v hv hvsupp
  have hφc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hjoint
    exact contMDiff_iff_contDiff.mp hjoint
  have hzero : ∀ u, φ 0 u = u := fun u => curveAt_zero v hcomplete u
  have hadd : ∀ s t u, φ (s + t) u = φ t (φ s u) := fun s t u =>
    curveAt_add v hv1 hcomplete u s t
  have hfix : ∀ s u, u ∉ Icc a' b' → φ s u = u := fun s u hu =>
    curveAt_eq_self_of_not_mem_tsupport v hv hcomplete (fun h => hu (hβsupp h)) s
  -- Each time-`s` map is continuous and injective, fixes `a' - 1 < b' + 1`, hence is increasing.
  have hmono : ∀ s, StrictMono (φ s) := by
    intro s
    have hc : Continuous (φ s) :=
      hφc.continuous.comp (continuous_const.prodMk continuous_id)
    have hinj : Injective (φ s) := curveAt_injective v hv1 hcomplete s
    rcases hc.strictMono_of_inj hinj with hsm | hsa
    · exact hsm
    · exfalso
      have h1 := hfix s (a' - 1) (fun h => by linarith [h.1])
      have h2 := hfix s (b' + 1) (fun h => by linarith [h.2])
      have hlt : a' - 1 < b' + 1 := by simp only [ha'def, hb'def]; linarith
      have := hsa hlt
      rw [h1, h2] at this
      linarith
  -- Each orbit is a differentiable solution of `u' = β u`.
  have hderiv : ∀ u t, HasDerivAt (fun s => φ s u) (β (φ t u)) t := by
    intro u t
    have hγ := curveAt_integralCurve v hcomplete u t
    have hf : HasFDerivAt (curveAt v hcomplete u)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (β (φ t u))) t := HasMFDerivAt.hasFDerivAt hγ
    have := hf.hasDerivAt
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
      using this
  have hβlip : ∃ K, LipschitzWith K (β : ℝ → ℝ) := by
    obtain ⟨K, hK⟩ := β.contDiff.lipschitzWith_of_hasCompactSupport β.hasCompactSupport
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact ⟨K, hK⟩
  obtain ⟨K, hK⟩ := hβlip
  -- Unit-speed translation for nonnegative times inside the plateau.
  have htrans_nonneg : ∀ s u, 0 ≤ s → u ∈ Icc m₁ m₂ → u + s ∈ Icc m₁ m₂ → φ s u = u + s := by
    intro s u hs hu hus
    have hEq := ODE_solution_unique (v := fun _ => (β : ℝ → ℝ)) (K := K) (a := 0) (b := s)
      (f := fun t => φ t u) (g := fun t => u + t) (fun _ => hK)
      (fun t _ => (hderiv u t).continuousAt.continuousWithinAt)
      (fun t _ => (hderiv u t).hasDerivWithinAt)
      ((continuous_const.add continuous_id).continuousOn)
      (fun t ht => by
        have hmem : u + t ∈ Icc (m₁ - ε) (m₂ + ε) :=
          ⟨by linarith [hu.1, ht.1], by linarith [hus.2, ht.2.le]⟩
        rw [hβ1 _ hmem]
        exact ((hasDerivAt_id t).const_add u).hasDerivWithinAt)
      (by simp only [hzero, add_zero])
    exact hEq ⟨hs, le_rfl⟩
  have htrans : ∀ s u, u ∈ Icc m₁ m₂ → u + s ∈ Icc m₁ m₂ → φ s u = u + s := by
    intro s u hu hus
    rcases le_total 0 s with hs | hs
    · exact htrans_nonneg s u hs hu hus
    · -- Run the nonnegative case backwards from `u + s`.
      have hback := htrans_nonneg (-s) (u + s) (by linarith) hus (by simpa using hu)
      have hcalc : φ s (φ (-s) (u + s)) = φ (-s + s) (u + s) := (hadd (-s) s (u + s)).symm
      rw [hback, neg_add_cancel, hzero] at hcalc
      simp only [add_neg_cancel_right] at hcalc
      exact hcalc
  exact ⟨a', b', by simp only [ha'def]; linarith, by simp only [ha'def, hb'def]; linarith,
    by simp only [hb'def]; linarith, φ, hφc, hzero, hadd, hfix, hmono, htrans⟩

section Graph

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HQ : Type*} [TopologicalSpace HQ] {J : ModelWithCorners ℝ F HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- **Graph-to-level isotopy in product coordinates** (shared kernel for LC35, LC47, LC55).
`Q` is any compact manifold (the level `Σ` of the blueprint), `h : Q → (a, b)` is `C^n`, and
`ρ ∈ (a, b)`. The family `Φ t` consists of `C^n` diffeomorphisms of `Q × ℝ`, jointly `C^n` in
`(t, z)` together with their inverses, preserving the first coordinate, strictly increasing on
fibres, fixed off the slab `Q × [a', b']` with `a < a' < b' < b`, with `Φ 0 = id`, and `Φ 1` maps
the closed subgraph, the graph and the open subgraph of `h` onto `{u ≤ ρ}`, `{u = ρ}`, `{u < ρ}`. -/
theorem exists_graphIsotopy [CompactSpace Q] {n : ℕ∞} {a b ρ : ℝ} (h : Q → ℝ)
    (hh : ContMDiff J 𝓘(ℝ, ℝ) n h) (hah : ∀ x, a < h x) (hhb : ∀ x, h x < b)
    (hρ : ρ ∈ Ioo a b) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧
    ∃ Φ : ℝ → Diffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (Q × ℝ) (Q × ℝ) n,
      Φ 0 = Diffeomorph.refl (J.prod 𝓘(ℝ, ℝ)) (Q × ℝ) n ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
        (fun p : ℝ × (Q × ℝ) => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
        (fun p : ℝ × (Q × ℝ) => (Φ p.1).symm p.2) ∧
      (∀ t z, (Φ t z).1 = z.1) ∧ (∀ t z, ((Φ t).symm z).1 = z.1) ∧
      (∀ t x, StrictMono (fun u => (Φ t (x, u)).2)) ∧
      (∀ t z, z.2 ∉ Icc a' b' → Φ t z = z ∧ (Φ t).symm z = z) ∧
      Φ 1 '' {z | z.2 ≤ h z.1} = {z | z.2 ≤ ρ} ∧
      Φ 1 '' {z | z.2 = h z.1} = {z | z.2 = ρ} ∧
      Φ 1 '' {z | z.2 < h z.1} = {z | z.2 < ρ} := by
  classical
  -- A closed interval `[m₁, m₂] ⊆ (a, b)` containing `ρ` and all values of `h`.
  set K : Set ℝ := insert ρ (range h) with hKdef
  have hK : IsCompact K := (isCompact_range hh.continuous).insert ρ
  have hKne : K.Nonempty := ⟨ρ, mem_insert ρ _⟩
  have hKab : K ⊆ Ioo a b := by
    rintro u (rfl | ⟨x, rfl⟩)
    · exact hρ
    · exact ⟨hah x, hhb x⟩
  set m₁ : ℝ := sInf K with hm₁def
  set m₂ : ℝ := sSup K with hm₂def
  have hm₁K : m₁ ∈ K := hK.sInf_mem hKne
  have hm₂K : m₂ ∈ K := hK.sSup_mem hKne
  have hmemK : ∀ u ∈ K, u ∈ Icc m₁ m₂ := fun u hu =>
    ⟨csInf_le hK.bddBelow hu, le_csSup hK.bddAbove hu⟩
  have hρm : ρ ∈ Icc m₁ m₂ := hmemK ρ (mem_insert ρ _)
  have hhm : ∀ x, h x ∈ Icc m₁ m₂ := fun x => hmemK (h x) (mem_insert_of_mem ρ ⟨x, rfl⟩)
  obtain ⟨a', b', ha', hab', hb', φ, hφ, hzero, hadd, hfix, hmono, htrans⟩ :=
    exists_real_flow_translating (hKab hm₁K).1 (hρm.1.trans hρm.2) (hKab hm₂K).2
  -- The flow as a map of manifolds.
  have hφm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n (fun p : ℝ × ℝ => φ p.1 p.2) := by
    have h' := contMDiff_iff_contDiff.mpr hφ
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact h'.of_le (by exact_mod_cast le_top)
  -- Forward and backward maps.
  let fwd : ℝ → Q × ℝ → Q × ℝ := fun t z => (z.1, φ (t * (ρ - h z.1)) z.2)
  let bwd : ℝ → Q × ℝ → Q × ℝ := fun t z => (z.1, φ (-(t * (ρ - h z.1))) z.2)
  have hinv₁ : ∀ s u, φ (-s) (φ s u) = u := fun s u => by
    rw [← hadd, add_neg_cancel, hzero]
  have hinv₂ : ∀ s u, φ s (φ (-s) u) = u := fun s u => by
    rw [← hadd, neg_add_cancel, hzero]
  have hjoint : ∀ σ : ℝ, ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
      (fun p : ℝ × (Q × ℝ) => (p.2.1, φ (σ * (p.1 * (ρ - h p.2.1))) p.2.2)) := by
    intro σ
    have hpoly : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n
        (fun q : ℝ × ℝ => σ * (q.1 * (ρ - q.2))) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact contMDiff_iff_contDiff.mpr (by fun_prop)
    have hscalar : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) n
        (fun p : ℝ × (Q × ℝ) => σ * (p.1 * (ρ - h p.2.1))) :=
      hpoly.comp (contMDiff_fst.prodMk (hh.comp (contMDiff_fst.comp contMDiff_snd)))
    exact (contMDiff_fst.comp contMDiff_snd).prodMk
      (hφm.comp (hscalar.prodMk (contMDiff_snd.comp contMDiff_snd)))
  have hfwd : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
      (fun p : ℝ × (Q × ℝ) => fwd p.1 p.2) := by
    simpa only [one_mul] using hjoint 1
  have hbwd : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
      (fun p : ℝ × (Q × ℝ) => bwd p.1 p.2) := by
    simpa only [neg_one_mul] using hjoint (-1)
  have hslice : ∀ {f : ℝ × (Q × ℝ) → Q × ℝ},
      ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n f → ∀ t : ℝ,
        ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) n (fun z => f (t, z)) :=
    fun hf t => hf.comp (contMDiff_const.prodMk contMDiff_id)
  let Φ : ℝ → Diffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (Q × ℝ) (Q × ℝ) n := fun t =>
    { toFun := fwd t
      invFun := bwd t
      left_inv := fun z => by
        simp only [fwd, bwd]
        rw [hinv₁]
      right_inv := fun z => by
        simp only [fwd, bwd]
        rw [hinv₂]
      contMDiff_toFun := hslice hfwd t
      contMDiff_invFun := hslice hbwd t }
  have hΦ : ∀ t z, Φ t z = (z.1, φ (t * (ρ - h z.1)) z.2) := fun _ _ => rfl
  have hΦs : ∀ t z, (Φ t).symm z = (z.1, φ (-(t * (ρ - h z.1))) z.2) := fun _ _ => rfl
  -- The time-one inverse sends the level `ρ` over `x` back to `h x`.
  have hlevel : ∀ x, φ (-(1 * (ρ - h x))) ρ = h x := by
    intro x
    have ht := htrans (ρ - h x) (h x) (hhm x) (by simpa using hρm)
    calc φ (-(1 * (ρ - h x))) ρ = φ (-(ρ - h x)) (φ (ρ - h x) (h x)) := by
          rw [one_mul, ht, add_sub_cancel]
      _ = h x := hinv₁ _ _
  have hsymm_le : ∀ w : Q × ℝ, ((Φ 1).symm w).2 ≤ h ((Φ 1).symm w).1 ↔ w.2 ≤ ρ := by
    intro w
    rw [hΦs]
    dsimp only
    have key := (hmono (-(1 * (ρ - h w.1)))).le_iff_le (a := w.2) (b := ρ)
    rwa [hlevel w.1] at key
  have hsymm_eq : ∀ w : Q × ℝ, ((Φ 1).symm w).2 = h ((Φ 1).symm w).1 ↔ w.2 = ρ := by
    intro w
    rw [hΦs]
    dsimp only
    have key := (hmono (-(1 * (ρ - h w.1)))).injective.eq_iff (a := w.2) (b := ρ)
    rwa [hlevel w.1] at key
  have hsymm_lt : ∀ w : Q × ℝ, ((Φ 1).symm w).2 < h ((Φ 1).symm w).1 ↔ w.2 < ρ := by
    intro w
    rw [hΦs]
    dsimp only
    have key := (hmono (-(1 * (ρ - h w.1)))).lt_iff_lt (a := w.2) (b := ρ)
    rwa [hlevel w.1] at key
  refine ⟨a', b', ha', hab', hb', Φ, ?_, hfwd, hbwd, fun _ _ => rfl, fun _ _ => rfl,
    fun t x => by change StrictMono (fun u => φ (t * (ρ - h x)) u); exact hmono _,
    ?_, ?_, ?_, ?_⟩
  · ext z
    · rfl
    · change φ (0 * (ρ - h z.1)) z.2 = z.2
      rw [zero_mul, hzero]
  · intro t z hz
    refine ⟨?_, ?_⟩
    · rw [hΦ, hfix _ _ hz]
    · rw [hΦs, hfix _ _ hz]
  · rw [Diffeomorph.image_eq_preimage_symm]
    ext w
    exact hsymm_le w
  · rw [Diffeomorph.image_eq_preimage_symm]
    ext w
    exact hsymm_eq w
  · rw [Diffeomorph.image_eq_preimage_symm]
    ext w
    exact hsymm_lt w

/-- **Graph-to-level isotopy, compact-support form** (the form consumed by LC35/LC47/LC55): one
compact `S ⊆ Q × (a, b)` outside which every `Φ t` and its inverse are the identity. -/
theorem exists_graphIsotopy_compactSupport [CompactSpace Q] {n : ℕ∞} {a b ρ : ℝ} (h : Q → ℝ)
    (hh : ContMDiff J 𝓘(ℝ, ℝ) n h) (hah : ∀ x, a < h x) (hhb : ∀ x, h x < b)
    (hρ : ρ ∈ Ioo a b) :
    ∃ Φ : ℝ → Diffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (Q × ℝ) (Q × ℝ) n,
      Φ 0 = Diffeomorph.refl (J.prod 𝓘(ℝ, ℝ)) (Q × ℝ) n ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
        (fun p : ℝ × (Q × ℝ) => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, ℝ))) (J.prod 𝓘(ℝ, ℝ)) n
        (fun p : ℝ × (Q × ℝ) => (Φ p.1).symm p.2) ∧
      (∀ t z, (Φ t z).1 = z.1) ∧ (∀ t z, ((Φ t).symm z).1 = z.1) ∧
      (∀ t x, StrictMono (fun u => (Φ t (x, u)).2)) ∧
      (∃ S : Set (Q × ℝ), IsCompact S ∧ S ⊆ univ ×ˢ Ioo a b ∧
        ∀ t, ∀ z ∉ S, Φ t z = z ∧ (Φ t).symm z = z) ∧
      Φ 1 '' {z | z.2 ≤ h z.1} = {z | z.2 ≤ ρ} ∧
      Φ 1 '' {z | z.2 = h z.1} = {z | z.2 = ρ} ∧
      Φ 1 '' {z | z.2 < h z.1} = {z | z.2 < ρ} := by
  obtain ⟨a', b', ha', -, hb', Φ, h0, hj, hjs, h1, h1s, hm, hfix, hle, heq, hlt⟩ :=
    exists_graphIsotopy h hh hah hhb hρ
  refine ⟨Φ, h0, hj, hjs, h1, h1s, hm, ⟨univ ×ˢ Icc a' b', isCompact_univ.prod isCompact_Icc,
    ?_, fun t z hz => hfix t z (fun h' => hz ⟨mem_univ _, h'⟩)⟩, hle, heq, hlt⟩
  rintro z ⟨-, hz⟩
  exact ⟨mem_univ _, ha'.trans_le hz.1, hz.2.trans_lt hb'⟩

end Graph

end DifferentialGeometry.Geometry.Collapse
