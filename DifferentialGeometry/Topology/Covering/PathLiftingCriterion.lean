import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Covering maps from lifting of smooth paths

* `continuousOn_lift_family`: if `F : X → Y` is a local homeomorphism with `X` Hausdorff and
  every path `t ↦ G (a, t)`, `a ∈ S`, of a continuous family has a lift `t ↦ β (a, t)` on
  `[0, 1]` starting at a fixed point, then `β` is jointly continuous on `S × [0, 1]`.
* `isCoveringMap_of_forall_smooth_path_lift`: a surjective local homeomorphism `F : X → M`
  onto a boundaryless manifold, with `X` Hausdorff, along which every smooth path `[0, 1] → M`
  lifts from every point of the fibre over its start, is a covering map. The evenly covered
  neighbourhood of `x` is a chart ball; its sheets are the images of the sections obtained by
  lifting the straight segments of the chart from `x`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

section Family

variable {X Y A : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
  [TopologicalSpace A]

omit [T2Space X] in
private theorem continuousOn_prod_Icc_union {β : A × ℝ → X} {U : Set A} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (h₁ : ContinuousOn β (U ×ˢ Icc a b))
    (h₂ : ContinuousOn β (U ×ˢ Icc b c)) : ContinuousOn β (U ×ˢ Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc, prod_union]
  have hc₁ : closure (U ×ˢ Icc a b) ⊆ univ ×ˢ Icc a b := by
    rw [closure_prod_eq, isClosed_Icc.closure_eq]
    exact prod_mono (subset_univ _) le_rfl
  have hc₂ : closure (U ×ˢ Icc b c) ⊆ univ ×ˢ Icc b c := by
    rw [closure_prod_eq, isClosed_Icc.closure_eq]
    exact prod_mono (subset_univ _) le_rfl
  intro x hx
  apply ContinuousWithinAt.union
  · by_cases hx₁ : x ∈ U ×ˢ Icc a b
    · exact h₁ x hx₁
    · apply continuousWithinAt_of_notMem_closure
      intro hcl
      apply hx₁
      rcases hx with hx | hx
      · exact hx
      · exact ⟨hx.1, (hc₁ hcl).2⟩
  · by_cases hx₂ : x ∈ U ×ˢ Icc b c
    · exact h₂ x hx₂
    · apply continuousWithinAt_of_notMem_closure
      intro hcl
      apply hx₂
      rcases hx with hx | hx
      · exact ⟨hx.1, (hc₂ hcl).2⟩
      · exact hx

theorem continuousOn_lift_family {F : X → Y} (hF : IsLocalHomeomorph F) {S : Set A}
    (hS : IsOpen S) {G : A × ℝ → Y} (hG : ContinuousOn G (S ×ˢ univ)) {e₀ : X}
    {β : A × ℝ → X} (hβc : ∀ a ∈ S, ContinuousOn (fun t => β (a, t)) (Icc 0 1))
    (hβ0 : ∀ a ∈ S, β (a, 0) = e₀)
    (hβF : ∀ a ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, F (β (a, t)) = G (a, t)) :
    ContinuousOn β (S ×ˢ Icc 0 1) := by
  have hsep := T2Space.isSeparatedMap F
  have hinj := hF.isLocallyInjective
  rintro ⟨a₀, t₀⟩ ⟨ha₀, ht₀⟩
  let T : Set ℝ :=
    {t | t ∈ Icc (0 : ℝ) 1 ∧ ∃ U ∈ 𝓝 a₀, U ⊆ S ∧ ContinuousOn β (U ×ˢ Icc 0 t)}
  have h0T : (0 : ℝ) ∈ T := by
    refine ⟨⟨le_rfl, zero_le_one⟩, S, hS.mem_nhds ha₀, subset_rfl, ?_⟩
    refine (continuousOn_const (c := e₀)).congr ?_
    rintro ⟨a, t⟩ ⟨ha, ht⟩
    have h : t = 0 := le_antisymm ht.2 ht.1
    subst h
    exact hβ0 a ha
  have hbdd : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  have hTne : T.Nonempty := ⟨0, h0T⟩
  obtain ⟨hts0, hts1⟩ : sSup T ∈ Icc (0 : ℝ) 1 :=
    ⟨le_csSup hbdd h0T, csSup_le hTne fun t ht => ht.1.2⟩
  obtain ⟨e, hes, hFe⟩ := hF (β (a₀, sSup T))
  have hev : (fun t => β (a₀, t)) ⁻¹' e.source ∈ 𝓝[Icc (0 : ℝ) 1] sSup T :=
    (hβc a₀ ha₀ _ ⟨hts0, hts1⟩).preimage_mem_nhdsWithin (e.open_source.mem_nhds hes)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let K : Set ℝ := Icc (sSup T - δ / 2) (sSup T + δ / 2) ∩ Icc 0 1
  have hK : IsCompact K := isCompact_Icc.inter_right isClosed_Icc
  have hKsrc : ∀ s ∈ K, β (a₀, s) ∈ e.source := by
    intro s hs
    refine hδs ⟨?_, hs.2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1.1, hs.1.2]
  let O : Set (A × ℝ) := (S ×ˢ univ) ∩ G ⁻¹' e.target
  have hO : IsOpen O := hG.isOpen_inter_preimage (hS.prod isOpen_univ) e.open_target
  have hKO : {a₀} ×ˢ K ⊆ O := by
    rintro ⟨a, s⟩ ⟨ha, hs⟩
    rw [mem_singleton_iff] at ha
    subst ha
    refine ⟨⟨ha₀, trivial⟩, ?_⟩
    change G (a, s) ∈ e.target
    rw [← hβF a ha₀ s hs.2, hFe]
    exact e.map_source (hKsrc s hs)
  obtain ⟨u, v, hu, -, hau, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hO hKO
  obtain ⟨t₁, ht₁T, ht₁⟩ := exists_lt_of_lt_csSup hTne (show sSup T - δ / 2 < sSup T by linarith)
  have ht₁ts : t₁ ≤ sSup T := le_csSup hbdd ht₁T
  obtain ⟨⟨ht₁0, ht₁1⟩, U₁, hU₁, hU₁S, hβU₁⟩ := ht₁T
  have hcontA : ContinuousAt (fun a => β (a, t₁)) a₀ := by
    have h := hβU₁ (a₀, t₁) ⟨mem_of_mem_nhds hU₁, ⟨ht₁0, le_rfl⟩⟩
    have h2 : ContinuousWithinAt (fun a => β (a, t₁)) U₁ a₀ :=
      ContinuousWithinAt.comp (f := fun a => (a, t₁)) h
        (continuousWithinAt_id.prodMk continuousWithinAt_const)
        (fun a ha => ⟨ha, ⟨ht₁0, le_rfl⟩⟩)
    exact h2.continuousAt hU₁
  have ht₁src : β (a₀, t₁) ∈ e.source :=
    hKsrc t₁ ⟨⟨by linarith, by linarith⟩, ⟨ht₁0, ht₁1⟩⟩
  have hU'' : {a | β (a, t₁) ∈ e.source} ∈ 𝓝 a₀ :=
    hcontA.preimage_mem_nhds (e.open_source.mem_nhds ht₁src)
  let U₂ : Set A := U₁ ∩ u ∩ {a | β (a, t₁) ∈ e.source}
  have hU₂ : U₂ ∈ 𝓝 a₀ := inter_mem (inter_mem hU₁ (hu.mem_nhds (hau rfl))) hU''
  have hU₂S : U₂ ⊆ S := fun a ha => hU₁S ha.1.1
  let t₂ : ℝ := min (sSup T + δ / 2) 1
  have ht₁t₂ : t₁ ≤ t₂ := le_min (by linarith) ht₁1
  have hst₂ : sSup T ≤ t₂ := le_min (by linarith) hts1
  have hIcc : Icc t₁ t₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht₁0 (min_le_right _ _)
  have hmemK : ∀ s ∈ Icc t₁ t₂, s ∈ K := fun s hs =>
    ⟨⟨by linarith [hs.1], le_trans hs.2 (min_le_left _ _)⟩, hIcc hs⟩
  have htarget : ∀ a ∈ U₂, ∀ s ∈ Icc t₁ t₂, G (a, s) ∈ e.target := fun a ha s hs =>
    (huv ⟨ha.1.2, hKv (hmemK s hs)⟩).2
  have hagree : ∀ a ∈ U₂, ∀ s ∈ Icc t₁ t₂, β (a, s) = e.symm (G (a, s)) := by
    intro a ha s hs
    have haS : a ∈ S := hU₂S ha
    have hGa : ContinuousOn (fun s => G (a, s)) (Icc t₁ t₂) :=
      hG.comp (continuousOn_const.prodMk continuousOn_id) (fun s _ => ⟨haS, trivial⟩)
    have heq := hsep.eqOn_of_comp_eqOn hinj (s := Icc t₁ t₂) isPreconnected_Icc
      ((hβc a haS).mono hIcc) (e.continuousOn_symm.comp hGa (fun s hs => htarget a ha s hs))
      (by
        intro s hs
        simp only [comp_apply]
        rw [hβF a haS s (hIcc hs), hFe, e.right_inv (htarget a ha s hs)])
      (a := t₁) ⟨le_rfl, ht₁t₂⟩
      (by
        have h1 := hβF a haS t₁ ⟨ht₁0, ht₁1⟩
        rw [hFe] at h1
        change β (a, t₁) = e.symm (G (a, t₁))
        rw [← h1, e.left_inv ha.2])
    exact heq hs
  have hc₂ : ContinuousOn β (U₂ ×ˢ Icc t₁ t₂) := by
    have hcomp : ContinuousOn (fun p : A × ℝ => e.symm (G p)) (U₂ ×ˢ Icc t₁ t₂) :=
      e.continuousOn_symm.comp (hG.mono (fun p hp => ⟨hU₂S hp.1, trivial⟩))
        (fun p hp => htarget p.1 hp.1 p.2 hp.2)
    exact hcomp.congr (fun p hp => hagree p.1 hp.1 p.2 hp.2)
  have hc₁ : ContinuousOn β (U₂ ×ˢ Icc 0 t₁) :=
    hβU₁.mono (prod_mono (fun a ha => ha.1.1) le_rfl)
  have hc := continuousOn_prod_Icc_union ht₁0 ht₁t₂ hc₁ hc₂
  have ht₂T : t₂ ∈ T :=
    ⟨⟨le_trans hts0 hst₂, min_le_right _ _⟩, U₂, hU₂, hU₂S, hc⟩
  have ht₂le : t₂ ≤ sSup T := le_csSup hbdd ht₂T
  have ht₂one : t₂ = 1 := by
    rcases min_choice (sSup T + δ / 2) 1 with h | h
    · have h' : t₂ = sSup T + δ / 2 := h
      linarith
    · exact h
  rw [ht₂one] at hc
  refine (hc (a₀, t₀) ⟨mem_of_mem_nhds hU₂, ht₀⟩).mono_of_mem_nhdsWithin ?_
  exact Filter.mem_of_superset
    (inter_mem_nhdsWithin (S ×ˢ Icc (0 : ℝ) 1) (prod_mem_nhds hU₂ univ_mem))
    (fun p hp => ⟨hp.2.1, hp.1.2⟩)

end Family

section Covering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {X : Type*} [TopologicalSpace X] [T2Space X]

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space X] in
private theorem isOpen_image_section {F : X → M} (hF : IsLocalHomeomorph F) {V : Set M}
    (hV : IsOpen V) {s : M → X} (hs : ContinuousOn s V) (hFs : ∀ m ∈ V, F (s m) = m) :
    IsOpen (s '' V) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨e, hes, hFe⟩ := hF (s m)
  refine ⟨e.source ∩ F ⁻¹' (V ∩ s ⁻¹' e.source), ?_, ?_, ?_⟩
  · rintro w ⟨hw, hwV, hws⟩
    refine ⟨F w, hwV, ?_⟩
    apply e.injOn hws hw
    rw [← hFe]
    exact hFs (F w) hwV
  · exact e.open_source.inter
      ((hs.isOpen_inter_preimage hV e.open_source).preimage hF.continuous)
  · refine ⟨hes, ?_⟩
    rw [mem_preimage, hFs m hm]
    exact ⟨hm, hes⟩

theorem isCoveringMap_of_forall_smooth_path_lift {F : X → M} (hF : IsLocalHomeomorph F)
    (hsurj : Surjective F)
    (hlift : ∀ γ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) → ∀ z : X, F z = γ 0 →
      ∃ η : ℝ → X, ContinuousOn η (Icc 0 1) ∧ η 0 = z ∧ ∀ t ∈ Icc (0 : ℝ) 1, F (η t) = γ t) :
    IsCoveringMap F := by
  classical
  have hsep := T2Space.isSeparatedMap F
  have hinj := hF.isLocallyInjective
  intro x
  let φ := extChartAt I x
  let c : E := φ x
  obtain ⟨r, hr, hrT⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x) c (mem_extChartAt_target x)
  let B : Set E := Metric.ball c r
  have hseg : ∀ a ∈ B, ∀ s ∈ Icc (0 : ℝ) 1, c + s • (a - c) ∈ B := by
    intro a ha s hs
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    rw [Metric.mem_ball, dist_eq_norm] at ha
    calc s * ‖a - c‖ ≤ 1 * ‖a - c‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ < r := by rwa [one_mul]
  let G : E × ℝ → M := fun p =>
    φ.symm (c + ((projIcc (0 : ℝ) 1 zero_le_one p.2 : Icc (0 : ℝ) 1) : ℝ) • (p.1 - c))
  have hGc : ContinuousOn G (B ×ˢ univ) := by
    refine (continuousOn_extChartAt_symm x).comp (Continuous.continuousOn ?_) ?_
    · exact continuous_const.add ((continuous_subtype_val.comp
        (continuous_projIcc.comp continuous_snd)).smul (continuous_fst.sub continuous_const))
    · intro p hp
      exact hrT (hseg p.1 hp.1 _ (projIcc (0 : ℝ) 1 zero_le_one p.2).2)
  have hGeq : ∀ a, ∀ s ∈ Icc (0 : ℝ) 1, G (a, s) = φ.symm (c + s • (a - c)) := by
    intro a s hs
    simp only [G, projIcc_of_mem _ hs]
  have hGsmooth : ∀ a ∈ B, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => G (a, s)) (Icc 0 1) := by
    intro a ha
    have hpath : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => c + s • (a - c)) :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
    exact ((contMDiffOn_extChartAt_symm x).comp hpath.contMDiffOn
      (fun s hs => hrT (hseg a ha s hs))).congr (fun s hs => hGeq a s hs)
  have hGrev : ∀ a ∈ B, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => G (a, 1 - s)) (Icc 0 1) := by
    intro a ha
    have hpath : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => c + (1 - s) • (a - c)) :=
      (contDiff_const.add ((contDiff_const.sub contDiff_id).smul contDiff_const)).contMDiff
    have hmem : ∀ s ∈ Icc (0 : ℝ) 1, 1 - s ∈ Icc (0 : ℝ) 1 := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact ((contMDiffOn_extChartAt_symm x).comp hpath.contMDiffOn
      (fun s hs => hrT (hseg a ha (1 - s) (hmem s hs)))).congr
      (fun s hs => hGeq a (1 - s) (hmem s hs))
  have hG0 : ∀ a, G (a, 0) = x := by
    intro a
    rw [hGeq a 0 ⟨le_rfl, zero_le_one⟩, zero_smul, add_zero]
    exact extChartAt_to_inv x
  let V : Set M := φ.source ∩ φ ⁻¹' B
  have hVopen : IsOpen V :=
    (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
      Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, Metric.mem_ball_self hr⟩
  have hG1 : ∀ m ∈ V, G (φ m, 1) = m := by
    intro m hm
    rw [hGeq _ 1 ⟨zero_le_one, le_rfl⟩, one_smul, add_sub_cancel]
    exact φ.left_inv hm.1
  have hVimg : V = φ.symm '' B := by
    ext m
    constructor
    · rintro ⟨hm, hmB⟩
      exact ⟨φ m, hmB, φ.left_inv hm⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨φ.map_target (hrT ha), ?_⟩
      rw [mem_preimage, φ.right_inv (hrT ha)]
      exact ha
  have hVconn : IsPreconnected V := by
    rw [hVimg]
    exact (convex_ball c r).isPreconnected.image _
      ((continuousOn_extChartAt_symm x).mono hrT)
  let Fx : Set X := F ⁻¹' {x}
  have hl : ∀ u : Fx, ∀ a : B, ∃ η : ℝ → X, ContinuousOn η (Icc 0 1) ∧ η 0 = u ∧
      ∀ t ∈ Icc (0 : ℝ) 1, F (η t) = G (a, t) :=
    fun u a => hlift _ (hGsmooth a a.2) u (by rw [hG0]; exact u.2)
  choose η hηc hη0 hηF using hl
  let β : Fx → E × ℝ → X := fun u p => if h : p.1 ∈ B then η u ⟨p.1, h⟩ p.2 else u
  have hβapp : ∀ u, ∀ a (ha : a ∈ B) t, β u (a, t) = η u ⟨a, ha⟩ t := by
    intro u a ha t
    simp only [β, ha, ↓reduceDIte]
  have hβc : ∀ u, ∀ a ∈ B, ContinuousOn (fun t => β u (a, t)) (Icc 0 1) := fun u a ha =>
    (hηc u ⟨a, ha⟩).congr (fun t _ => hβapp u a ha t)
  have hβ0 : ∀ u, ∀ a ∈ B, β u (a, 0) = u := fun u a ha => by
    rw [hβapp u a ha, hη0]
  have hβF : ∀ u, ∀ a ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, F (β u (a, t)) = G (a, t) :=
    fun u a ha t ht => by rw [hβapp u a ha, hηF u ⟨a, ha⟩ t ht]
  have hβcont : ∀ u, ContinuousOn (β u) (B ×ˢ Icc 0 1) := fun u =>
    continuousOn_lift_family hF Metric.isOpen_ball hGc (hβc u) (hβ0 u) (hβF u)
  let sec : Fx → M → X := fun u m => β u (φ m, 1)
  have hsecc : ∀ u, ContinuousOn (sec u) V := fun u =>
    (hβcont u).comp (((continuousOn_extChartAt x).mono inter_subset_left).prodMk
      continuousOn_const) (fun m hm => ⟨hm.2, ⟨zero_le_one, le_rfl⟩⟩)
  have hsecF : ∀ u, ∀ m ∈ V, F (sec u m) = m := fun u m hm => by
    change F (β u (φ m, 1)) = m
    rw [hβF u _ hm.2 1 ⟨zero_le_one, le_rfl⟩, hG1 m hm]
  have hβuniq : ∀ u : Fx, ∀ a ∈ B, ∀ ζ : ℝ → X, ContinuousOn ζ (Icc 0 1) → ζ 0 = u →
      (∀ t ∈ Icc (0 : ℝ) 1, F (ζ t) = G (a, t)) → β u (a, 1) = ζ 1 := by
    intro u a ha ζ hζc hζ0 hζF
    exact hsep.eqOn_of_comp_eqOn hinj isPreconnected_Icc (hβc u a ha) hζc
      (fun t ht => by simp only [comp_apply]; rw [hβF u a ha t ht, hζF t ht])
      (a := 0) ⟨le_rfl, zero_le_one⟩ ((hβ0 u a ha).trans hζ0.symm) ⟨zero_le_one, le_rfl⟩
  have hsecx : ∀ u : Fx, sec u x = u := by
    intro u
    have hcB : φ x ∈ B := Metric.mem_ball_self hr
    exact hβuniq u _ hcB (fun _ => (u : X)) continuousOn_const rfl
      (fun t ht => by rw [u.2, hGeq _ t ht, sub_self, smul_zero, add_zero]; exact
        (extChartAt_to_inv x).symm)
  let sheet : Fx → Set X := fun u => sec u '' V
  have hsheet_open : ∀ u, IsOpen (sheet u) := fun u =>
    isOpen_image_section hF hVopen (hsecc u) (hsecF u)
  have hsheet_inj : ∀ u, InjOn F (sheet u) := by
    rintro u _ ⟨m₁, hm₁, rfl⟩ _ ⟨m₂, hm₂, rfl⟩ h
    rw [hsecF u m₁ hm₁, hsecF u m₂ hm₂] at h
    rw [h]
  have hsheet_surj : ∀ u, SurjOn F (sheet u) V := fun u m hm =>
    ⟨sec u m, ⟨m, hm, rfl⟩, hsecF u m hm⟩
  have hsheet_disjoint : Pairwise (Disjoint on sheet) := by
    intro u₁ u₂ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨m₁, hm₁, rfl⟩ ⟨m₂, hm₂, h⟩
    have hm : m₂ = m₁ := by
      have := congrArg F h
      rwa [hsecF u₂ m₂ hm₂, hsecF u₁ m₁ hm₁] at this
    subst hm
    have heq := hsep.eqOn_of_comp_eqOn hinj hVconn (hsecc u₁) (hsecc u₂)
      (fun m hm => by simp only [comp_apply]; rw [hsecF u₁ m hm, hsecF u₂ m hm])
      hm₂ h.symm hxV
    apply hne
    apply Subtype.ext
    rw [← hsecx u₁, ← hsecx u₂]
    exact heq
  have hsheet_exhaustive : F ⁻¹' V ⊆ ⋃ u, sheet u := by
    intro z hz
    let a : E := φ (F z)
    have ha : a ∈ B := hz.2
    obtain ⟨ζ, hζc, hζ0, hζF⟩ := hlift (fun s => G (a, 1 - s)) (hGrev a ha) z
      (by simp only [sub_zero]; exact (hG1 (F z) hz).symm)
    have hζ1 : F (ζ 1) = x := by
      rw [hζF 1 ⟨zero_le_one, le_rfl⟩, sub_self, hG0]
    let u : Fx := ⟨ζ 1, hζ1⟩
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, 1 - t ∈ Icc (0 : ℝ) 1 := fun t ht =>
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hz' : β u (a, 1) = z := by
      have h := hβuniq u a ha (fun t => ζ (1 - t))
        (hζc.comp (continuousOn_const.sub continuousOn_id) hmem)
        (by simp only [sub_zero]; rfl)
        (fun t ht => by
          rw [hζF (1 - t) (hmem t ht), sub_sub_cancel])
      rw [h, sub_self, hζ0]
    exact mem_iUnion.mpr ⟨u, F z, hz, hz'⟩
  have hopen_iff : ∀ u {W : Set M}, W ⊆ V → (IsOpen W ↔ IsOpen (F ⁻¹' W ∩ sheet u)) := by
    intro u W hWV
    constructor
    · intro hW
      exact (hW.preimage hF.continuous).inter (hsheet_open u)
    · intro hpre
      have himage : F '' (F ⁻¹' W ∩ sheet u) = W := by
        apply Subset.antisymm
        · rintro _ ⟨y, ⟨hyW, -⟩, rfl⟩
          exact hyW
        · intro m hmW
          obtain ⟨y, hy, hFy⟩ := hsheet_surj u (hWV hmW)
          exact ⟨y, ⟨by rw [mem_preimage, hFy]; exact hmW, hy⟩, hFy⟩
      rw [← himage]
      exact hF.isOpenMap _ hpre
  obtain ⟨z₀, hz₀⟩ := hsurj x
  let _ : Nonempty Fx := ⟨⟨z₀, hz₀⟩⟩
  let _ : Nonempty (M → X) := ⟨fun _ => z₀⟩
  let _ : DiscreteTopology Fx :=
    (IsDiscrete.of_openPartialHomeomorph F subset_rfl
      (fun e _ => by
        obtain ⟨ψ, he, hψ⟩ := hF e
        exact ⟨ψ, he, hψ.symm⟩)).1
  refine IsEvenlyCovered.of_trivialization
    (t := hVopen.trivializationDiscrete (ι := Fx) sheet V hopen_iff
      hsheet_inj hsheet_surj hsheet_disjoint hsheet_exhaustive) ?_
  simpa only [IsOpen.trivializationDiscrete_baseSet] using hxV

end Covering

end DifferentialGeometry
