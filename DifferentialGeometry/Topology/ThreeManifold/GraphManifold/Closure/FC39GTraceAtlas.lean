import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceRows

/-!
# FC39 GROUP G, lane FC39-G-TRACE: the labelled trace atlas

External draft task 58 §二 F2 (disposition D58-3; sheet `build-logs/resume/sheet-FC39-G-TRACE.md`):
the COMMON lemma pack for the global-face lane (F3–F6) and the arc lane (A2). All statements are
about ONE `Rw : FC39RowsV2 W E`. Write `κ_e = Rw.labelledTubes.chart e`, `X = κ_e¹`, `Y_e = κ_e²`.

* **local avoidance** `exists_open_avoid_GTR`: every base point has an open neighbourhood missed by
  every trace not through it (finitely many compact traces);
* **corner facts** on the raw tube base `V_e`: `mem_cbase_iff_of_mem_base_GTR` (`C₁ ∩ V_e = {X ≥ 0,
  Y_e ≥ 0}`), `mem_baseTrace_vertical_iff_GTR` (`B (.vertical e.component) ∩ V_e = {X = 0, Y_e ≥ 0}`),
  `snd_eq_zero_of_mem_baseTrace_horizontal_GTR`; and `exists_corner_atlas_GTR`: an open `V ∋ rimBase e`
  inside `V_e` on which also `B (.horizontal (horizontal e)) = {X ≥ 0, Y_e = 0}` and every other
  trace is absent (any smaller open set inherits all clauses: they are pointwise);
* **exhaustiveness** `mem_localFaces_iff_GTR`: for EVERY `local_faces` triple `(U, L, φ)` at a point
  `c` of `∂C₁`, `f ∈ L ↔ c ∈ B f` (no unregistered label touches; at a registered corner a single
  smooth label is excluded by the quadrant lemma, `false_of_single_label_at_corner_GTR`);
* **the labelled atlas** `labelled_baseTrace_atlas_GTR`: at every `c ∈ ∂C₁` an open `U ∋ c`, the
  label set `L = {f | c ∈ B f}` (one or two labels) and functions `φ f` smooth on `U` with
  `B f ∩ U = {C₁ ∩ U, φ f = 0}`, independent differentials, `C₁ ∩ U = {∀ f ∈ L, φ f ≤ 0}`, and
  `B f ∩ U = ∅` for every other label; at a one-label point the trace is the whole regular level set
  `B f ∩ U = {c' ∈ U | φ f c' = 0}` (`baseTrace_inter_eq_zero_of_single_GTR`: an embedded
  one-dimensional face with the circle region on its side `φ f ≤ 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace CircleBundle

variable (R : CircleBundle W)

/-- A whole fibre lies in a set described uniformly on its points. -/
theorem fibre_subset_iff_GTR {c : R.Base} {S : Set W.Carrier} {P : Prop}
    (h : ∀ y : R.domain, R.proj y = c → ((y : W.Carrier) ∈ S ↔ P)) : R.fibre c ⊆ S ↔ P := by
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := R.fibre_nonempty_GSAFE c
  constructor
  · intro hsub
    exact (h y hy).1 (hsub ⟨y, hy, rfl⟩)
  · rintro hP _ ⟨z, hz, rfl⟩
    exact (h z hz).2 hP

variable {R} in
/-- A base point lies over `C₁` iff its whole fibre lies in the circle region. -/
theorem mem_cbase_iff_fibre_subset_region_GTR {c : R.Base} :
    c ∈ R.cbase ↔ R.fibre c ⊆ R.region := by
  refine ⟨R.fibre_subset_region_GTR, fun h => ?_⟩
  obtain ⟨x, hx⟩ := R.fibre_nonempty_GSAFE c
  exact R.mem_cbase_of_mem_fibre_region_GTR hx (h hx)

end CircleBundle

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-! ## Local avoidance -/

/-- **Local avoidance.** Every base point has an open neighbourhood missed by every trace not
through it. -/
theorem exists_open_avoid_GTR (c : Rw.circle.Base) :
    ∃ V : Set Rw.circle.Base, IsOpen V ∧ c ∈ V ∧
      ∀ f : Rw.CircleFace, c ∉ Rw.baseTrace f → Disjoint (Rw.baseTrace f) V := by
  have := Rw.finite_circleFace_GTR
  refine ⟨(⋃ f ∈ {f : Rw.CircleFace | c ∉ Rw.baseTrace f}, Rw.baseTrace f)ᶜ, ?_, ?_, ?_⟩
  · exact ((toFinite _).isClosed_biUnion fun f _ =>
      (Rw.isCompact_baseTrace_GTR f).isClosed).isOpen_compl
  · intro hc
    obtain ⟨f, hf, hcf⟩ := mem_iUnion₂.1 hc
    exact hf hcf
  · intro f hf
    exact Set.disjoint_left.2 fun c' hc' hc'V => hc'V (mem_iUnion₂.2 ⟨f, hf, hc'⟩)

/-! ## Corner facts -/

variable {Rw} in
/-- **`C₁ ∩ V_e` is the closed quadrant** in the corner chart (`region_side`). -/
theorem mem_cbase_iff_of_mem_base_GTR {e : Rw.edge.EdgeEnd} {c : Rw.circle.Base}
    (hc : c ∈ Rw.labelledTubes.base e) :
    c ∈ Rw.circle.cbase ↔
      0 ≤ (Rw.labelledTubes.chart e c).1 ∧ 0 ≤ (Rw.labelledTubes.chart e c).2 := by
  rw [CircleBundle.mem_cbase_iff_fibre_subset_region_GTR]
  apply Rw.circle.fibre_subset_iff_GTR
  intro y hy
  subst hy
  exact Rw.labelledTubes.region_side hc

variable {Rw} in
/-- **`B (.vertical e.component) ∩ V_e = {X = 0, Y_e ≥ 0}`** (`edge_side`, `region_side`). -/
theorem mem_baseTrace_vertical_iff_GTR {e : Rw.edge.EdgeEnd} {c : Rw.circle.Base}
    (hc : c ∈ Rw.labelledTubes.base e) :
    c ∈ Rw.baseTrace (.vertical e.component) ↔
      (Rw.labelledTubes.chart e c).1 = 0 ∧ 0 ≤ (Rw.labelledTubes.chart e c).2 := by
  have key : Rw.circle.fibre c ⊆ circleFaceSet Rw.slim Rw.edge (.vertical e.component) ↔
      (0 ≤ (Rw.labelledTubes.chart e c).2 ∧ (Rw.labelledTubes.chart e c).1 ≤ 0) ∧
        (0 ≤ (Rw.labelledTubes.chart e c).1 ∧ 0 ≤ (Rw.labelledTubes.chart e c).2) := by
    apply Rw.circle.fibre_subset_iff_GTR
    intro y hy
    subst hy
    change (y : W.Carrier) ∈ Rw.edge.wholeVertical e.component ↔ _
    rw [Rw.wholeVertical_eq_GTR, mem_inter_iff, Rw.labelledTubes.edge_side hc,
      Rw.labelledTubes.region_side hc]
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := key.1 h
    exact ⟨le_antisymm h2 h3, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_cbase_iff_of_mem_base_GTR hc).2 ⟨h1.ge, h2⟩,
      key.2 ⟨⟨h2, h1.le⟩, h1.ge, h2⟩⟩

/-- On `V_e`, the trace of the registered horizontal face lies on `{Y_e = 0}` (`face_eq`). -/
theorem snd_eq_zero_of_mem_baseTrace_horizontal_GTR {e : Rw.edge.EdgeEnd} {c : Rw.circle.Base}
    (hc : c ∈ Rw.labelledTubes.base e)
    (hcH : c ∈ Rw.baseTrace (.horizontal (Rw.junctions.horizontal e))) :
    (Rw.labelledTubes.chart e c).2 = 0 := by
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := Rw.circle.fibre_nonempty_GSAFE c
  have hyc : Rw.circle.proj y = c := hy
  have hyF := hcH.2 ⟨y, hy, rfl⟩
  have h0 := (Rw.residualSet_subset_GTR _ hyF).2
  subst hyc
  rw [Rw.labelledTubes.face_eq e y hc]
  exact h0

/-- A point of `V_e` on the closed quadrant with `Y_e = 0` lies in `∂C₁` (points below it in the
chart leave `C₁`). -/
theorem mem_frontier_of_snd_eq_zero_GTR {e : Rw.edge.EdgeEnd} {c : Rw.circle.Base}
    (hc : c ∈ Rw.labelledTubes.base e) (hX : 0 ≤ (Rw.labelledTubes.chart e c).1)
    (hY : (Rw.labelledTubes.chart e c).2 = 0) : c ∈ frontier Rw.circle.cbase := by
  set κ := Rw.labelledTubes.chart e with hκ
  let K := κ.toOpenPartialHomeomorph
  have hsrc : c ∈ K.source := by
    change c ∈ κ.source
    rw [Rw.labelledTubes.chart_source e]
    exact hc
  have hcc : c ∈ Rw.circle.cbase := (mem_cbase_iff_of_mem_base_GTR hc).2 ⟨hX, hY.ge⟩
  refine ⟨subset_closure hcc, fun hint => ?_⟩
  have htgt : K c ∈ K.target := K.map_source hsrc
  have hline : Tendsto (fun s : ℝ => K c + ((0 : ℝ), -s)) (𝓝[>] 0) (𝓝 (K c)) := by
    have h : Tendsto (fun s : ℝ => K c + ((0 : ℝ), -s)) (𝓝 0) (𝓝 (K c + ((0 : ℝ), -0))) :=
      ((continuous_const.add (continuous_const.prodMk continuous_neg))).tendsto 0
    simp only [neg_zero, Prod.mk_zero_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hsymm : Tendsto K.symm (𝓝 (K c)) (𝓝 c) := by
    have h := K.continuousAt_symm htgt
    rwa [ContinuousAt, K.left_inv hsrc] at h
  have hev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), K c + ((0 : ℝ), -s) ∈ K.target :=
    hline.eventually (K.open_target.mem_nhds htgt)
  have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), K.symm (K c + ((0 : ℝ), -s)) ∈
      interior Rw.circle.cbase ∩ K.source :=
    (hsymm.comp hline).eventually ((isOpen_interior.inter K.open_source).mem_nhds ⟨hint, hsrc⟩)
  obtain ⟨s, h1, h2, hs⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have hspos : (0 : ℝ) < s := hs
  have hsb : K.symm (K c + ((0 : ℝ), -s)) ∈ Rw.labelledTubes.base e := by
    have h := h2.2
    change _ ∈ κ.source at h
    rw [Rw.labelledTubes.chart_source e] at h
    exact h
  have hq := ((mem_cbase_iff_of_mem_base_GTR hsb).1 (interior_subset h2.1)).2
  have hr : κ (K.symm (K c + ((0 : ℝ), -s))) = K c + ((0 : ℝ), -s) := K.right_inv h1
  rw [hr] at hq
  have : (K c).2 = 0 := hY
  simp only [Prod.snd_add, this, zero_add] at hq
  linarith

/-- **The corner atlas at a registered rim base point.** An open `V ∋ rimBase e` inside the raw
tube base `V_e` on which `C₁` is the quadrant, the vertical trace is `{X = 0}`, the horizontal
trace of the registered face is `{Y_e = 0}` (both inside `C₁`), and every other trace is absent. -/
theorem exists_corner_atlas_GTR (e : Rw.edge.EdgeEnd) :
    ∃ V : TopologicalSpace.Opens Rw.circle.Base, Rw.junctions.rimBase e.1 ∈ V ∧
      (V : Set Rw.circle.Base) ⊆ Rw.labelledTubes.base e ∧
      (∀ c ∈ V, c ∈ Rw.circle.cbase ↔
        0 ≤ (Rw.labelledTubes.chart e c).1 ∧ 0 ≤ (Rw.labelledTubes.chart e c).2) ∧
      (∀ c ∈ V, c ∈ Rw.baseTrace (.vertical e.component) ↔
        c ∈ Rw.circle.cbase ∧ (Rw.labelledTubes.chart e c).1 = 0) ∧
      (∀ c ∈ V, c ∈ Rw.baseTrace (.horizontal (Rw.junctions.horizontal e)) ↔
        c ∈ Rw.circle.cbase ∧ (Rw.labelledTubes.chart e c).2 = 0) ∧
      ∀ f : Rw.CircleFace, f ≠ .vertical e.component →
        f ≠ .horizontal (Rw.junctions.horizontal e) →
        Disjoint (Rw.baseTrace f) (V : Set Rw.circle.Base) := by
  obtain ⟨V₀, hV₀, hcV₀, havoid⟩ := Rw.exists_open_avoid_GTR (Rw.junctions.rimBase e.1)
  refine ⟨⟨V₀ ∩ Rw.labelledTubes.base e, hV₀.inter (Rw.labelledTubes.base e).isOpen⟩,
    ⟨hcV₀, Rw.labelledTubes.rimBase_mem e⟩, inter_subset_right, ?_, ?_, ?_, ?_⟩
  · exact fun c hc => mem_cbase_iff_of_mem_base_GTR hc.2
  · intro c hc
    rw [mem_baseTrace_vertical_iff_GTR hc.2, mem_cbase_iff_of_mem_base_GTR hc.2]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.ge, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩
      exact ⟨h1, h2⟩
  · intro c hc
    constructor
    · intro hcH
      exact ⟨hcH.1, Rw.snd_eq_zero_of_mem_baseTrace_horizontal_GTR hc.2 hcH⟩
    · rintro ⟨hcc, hY⟩
      have hX := ((mem_cbase_iff_of_mem_base_GTR hc.2).1 hcc).1
      rcases hX.lt_or_eq with hX | hX
      · obtain ⟨g, hg⟩ := Rw.exists_mem_baseTrace_GTR
          (Rw.mem_frontier_of_snd_eq_zero_GTR hc.2 hX.le hY)
        by_cases hg0 : Rw.junctions.rimBase e.1 ∈ Rw.baseTrace g
        · have hg' : g ∈ ({.vertical e.component, .horizontal (Rw.junctions.horizontal e)} :
              Set Rw.CircleFace) := by
            rw [← Rw.labels_rimBase_eq_GTR e]
            exact hg0
          rcases hg' with rfl | rfl
          · exact absurd ((mem_baseTrace_vertical_iff_GTR hc.2).1 hg).1 hX.ne'
          · exact hg
        · exact absurd hc.1 (Set.disjoint_left.1 (havoid g hg0) hg)
      · have hκ : Rw.labelledTubes.chart e c =
            Rw.labelledTubes.chart e (Rw.junctions.rimBase e.1) := by
          rw [Rw.labelledTubes.chart_center e]
          exact Prod.ext hX.symm hY
        have hsrc : ∀ c' ∈ Rw.labelledTubes.base e, c' ∈ (Rw.labelledTubes.chart e).source :=
          fun c' hc' => by rw [Rw.labelledTubes.chart_source e]; exact hc'
        have hceq : c = Rw.junctions.rimBase e.1 :=
          (Rw.labelledTubes.chart e).toPartialEquiv.injOn (hsrc c hc.2)
            (hsrc _ (Rw.labelledTubes.rimBase_mem e)) hκ
        rw [hceq]
        exact Rw.rimBase_mem_baseTrace_horizontal_GTR e
  · intro f hfV hfH
    refine (havoid f fun h0 => ?_).mono_right inter_subset_left
    have hf' : f ∈ ({.vertical e.component, .horizontal (Rw.junctions.horizontal e)} :
        Set Rw.CircleFace) := by
      rw [← Rw.labels_rimBase_eq_GTR e]
      exact h0
    rcases hf' with h | h
    · exact hfV h
    · exact hfH h

/-- A registered rim base point carries exactly two labels. -/
theorem ncard_labels_rimBase_GTR (e : Rw.edge.EdgeEnd) :
    {f : Rw.CircleFace | Rw.junctions.rimBase e.1 ∈ Rw.baseTrace f}.ncard = 2 := by
  rw [Rw.labels_rimBase_eq_GTR e, ncard_pair (by simp)]

/-! ## Exhaustiveness -/

/-- **A registered corner is not a one-label smooth boundary point.** No function smooth near
`rimBase e` with a regular zero there cuts out `C₁` as its sublevel set (the quadrant lemma in the
corner chart). -/
theorem false_of_single_label_at_corner_GTR (e : Rw.edge.EdgeEnd)
    {U : TopologicalSpace.Opens Rw.circle.Base} (hcU : Rw.junctions.rimBase e.1 ∈ U)
    {φ : Rw.circle.Base → ℝ} (hφ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ U)
    (hφ0 : φ (Rw.junctions.rimBase e.1) = 0)
    (hdφ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ (Rw.junctions.rimBase e.1) ≠ 0)
    (hcb : ∀ c ∈ U, c ∈ Rw.circle.cbase ↔ φ c ≤ 0) : False := by
  set c₀ := Rw.junctions.rimBase e.1 with hc₀
  set κ := Rw.labelledTubes.chart e with hκ
  let K := κ.toOpenPartialHomeomorph
  have hsrc : c₀ ∈ K.source := by
    change c₀ ∈ κ.source
    rw [Rw.labelledTubes.chart_source e]
    exact Rw.labelledTubes.rimBase_mem e
  have hK0 : K c₀ = 0 := Rw.labelledTubes.chart_center e
  have htgt : (0 : ℝ × ℝ) ∈ K.target := hK0 ▸ K.map_source hsrc
  have hsymm0 : K.symm 0 = c₀ := by rw [← hK0]; exact K.left_inv hsrc
  have hsymm : Tendsto K.symm (𝓝 0) (𝓝 c₀) := by
    have h := K.continuousAt_symm htgt
    rwa [ContinuousAt, hsymm0] at h
  set g : ℝ × ℝ → ℝ := fun q => φ (K.symm q) with hg
  -- the sublevel set of `g` is the quadrant near `0`
  have hQ : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), (g q ≤ 0 ↔ 0 ≤ q.1 ∧ 0 ≤ q.2) := by
    have hev1 : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q ∈ K.target := K.open_target.mem_nhds htgt
    have hev2 : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), K.symm q ∈ (U : Set Rw.circle.Base) ∩ K.source :=
      hsymm.eventually ((U.isOpen.inter K.open_source).mem_nhds ⟨hcU, hsrc⟩)
    filter_upwards [hev1, hev2] with q hq1 hq2
    have hqb : K.symm q ∈ Rw.labelledTubes.base e := by
      have h := hq2.2
      change _ ∈ κ.source at h
      rw [Rw.labelledTubes.chart_source e] at h
      exact h
    rw [hg]
    simp only
    rw [← hcb _ hq2.1, mem_cbase_iff_of_mem_base_GTR hqb]
    have hr : κ (K.symm q) = q := K.right_inv hq1
    rw [hr]
  -- `g` is differentiable at `0`
  have hφat : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ c₀ := hφ.contMDiffAt (U.isOpen.mem_nhds hcU)
  have hsymmat : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ K.symm 0 :=
    (κ.symm.contMDiffOn 0 htgt).contMDiffAt (K.open_target.mem_nhds htgt)
  have hgat : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ g 0 := by
    have hφat' : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ (K.symm 0) := by rw [hsymm0]; exact hφat
    exact hφat'.comp 0 hsymmat
  have hgd : DifferentiableAt ℝ g 0 :=
    mdifferentiableAt_iff_differentiableAt.1 (hgat.mdifferentiableAt (by decide))
  have hg0 : g 0 = 0 := by rw [hg]; simp only; rw [hsymm0]; exact hφ0
  -- its derivative is nonzero: `φ = g ∘ κ` near `c₀`
  have hgne : fderiv ℝ g 0 ≠ 0 := by
    intro h0
    apply hdφ
    have heq : φ =ᶠ[𝓝 c₀] g ∘ K := by
      filter_upwards [K.open_source.mem_nhds hsrc] with c hc
      simp only [hg, Function.comp_apply]
      rw [K.left_inv hc]
    have hKat : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) K c₀ :=
      κ.mdifferentiableAt (by decide) hsrc
    have hgat' : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) g (K c₀) := by
      rw [hK0]
      exact hgat.mdifferentiableAt (by decide)
    rw [heq.mfderiv_eq, mfderiv_comp c₀ hgat' hKat, hK0, mfderiv_eq_fderiv, h0]
    rfl
  exact not_eventually_quadrant_iff_GTR hgd.hasFDerivAt hg0 hgne hQ

variable {Rw} in
/-- **Exhaustiveness.** For every `local_faces` triple `(U, L, φ)` at a point `c` of `∂C₁`, the
labels of `L` are exactly the labels whose trace contains `c`. -/
theorem mem_localFaces_iff_GTR {c : Rw.circle.Base} (hc : c ∈ frontier Rw.circle.cbase)
    {U : TopologicalSpace.Opens Rw.circle.Base} (hcU : c ∈ U) {L : Finset Rw.CircleFace}
    {φ : Rw.CircleFace → Rw.circle.Base → ℝ} (hL1 : 1 ≤ L.card)
    (hφ : ∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
      {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ f c' = 0} =
        {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧
          Rw.circle.fibre c' ⊆ circleFaceSet Rw.slim Rw.edge f})
    (hsurj : Surjective fun w : TangentSpace (𝓡 2) c =>
      fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w)
    (hcb : Rw.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}) {f : Rw.CircleFace} :
    f ∈ L ↔ c ∈ Rw.baseTrace f := by
  refine ⟨fun hf => Rw.mem_baseTrace_of_localFace_GTR hc hcU (hφ f hf).2.1 (hφ f hf).2.2, ?_⟩
  intro hcf
  by_contra hfL
  obtain ⟨g, hg⟩ := Finset.card_pos.1 (by omega : 0 < L.card)
  have hcg : c ∈ Rw.baseTrace g :=
    Rw.mem_baseTrace_of_localFace_GTR hc hcU (hφ g hg).2.1 (hφ g hg).2.2
  have hfg : f ≠ g := fun h => hfL (h ▸ hg)
  obtain ⟨e, rfl, -⟩ := Rw.label_classification_GTR hcf hcg hfg
  -- every label of `L` is a label at the corner, `f` is the other one: `L = {g}`
  have hlab : ∀ h ∈ L, h = g := by
    intro h hh
    by_contra hhg
    have hch := Rw.mem_baseTrace_of_localFace_GTR hc hcU (hφ h hh).2.1 (hφ h hh).2.2
    have hfh : f ≠ h := fun h' => hfL (h' ▸ hh)
    have hs : ({f, g, h} : Set Rw.CircleFace) ⊆
        {.vertical e.component, .horizontal (Rw.junctions.horizontal e)} := by
      rw [← Rw.labels_rimBase_eq_GTR e]
      rintro x (rfl | rfl | rfl)
      · exact hcf
      · exact hcg
      · exact hch
    have hcard := ncard_le_ncard hs (toFinite _)
    rw [ncard_insert_of_notMem (by simp [hfg, hfh]), ncard_pair (Ne.symm hhg)] at hcard
    have := ncard_insert_le (CircleFaceLabel.vertical e.component : Rw.CircleFace)
      {(.horizontal (Rw.junctions.horizontal e) : Rw.CircleFace)}
    rw [ncard_singleton] at this
    omega
  have hdφ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ g) (Rw.junctions.rimBase e.1) ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := hsurj (fun _ => 1)
    have h1 := congrFun hw ⟨g, hg⟩
    simp only [h0, zero_apply] at h1
    have h1' : (0 : ℝ) = 1 := h1
    norm_num at h1'
  refine Rw.false_of_single_label_at_corner_GTR e hcU (hφ g hg).1 (hφ g hg).2.1 hdφ ?_
  intro c' hc'
  constructor
  · intro hc'c
    have h : c' ∈ {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
      rw [← hcb]
      exact ⟨hc'c, hc'⟩
    exact h.2 g hg
  · intro hle
    have h : c' ∈ {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} :=
      ⟨hc', fun h hh => (hlab h hh) ▸ hle⟩
    rw [← hcb] at h
    exact h.1

/-! ## The labelled trace atlas -/

/-- **The labelled base-trace atlas.** At every point `c` of `∂C₁`: an open `U ∋ c`, the finite
set `L` of EXACTLY the labels whose trace contains `c` (one or two), and functions `φ f` smooth on
`U` with a regular common zero at `c`, the traces of the labels of `L` cut out inside `C₁ ∩ U` as
zero sets, `C₁ ∩ U = {∀ f ∈ L, φ f ≤ 0}`, and every other trace missing `U`. -/
theorem labelled_baseTrace_atlas_GTR {c : Rw.circle.Base} (hc : c ∈ frontier Rw.circle.cbase) :
    ∃ U : TopologicalSpace.Opens Rw.circle.Base, c ∈ U ∧
      ∃ (L : Finset Rw.CircleFace) (φ : Rw.CircleFace → Rw.circle.Base → ℝ),
        (∀ f, f ∈ L ↔ c ∈ Rw.baseTrace f) ∧ 1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          Rw.baseTrace f ∩ U = {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ f c' = 0}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        Rw.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} ∧
        ∀ f, f ∉ L → Disjoint (Rw.baseTrace f) (U : Set Rw.circle.Base) := by
  obtain ⟨U, hcU, L, φ, hL1, hL2, hφ, hsurj, hcb⟩ := Rw.junctions.local_faces c hc
  have hmem : ∀ f, f ∈ L ↔ c ∈ Rw.baseTrace f := fun _ =>
    mem_localFaces_iff_GTR hc hcU hL1 hφ hsurj hcb
  obtain ⟨V, hV, hcV, havoid⟩ := Rw.exists_open_avoid_GTR c
  refine ⟨⟨U ∩ V, U.isOpen.inter hV⟩, ⟨hcU, hcV⟩, L, φ, hmem, hL1, hL2, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨hsm, h0, heq⟩ := hφ f hf
    refine ⟨hsm.mono inter_subset_left, h0, ?_⟩
    ext c'
    constructor
    · rintro ⟨⟨hc'c, hc'S⟩, hc'U, hc'V⟩
      have h : c' ∈ {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧
          Rw.circle.fibre c' ⊆ circleFaceSet Rw.slim Rw.edge f} := ⟨hc'U, hc'c, hc'S⟩
      rw [← heq] at h
      exact ⟨⟨hc'U, hc'V⟩, hc'c, h.2.2⟩
    · rintro ⟨⟨hc'U, hc'V⟩, hc'c, h0'⟩
      have h : c' ∈ {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ f c' = 0} := ⟨hc'U, hc'c, h0'⟩
      rw [heq] at h
      exact ⟨⟨hc'c, h.2.2⟩, hc'U, hc'V⟩
  · exact hsurj
  · ext c'
    constructor
    · rintro ⟨hc'c, hc'U, hc'V⟩
      have h : c' ∈ Rw.circle.cbase ∩ U := ⟨hc'c, hc'U⟩
      rw [hcb] at h
      exact ⟨⟨hc'U, hc'V⟩, h.2⟩
    · rintro ⟨⟨hc'U, hc'V⟩, hle⟩
      have h : c' ∈ {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := ⟨hc'U, hle⟩
      rw [← hcb] at h
      exact ⟨h.1, hc'U, hc'V⟩
  · intro f hf
    exact (havoid f fun h => hf ((hmem f).2 h)).mono_right inter_subset_right

/-- **A one-label trace is a whole regular level set.** On an open set `U` on which `C₁` is the
sublevel set `{φ ≤ 0}` of ONE function (a one-label chart of `labelled_baseTrace_atlas_GTR`) and the
trace of `f` is the zero set of `φ` inside `C₁`, the trace is the whole zero set of `φ` in `U` (the
circle region lies on its side `φ ≤ 0`). -/
theorem baseTrace_inter_eq_zero_of_single_GTR {U : TopologicalSpace.Opens Rw.circle.Base} {f : Rw.CircleFace}
    {φ : Rw.circle.Base → ℝ}
    (hcb : Rw.circle.cbase ∩ U = {c' | c' ∈ U ∧ φ c' ≤ 0})
    (heq : Rw.baseTrace f ∩ U = {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ c' = 0}) :
    Rw.baseTrace f ∩ U = {c' | c' ∈ U ∧ φ c' = 0} := by
  rw [heq]
  ext c'
  constructor
  · rintro ⟨hU, -, h0⟩
    exact ⟨hU, h0⟩
  · rintro ⟨hU, h0⟩
    have h : c' ∈ {c' | c' ∈ U ∧ φ c' ≤ 0} := ⟨hU, h0.le⟩
    rw [← hcb] at h
    exact ⟨hU, h.1, h0⟩

end FC39RowsV2

end GC.GraphManifold.Assembly.FC39P0
