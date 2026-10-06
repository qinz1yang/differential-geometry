import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalDecompositionOBDd

/-!
# The pieces of a regular domain along an embedded arc (lane S-BD2d, `_OBDd`), group G10c

Lane O-BD1 (by S-BD2d). In a one-dimensional base `Bs` with a graph atlas, a continuous injective
arc `γ : [0, 1] → Bs`:

* `exists_open_inter_subset_arc_image_OBDd`: a point `γ t₀`, `0 < t₀ < 1`, has an open neighbourhood
  `G` with `G ∩ Bs ⊆ γ ((t₀ - δ, t₀ + δ))` (the interior of an embedded arc is relatively open: the
  chart coordinate `κ ∘ γ` is injective and continuous, hence monotone with open image).
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **The interior of an embedded arc is relatively open in a graph-atlas base.** -/
theorem exists_open_inter_subset_arc_image_OBDd (At : GraphAtlas1_BCF ι Bs) {arc : ℝ → H}
    (hc : ContinuousOn arc (Icc 0 1)) (hinj : InjOn arc (Icc 0 1))
    (hmaps : MapsTo arc (Icc 0 1) Bs) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : Set H, IsOpen G ∧ arc t₀ ∈ G ∧ G ∩ Bs ⊆ arc '' Ioo (t₀ - δ) (t₀ + δ) := by
  have hy : arc t₀ ∈ Bs := hmaps ⟨ht₀.1.le, ht₀.2.le⟩
  have hcov : arc t₀ ∈ ⋃ j, At.param j '' At.dom j := by rw [← At.cover]; exact hy
  obtain ⟨j, b₀, hb₀, hpb⟩ := mem_iUnion.1 hcov |>.imp fun j hj => hj
  obtain ⟨V, hVo, hVB⟩ := At.piece_relOpen j
  have hcat : ContinuousAt arc t₀ := hc.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hVn : V ∈ 𝓝 (arc t₀) :=
    hVo.mem_nhds (by
      have : arc t₀ ∈ V ∩ Bs := hVB ▸ ⟨b₀, hb₀, hpb⟩
      exact this.1)
  have hev1 : ∀ᶠ t in 𝓝 t₀, arc t ∈ V := hcat.eventually hVn
  have hev2 : ∀ᶠ t in 𝓝 t₀, t ∈ Icc (0 : ℝ) 1 := Icc_mem_nhds ht₀.1 ht₀.2
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  set ε₂ : ℝ := min (ε / 2) (δ / 2) with hε₂
  have hε₂pos : 0 < ε₂ := lt_min (by linarith) (by linarith)
  have hwin : ∀ t ∈ Icc (t₀ - ε₂) (t₀ + ε₂), arc t ∈ V ∧ t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    apply hεW
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left (ε / 2) (δ / 2)]
  -- the chart coordinate along the arc
  have hpar : ∀ t ∈ Icc (t₀ - ε₂) (t₀ + ε₂), At.coord j (arc t) ∈ At.dom j ∧
      At.param j (At.coord j (arc t)) = arc t := by
    intro t ht
    obtain ⟨hV, hI⟩ := hwin t ht
    have : arc t ∈ V ∩ Bs := ⟨hV, hmaps hI⟩
    rw [hVB] at this
    obtain ⟨b, hb, hbt⟩ := this
    have hcb : At.coord j (arc t) = b := by rw [← hbt]; exact At.coord_param j b hb
    exact ⟨hcb ▸ hb, by rw [hcb]; exact hbt⟩
  have hucont : ContinuousOn (fun t => At.coord j (arc t)) (Icc (t₀ - ε₂) (t₀ + ε₂)) :=
    (At.coord j).continuous.comp_continuousOn
      (hc.mono fun t ht => (hwin t ht).2)
  have huinj : InjOn (fun t => At.coord j (arc t)) (Icc (t₀ - ε₂) (t₀ + ε₂)) := by
    intro t ht t' ht' h
    apply hinj (hwin t ht).2 (hwin t' ht').2
    rw [← (hpar t ht).2, ← (hpar t' ht').2]
    exact congrArg (At.param j) h
  have hle : t₀ - ε₂ ≤ t₀ + ε₂ := by linarith
  have hmem0 : t₀ ∈ Icc (t₀ - ε₂) (t₀ + ε₂) := ⟨by linarith, by linarith⟩
  have hmemL : t₀ - ε₂ ∈ Icc (t₀ - ε₂) (t₀ + ε₂) := ⟨le_rfl, hle⟩
  have hmemR : t₀ + ε₂ ∈ Icc (t₀ - ε₂) (t₀ + ε₂) := ⟨hle, le_rfl⟩
  -- an open interval of coordinates inside the image of the open window
  have hoint : ∃ O : Set ℝ, IsOpen O ∧ At.coord j (arc t₀) ∈ O ∧
      O ⊆ (fun t => At.coord j (arc t)) '' Ioo (t₀ - ε₂) (t₀ + ε₂) := by
    rcases hucont.strictMonoOn_of_injOn_Icc' hle huinj with hmono | hanti
    · have h1 : At.coord j (arc (t₀ - ε₂)) < At.coord j (arc t₀) :=
        hmono hmemL hmem0 (by linarith)
      have h2 : At.coord j (arc t₀) < At.coord j (arc (t₀ + ε₂)) :=
        hmono hmem0 hmemR (by linarith)
      exact ⟨Ioo _ _, isOpen_Ioo, ⟨h1, h2⟩, intermediate_value_Ioo hle hucont⟩
    · have h1 : At.coord j (arc (t₀ + ε₂)) < At.coord j (arc t₀) :=
        hanti hmem0 hmemR (by linarith)
      have h2 : At.coord j (arc t₀) < At.coord j (arc (t₀ - ε₂)) :=
        hanti hmemL hmem0 (by linarith)
      exact ⟨Ioo _ _, isOpen_Ioo, ⟨h1, h2⟩, intermediate_value_Ioo' hle hucont⟩
  obtain ⟨O, hOo, hO0, hOsub⟩ := hoint
  have hOdom : O ⊆ At.dom j := by
    intro b hb
    obtain ⟨t, ht, rfl⟩ := hOsub hb
    exact (hpar t (Ioo_subset_Icc_self ht)).1
  obtain ⟨V', hV'o, hV'B⟩ := At.image_relOpen_BCF hOo hOdom
  refine ⟨V', hV'o, ?_, ?_⟩
  · have : At.param j (At.coord j (arc t₀)) ∈ V' ∩ Bs := hV'B ▸ ⟨_, hO0, rfl⟩
    rw [(hpar t₀ hmem0).2] at this
    exact this.1
  · intro y hy
    rw [hV'B] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨t, ht, rfl⟩ := hOsub hb
    refine ⟨t, ?_, (hpar t (Ioo_subset_Icc_self ht)).2.symm⟩
    constructor <;> linarith [ht.1, ht.2, min_le_right (ε / 2) (δ / 2)]

/-- **The pieces of a regular domain along an embedded arc** (`A = γ⁻¹(C)`): `C ⊆ Bs` relatively
closed and regular with finite frontier along the arc, and no frontier point at the arc ends, give
finitely many disjoint nondegenerate closed parameter intervals `[s i, e i]` with
`γ⁻¹(C) ∩ [0, 1] = ⋃ [s i, e i]`, each end being an end of the arc or a frontier point of `C`. -/
theorem exists_arc_pieces_OBDd (At : GraphAtlas1_BCF ι Bs) {arc : ℝ → H}
    (hc : ContinuousOn arc (Icc 0 1)) (hinj : InjOn arc (Icc 0 1))
    (hmaps : MapsTo arc (Icc 0 1) Bs) {C : Set H}
    (hCcl : ∃ F : Set H, IsClosed F ∧ C = F ∩ Bs)
    (hreg : C ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)))
    (hfin : ((C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) ∩
      arc '' Icc 0 1).Finite)
    (hends : ∀ t ∈ ({0, 1} : Set ℝ), arc t ∈ C →
      arc t ∈ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) :
    ∃ (N : ℕ) (s e : Fin N → ℝ), (∀ i, 0 ≤ s i ∧ s i < e i ∧ e i ≤ 1) ∧
      (Icc (0 : ℝ) 1 ∩ arc ⁻¹' C = ⋃ i, Icc (s i) (e i)) ∧
      (Pairwise fun i j => Disjoint (Icc (s i) (e i)) (Icc (s j) (e j))) ∧
      (∀ i, (s i = 0 ∨ arc (s i) ∈ C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs)) ∧
        (e i = 1 ∨ arc (e i) ∈ C \ Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs))) := by
  classical
  obtain ⟨F, hF, hCF⟩ := hCcl
  set A : Set ℝ := Icc (0 : ℝ) 1 ∩ arc ⁻¹' C with hA
  set R : Set H := Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs) with hR
  have hAcl : IsClosed A := by
    have h1 : IsClosed (Icc (0 : ℝ) 1 ∩ arc ⁻¹' F) :=
      hc.preimage_isClosed_of_isClosed isClosed_Icc hF
    have h2 : A = Icc (0 : ℝ) 1 ∩ arc ⁻¹' F := by
      ext t
      constructor
      · rintro ⟨ht, htC⟩
        refine ⟨ht, ?_⟩
        rw [hCF] at htC
        exact htC.1
      · rintro ⟨ht, htF⟩
        refine ⟨ht, ?_⟩
        rw [hCF]
        exact ⟨htF, hmaps ht⟩
    rw [h2]
    exact h1
  have hAb : A ⊆ Icc 0 1 := inter_subset_left
  have hRC : R ⊆ C := by
    intro z hz
    obtain ⟨hzB, G, -, hzG, hGC⟩ := mem_image_interior_preimage_val_iff.1 hz
    exact hGC ⟨hzG, hzB⟩
  -- near a relative interior point of `C` along the arc, the arc stays in `C`
  have hH1 : ∀ t ∈ Icc (0 : ℝ) 1, arc t ∈ R → ∃ η > 0, ∀ t' ∈ Icc (0 : ℝ) 1, |t' - t| < η →
      t' ∈ A := by
    intro t ht htR
    obtain ⟨-, G, hGo, htG, hGC⟩ := mem_image_interior_preimage_val_iff.1 htR
    have h1 : arc ⁻¹' G ∈ 𝓝[Icc (0 : ℝ) 1] t := hc t ht (hGo.mem_nhds htG)
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhdsWithin_iff.1 h1
    refine ⟨η, hη, fun t' ht' hlt => ?_⟩
    have hmem : t' ∈ Metric.ball t η ∩ Icc (0 : ℝ) 1 :=
      ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact hlt, ht'⟩
    exact ⟨ht', hGC ⟨hηsub hmem, hmaps ht'⟩⟩
  have hH2 : ∀ t ∈ frontier A, t = 0 ∨ t = 1 ∨ arc t ∈ C \ R := by
    intro t htf
    have htA : t ∈ A := by
      have := htf.1
      rwa [hAcl.closure_eq] at this
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    by_cases ht1 : t = 1
    · exact Or.inr (Or.inl ht1)
    right; right
    refine ⟨htA.2, fun htR => htf.2 ?_⟩
    obtain ⟨η, hη, hηA⟩ := hH1 t htA.1 htR
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne htA.1.1 (Ne.symm ht0),
      lt_of_le_of_ne htA.1.2 ht1⟩
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Ioo_mem_nhds (a := t - min η (min t (1 - t)))
      (b := t + min η (min t (1 - t))) (by
        have : 0 < min η (min t (1 - t)) := lt_min hη (lt_min htI.1 (by linarith [htI.2]))
        linarith) (by
        have : 0 < min η (min t (1 - t)) := lt_min hη (lt_min htI.1 (by linarith [htI.2]))
        linarith)) ?_
    intro t' ht'
    have hm1 := min_le_left η (min t (1 - t))
    have hm2 : min η (min t (1 - t)) ≤ min t (1 - t) := min_le_right _ _
    have hm3 := min_le_left t (1 - t)
    have hm4 := min_le_right t (1 - t)
    apply hηA
    · constructor <;> linarith [ht'.1, ht'.2]
    · rw [abs_lt]
      constructor <;> linarith [ht'.1, ht'.2]
  have hH3 : ∀ t ∈ A, ∀ δ > 0, ∃ t' ∈ A, t' ≠ t ∧ |t' - t| < δ := by
    intro t htA δ hδ
    by_cases htR : arc t ∈ R
    · obtain ⟨η, hη, hηA⟩ := hH1 t htA.1 htR
      set r : ℝ := min (min η δ) 1 / 2 with hr
      have hrpos : 0 < r := by
        have : 0 < min (min η δ) 1 := lt_min (lt_min hη hδ) one_pos
        rw [hr]; linarith
      have hr1 : r ≤ 1 / 2 := by
        rw [hr]; have := min_le_right (min η δ) 1; linarith
      have hr2 : r < η := by
        rw [hr]
        have h1 := min_le_left (min η δ) 1
        have h2 := min_le_left η δ
        have : 0 < min (min η δ) 1 := lt_min (lt_min hη hδ) one_pos
        linarith
      have hr3 : r < δ := by
        rw [hr]
        have h1 := min_le_left (min η δ) 1
        have h2 := min_le_right η δ
        have : 0 < min (min η δ) 1 := lt_min (lt_min hη hδ) one_pos
        linarith
      by_cases ht2 : t ≤ 1 / 2
      · have hI : t + r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [htA.1.1], by linarith⟩
        refine ⟨t + r, hηA _ hI (by rw [abs_lt]; constructor <;> linarith), by linarith, ?_⟩
        rw [abs_lt]; constructor <;> linarith
      · have hI : t - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [htA.1.2]⟩
        refine ⟨t - r, hηA _ hI (by rw [abs_lt]; constructor <;> linarith), by linarith, ?_⟩
        rw [abs_lt]; constructor <;> linarith
    · have h0 : t ≠ 0 := fun h => htR (hends t (Or.inl h) htA.2)
      have h1 : t ≠ 1 := fun h => htR (hends t (Or.inr (mem_singleton_iff.2 h)) htA.2)
      have htI : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne htA.1.1 (Ne.symm h0), lt_of_le_of_ne htA.1.2 h1⟩
      set δ' : ℝ := min δ (min t (1 - t)) with hδ'
      have hδ'pos : 0 < δ' := lt_min hδ (lt_min htI.1 (by linarith [htI.2]))
      have hδ1 : δ' ≤ δ := min_le_left _ _
      have hδ2 : δ' ≤ t := (min_le_right _ _).trans (min_le_left _ _)
      have hδ3 : δ' ≤ 1 - t := (min_le_right _ _).trans (min_le_right _ _)
      obtain ⟨G, hGo, htG, hGsub⟩ := exists_open_inter_subset_arc_image_OBDd At hc hinj hmaps htI
        hδ'pos
      have hcl : arc t ∈ closure R := hreg htA.2
      obtain ⟨z, hzG, hzR⟩ := mem_closure_iff.1 hcl G hGo htG
      have hzB : z ∈ Bs := (mem_image_interior_preimage_val_iff.1 hzR).1
      obtain ⟨t', ht', hzt⟩ := hGsub ⟨hzG, hzB⟩
      have ht'I : t' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
      refine ⟨t', ⟨ht'I, by change arc t' ∈ C; rw [hzt]; exact hRC hzR⟩, ?_, ?_⟩
      · intro hteq
        rw [hteq] at hzt
        rw [← hzt] at hzR
        exact htR hzR
      · rw [abs_lt]; constructor <;> linarith [ht'.1, ht'.2]
  -- the frontier of `A` is finite
  have hFfin : (({0, 1} : Set ℝ) ∪ (Icc (0 : ℝ) 1 ∩ arc ⁻¹' (C \ R))).Finite := by
    refine (Set.toFinite _).union ?_
    refine Set.Finite.of_finite_image (f := arc) ?_ (hinj.mono inter_subset_left)
    refine hfin.subset ?_
    rintro _ ⟨t, ⟨ht, htC⟩, rfl⟩
    exact ⟨htC, ⟨t, ht, rfl⟩⟩
  have hfrF : frontier A ⊆ ({0, 1} : Set ℝ) ∪ (Icc (0 : ℝ) 1 ∩ arc ⁻¹' (C \ R)) := by
    intro t htf
    have htA : t ∈ A := by
      have := htf.1
      rwa [hAcl.closure_eq] at this
    rcases hH2 t htf with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (mem_singleton_iff.2 h))
    · exact Or.inr ⟨htA.1, h⟩
  obtain ⟨N, s, e, hlt, hfr, hdec, hdisj⟩ := exists_Icc_decomposition_OBDd hAcl hAb hFfin hfrF hH3
  have hsA : ∀ i, s i ∈ A := fun i => by
    have := (hfr i).1.1
    rwa [hAcl.closure_eq] at this
  have heA : ∀ i, e i ∈ A := fun i => by
    have := (hfr i).2.1
    rwa [hAcl.closure_eq] at this
  refine ⟨N, s, e, fun i => ⟨(hsA i).1.1, hlt i, (heA i).1.2⟩, hdec, hdisj, fun i => ⟨?_, ?_⟩⟩
  · rcases hH2 _ (hfr i).1 with h | h | h
    · exact Or.inl h
    · exact absurd h (ne_of_lt (lt_of_lt_of_le (hlt i) (heA i).1.2))
    · exact Or.inr h
  · rcases hH2 _ (hfr i).2 with h | h | h
    · exact absurd h (ne_of_gt (lt_of_le_of_lt (hsA i).1.1 (hlt i)))
    · exact Or.inl h
    · exact Or.inr h

end DifferentialGeometry.Topology
