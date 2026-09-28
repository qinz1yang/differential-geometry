import DifferentialGeometry.Topology.VanKampen.BoundaryCollarOrientation

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Topology.Collar

universe u v

theorem clusterPt_mem_closure_of_mem {X : Type*} [TopologicalSpace X] {x : X}
    {f : Filter X} {s : Set X} (h : ClusterPt x f) (hs : s ∈ f) : x ∈ closure s :=
  ClusterPt.mem_closure (h.mono (Filter.le_principal_iff.mpr hs))

theorem clusterPt_mem_closure_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : Continuous g) {x : X} {f : Filter X} {s : Set Y}
    (h : ClusterPt x f) (hs : {q | g q ∈ s} ∈ f) : g x ∈ closure s := by
  rw [mem_closure_iff]
  intro o ho hgo
  let : (𝓝 x ⊓ f).NeBot := h
  have hO : g ⁻¹' o ∈ 𝓝 x :=
    hg.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds ho hgo)
  obtain ⟨q, hq1, hq2⟩ := Filter.nonempty_of_mem
    (Filter.mem_inf_iff.mpr ⟨_, hO, _, hs, rfl⟩)
  exact ⟨g q, hq1, hq2⟩

theorem image_core_eq_range {A : Type*} {X : Type*} (c : A × ℝ → X) (e : A → X)
    (h : ∀ a, c (a, 0) = e a) :
    c '' ((univ : Set A) ×ˢ ({0} : Set ℝ)) = range e := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq2 : q.2 = 0 := hq.2
    have hc : c q = e q.1 := by
      rw [← h q.1]
      exact congrArg c (Prod.ext rfl hq2)
    exact ⟨q.1, hc.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(a, 0), ⟨trivial, rfl⟩, h a⟩

theorem exists_pos_disjoint_of_shrinking_families
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {E₁ : Type*} [TopologicalSpace E₁] {E₂ : Type*} [TopologicalSpace E₂]
    {K₁ : Set E₁} {K₂ : Set E₂} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {core₁ : Set E₁} {core₂ : Set E₂} {c₁ : E₁ → X} {c₂ : E₂ → X}
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    {V₁ : ℝ → Set E₁} {V₂ : ℝ → Set E₂}
    (hV₁ : ∀ δ, 0 < δ → δ ≤ 1 → V₁ δ ⊆ K₁)
    (hV₂ : ∀ δ, 0 < δ → δ ≤ 1 → V₂ δ ⊆ K₂)
    (hm₁ : ∀ {a b : ℝ}, 0 < a → a ≤ b → V₁ a ⊆ V₁ b)
    (hm₂ : ∀ {a b : ℝ}, 0 < a → a ≤ b → V₂ a ⊆ V₂ b)
    (hcore₁ : ∀ x, (∀ δ, 0 < δ → x ∈ closure (V₁ δ)) → x ∈ core₁)
    (hcore₂ : ∀ y, (∀ δ, 0 < δ → y ∈ closure (V₂ δ)) → y ∈ core₂)
    (hdisj : Disjoint (c₁ '' core₁) (c₂ '' core₂)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ Disjoint (c₁ '' V₁ δ) (c₂ '' V₂ δ) := by
  by_contra h
  rw [not_exists] at h
  have hne : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (c₁ '' V₁ δ ∩ c₂ '' V₂ δ).Nonempty := by
    intro δ hδ hδ1
    by_contra hcon
    exact h δ ⟨hδ, hδ1,
      Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hcon)⟩
  have hδpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hδle : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  choose u hu using fun n : ℕ => hne (1 / ((n : ℝ) + 1)) (hδpos n) (hδle n)
  choose p hp using fun n : ℕ =>
    (Set.mem_image c₁ (V₁ (1 / ((n : ℝ) + 1))) (u n)).mp (hu n).1
  choose r hr using fun n : ℕ =>
    (Set.mem_image c₂ (V₂ (1 / ((n : ℝ) + 1))) (u n)).mp (hu n).2
  have hpc : ∀ n, c₁ (p n) = u n := fun n => (hp n).2
  have hrd : ∀ n, c₂ (r n) = u n := fun n => (hr n).2
  have htail : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < δ := by
    intro δ hδ
    refine Filter.mem_atTop_sets.mpr ⟨Nat.ceil (1 / δ) + 1, fun n hn => ?_⟩
    have h1 : 1 / δ < (n : ℝ) := by
      have h2 : (Nat.ceil (1 / δ) : ℝ) + 1 ≤ (n : ℝ) := by
        have hcast : ((Nat.ceil (1 / δ) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        simpa using hcast
      have h3 : 1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil _
      linarith
    have h4 : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp h1
    change 1 / ((n : ℝ) + 1) < δ
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  let g : ℕ → E₁ × E₂ := fun n => (p n, r n)
  let F : Filter (E₁ × E₂) := Filter.map g Filter.atTop
  let T : Set (E₁ × E₂) := {q | c₁ q.1 = c₂ q.2}
  have hFne : F.NeBot := (Filter.atTop_neBot (α := ℕ)).map g
  have hTc : IsClosed T :=
    isClosed_diagonal.preimage ((hc₁.comp continuous_fst).prodMk (hc₂.comp continuous_snd))
  have hFK : K₁ ×ˢ K₂ ∈ F := by
    rw [Filter.mem_map]
    refine Filter.mem_atTop_sets.mpr ⟨0, fun n _ => ?_⟩
    exact ⟨hV₁ _ (hδpos n) (hδle n) (hp n).1, hV₂ _ (hδpos n) (hδle n) (hr n).1⟩
  have hFT : T ∈ F := by
    rw [Filter.mem_map]
    have huniv : g ⁻¹' T = univ := by
      refine Set.eq_univ_of_forall fun n => ?_
      change c₁ (p n) = c₂ (r n)
      rw [hpc n, hrd n]
    rw [huniv]
    exact Filter.univ_mem
  have hFle : F ≤ 𝓟 ((K₁ ×ˢ K₂) ∩ T) :=
    Filter.le_principal_iff.mpr (Filter.inter_mem hFK hFT)
  let : F.NeBot := hFne
  obtain ⟨x, hx, hcl⟩ := ((hK₁.prod hK₂).inter_right hTc) hFle
  have hxT : c₁ x.1 = c₂ x.2 := hx.2
  have hb₁ : ∀ δ, 0 < δ → x.1 ∈ closure (V₁ δ) := by
    intro δ hδ
    have hev : {q : E₁ × E₂ | q.1 ∈ V₁ δ} ∈ F := by
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (htail δ hδ) fun n hn => ?_
      exact hm₁ (by positivity) hn.le (hp n).1
    exact clusterPt_mem_closure_image continuous_fst hcl hev
  have hb₂ : ∀ δ, 0 < δ → x.2 ∈ closure (V₂ δ) := by
    intro δ hδ
    have hev : {q : E₁ × E₂ | q.2 ∈ V₂ δ} ∈ F := by
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (htail δ hδ) fun n hn => ?_
      exact hm₂ (by positivity) hn.le (hr n).1
    exact clusterPt_mem_closure_image continuous_snd hcl hev
  exact (Set.disjoint_left.mp hdisj) (mem_image_of_mem c₁ (hcore₁ x.1 hb₁))
    (hxT ▸ mem_image_of_mem c₂ (hcore₂ x.2 hb₂))

theorem disjointFamily_of_shrinking_families
    {X : Type u} [TopologicalSpace X] [T2Space X] {ι : Type v} [Finite ι]
    {E : ι → Type u} [∀ i, TopologicalSpace (E i)]
    {K : ∀ i, Set (E i)} (hK : ∀ i, IsCompact (K i))
    {core : ∀ i, Set (E i)} {c : ∀ i, E i → X} (hc : ∀ i, Continuous (c i))
    {V : ∀ i, ℝ → Set (E i)}
    (hV : ∀ i δ, 0 < δ → δ ≤ 1 → V i δ ⊆ K i)
    (hm : ∀ i {a b : ℝ}, 0 < a → a ≤ b → V i a ⊆ V i b)
    (hcore : ∀ i x, (∀ δ, 0 < δ → x ∈ closure (V i δ)) → x ∈ core i)
    (hdisj : Pairwise fun i j => Disjoint (c i '' core i) (c j '' core j)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      Pairwise fun i j => Disjoint (c i '' V i δ) (c j '' V j δ) := by
  classical
  let := Fintype.ofFinite ι
  have hpair : ∀ i j : ι, i ≠ j → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      Disjoint (c i '' V i δ) (c j '' V j δ) :=
    fun i j hij => exists_pos_disjoint_of_shrinking_families (hK i) (hK j) (hc i) (hc j)
      (fun δ hδ hδ1 => hV i δ hδ hδ1) (fun δ hδ hδ1 => hV j δ hδ hδ1)
      (fun {a b} ha hab => hm i ha hab) (fun {a b} ha hab => hm j ha hab)
      (fun x hx => hcore i x hx) (fun y hy => hcore j y hy) (hdisj hij)
  let P : Finset (ι × ι) := Finset.univ.filter fun p => p.1 ≠ p.2
  by_cases hP : P.Nonempty
  · let w : ι × ι → ℝ := fun p => if h : p.1 ≠ p.2 then (hpair p.1 p.2 h).choose else 1
    have hwinf : 0 < P.inf' hP w := by
      rw [Finset.lt_inf'_iff]
      intro p hp
      rw [Finset.mem_filter] at hp
      simp only [w, dite_eq_left hp.2]
      exact (hpair p.1 p.2 hp.2).choose_spec.1
    have hpos : 0 < min (P.inf' hP w) 1 := lt_min hwinf one_pos
    refine ⟨min (P.inf' hP w) 1, hpos, min_le_right _ _, fun i j hij => ?_⟩
    have hmem : (i, j) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    have hwij : w (i, j) = (hpair i j hij).choose := by simp only [w, dite_eq_left hij]
    have hle : P.inf' hP w ≤ w (i, j) := Finset.inf'_le w hmem
    have hmin : min (P.inf' hP w) 1 ≤ (hpair i j hij).choose := by
      rw [hwij] at hle
      exact (min_le_left _ _).trans hle
    refine Disjoint.mono (image_mono fun q hq => hm i hpos hmin hq)
      (image_mono fun q hq => hm j hpos hmin hq)
      (hpair i j hij).choose_spec.2.2
  · refine ⟨1, one_pos, le_rfl, fun i j hij => ?_⟩
    exfalso
    have hmem : (i, j) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hP] at hmem
    simp at hmem

theorem exists_pos_disjoint_images_of_disjoint_cores
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {B : Type*} [TopologicalSpace B] [CompactSpace B]
    {c : A × ℝ → X} {d : B × ℝ → X} {e : A → X} {f : B → X}
    (hc : Topology.IsOpenEmbedding c) (hd : Topology.IsOpenEmbedding d)
    (he : ∀ a, c (a, 0) = e a) (hf : ∀ b, d (b, 0) = f b)
    (hdisj : Disjoint (range e) (range f)) :
    ∃ δ : ℝ, 0 < δ ∧
      Disjoint (c '' {q : A × ℝ | |q.2| < δ}) (d '' {q : B × ℝ | |q.2| < δ}) := by
  obtain ⟨δ, hδ, _, hd'⟩ := exists_pos_disjoint_of_shrinking_families
    (E₁ := A × ℝ) (E₂ := B × ℝ)
    (K₁ := (univ : Set A) ×ˢ Icc (-1 : ℝ) 1)
    (K₂ := (univ : Set B) ×ˢ Icc (-1 : ℝ) 1)
    (core₁ := (univ : Set A) ×ˢ ({0} : Set ℝ))
    (core₂ := (univ : Set B) ×ˢ ({0} : Set ℝ))
    (isCompact_univ.prod isCompact_Icc) (isCompact_univ.prod isCompact_Icc)
    hc.continuous hd.continuous
    (V₁ := fun δ => (univ : Set A) ×ˢ Ioo (-δ) δ)
    (V₂ := fun δ => (univ : Set B) ×ˢ Ioo (-δ) δ)
    (fun δ hδ hδ1 => fun q hq => ⟨trivial,
      ⟨by linarith [neg_le_neg hδ1, hq.2.1], by linarith [hq.2.2, hδ1]⟩⟩)
    (fun δ hδ hδ1 => fun q hq => ⟨trivial,
      ⟨by linarith [neg_le_neg hδ1, hq.2.1], by linarith [hq.2.2, hδ1]⟩⟩)
    (fun {a b} ha hab => fun q hq => ⟨trivial,
      ⟨by linarith [ha, hq.2.1, hab], by linarith [hq.2.2, hab]⟩⟩)
    (fun {a b} ha hab => fun q hq => ⟨trivial,
      ⟨by linarith [ha, hq.2.1, hab], by linarith [hq.2.2, hab]⟩⟩)
    (fun x hx => by
      have hzero : x.2 = 0 := by
        by_contra hne
        have hε : 0 < |x.2| / 2 := half_pos (abs_pos.mpr hne)
        have hcl := hx (|x.2| / 2) hε
        have hsub : closure ((univ : Set A) ×ˢ Ioo (-(|x.2| / 2)) (|x.2| / 2)) ⊆
            {q : A × ℝ | q.2 ∈ Icc (-(|x.2| / 2)) (|x.2| / 2)} :=
          closure_minimal (fun q hq => Ioo_subset_Icc_self hq.2)
            (isClosed_Icc.preimage continuous_snd)
        have hle : |x.2| ≤ |x.2| / 2 := abs_le.mpr (hsub hcl)
        have hz : |x.2| = 0 := by linarith [abs_nonneg x.2]
        exact hne (abs_eq_zero.mp hz)
      exact ⟨trivial, by simpa using hzero⟩)
    (fun y hy => by
      have hzero : y.2 = 0 := by
        by_contra hne
        have hε : 0 < |y.2| / 2 := half_pos (abs_pos.mpr hne)
        have hcl := hy (|y.2| / 2) hε
        have hsub : closure ((univ : Set B) ×ˢ Ioo (-(|y.2| / 2)) (|y.2| / 2)) ⊆
            {q : B × ℝ | q.2 ∈ Icc (-(|y.2| / 2)) (|y.2| / 2)} :=
          closure_minimal (fun q hq => Ioo_subset_Icc_self hq.2)
            (isClosed_Icc.preimage continuous_snd)
        have hle : |y.2| ≤ |y.2| / 2 := abs_le.mpr (hsub hcl)
        have hz : |y.2| = 0 := by linarith [abs_nonneg y.2]
        exact hne (abs_eq_zero.mp hz)
      exact ⟨trivial, by simpa using hzero⟩)
    (hdisj := by rw [image_core_eq_range c e he, image_core_eq_range d f hf]; exact hdisj)
  refine ⟨δ, hδ, ?_⟩
  have hA : {q : A × ℝ | |q.2| < δ} = (univ : Set A) ×ˢ Ioo (-δ) δ := by
    ext q
    exact ⟨fun h => ⟨trivial, abs_lt.mp h⟩, fun h => abs_lt.mpr h.2⟩
  have hB : {q : B × ℝ | |q.2| < δ} = (univ : Set B) ×ˢ Ioo (-δ) δ := by
    ext q
    exact ⟨fun h => ⟨trivial, abs_lt.mp h⟩, fun h => abs_lt.mpr h.2⟩
  rw [hA, hB]
  exact hd'

end DifferentialGeometry.Topology.Collar

namespace DifferentialGeometry.Topology.Collar

universe u v

theorem disjointBoundaryCollarFamily
    {X : Type u} [TopologicalSpace X] [T2Space X] {ι : Type v} [Finite ι]
    {S : ι → Type u} [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)]
    {e : ∀ i, S i → X} {c : ∀ i, S i × ℝ → X}
    (hc : ∀ i, Topology.IsOpenEmbedding (c i))
    (h0 : ∀ i s, c i (s, 0) = e i s)
    (hdisj : Pairwise fun i j => Disjoint (range (e i)) (range (e j))) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise fun i j =>
      Disjoint (c i '' {q : S i × ℝ | |q.2| < δ})
        (c j '' {q : S j × ℝ | |q.2| < δ}) := by
  obtain ⟨δ, hδ, _, hpair⟩ := disjointFamily_of_shrinking_families
    (E := fun i => S i × ℝ)
    (K := fun i => (univ : Set (S i)) ×ˢ Icc (-1 : ℝ) 1)
    (core := fun i => (univ : Set (S i)) ×ˢ ({0} : Set ℝ))
    (c := c) (hc := fun i => (hc i).continuous)
    (V := fun i δ => (univ : Set (S i)) ×ˢ Ioo (-δ) δ)
    (fun i => isCompact_univ.prod isCompact_Icc)
    (fun i δ hδ hδ1 q hq => ⟨trivial,
      ⟨by linarith [neg_le_neg hδ1, hq.2.1], by linarith [hq.2.2, hδ1]⟩⟩)
    (fun i {a b} ha hab q hq => ⟨trivial,
      ⟨by linarith [ha, hq.2.1, hab], by linarith [hq.2.2, hab]⟩⟩)
    (fun i x hx => by
      have hzero : x.2 = 0 := by
        by_contra hne
        have hε : 0 < |x.2| / 2 := half_pos (abs_pos.mpr hne)
        have hcl := hx (|x.2| / 2) hε
        have hsub : closure ((univ : Set (S i)) ×ˢ Ioo (-(|x.2| / 2)) (|x.2| / 2)) ⊆
            {q : S i × ℝ | q.2 ∈ Icc (-(|x.2| / 2)) (|x.2| / 2)} :=
          closure_minimal (fun q hq => Ioo_subset_Icc_self hq.2)
            (isClosed_Icc.preimage continuous_snd)
        have hle : |x.2| ≤ |x.2| / 2 := abs_le.mpr (hsub hcl)
        have hz : |x.2| = 0 := by linarith [abs_nonneg x.2]
        exact hne (abs_eq_zero.mp hz)
      exact ⟨trivial, by simpa using hzero⟩)
    (fun i j hij => by
      change Disjoint (c i '' ((univ : Set (S i)) ×ˢ ({0} : Set ℝ)))
        (c j '' ((univ : Set (S j)) ×ˢ ({0} : Set ℝ)))
      rw [image_core_eq_range (c i) (e i) (h0 i), image_core_eq_range (c j) (e j) (h0 j)]
      exact hdisj hij)
  have hset : ∀ i, {q : S i × ℝ | |q.2| < δ} = (univ : Set (S i)) ×ˢ Ioo (-δ) δ := by
    intro i
    ext q
    exact ⟨fun h => ⟨trivial, abs_lt.mp h⟩, fun h => abs_lt.mpr h.2⟩
  exact ⟨δ, hδ, fun i j hij => by
    change Disjoint (c i '' {q : S i × ℝ | |q.2| < δ}) (c j '' {q : S j × ℝ | |q.2| < δ})
    rw [hset i, hset j]
    exact hpair hij⟩

theorem image_halfCore_eq_range {A : Type*} {X : Type*}
    (c : A × {t : ℝ // 0 ≤ t} → X) (e : A → X) (h : ∀ a, c (a, 0) = e a) :
    c '' ((univ : Set A) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0}) = range e := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq2 : q.2 = 0 := Subtype.ext hq.2
    have hc : c q = e q.1 := by
      rw [← h q.1]
      exact congrArg c (Prod.ext rfl hq2)
    exact ⟨q.1, hc.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(a, 0), ⟨trivial, rfl⟩, h a⟩

theorem mem_core_of_mem_closure_halfSpace {T : Type*} [TopologicalSpace T]
    (z : T × {t : ℝ // 0 ≤ t})
    (hz : ∀ δ, 0 < δ → z ∈ closure
      ((univ : Set T) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ})) :
    z ∈ (univ : Set T) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0} := by
  have hbound : ∀ δ : ℝ, 0 < δ → (z.2 : ℝ) ∈ Icc (0 : ℝ) δ := by
    intro δ hδ
    have hcl := hz δ hδ
    have hsub : closure ((univ : Set T) ×ˢ
        {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ}) ⊆
        {q : T × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) ∈ Icc (0 : ℝ) δ} :=
      closure_minimal (fun q hq => ⟨q.2.2, le_of_lt hq.2⟩)
        (isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd))
    exact hsub hcl
  have hzero : (z.2 : ℝ) = 0 := by
    have h1 : (z.2 : ℝ) ≤ 0 := by
      by_contra hgt
      have h2 : (z.2 : ℝ) ≤ (z.2 : ℝ) / 2 := by
        have := (hbound ((z.2 : ℝ) / 2) (by linarith)).2
        linarith
      linarith
    have h3 : 0 ≤ (z.2 : ℝ) := (hbound 1 one_pos).1
    linarith
  exact ⟨trivial, hzero⟩

theorem isCompact_halfSpace_le_one :
    IsCompact {t : {t : ℝ // 0 ≤ t} | (t : ℝ) ≤ 1} := by
  rw [IsEmbedding.isCompact_iff IsEmbedding.subtypeVal]
  have himg : Subtype.val '' {t : {t : ℝ // 0 ≤ t} | (t : ℝ) ≤ 1} = Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, ht⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [himg]
  exact isCompact_Icc

theorem exists_pos_disjoint_halfCollar_pair
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {B : Type*} [TopologicalSpace B] [CompactSpace B]
    {c : A × {t : ℝ // 0 ≤ t} → X} {d : B × {t : ℝ // 0 ≤ t} → X}
    {e : A → X} {f : B → X}
    (hc : Continuous c) (hd : Continuous d)
    (he : ∀ a, c (a, 0) = e a) (hf : ∀ b, d (b, 0) = f b)
    (hdisj : Disjoint (range e) (range f)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      Disjoint (c '' {q : A × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ})
        (d '' {q : B × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ}) := by
  obtain ⟨δ, hδ, hδ1, hd'⟩ := exists_pos_disjoint_of_shrinking_families
    (E₁ := A × {t : ℝ // 0 ≤ t}) (E₂ := B × {t : ℝ // 0 ≤ t})
    (K₁ := (univ : Set A) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) ≤ 1})
    (K₂ := (univ : Set B) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) ≤ 1})
    (core₁ := (univ : Set A) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0})
    (core₂ := (univ : Set B) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0})
    (isCompact_univ.prod isCompact_halfSpace_le_one)
    (isCompact_univ.prod isCompact_halfSpace_le_one)
    hc hd
    (V₁ := fun δ => (univ : Set A) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ})
    (V₂ := fun δ => (univ : Set B) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ})
    (fun δ hδ hδ1 q hq => ⟨trivial, by
      have hlt : (q.2 : ℝ) < δ := hq.2
      change (q.2 : ℝ) ≤ 1
      linarith⟩)
    (fun δ hδ hδ1 q hq => ⟨trivial, by
      have hlt : (q.2 : ℝ) < δ := hq.2
      change (q.2 : ℝ) ≤ 1
      linarith⟩)
    (fun {a b} ha hab q hq => ⟨trivial, by
      have hlt : (q.2 : ℝ) < a := hq.2
      change (q.2 : ℝ) < b
      linarith⟩)
    (fun {a b} ha hab q hq => ⟨trivial, by
      have hlt : (q.2 : ℝ) < a := hq.2
      change (q.2 : ℝ) < b
      linarith⟩)
    (fun x hx => mem_core_of_mem_closure_halfSpace x hx)
    (fun y hy => mem_core_of_mem_closure_halfSpace y hy)
    (by rw [image_halfCore_eq_range c e he, image_halfCore_eq_range d f hf]; exact hdisj)
  have hA : {q : A × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ} =
      (univ : Set A) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ} := by
    ext q
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  have hB : {q : B × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ} =
      (univ : Set B) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ} := by
    ext q
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [← hA, ← hB] at hd'
  exact ⟨δ, hδ, hδ1, hd'⟩

end DifferentialGeometry.Topology.Collar

namespace DifferentialGeometry.Topology.Collar

universe u v

theorem disjointHalfCollarFamily
    {X : Type u} [TopologicalSpace X] [T2Space X] {ι : Type v} [Finite ι]
    {S : ι → Type u} [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)]
    {e : ∀ i, S i → X} {c : ∀ i, S i × {t : ℝ // 0 ≤ t} → X}
    (hc : ∀ i, Continuous (c i))
    (h0 : ∀ i s, c i (s, 0) = e i s)
    (hdisj : Pairwise fun i j => Disjoint (range (e i)) (range (e j))) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise fun i j =>
      Disjoint (c i '' {q : S i × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ})
        (c j '' {q : S j × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ}) := by
  obtain ⟨δ, hδ, _, hpair⟩ := disjointFamily_of_shrinking_families
    (E := fun i => S i × {t : ℝ // 0 ≤ t})
    (K := fun i => (univ : Set (S i)) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) ≤ 1})
    (core := fun i => (univ : Set (S i)) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0})
    (c := c) (hc := hc)
    (V := fun i δ => (univ : Set (S i)) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ})
    (fun i => isCompact_univ.prod isCompact_halfSpace_le_one)
    (fun i δ hδ hδ1 q hq => ⟨trivial, by
      have hlt : (q.2 : ℝ) < δ := hq.2
      change (q.2 : ℝ) ≤ 1
      linarith⟩)
    (fun i {a b} ha hab q hq => ⟨trivial, by
      have hlt : (q.2 : ℝ) < a := hq.2
      change (q.2 : ℝ) < b
      linarith⟩)
    (fun i x hx => mem_core_of_mem_closure_halfSpace x hx)
    (fun i j hij => by
      change Disjoint (c i '' ((univ : Set (S i)) ×ˢ
          {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0}))
        (c j '' ((univ : Set (S j)) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) = 0}))
      rw [image_halfCore_eq_range (c i) (e i) (h0 i),
        image_halfCore_eq_range (c j) (e j) (h0 j)]
      exact hdisj hij)
  have hset : ∀ i, {q : S i × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ} =
      (univ : Set (S i)) ×ˢ {t : {t : ℝ // 0 ≤ t} | (t : ℝ) < δ} := by
    intro i
    ext q
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  exact ⟨δ, hδ, fun i j hij => by
    change Disjoint (c i '' {q : S i × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ})
      (c j '' {q : S j × {t : ℝ // 0 ≤ t} | (q.2 : ℝ) < δ})
    rw [hset i, hset j]
    exact hpair hij⟩

end DifferentialGeometry.Topology.Collar

namespace DifferentialGeometry.Topology.Collar

universe u v

theorem exists_common_width_of_finite_twoSidedCollars
    {X : Type u} [TopologicalSpace X] [T2Space X] {ι : Type v} [Finite ι]
    {S : ι → Type u} [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)]
    {e : ∀ i, S i → X}
    (c : ∀ i, DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar (e i))
    (hdisj : Pairwise fun i j => Disjoint (range (e i)) (range (e j))) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise fun i j =>
      Disjoint ((c i).toFun '' {q : S i × ℝ | |q.2| < δ})
        ((c j).toFun '' {q : S j × ℝ | |q.2| < δ}) :=
  disjointBoundaryCollarFamily (c := fun i => (c i).toFun)
    (fun i => (c i).isOpenEmbedding_toFun) (fun i s => (c i).zero_eq s) hdisj

end DifferentialGeometry.Topology.Collar
