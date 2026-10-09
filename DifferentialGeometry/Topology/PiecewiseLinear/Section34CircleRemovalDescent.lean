/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem IsPLHomeomorphInto.congr_of_eqOn {n : ℕ} {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] {f g : M → N} {K : Set M}
    (hf : IsPLHomeomorphInto n f K) (hfg : EqOn f g K) : IsPLHomeomorphInto n g K := by
  obtain ⟨hpl, hinj, hinv⟩ := hf
  have himg : f '' K = g '' K := hfg.image_eq
  refine ⟨hpl.congr hfg.symm, hinj.congr hfg, fun y hy => ?_⟩
  rw [← himg] at hy ⊢
  obtain ⟨k, hk, hkinv⟩ := hinv y hy
  exact ⟨k, hk, fun x hx => (congrArg k (hfg hx).symm).trans (hkinv hx)⟩

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

abbrev Section34RemovalGood (U : Set M₁) (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (Cp CpBd Cc : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
    (Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (cnt₀ : Section34EdgeIndex 𝒦 𝒦' → ℕ)
    (G₀ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (S : Set (Section34EdgeIndex 𝒦 𝒦'))
    (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
    (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂) : Prop :=
  Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp Tp
      cnt Pg G ∧
    (∀ e ∈ S, cnt e = 1) ∧ (∀ e ∉ S, cnt e = cnt₀ e) ∧
    (∀ w, EqOn (G w) (G₀ w) {x ∈ Cc w | ∀ e, G₀ w x ∉ interior (Sp e)}) ∧
    ∀ w, EqOn (G w) (G₀ w) (simplexBody 𝒦' w.1)

omit [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
abbrev Section34RemovalLe {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (Sp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (K : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (S₁ : Set (Section34EdgeIndex 𝒦 𝒦')) (G₁ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
    (S₂ : Set (Section34EdgeIndex 𝒦 𝒦')) (G₂ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) : Prop :=
  S₁ ⊆ S₂ ∧ ∀ w, (∀ e ∈ S₂ \ S₁, ¬ (Sp e ∩ K w).Nonempty) → G₂ w = G₁ w

omit [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34RemovalLe_trans {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {Sp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {K : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {S₁ S₂ S₃ : Set (Section34EdgeIndex 𝒦 𝒦')}
    {G₁ G₂ G₃ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
    (h₁₂ : Section34RemovalLe Sp K S₁ G₁ S₂ G₂) (h₂₃ : Section34RemovalLe Sp K S₂ G₂ S₃ G₃) :
    Section34RemovalLe Sp K S₁ G₁ S₃ G₃ := by
  obtain ⟨hS₁₂, hG₁₂⟩ := h₁₂
  obtain ⟨hS₂₃, hG₂₃⟩ := h₂₃
  refine ⟨hS₁₂.trans hS₂₃, fun w hw => ?_⟩
  rw [hG₂₃ w fun e he => hw e ⟨he.1, fun h1 => he.2 (hS₁₂ h1)⟩,
    hG₁₂ w fun e he => hw e ⟨hS₂₃ he.1, he.2⟩]

variable {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂}

theorem section34PiercingConditions_congr_of_eqOn
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ} {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
    {G₁ G₂ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂} (hG : ∀ w, EqOn (G₁ w) (G₂ w) (Cc w))
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G₁) :
    Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp Tp
      cnt Pg G₂ := by
  obtain ⟨-, -, hsubs, -, hcp, hbody, -, -, -, -, -, htube, hSnCc, -, hAa, hBb, -⟩ := hprep
  have him : ∀ w (s : Set M₁), s ⊆ Cc w → G₂ w '' s = G₁ w '' s :=
    fun w s hs => (((hG w).mono hs).image_eq).symm
  have hCp : ∀ w, Cp w ⊆ Cc w := fun w => (hsubs w).2.1
  have hBd : ∀ w, CpBd w ⊆ Cc w := fun w => (hcp w).boundary_subset.trans (hCp w)
  have hBody : ∀ w, simplexBody 𝒦' w.1 ⊆ Cc w :=
    fun w => ((hbody w).trans interior_subset).trans (hCp w)
  have hSn₁ : ∀ e, Sn e ⊆ Cc (ends e).1 := fun e => hSnCc e _ (Or.inl rfl)
  have hSn₂ : ∀ e, Sn e ⊆ Cc (ends e).2 := fun e => hSnCc e _ (Or.inr rfl)
  have hTn₁ : ∀ e, Tn e ⊆ Cc (ends e).1 :=
    fun e => ((htube e).1.trans interior_subset).trans (hSn₁ e)
  have hAa₁ : ∀ e, Aa e ⊆ Cc (ends e).1 := by
    intro e
    rw [(hAa e).1]
    exact inter_subset_left.trans (hBd _)
  have hAb₀ : ∀ e, Ab₀ e ⊆ Cc (ends e).1 := fun e => (hAa e).2.first_subset.trans (hAa₁ e)
  have hAb₁ : ∀ e, Ab₁ e ⊆ Cc (ends e).1 := fun e => (hAa e).2.second_subset.trans (hAa₁ e)
  have hBb₂ : ∀ e, Bb e ⊆ Cc (ends e).2 := fun e => (hBb e).1.trans (hBd _)
  have hBb₀₁ : ∀ e, Bb₀ e ∪ Bb₁ e ⊆ Cc (ends e).2 :=
    fun e => (union_subset (hBb e).2.first_subset (hBb e).2.second_subset).trans (hBb₂ e)
  have hAad : ∀ e, Aa e \ (Ab₀ e ∪ Ab₁ e) ⊆ Cc (ends e).1 := fun e => sdiff_subset.trans (hAa₁ e)
  have hBbd : ∀ e, Bb e \ (Bb₀ e ∪ Bb₁ e) ⊆ Cc (ends e).2 := fun e => sdiff_subset.trans (hBb₂ e)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19,
    p20, p21, p22⟩ := hpack
  refine ⟨fun w => (p1 w).congr_of_eqOn (hG w), fun w => ?_, fun e => ?_, fun e => ?_, p5, p6,
    fun e => ?_, fun e => ?_, fun e => ?_, p10, fun w => ((p11 w).congr_of_eqOn
      ((hG w).mono (hCp w))), fun w e => ?_, fun e w hw₁ hw₂ => ?_, fun w w' hww' => ?_,
    fun e => ?_, fun e => ?_, fun e => ?_, fun e i hi => ?_, p19, fun e => ?_,
    fun e d hed => ?_, fun w w' hww' => ?_⟩
  · rw [him w _ subset_rfl]
    exact p2 w
  · rw [him _ _ (hSn₂ e), him _ _ (hSn₁ e)]
    exact p3 e
  · rw [him _ _ (hSn₁ e), him _ _ (hTn₁ e)]
    exact p4 e
  · rw [him _ _ (hBd _), him _ _ (hBd _), him _ _ (hAad e), him _ _ (hBbd e)]
    exact p7 e
  · rw [him _ _ (hAb₀ e), him _ _ (hCp _), him _ _ (hAb₁ e)]
    exact p8 e
  · rw [him _ _ (hBb₂ e), him _ _ (hBb₀₁ e)]
    exact p9 e
  · rw [him _ _ (hBody w)]
    exact p12 w e
  · rw [him _ _ (hBd w)]
    exact p13 e w hw₁ hw₂
  · rw [him _ _ (hCp w), him _ _ (hCp w')]
    exact p14 w w' hww'
  · rw [him _ _ (hBb₂ e), him _ _ (hCp _)]
    exact p15 e
  · rw [him _ _ (hBb₂ e), him _ _ (hCp _)]
    exact p16 e
  · rw [him _ _ (hAa₁ e), him _ _ (hBb₂ e)]
    exact p17 e
  · rw [him _ _ (hAad e), him _ _ (hBbd e)]
    exact p18 e i hi
  · rw [him _ _ (hAa₁ e), him _ _ (hBb₂ e)]
    exact p20 e
  · rw [him _ _ (hCp _), him _ _ (hCp _), him _ _ (hCp _), him _ _ (hCp _)]
    exact p21 e d hed
  · rw [him _ _ (hCp w')]
    exact p22 w w' hww'

theorem exists_section34PiercingConditions_count_le_one_of_step
    (hstep : ∀ (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G →
      ∀ e₀ : Section34EdgeIndex 𝒦 𝒦', 1 < cnt e₀ →
      ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
        (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
        Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
            Sp Tp cnt' Pg' G' ∧
          cnt' e₀ < cnt e₀ ∧
          (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
          (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
          ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
            G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') :
    ∀ (n : ℕ) (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G → cnt e₀ ≤ n →
      ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
        (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
        Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
            Sp Tp cnt' Pg' G' ∧
          cnt' e₀ ≤ 1 ∧ (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
          ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)} := by
  intro n
  induction n with
  | zero =>
      intro G cnt Pg hp hle
      exact ⟨G, cnt, Pg, hp, by omega, fun _ _ => rfl, fun w => Set.eqOn_refl (G w) _⟩
  | succ n ih =>
      intro G cnt Pg hp hle
      by_cases h1 : cnt e₀ ≤ 1
      · exact ⟨G, cnt, Pg, hp, h1, fun _ _ => rfl, fun w => Set.eqOn_refl (G w) _⟩
      · obtain ⟨G₁, cnt₁, Pg₁, hp₁, hdrop, hfix, hoff, -⟩ := hstep G cnt Pg hp e₀ (by omega)
        obtain ⟨G₂, cnt₂, Pg₂, hp₂, hle₂, hfix₂, hoff₂⟩ := ih G₁ cnt₁ Pg₁ hp₁ (by omega)
        refine ⟨G₂, cnt₂, Pg₂, hp₂, hle₂, fun e he => (hfix₂ e he).trans (hfix e he), ?_⟩
        intro w x hx
        have hx1 : G₁ w x = G w x := hoff w hx
        have hx2 : x ∈ {x ∈ Cc w | G₁ w x ∉ interior (Sp e₀)} := by
          refine ⟨hx.1, ?_⟩
          rw [hx1]
          exact hx.2
        exact (hoff₂ w hx2).trans hx1

theorem exists_section34RemovalGood_upperBound (K : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (hKfin : ∀ w, {e | (Sp e ∩ K w).Nonempty}.Finite)
    (cnt₀ : Section34EdgeIndex 𝒦 𝒦' → ℕ) (G₀ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
    (c : Set (Set (Section34EdgeIndex 𝒦 𝒦') × (Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) ×
      (Section34EdgeIndex 𝒦 𝒦' → ℕ) × (Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂)))
    (hcne : c.Nonempty)
    (hgood : ∀ a ∈ c, Section34RemovalGood U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt₀ G₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
    (hchain : IsChain (fun a b : Set (Section34EdgeIndex 𝒦 𝒦') ×
      (Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) × (Section34EdgeIndex 𝒦 𝒦' → ℕ) ×
      (Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂) => Section34RemovalLe Sp K a.1 a.2.1 b.1 b.2.1) c) :
    ∃ (S : Set (Section34EdgeIndex 𝒦 𝒦')) (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
      (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ) (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34RemovalGood U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt₀ G₀
        S G cnt Pg ∧ ∀ a ∈ c, Section34RemovalLe Sp K a.1 a.2.1 S G := by
  classical
  have hcov : ∀ F : Finset (Section34EdgeIndex 𝒦 𝒦'),
      (↑F : Set (Section34EdgeIndex 𝒦 𝒦')) ⊆ ⋃ a ∈ c, a.1 →
        ∃ a ∈ c, (↑F : Set (Section34EdgeIndex 𝒦 𝒦')) ⊆ a.1 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        intro _
        obtain ⟨a, ha⟩ := hcne
        exact ⟨a, ha, by simp⟩
    | insert e F heF ih =>
        intro hF
        rw [Finset.coe_insert, insert_subset_iff] at hF
        obtain ⟨a, ha, haF⟩ := ih hF.2
        obtain ⟨b, hb, heb⟩ := mem_iUnion₂.mp hF.1
        rw [Finset.coe_insert]
        rcases eq_or_ne a b with rfl | hab
        · exact ⟨a, ha, insert_subset heb haF⟩
        · rcases hchain ha hb hab with hle | hle
          · exact ⟨b, hb, insert_subset heb (haF.trans hle.1)⟩
          · exact ⟨a, ha, insert_subset (hle.1 heb) haF⟩
  have hFw : ∀ w, ∃ a ∈ c, ∀ e ∈ ⋃ a ∈ c, a.1, (Sp e ∩ K w).Nonempty → e ∈ a.1 := by
    intro w
    obtain ⟨a, ha, hsub⟩ := hcov ((hKfin w).toFinset.filter fun e => e ∈ ⋃ a ∈ c, a.1)
      fun e he => (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
    exact ⟨a, ha, fun e he hne => hsub (Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨(hKfin w).mem_toFinset.mpr hne, he⟩))⟩
  choose A hA hAsub using hFw
  have hkey : ∀ w, ∀ b ∈ c, (∀ e ∈ ⋃ a ∈ c, a.1, (Sp e ∩ K w).Nonempty → e ∈ b.1) →
      b.2.1 w = (A w).2.1 w := by
    intro w b hb hbF
    rcases eq_or_ne b (A w) with rfl | hne
    · rfl
    · rcases hchain hb (hA w) hne with hle | hle
      · exact (hle.2 w fun e he hne' =>
          he.2 (hbF e (mem_iUnion₂.mpr ⟨A w, hA w, he.1⟩) hne')).symm
      · exact hle.2 w fun e he hne' => he.2 (hAsub w e (mem_iUnion₂.mpr ⟨b, hb, he.1⟩) hne')
  let Gl : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂ := fun w => (A w).2.1 w
  let cntl : Section34EdgeIndex 𝒦 𝒦' → ℕ := fun e => if e ∈ ⋃ a ∈ c, a.1 then 1 else cnt₀ e
  have hagree : ∀ (L : Finset (Section34VertexIndex 𝒦 𝒦'))
      (D : Finset (Section34EdgeIndex 𝒦 𝒦')),
      ∃ a ∈ c, (∀ w ∈ L, a.2.1 w = Gl w) ∧ ∀ e ∈ D, a.2.2.1 e = cntl e := by
    intro L D
    obtain ⟨a, ha, hsub⟩ := hcov ((L.biUnion fun w => (hKfin w).toFinset.filter
      fun e => e ∈ ⋃ a ∈ c, a.1) ∪ D.filter fun e => e ∈ ⋃ a ∈ c, a.1) (by
        intro e he
        rcases Finset.mem_union.mp (Finset.mem_coe.mp he) with he | he
        · obtain ⟨w, -, hew⟩ := Finset.mem_biUnion.mp he
          exact (Finset.mem_filter.mp hew).2
        · exact (Finset.mem_filter.mp he).2)
    obtain ⟨-, hone, hzero, -, -⟩ := hgood a ha
    refine ⟨a, ha, fun w hw => hkey w a ha fun e he hne => hsub (Finset.mem_coe.mpr
      (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr
        ⟨(hKfin w).mem_toFinset.mpr hne, he⟩⟩)))), fun e he => ?_⟩
    by_cases heS : e ∈ ⋃ a ∈ c, a.1
    · rw [hone e (hsub (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨he, heS⟩)))))]
      exact (ite_eq_left heS).symm
    · have hea : e ∉ a.1 := fun hea => heS (mem_iUnion₂.mpr ⟨a, ha, hea⟩)
      rw [hzero e hea]
      exact (ite_eq_right heS).symm
  have hB : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ a ∈ c, (a.2.1 (ends e).1 = Gl (ends e).1 ∧
      a.2.1 (ends e).2 = Gl (ends e).2) ∧ a.2.2.1 e = cntl e := by
    intro e
    obtain ⟨a, ha, hL, hD⟩ := hagree {(ends e).1, (ends e).2} {e}
    exact ⟨a, ha, ⟨hL _ (by simp), hL _ (by simp)⟩, hD e (by simp)⟩
  choose B hBc hBG hBcnt using hB
  let Pgl : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂ := fun e => (B e).2.2.2 e
  obtain ⟨a₀, ha₀⟩ := hcne
  obtain ⟨-, -, -, -, q5, q6, -, -, -, q10, -⟩ := (hgood a₀ ha₀).1
  refine ⟨⋃ a ∈ c, a.1, Gl, cntl, Pgl, ⟨⟨fun w => ?_, fun w => ?_, fun e => ?_, fun e => ?_, q5,
    q6, fun e => ?_, fun e => ?_, fun e => ?_, q10, fun w => ?_, fun w e => ?_,
    fun e w hw₁ hw₂ => ?_, fun w w' hww' => ?_, fun e => ?_, fun e => ?_, fun e => ?_,
    fun e i hi => ?_, fun e i hi j hj hij => ?_, fun e => ?_, fun e d hed => ?_,
    fun w w' hww' => ?_⟩, fun e he => ite_eq_left he, fun e he => ite_eq_right he, fun w => ?_,
    fun w => ?_⟩, fun a ha => ⟨fun e he => mem_iUnion₂.mpr ⟨a, ha, he⟩, fun w hw => ?_⟩⟩
  · obtain ⟨a, ha, hL, -⟩ := hagree {w} ∅
    obtain ⟨p, -⟩ := (hgood a ha).1
    rw [← hL w (by simp)]
    exact p w
  · obtain ⟨a, ha, hL, -⟩ := hagree {w} ∅
    obtain ⟨-, p, -⟩ := (hgood a ha).1
    rw [← hL w (by simp)]
    exact p w
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2} ∅
    obtain ⟨-, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1} ∅
    obtain ⟨-, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2} ∅
    obtain ⟨-, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2} ∅
    obtain ⟨-, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).2} ∅
    obtain ⟨-, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {w} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL w (by simp)]
    exact p w
  · obtain ⟨a, ha, hL, -⟩ := hagree {w} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL w (by simp)]
    exact p w e
  · obtain ⟨a, ha, hL, -⟩ := hagree {w} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL w (by simp)]
    exact p e w hw₁ hw₂
  · obtain ⟨a, ha, hL, -⟩ := hagree {w, w'} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL w (by simp), ← hL w' (by simp)]
    exact p w w' hww'
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood (B e) (hBc e)).1
    rw [← (hBG e).1, ← (hBG e).2, ← hBcnt e]
    exact p e
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood (B e) (hBc e)).1
    rw [← hBcnt e] at hi
    rw [← (hBG e).1, ← (hBG e).2]
    exact p e i hi
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ :=
      (hgood (B e) (hBc e)).1
    rw [← hBcnt e] at hi hj
    exact p e i hi j hj hij
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp)]
    exact p e
  · obtain ⟨a, ha, hL, -⟩ := hagree {(ends e).1, (ends e).2, (ends d).1, (ends d).2} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p, -⟩ := (hgood a ha).1
    rw [← hL (ends e).1 (by simp), ← hL (ends e).2 (by simp), ← hL (ends d).1 (by simp),
      ← hL (ends d).2 (by simp)]
    exact p e d hed
  · obtain ⟨a, ha, hL, -⟩ := hagree {w'} ∅
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p⟩ := (hgood a ha).1
    rw [← hL w' (by simp)]
    exact p w w' hww'
  · exact (hgood (A w) (hA w)).2.2.2.1 w
  · exact (hgood (A w) (hA w)).2.2.2.2 w
  · refine (hkey w a ha fun e he hne => ?_).symm
    by_contra hea
    exact hw e ⟨he, hea⟩ hne

theorem exists_section34RemovalGood_insert
    (hstep : ∀ (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G →
      ∀ e₀ : Section34EdgeIndex 𝒦 𝒦', 1 < cnt e₀ →
      ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
        (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
        Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
            Sp Tp cnt' Pg' G' ∧
          cnt' e₀ < cnt e₀ ∧
          (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
          (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
          ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
            G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (K : Section34VertexIndex 𝒦 𝒦' → Set M₂) (hQK : ∀ w, Q w ⊆ K w)
    (cnt₀ : Section34EdgeIndex 𝒦 𝒦' → ℕ) (G₀ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
    {S : Set (Section34EdgeIndex 𝒦 𝒦')} {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
    {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ} {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
    (hgood : Section34RemovalGood U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp Tp
      cnt₀ G₀ S G cnt Pg)
    {e₀ : Section34EdgeIndex 𝒦 𝒦'} (he₀ : e₀ ∉ S) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34RemovalGood U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt₀ G₀
        (insert e₀ S) G' cnt' Pg' ∧ Section34RemovalLe Sp K S G (insert e₀ S) G' := by
  classical
  obtain ⟨hpc, hone, hzero, hoff, hbody⟩ := hgood
  obtain ⟨G₁, cnt₁, Pg₁, hpc₁, hle₁, hfix₁, hoff₁⟩ :=
    exists_section34PiercingConditions_count_le_one_of_step hstep e₀ (cnt e₀) G cnt Pg hpc le_rfl
  obtain ⟨-, hGQ, -, -, -, -, -, -, -, -, -, hmark, -⟩ := hpc
  let G₂ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂ :=
    fun w => if (Sp e₀ ∩ K w).Nonempty then G₁ w else G w
  have hG₂ : ∀ w, EqOn (G₁ w) (G₂ w) (Cc w) := by
    intro w x hx
    by_cases hw : (Sp e₀ ∩ K w).Nonempty
    · simp only [G₂, ite_eq_left hw]
    · simp only [G₂, ite_eq_right hw]
      exact hoff₁ w ⟨hx, fun hint =>
        hw ⟨G w x, interior_subset hint, hQK w (hGQ w ⟨x, hx, rfl⟩)⟩⟩
  have hpc₂ := section34PiercingConditions_congr_of_eqOn hprep hG₂ hpc₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -⟩ := hpc₁
  have hcnt₁ : cnt₁ e₀ = 1 := le_antisymm hle₁ (h17 e₀).1
  refine ⟨G₂, cnt₁, Pg₁, ⟨hpc₂, fun e he => ?_, fun e he => ?_, fun w x hx => ?_,
    fun w x hx => ?_⟩, subset_insert e₀ S, fun w hw => ?_⟩
  · rcases mem_insert_iff.mp he with rfl | heS
    · exact hcnt₁
    · rw [hfix₁ e fun h => he₀ (h ▸ heS)]
      exact hone e heS
  · have hne : e ≠ e₀ := fun h => he (h ▸ mem_insert e₀ S)
    rw [hfix₁ e hne]
    exact hzero e fun heS => he (mem_insert_of_mem e₀ heS)
  · have hGx : G w x = G₀ w x := hoff w hx
    have h1 : G₁ w x = G w x := hoff₁ w ⟨hx.1, by rw [hGx]; exact hx.2 e₀⟩
    rw [← (hG₂ w hx.1), h1, hGx]
  · have hxC : x ∈ Cc w := by
      obtain ⟨-, -, hsubs, -, -, hb, -⟩ := hprep
      exact (hsubs w).2.1 (interior_subset (hb w hx))
    have h1 : G₁ w x = G w x := hoff₁ w ⟨hxC, fun hint =>
      disjoint_left.mp (hmark w e₀) ⟨x, hx, rfl⟩ (interior_subset hint)⟩
    rw [← (hG₂ w hxC), h1]
    exact hbody w hx
  · have hno : ¬ (Sp e₀ ∩ K w).Nonempty := hw e₀ ⟨mem_insert e₀ S, he₀⟩
    exact ite_eq_right hno

theorem exists_section34ProtectedCircleRemoval_of_step
    (hstep : ∀ (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G →
      ∀ e₀ : Section34EdgeIndex 𝒦 𝒦', 1 < cnt e₀ →
      ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
        (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
        Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
            Sp Tp cnt' Pg' G' ∧
          cnt' e₀ < cnt e₀ ∧
          (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
          (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
          ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
            G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
    {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (K : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (hK : ∀ w, IsCompact (K w) ∧ Q w ⊆ K w ∧ K w ⊆ h '' U) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        (∀ e, cnt' e = 1) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)}) ∧
        ∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1) := by
  classical
  have hKfin : ∀ w, {e | (Sp e ∩ K w).Nonempty}.Finite := by
    intro w
    obtain ⟨-, -, -, -, hlf, -⟩ := hpack
    have hcpt : IsCompact {y : h '' U | (y : M₂) ∈ K w} := by
      rw [Subtype.isCompact_iff]
      convert (hK w).1 using 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, (hK w).2.2 hy⟩, hy, rfl⟩
    refine (hlf.finite_nonempty_inter_compact hcpt).subset ?_
    rintro e ⟨y, hyS, hyK⟩
    exact ⟨⟨y, (hK w).2.2 hyK⟩, hyS, hyK⟩
  have hinit : Section34RemovalGood U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp
      Tp cnt G ∅ G cnt Pg :=
    ⟨hpack, fun e he => (notMem_empty e he).elim, fun _ _ => rfl, fun w => eqOn_refl _ _,
      fun w => eqOn_refl _ _⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (r := fun a b : {a : Set (Section34EdgeIndex 𝒦 𝒦') ×
      (Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) × (Section34EdgeIndex 𝒦 𝒦' → ℕ) ×
      (Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂) // Section34RemovalGood U 𝒦 𝒦' h Q ends Cp CpBd
        Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt G a.1 a.2.1 a.2.2.1 a.2.2.2} =>
      Section34RemovalLe Sp K a.1.1 a.1.2.1 b.1.1 b.1.2.1)
    (fun c hc => by
      rcases c.eq_empty_or_nonempty with hce | hce
      · exact ⟨⟨(∅, G, cnt, Pg), hinit⟩, fun a ha => by rw [hce] at ha; exact ha.elim⟩
      · obtain ⟨S, G', cnt', Pg', hgood', hub⟩ := exists_section34RemovalGood_upperBound K hKfin
          cnt G (Subtype.val '' c) (hce.image _)
          (by rintro _ ⟨a, -, rfl⟩; exact a.2)
          (by
            rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
            exact hc ha hb fun h => hab (congrArg Subtype.val h))
        exact ⟨⟨(S, G', cnt', Pg'), hgood'⟩, fun a ha => hub a.1 ⟨a, ha, rfl⟩⟩)
    (fun h₁ h₂ => section34RemovalLe_trans h₁ h₂)
  have hall : ∀ e, e ∈ m.1.1 := by
    intro e
    by_contra he
    obtain ⟨G', cnt', Pg', hgood', hle⟩ := exists_section34RemovalGood_insert hstep hprep K
      (fun w => (hK w).2.1) cnt G m.2 he
    have hback := hm ⟨(insert e m.1.1, G', cnt', Pg'), hgood'⟩ hle
    exact he (hback.1 (mem_insert e m.1.1))
  obtain ⟨hpc, hone, -, hoff, hbody⟩ := m.2
  exact ⟨m.1.2.1, m.1.2.2.1, m.1.2.2.2, hpc, fun e => hone e (hall e), hoff, hbody⟩

end DifferentialGeometry.Topology.PiecewiseLinear
