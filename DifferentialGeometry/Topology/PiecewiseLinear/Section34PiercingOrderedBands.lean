import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingCircleOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedAnnularBandsTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_lateral_bands_of_ordered_caps {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ T : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) {n : ℕ} {J D₀ D₁ : Fin n → Set M}
    (hcap : ∀ i, IsPLCellOn 2 (D₀ i) (J i) ∧ IsPLCellOn 2 (D₁ i) (J i) ∧
      D₀ i ∪ D₁ i = B ∧ D₀ i ∩ D₁ i = J i ∧ A₀ ⊆ D₀ i ∧ A₁ ⊆ D₁ i)
    (hdis : ∀ i j, i < j → Disjoint (D₀ i) (D₁ j))
    (hleft : ∀ i j, J i ⊆ D₀ j ↔ i ≤ j)
    (hright : ∀ i j, J i ⊆ D₁ j ↔ j ≤ i)
    (hJA : ∀ i, J i ⊆ A) (hJend : ∀ i, Disjoint (J i) (A₀ ∪ A₁))
    (htrace : A ∩ T ⊆ ⋃ i, J i) :
    ∀ i j, i < j →
      ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
        (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = S ∧
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = J i ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = J j ∧
      (∀ k, J k ⊆ (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
        i ≤ k ∧ k ≤ j) ∧
      (j.val = i.val + 1 →
        Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) T) := by
  intro i j hij
  obtain ⟨P, u, f, hP, hu, himageS, hf, hfP, hfimage, hf₀, hf₁⟩ :=
    hS.exists_lateral_annulus_eq_inter_of_disk_caps
      (hcap i).1 (hcap j).2.1 (hcap i).2.2.1 (hcap i).2.2.2.1
      (hcap j).2.2.1 (hcap j).2.2.2.1 (hdis i j hij)
  have hmaps : MapsTo f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hfP ⟨x, hx, rfl⟩
  have hcont : ContinuousOn (u ∘ f) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hmaps
  have hinj : InjOn (u ∘ f) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    hu.injOn.comp hf.bijOn.injOn hmaps
  have hsubB : D₁ i ∩ D₀ j ⊆ B :=
    inter_subset_left.trans ((hcap i).2.2.1 ▸ subset_union_right)
  have hsubA : D₁ i ∩ D₀ j ⊆ A := by
    have hconn := ((isConnected_stdSimplexBoundary 0).prod
      (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1))).image (u ∘ f) hcont
    rw [hfimage] at hconn
    apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAB hsubB
      hconn.isPreconnected
    · have hne : (J i).Nonempty := by
        rw [← hf₀]
        have hprod := (isConnected_stdSimplexBoundary 0).nonempty.prod
          (singleton_nonempty (0 : ℝ))
        exact hprod.image (u ∘ f)
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, ⟨((hcap i).2.2.2.1.superset hx).2, (hleft i j).mpr hij.le hx⟩,
        hJA i hx⟩
    · refine disjoint_left.mpr fun x hx hxrim => ?_
      rcases hxrim with hx₀ | hx₁
      · exact disjoint_left.mp (hJend i)
          ((hcap i).2.2.2.1.subset ⟨(hcap i).2.2.2.2.1 hx₀, hx.1⟩) (Or.inl hx₀)
      · exact disjoint_left.mp (hJend j)
          ((hcap j).2.2.2.1.subset ⟨hx.2, (hcap j).2.2.2.2.2 hx₁⟩) (Or.inr hx₁)
  refine ⟨P, u, f, hP, hu, himageS, hf, hfP, hfimage, hfimage ▸ hsubA,
    hf₀, hf₁, ?_, ?_⟩
  · intro k
    rw [hfimage]
    exact subset_inter_of_ordered_caps_iff hleft hright i j k
  · intro hadj
    have hempty := disjoint_open_lateral_trace_of_adjacent_caps
      (fun k => (hcap k).2.2.2.1) hdis hadj hinj hfimage hf₀ hf₁
    refine disjoint_left.mpr fun x hx hxT => disjoint_left.mp hempty hx ?_
    have hxclosed := image_mono (prod_mono_right Ioo_subset_Icc_self) hx
    exact htrace ⟨hsubA (hfimage.subset hxclosed), hxT⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

private theorem piercing_sphere_trace_subset
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (σ : Fin (cnt e) ≃ Fin (cnt e)) :
    G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
      ⋃ i, Pg e (σ i).val := by
  obtain ⟨-, -, -, -, -, -, hcross, -, -, -, -, -, -, -, -, -, hcount, -⟩ := hpack
  intro x hx
  have hx' := (hcross e hx).1
  have hxA := image_mono sdiff_subset hx'.1
  have hxB := image_mono sdiff_subset hx'.2
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp ((hcount e).2.subset ⟨hxA, hxB⟩)
  refine mem_iUnion.mpr ⟨σ.symm ⟨k, hk⟩, ?_⟩
  simpa only [σ.apply_symm_apply] using hxk

theorem exists_section34_piercing_first_ordered_bands
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (σ : Fin (cnt e) ≃ Fin (cnt e)) (D₀ D₁ : Fin (cnt e) → Set M₂),
      (∀ i, IsPLCellOn 2 (D₀ i) (Pg e (σ i).val) ∧
        IsPLCellOn 2 (D₁ i) (Pg e (σ i).val) ∧
        D₀ i ∪ D₁ i = G (ends e).1 '' CpBd (ends e).1 ∧
        D₀ i ∩ D₁ i = Pg e (σ i).val ∧
        G (ends e).1 '' Ab₀ e ⊆ D₀ i ∧ G (ends e).1 '' Ab₁ e ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₁ j ↔ j ≤ i) ∧
      ∀ i j, i < j →
        ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
          (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cp (ends e).1 ∧
        IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).1 '' Aa e ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ i).val ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ j).val ∧
        (∀ k, Pg e (σ k).val ⊆ (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
          i ≤ k ∧ k ≤ j) ∧
        (j.val = i.val + 1 →
          Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
            (G (ends e).2 '' CpBd (ends e).2)) := by
  obtain ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright⟩ :=
    exists_section34_piercing_first_circle_order hprep hpack e hess
  have hann := (section34_piercing_annuli hprep hpack e).1
  have htrace := piercing_sphere_trace_subset hpack e σ
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAnn, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hACp := ((hAnn e).1 ▸ inter_subset_left).trans (hCp (ends e).1).boundary_subset
  have hends (i : Fin (cnt e)) : Disjoint (Pg e (σ i).val)
      (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e (σ i).val (σ i).isLt).2 hy).1
    have hzCp := hACp ((union_subset (hAnn e).2.first_subset (hAnn e).2.second_subset) hz)
    have heq := (hGcp (ends e).1).injOn (hACp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  refine ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright, ?_⟩
  have hcell := (hCp (ends e).1).image (hGcp (ends e).1)
  have hAB := image_mono ((hAnn e).1 ▸ inter_subset_left) (f := G (ends e).1)
  apply hcell.exists_lateral_bands_of_ordered_caps hann
    hAB hcap hdis hleft hright ?_ hends
    ((inter_subset_inter_left _ hAB).trans htrace)
  intro i x hx
  exact image_mono sdiff_subset ((hPg e (σ i).val (σ i).isLt).2 hx).1

theorem exists_section34_piercing_second_ordered_bands
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (σ : Fin (cnt e) ≃ Fin (cnt e)) (D₀ D₁ : Fin (cnt e) → Set M₂),
      (∀ i, IsPLCellOn 2 (D₀ i) (Pg e (σ i).val) ∧
        IsPLCellOn 2 (D₁ i) (Pg e (σ i).val) ∧
        D₀ i ∪ D₁ i = G (ends e).2 '' CpBd (ends e).2 ∧
        D₀ i ∩ D₁ i = Pg e (σ i).val ∧
        G (ends e).2 '' Bb₀ e ⊆ D₀ i ∧ G (ends e).2 '' Bb₁ e ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₁ j ↔ j ≤ i) ∧
      ∀ i j, i < j →
        ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
          (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).2 '' Cp (ends e).2 ∧
        IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ i).val ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ j).val ∧
        (∀ k, Pg e (σ k).val ⊆ (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
          i ≤ k ∧ k ≤ j) ∧
        (j.val = i.val + 1 →
          Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
            (G (ends e).1 '' CpBd (ends e).1)) := by
  obtain ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright⟩ :=
    exists_section34_piercing_second_circle_order hprep hpack e hess
  have hann := (section34_piercing_annuli hprep hpack e).2
  have htrace := piercing_sphere_trace_subset hpack e σ
  rw [inter_comm] at htrace
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hAnn, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hACp := (hAnn e).1.trans (hCp (ends e).2).boundary_subset
  have hends (i : Fin (cnt e)) : Disjoint (Pg e (σ i).val)
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e (σ i).val (σ i).isLt).2 hy).2
    have hzCp := hACp ((union_subset (hAnn e).2.first_subset (hAnn e).2.second_subset) hz)
    have heq := (hGcp (ends e).2).injOn (hACp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  refine ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright, ?_⟩
  have hcell := (hCp (ends e).2).image (hGcp (ends e).2)
  have hAB := image_mono (hAnn e).1 (f := G (ends e).2)
  apply hcell.exists_lateral_bands_of_ordered_caps hann
    hAB hcap hdis hleft hright ?_ hends
    ((inter_subset_inter_left _ hAB).trans htrace)
  intro i x hx
  exact image_mono sdiff_subset ((hPg e (σ i).val (σ i).isLt).2 hx).2

end DifferentialGeometry.Topology.PiecewiseLinear
