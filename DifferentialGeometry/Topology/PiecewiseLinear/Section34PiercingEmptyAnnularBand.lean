import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingAnnularBand
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleAdjacency

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_empty_annular_band_of_essential_family {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (C : Set (Set M)) (hC : C.Finite) (hcard : 1 < C.ncard)
    (hCsph : ∀ J ∈ C, IsPolyhedralSphere (n := 3) 1 J) (hCA : ∀ J ∈ C, J ⊆ A)
    (hCend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁)) (hCdisj : C.PairwiseDisjoint id)
    (hCess : ∀ J ∈ C, ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A) :
    ∃ J ∈ C, ∃ L ∈ C, J ≠ L ∧
      ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
        (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L ∧
      Disjoint ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (⋃₀ C) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ image_mono hfront)
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτc : ContinuousOn τ (u '' P) := (hu.isPLOn_inverse hleft).continuousOn
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hA' := hA.image_of_continuousOn_injOn (hτc.mono hAP) (hτi.mono hAP)
  have hA'S : τ '' A ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hAB hx
    rw [hleft (hfront hz)]
    exact hz
  have hback (X : Set M) (hXA : X ⊆ A) : u '' (τ '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hAP (hXA hx))).trans (image_id' X)
  have hdisj {X Y : Set M} (hXA : X ⊆ A) (hYA : Y ⊆ A) (hXY : Disjoint X Y) :
      Disjoint (τ '' X) (τ '' Y) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq := hτi (hAP (hXA hx)) (hAP (hYA hy)) hxy.symm
    exact disjoint_left.mp hXY hx (heq ▸ hy)
  have hess {X : Set M} (hXA : X ⊆ A)
      (hXess : ¬ ∃ D : Set M, IsPLCellOn 2 D X ∧ D ⊆ A) :
      ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
        (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
          q '' stdSimplexBoundary 2 = τ '' X := by
    rintro ⟨D, q, hq, hDA, hqb⟩
    have hDP := (hDA.trans hA'S).trans hfront
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly hDP).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono hDP)
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rw [hqb, hback X hXA] at hc
    exact hXess ⟨u '' D, hc, hback A Subset.rfl ▸ image_mono hDA⟩
  let C' := (fun J : Set M => τ '' J) '' C
  have himg : InjOn (fun J : Set M => τ '' J) C := by
    intro J hJ L hL hJL
    change τ '' J = τ '' L at hJL
    rw [← hback J (hCA J hJ), ← hback L (hCA L hL), hJL]
  have hcard' : 1 < C'.ncard := by
    dsimp only [C']
    rw [himg.ncard_image]
    exact hcard
  have hC'sph : ∀ J ∈ C', IsPLSphere 1 J := by
    rintro _ ⟨J, hJ, rfl⟩
    exact hu.isPLSphere_invFunOn_image (hCsph J hJ) ((hCA J hJ).trans hAP)
  have hC'A : ∀ J ∈ C', J ⊆ τ '' A := by
    rintro _ ⟨J, hJ, rfl⟩
    exact image_mono (hCA J hJ)
  have hendA := union_subset hA.first_subset hA.second_subset
  have hC'end : ∀ J ∈ C', Disjoint J (τ '' A₀ ∪ τ '' A₁) := by
    rintro _ ⟨J, hJ, rfl⟩
    rw [← image_union]
    exact hdisj (hCA J hJ) hendA (hCend J hJ)
  have hC'disj : C'.PairwiseDisjoint id := by
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hJL
    exact hdisj (hCA J hJ) (hCA L hL)
      (hCdisj hJ hL (fun h => hJL (congrArg (fun K => τ '' K) h)))
  have hC'ess : ∀ J ∈ C', ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
        q '' stdSimplexBoundary 2 = J := by
    rintro _ ⟨J, hJ, rfl⟩
    exact hess (hCA J hJ) (hCess J hJ)
  obtain ⟨J', ⟨J, hJ, rfl⟩, L', ⟨L, hL, rfl⟩, hJL, φ, hφ, hφA, hφ₀, hφ₁, hempty⟩ :=
    hP.isPLSphere_frontier.exists_empty_annular_band_of_essential_family hA' hA'S C'
      (hC.image _) hcard' hC'sph hC'A hC'end hC'disj hC'ess
  have hbandP := (hφA.trans hA'S).trans hfront
  refine ⟨J, hJ, L, hL, fun h => hJL (congrArg (fun K => τ '' K) h),
    P, u, φ, hP, hu, hφ, hbandP, ?_, ?_, ?_, ?_⟩
  · rw [image_comp]
    exact hback A Subset.rfl ▸ image_mono hφA
  · rw [image_comp, hφ₀, hback J (hCA J hJ)]
  · rw [image_comp, hφ₁, hback L (hCA L hL)]
  · refine disjoint_left.mpr ?_
    rintro y ⟨z, hz, rfl⟩ ⟨K, hK, hzK⟩
    have hzP : φ z ∈ P := hbandP ⟨z, ⟨hz.1, Ioo_subset_Icc_self hz.2⟩, rfl⟩
    exact disjoint_left.mp hempty ⟨z, hz, rfl⟩
      ⟨τ '' K, ⟨K, hK, rfl⟩, ⟨u (φ z), hzK, hleft hzP⟩⟩

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

theorem exists_section34_piercing_empty_annular_band
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hlt : 1 < cnt e)
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ i < cnt e, ∃ j < cnt e, i ≠ j ∧
      ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
        (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j ∧
      Disjoint ((u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
        (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e) := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, hcount, hPg, hdisj, -⟩ := hpack
  have hBCp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hends (k : ℕ) (hk : k < cnt e) :
      Disjoint (Pg e k) (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e k hk).2 hy).2
    have hzCp := hBCp ((union_subset (hBb e).2.first_subset (hBb e).2.second_subset) hz)
    have heq := (hGcp (ends e).2).injOn (hBCp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hsub (k : ℕ) (hk : k < cnt e) : Pg e k ⊆ G (ends e).2 '' Bb e := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := ((hPg e k hk).2 hx).2
    exact ⟨z, hz.1, hzx⟩
  let C := range (fun i : Fin (cnt e) => Pg e i.val)
  have hne (i : Fin (cnt e)) : (Pg e i.val).Nonempty := by
    obtain ⟨T, hT⟩ := (hPg e i.val i.isLt).1
    exact T.piece.bijOn.image_eq ▸ hT.nonempty.image T.piece.map
  have hinj : Function.Injective (fun i : Fin (cnt e) => Pg e i.val) := by
    intro i j hij
    change Pg e i.val = Pg e j.val at hij
    apply Fin.ext
    by_contra hneij
    obtain ⟨x, hx⟩ := hne i
    exact disjoint_left.mp (hdisj e i.val i.isLt j.val j.isLt hneij)
      hx (hij ▸ hx)
  have hcard : 1 < C.ncard := by
    dsimp only [C]
    rw [Set.ncard_range_of_injective hinj]
    simpa only [Nat.card_fin] using hlt
  have hCsph : ∀ J ∈ C, IsPolyhedralSphere (n := 3) 1 J := by
    rintro _ ⟨i, rfl⟩
    exact (hPg e i.val i.isLt).1
  have hCA : ∀ J ∈ C, J ⊆ G (ends e).2 '' Bb e := by
    rintro _ ⟨i, rfl⟩
    exact hsub i.val i.isLt
  have hCend : ∀ J ∈ C,
      Disjoint J (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rintro _ ⟨i, rfl⟩
    exact hends i.val i.isLt
  have hCdisj : C.PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hdisj e i.val i.isLt j.val j.isLt
      (fun h => hij (congrArg (Pg e) h))
  have hCess : ∀ J ∈ C, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D J ∧ D ⊆ G (ends e).2 '' Bb e := by
    rintro _ ⟨i, rfl⟩
    exact hess i.val i.isLt
  obtain ⟨J, ⟨i, rfl⟩, L, ⟨j, rfl⟩, hij, P, u, φ, hP, hu, hφ, hφP,
    hφA, hφ₀, hφ₁, hempty⟩ :=
    ((hCp (ends e).2).image (hGcp (ends e).2)).exists_empty_annular_band_of_essential_family
      hann (image_mono (hBb e).1) C (finite_range _) hcard hCsph hCA hCend hCdisj hCess
  refine ⟨i.val, i.isLt, j.val, j.isLt, fun h => hij (congrArg (Pg e) h),
    P, u, φ, hP, hu, hφ, hφP, hφA, hφ₀, hφ₁, ?_⟩
  have htrace : ⋃₀ C = G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e := by
    rw [(hcount e).2]
    ext x
    constructor
    · rintro ⟨J, ⟨k, rfl⟩, hx⟩
      exact mem_iUnion₂.mpr ⟨k.val, k.isLt, hx⟩
    · intro hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      exact ⟨Pg e k, ⟨⟨k, hk⟩, rfl⟩, hxk⟩
  rwa [htrace] at hempty

end DifferentialGeometry.Topology.PiecewiseLinear
