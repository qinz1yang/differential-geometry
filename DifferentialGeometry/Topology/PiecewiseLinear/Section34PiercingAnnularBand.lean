import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusCircleDichotomy
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCirclePair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_annular_band_of_essential_pair {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J L : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hL : IsPolyhedralSphere (n := 3) 1 L) (hJA : J ⊆ A) (hLA : L ⊆ A)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A)
    (hLess : ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L := by
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
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
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
  have hendA := union_subset hA.first_subset hA.second_subset
  obtain ⟨φ, hφ, hφA, hφ₀, hφ₁⟩ :=
    hP.isPLSphere_frontier.exists_annular_band_of_essential_pair hA' hA'S
      (hu.isPLSphere_invFunOn_image hJ (hJA.trans hAP))
      (hu.isPLSphere_invFunOn_image hL (hLA.trans hAP))
      (image_mono hJA) (image_mono hLA) (hdisj hJA hLA hJL)
      (by rw [← image_union]; exact hdisj hJA hendA hJend)
      (by rw [← image_union]; exact hdisj hLA hendA hLend)
      (hess hJA hJess) (hess hLA hLess)
  refine ⟨P, u, φ, hP, hu, hφ, (hφA.trans hA'S).trans hfront, ?_, ?_, ?_⟩
  · rw [image_comp]
    exact hback A Subset.rfl ▸ image_mono hφA
  · rw [image_comp, hφ₀, hback J hJA]
  · rw [image_comp, hφ₁, hback L hLA]

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

theorem exists_section34_piercing_annular_band
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, hdisj, -⟩ := hpack
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
  exact ((hCp (ends e).2).image (hGcp (ends e).2)).exists_annular_band_of_essential_pair
    hann (image_mono (hBb e).1) (hPg e i hi).1 (hPg e j hj).1 (hsub i hi) (hsub j hj)
    (hdisj e i hi j hj hij) (hends i hi) (hends j hj) hiess hjess

end DifferentialGeometry.Topology.PiecewiseLinear
