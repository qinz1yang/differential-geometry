import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingConfiguration
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_disk_in_annulus_or_separating_ends {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) :
    (∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A) ∨
    ∃ D₀ D₁ : Set M, D₀ ∪ D₁ = B ∧ D₀ ∩ D₁ = J ∧
      IsPLCellOn 2 D₀ J ∧ IsPLCellOn 2 D₁ J ∧ A₀ ⊆ D₀ ∧ A₁ ⊆ D₁ := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ image_mono hfront)
  have hJP : J ⊆ u '' P := hJA.trans hAP
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
  have hJ' : IsPLSphere 1 (τ '' J) := hu.isPLSphere_invFunOn_image hJ hJP
  have hends' : Disjoint (τ '' J) ((τ '' A₀) ∪ (τ '' A₁)) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyP := hAP ((union_subset hA.first_subset hA.second_subset) hy)
    have heq := hτi (hJP hx) hyP hxy.symm
    exact disjoint_left.mp hends hx (heq ▸ hy)
  have hback (X : Set M) (hXP : X ⊆ u '' P) : u '' (τ '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hXP hx)).trans (image_id' X)
  have hcell (D : Set (EuclideanSpace ℝ (Fin 3))) (q : (Fin 3 → ℝ) →
      EuclideanSpace ℝ (Fin 3)) (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D)
      (hDP : D ⊆ P) (hqb : q '' stdSimplexBoundary 2 = τ '' J) :
      IsPLCellOn 2 (u '' D) J := by
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly hDP).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono hDP)
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rwa [hqb, hback J hJP] at hc
  rcases hP.isPLSphere_frontier.exists_disk_in_annulus_or_separating_ends hA' hA'S hJ'
      (image_mono hJA) hends' with ⟨D, q, hq, hDA, hqb⟩ |
        ⟨D₀, D₁, q₀, q₁, hU, hI, hq₀, hq₁, hb₀, hb₁, h₀, h₁⟩
  · exact Or.inl ⟨u '' D, hcell D q hq ((hDA.trans hA'S).trans hfront) hqb,
      hback A hAP ▸ image_mono hDA⟩
  · have hD₀ : D₀ ⊆ P := (hU ▸ subset_union_left).trans hfront
    have hD₁ : D₁ ⊆ P := (hU ▸ subset_union_right).trans hfront
    refine Or.inr ⟨u '' D₀, u '' D₁, ?_, ?_, hcell D₀ q₀ hq₀ hD₀ hb₀,
      hcell D₁ q₁ hq₁ hD₁ hb₁, ?_, ?_⟩
    · rw [← image_union, hU, ← hB]
    · rw [← hu.injOn.image_inter hD₀ hD₁, hI, hback J hJP]
    · exact hback A₀ (hA.first_subset.trans hAP) ▸ image_mono h₀
    · exact hback A₁ (hA.second_subset.trans hAP) ▸ image_mono h₁

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

theorem section34_piercing_circle_disk_or_separating_ends
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e) :
    (∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) ∨
    ∃ D₀ D₁ : Set M₂, D₀ ∪ D₁ = G (ends e).2 '' CpBd (ends e).2 ∧
      D₀ ∩ D₁ = Pg e i ∧ IsPLCellOn 2 D₀ (Pg e i) ∧ IsPLCellOn 2 D₁ (Pg e i) ∧
      G (ends e).2 '' Bb₀ e ⊆ D₀ ∧ G (ends e).2 '' Bb₁ e ⊆ D₁ := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hBCp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hends : Disjoint (Pg e i) (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e i hi).2 hy).2
    have hzCp := hBCp ((union_subset (hBb e).2.first_subset (hBb e).2.second_subset) hz)
    have heq := (hGcp (ends e).2).injOn (hBCp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  exact ((hCp (ends e).2).image (hGcp (ends e).2)).exists_disk_in_annulus_or_separating_ends
    hann (image_mono (hBb e).1) (hPg e i hi).1
    (fun x hx => by
      obtain ⟨z, hz, hzx⟩ := ((hPg e i hi).2 hx).2
      exact ⟨z, hz.1, hzx⟩) hends

end DifferentialGeometry.Topology.PiecewiseLinear
