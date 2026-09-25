import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_sphere_model_of_disk_pair {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D F J : Set M} (hS : IsPLCellOn 3 S B)
    (hD : IsPLCellOn 2 D J) (hF : IsPLCellOn 2 F J)
    (hDS : D ⊆ S) (hFS : F ⊆ S) (hDF : D ∩ F = J) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (D' F' : Set (EuclideanSpace ℝ (Fin 3))),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ D' ∪ F' ⊆ P ∧
      u '' D' = D ∧ u '' F' = F ∧ IsPLSphere 2 (D' ∪ F') := by
  obtain ⟨P, r, u, hr, hu, hS, -⟩ := hS
  have hDP := hS ▸ hDS
  have hFP := hS ▸ hFS
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  obtain ⟨v, hv, hvJ⟩ := hF.exists_isPLHomeomorphOn_invFunOn hu hFP
  have hDF' : (τ '' D) ∩ (τ '' F) = q '' stdSimplexBoundary 2 := by
    rw [← hτi.image_inter hDP hFP, hDF]
    exact hqJ
  have hsub (A : Set M) (hA : A ⊆ u '' P) : τ '' A ⊆ P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hA hx
    rw [hleft hy]
    exact hy
  have hback (A : Set M) (hA : A ⊆ u '' P) : u '' (τ '' A) = A := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hA hx)).trans (image_id' A)
  exact ⟨P, u, τ '' D, τ '' F, ⟨r, hr⟩, hu, union_subset (hsub D hDP) (hsub F hFP),
    hback D hDP, hback F hFP,
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hq hv hDF' (hvJ.symm.trans hqJ)⟩

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

theorem exists_section34_matching_disk_pair
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i))
    (hDT : D ⊆ G (ends e).2 '' Bb e ∩ Tp e)
    (htrace : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i) :
    ∃ F : Set M₂, IsPLCellOn 2 F (Pg e i) ∧ F ⊆ G (ends e).1 '' Aa e ∧
      F ∩ D = Pg e i ∧ F ∪ D ⊆ Tp e ∧
      ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
        (F' D' : Set (EuclideanSpace ℝ (Fin 3))),
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ F' ∪ D' ⊆ P ∧
        u '' F' = F ∧ u '' D' = D ∧ IsPLSphere 2 (F' ∪ D') := by
  obtain ⟨F, hF, hFA⟩ := (section34_piercing_disk_annuli_iff hprep hpack e hi).mpr
    ⟨D, hD, hDT.trans inter_subset_left⟩
  obtain ⟨-, hCc, -, -, -, -, -, -, -, -, -, htor, hSnCc, -, hAa, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  have hAT : G (ends e).1 '' Aa e ⊆ Tp e := by
    rw [(htube e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  have hAB : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hFD : F ∩ D = Pg e i := by
    apply Subset.antisymm
    · exact fun x hx => htrace.subset ⟨hx.2, hAB (hFA hx.1)⟩
    · exact fun x hx => ⟨hF.boundary_subset hx, hD.boundary_subset hx⟩
  have hTCc : Tp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
    rw [(htube e).2]
    exact image_mono (((htor e).1.trans interior_subset).trans (hSnCc e _ (Or.inl rfl)))
  exact ⟨F, hF, hFA, hFD, union_subset (hFA.trans hAT) (hDT.trans inter_subset_right),
    ((hCc _).image (hG _)).exists_sphere_model_of_disk_pair hF hD
      ((hFA.trans hAT).trans hTCc) ((hDT.trans inter_subset_right).trans hTCc) hFD⟩

end DifferentialGeometry.Topology.PiecewiseLinear
