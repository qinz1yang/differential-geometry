import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidTorusFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_filling_of_disk_pair_in_torus {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKP : K.space ⊆ P)
    (hT : IsTopologicalSolidTorus K.space) {D F J : Set M}
    (hD : IsPLCellOn 2 D J) (hF : IsPLCellOn 2 F J)
    (hDT : D ⊆ u '' K.space) (hFT : F ⊆ u '' K.space) (hDF : D ∩ F = J) :
    ∃ B : Set M, IsPLCellOn 3 B (D ∪ F) ∧ B ⊆ u '' K.space := by
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hDP := hDT.trans (image_mono hKP)
  have hFP := hFT.trans (image_mono hKP)
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  obtain ⟨v, hv, hvJ⟩ := hF.exists_isPLHomeomorphOn_invFunOn hu hFP
  have hDF' : (τ '' D) ∩ (τ '' F) = q '' stdSimplexBoundary 2 := by
    rw [← hτi.image_inter hDP hFP, hDF]
    exact hqJ
  have hsub (A : Set M) (hA : A ⊆ u '' K.space) : τ '' A ⊆ K.space := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hA hx
    rw [hleft (hKP hy)]
    exact hy
  have hback (A : Set M) (hA : A ⊆ u '' P) : u '' (τ '' A) = A := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hA hx)).trans (image_id' A)
  have hS := isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hq hv hDF' (hvJ.symm.trans hqJ)
  obtain ⟨B, hB, hfront, hBT⟩ := hT.exists_isPLBall_subset_of_sphere hK hS
    (union_subset (hsub D hDT) (hsub F hFT))
  have huB : IsPLHomeomorphInto 3 u B :=
    (hu.isPLOn.mono_of_isPolyhedron hB.isPolyhedron (hBT.trans hKP)).isPLHomeomorphInto_model
      hB.isPolyhedron.isCompact (hu.injOn.mono (hBT.trans hKP))
  obtain ⟨r, hr⟩ := hB
  have hcell := (isPLCellOn_id_of_isPLBall hr).image huB
  rw [hr.image_stdSimplexBoundary_eq_frontier, hfront, image_union,
    hback D hDP, hback F hFP] at hcell
  exact ⟨u '' B, hcell, image_mono hBT⟩

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

theorem exists_section34_filling_of_disk_pair
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {D F J : Set M₂}
    (hD : IsPLCellOn 2 D J) (hF : IsPLCellOn 2 F J)
    (hDT : D ⊆ Tp e) (hFT : F ⊆ Tp e) (hDF : D ∩ F = J) :
    ∃ B : Set M₂, IsPLCellOn 3 B (D ∪ F) ∧ B ⊆ Tp e := by
  obtain ⟨P, u, _, _, _, hu, hCc, hN, -⟩ := exists_section34_inner_tube_bicollar hprep e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  have hNP : Tn e ⊆ u '' P := by
    rw [← hCc]
    exact ((htor e).1.trans interior_subset).trans (hSnCc e _ (Or.inl rfl))
  obtain ⟨K, hKfin, hKspace, hK⟩ := hu.exists_simplicialComplex_invFunOn_image hN hNP
  let _ : Finite K.faces := hKfin.to_subtype
  have hleft := hu.injOn.leftInvOn_invFunOn
  have hright := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hKP : K.space ⊆ P := by
    rw [hKspace]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hNP hx
    rw [hleft hy]
    exact hy
  have hKtor : IsTopologicalSolidTorus K.space := by
    rw [hKspace]
    apply ((htor e).2.2.1).image_of_continuousOn_injOn
      ((hu.isPLOn_inverse hleft).continuousOn.mono hNP)
    intro x hx y hy hxy
    rw [← hright (hNP hx), ← hright (hNP hy), hxy]
  have hback : u '' K.space = Tn e := by
    rw [hKspace, image_image]
    exact (image_congr fun x hx => hright (hNP hx)).trans (image_id' _)
  let v := G (ends e).1 ∘ u
  have hv : IsPLHomeomorphInto 3 v P := hu.comp_of_image_eq (hCc ▸ hG (ends e).1)
  have hvT : v '' K.space = Tp e := by
    dsimp only [v]
    rw [image_comp, hback, ← (htube e).2]
  obtain ⟨B, hB, hBT⟩ := hv.exists_filling_of_disk_pair_in_torus K hK hKP hKtor hD hF
    (hvT.symm ▸ hDT) (hvT.symm ▸ hFT) hDF
  exact ⟨B, hB, hvT ▸ hBT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
