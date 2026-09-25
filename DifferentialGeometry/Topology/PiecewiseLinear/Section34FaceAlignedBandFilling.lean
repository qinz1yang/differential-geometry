import DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceAlignedFillingCylinder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def Section34FaceAlignedBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (Cc Cp As Bs T D F J₀ J₁ : Set M) : Prop :=
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a : Fin 2 → ℝ × ℝ)
      (A₀ A₁ : Set (ℝ × ℝ)) (δ₀ δ₁ : ℝ → ℝ × ℝ),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCombinatorialSolidTorus R.space ∧
      IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)) ∧
      frontier R.space = g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' frontier R.space = D ∪ F ∧ u '' R.space ⊆ T ∧
      As ∩ u '' R.space = F ∧ Bs ∩ u '' R.space = D ∧
      u '' R.space ∩ frontier T = F ∩ frontier T ∧
      (u '' R.space ⊆ Cp ∨ u '' R.space ∩ Cp = F) ∧
      (∀ k, a k ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) ∧
      Function.Injective a ∧
      (u ∘ g) '' ({a 0} ×ˢ Icc (0 : ℝ) 1) = J₀ ∧
      (u ∘ g) '' ({a 1} ×ˢ Icc (0 : ℝ) 1) = J₁ ∧
      IsPLHomeomorphOn δ₀ (Icc 0 1) A₀ ∧ IsPLHomeomorphOn δ₁ (Icc 0 1) A₁ ∧
      δ₀ 0 = a 0 ∧ δ₀ 1 = a 1 ∧ δ₁ 0 = a 0 ∧ δ₁ 1 = a 1 ∧
      A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      A₀ ∩ A₁ = {a 0, a 1} ∧
      (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D

theorem Section34FaceAlignedBandFilling.toAlignedBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp As Bs T D F J₀ J₁ : Set M}
    (h : Section34FaceAlignedBandFilling Cc Cp As Bs T D F J₀ J₁) :
    Section34AlignedBandFilling Cc Cp As Bs T D F J₀ J₁ := by
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, -⟩ := h
  exact ⟨P, u, R, g, a, hP, hu, hcell, hRfin, hR, hRP, hsolid, hg, hends, hside,
    hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj, hzero, hone⟩

theorem Section34AlignedBandFilling.toFaceAlignedBandFilling {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp As Bs T D F J₀ J₁ : Set M}
    (h : Section34AlignedBandFilling Cc Cp As Bs T D F J₀ J₁)
    (hF : IsAnnulusOn F J₀ J₁) (hD : IsClosed D) (hDF : D ∩ F = J₀ ∪ J₁) :
    Section34FaceAlignedBandFilling Cc Cp As Bs T D F J₀ J₁ := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  obtain ⟨P, u, R, g, a, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone⟩ := h
  have hfrontR : frontier R.space ⊆ R.space := hsolid.isPolyhedron.isClosed.frontier_subset
  obtain ⟨hchart⟩ := hsolid.isPLTorus_frontier.nonempty_chartedSpace_image
    (hu.continuousOn.mono (hfrontR.trans hRP)) (hu.injOn.mono (hfrontR.trans hRP))
  let _ := hchart
  have hside' : (u ∘ g) ''
      (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) =
      u '' frontier R.space := by rw [image_comp, ← hside]
  have hcircle : IsPLSphere 1 (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
    obtain ⟨B, hBfin, hBspace⟩ := isPLBall_unit_square.isPolyhedron.exists_simplicialComplex
    let _ : Finite B.faces := hBfin.to_subtype
    have hB : IsPLBall 2 B.space := hBspace.symm ▸ isPLBall_unit_square
    rw [← hBspace, frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) B hB.isCombinatorialManifoldWithBoundary]
    exact isPLSphere_boundaryComplex_space_of_isPLBall B hB
  have hxy : a 0 ≠ a 1 := fun heq => (by decide : (0 : Fin 2) ≠ 1) (hinj heq)
  obtain ⟨A₀, A₁, δ₀, δ₁, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter,
      hface₀, hface₁⟩ :=
    hg.exists_base_arcs_of_annulus_pair hends hcircle
      isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
      (hu.continuousOn.mono hRP) (hu.injOn.mono hRP) hside' (ha 0) (ha 1) hxy
      (by simpa only [hzero, hone] using hF) hD hfront.symm
      (by simpa only [hzero, hone] using hDF)
  exact ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁⟩

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

theorem section34_face_aligned_band_filling_of_solid
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hD : IsClosed D) (hDF : D ∩ F = Pg e i ∪ Pg e j)
    (hfill : Section34SolidBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F) :
    Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j) := by
  have haligned := section34_aligned_band_filling_of_solid hprep hpack e hi hj hij
    hiess hjess hF hfill
  exact haligned.toFaceAlignedBandFilling hF hD hDF

end DifferentialGeometry.Topology.PiecewiseLinear
