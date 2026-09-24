import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceAlignedBandFilling
import Mathlib.Topology.Separation.Regular

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.exists_open_isolation_of_isClosed
    {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M]
    {S A A₀ A₁ B K Ω : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S) (hB : IsClosed B)
    (hdis : Disjoint (A \ (A₀ ∪ A₁)) B) (hK : IsClosed K)
    (hKA : K ⊆ A \ (A₀ ∪ A₁)) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ O : Set M, IsOpen O ∧ K ⊆ O ∧ closure O ⊆ Ω ∧
      closure O ∩ S ⊆ A \ (A₀ ∪ A₁) ∧ Disjoint (closure O) B := by
  let W := Ω \ ((closure (S \ A) ∪ B) ∪ (A₀ ∪ A₁))
  have hW : IsOpen W := hΩ.sdiff ((isClosed_closure.union hB).union
    (hA.ends_isCompact.1.union hA.ends_isCompact.2).isClosed)
  have hKW : K ⊆ W := by
    intro x hx
    refine ⟨hKΩ hx, ?_⟩
    rintro ((hxcl | hxB) | hxend)
    · have hn := hA.mem_nhdsWithin_of_not_mem_ends hAS (hKA hx).1 (hKA hx).2
      obtain ⟨V, hV, hVS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hn
      obtain ⟨y, hyV, hyS, hyA⟩ := mem_closure_iff_nhds.mp hxcl V hV
      exact hyA (hVS ⟨hyV, hyS⟩)
    · exact disjoint_left.mp hdis (hKA hx) hxB
    · exact (hKA hx).2 hxend
  obtain ⟨O, hO, hKO, hOW⟩ := normal_exists_closure_subset hK hW hKW
  refine ⟨O, hO, hKO, hOW.trans sdiff_subset, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, fun hend => (hOW hx.1).2 (Or.inr hend)⟩
    by_contra hxA
    exact (hOW hx.1).2 (Or.inl (Or.inl (subset_closure ⟨hx.2, hxA⟩)))
  · exact disjoint_left.mpr fun x hx hxB => (hOW hx).2 (Or.inl (Or.inr hxB))

theorem Section34FaceAlignedBandFilling.face_annuli_and_intersection
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp As Bs T D F J₀ J₁ : Set M}
    (h : Section34FaceAlignedBandFilling Cc Cp As Bs T D F J₀ J₁) :
    IsAnnulusOn F J₀ J₁ ∧ IsAnnulusOn D J₀ J₁ ∧ D ∩ F = J₀ ∪ J₁ := by
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, -, hu, -, -, -, hRP, -, hg, hends,
    -, -, -, -, -, -, -, -, -,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁⟩ := h
  have hA₀ : A₀ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hcover ▸ subset_union_left).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hA₁ : A₁ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    (hcover ▸ subset_union_right).trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hsub {A : Set (ℝ × ℝ)} (hA : A ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
      g '' (A ×ˢ Icc (0 : ℝ) 1) ⊆ P :=
    ((image_mono (prod_mono_left hA)).trans hg.image_eq.subset).trans hRP
  have hF := (hg.isAnnulusOn_base_arc hends hδ₀ hA₀).image_of_continuousOn_injOn
    (hu.continuousOn.mono (hsub hA₀)) (hu.injOn.mono (hsub hA₀))
  have hD := (hg.isAnnulusOn_base_arc hends hδ₁ hA₁).image_of_continuousOn_injOn
    (hu.continuousOn.mono (hsub hA₁)) (hu.injOn.mono (hsub hA₁))
  simp only [← image_comp, hface₀, hδ₀₀, hδ₀₁, hzero, hone] at hF
  simp only [← image_comp, hface₁, hδ₁₀, hδ₁₁, hzero, hone] at hD
  refine ⟨hF, hD, ?_⟩
  rw [← hface₁, ← hface₀, image_comp, image_comp,
    ← hu.injOn.image_inter (hsub hA₁) (hsub hA₀),
    hg.inter_images_base_regions hends hA₁ hA₀, inter_comm A₁ A₀, hinter,
    ← singleton_union, union_prod, image_union, image_union]
  simp only [← image_comp, hzero, hone]

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

theorem exists_section34_filling_face_isolation
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i j : ℕ} {D F : Set M₂}
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j))
    {K₀ K₁ Ω : Set M₂} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hKF : K₀ ⊆ F \ (Pg e i ∪ Pg e j)) (hKD : K₁ ⊆ D \ (Pg e i ∪ Pg e j))
    (hΩ : IsOpen Ω) (hKΩ : K₀ ∪ K₁ ⊆ Ω) :
    ∃ O₀ O₁ : Set M₂, IsOpen O₀ ∧ IsOpen O₁ ∧ K₀ ⊆ O₀ ∧ K₁ ⊆ O₁ ∧
      closure O₀ ⊆ Ω ∧ closure O₁ ⊆ Ω ∧ Disjoint (closure O₀) (closure O₁) ∧
      closure O₀ ∩ G (ends e).1 '' CpBd (ends e).1 ⊆ F \ (Pg e i ∪ Pg e j) ∧
      Disjoint (closure O₀) (G (ends e).2 '' CpBd (ends e).2) ∧
      closure O₁ ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ D \ (Pg e i ∪ Pg e j) ∧
      Disjoint (closure O₁) (G (ends e).1 '' CpBd (ends e).1) := by
  obtain ⟨hF, hD, hDF⟩ := hfill.face_annuli_and_intersection
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, -, -, -, -, -, -, -, -, -, -, -, -,
    hfirst, hsecond, -⟩ := hfill
  have hFA : F ⊆ G (ends e).1 '' CpBd (ends e).1 := fun x hx =>
    (hfirst.symm.subset hx).1
  have hDB : D ⊆ G (ends e).2 '' CpBd (ends e).2 := fun x hx =>
    (hsecond.symm.subset hx).1
  have hdisF : Disjoint (F \ (Pg e i ∪ Pg e j)) (G (ends e).2 '' CpBd (ends e).2) := by
    refine disjoint_left.mpr fun x hx hxB => ?_
    exact hx.2 (hDF.subset ⟨hsecond.subset ⟨hxB, (hfirst.symm.subset hx.1).2⟩, hx.1⟩)
  have hdisD : Disjoint (D \ (Pg e i ∪ Pg e j)) (G (ends e).1 '' CpBd (ends e).1) := by
    refine disjoint_left.mpr fun x hx hxA => ?_
    exact hx.2 (hDF.subset ⟨hx.1, hfirst.subset ⟨hxA, (hsecond.symm.subset hx.1).2⟩⟩)
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hAs : IsClosed (G (ends e).1 '' CpBd (ends e).1) :=
    hcellA.boundary_eq_frontier ▸ isClosed_frontier
  have hBs : IsClosed (G (ends e).2 '' CpBd (ends e).2) :=
    hcellB.boundary_eq_frontier ▸ isClosed_frontier
  have hKdis : Disjoint K₀ K₁ := hdisF.mono hKF ((hKD.trans sdiff_subset).trans hDB)
  obtain ⟨V₀, V₁, hV₀, hV₁, hKV₀, hKV₁, hVdis⟩ :=
    normal_separation hK₀.isClosed hK₁.isClosed hKdis
  obtain ⟨hchartA⟩ := hcellA.nonempty_chartedSpace_boundary
  obtain ⟨hchartB⟩ := hcellB.nonempty_chartedSpace_boundary
  let _ := hchartA
  let _ := hchartB
  obtain ⟨O₀, hO₀, hK₀O, hO₀sub, hO₀A, hO₀B⟩ :=
    hF.exists_open_isolation_of_isClosed hFA hBs hdisF hK₀.isClosed hKF (hΩ.inter hV₀)
      (fun x hx => ⟨hKΩ (Or.inl hx), hKV₀ hx⟩)
  obtain ⟨O₁, hO₁, hK₁O, hO₁sub, hO₁B, hO₁A⟩ :=
    hD.exists_open_isolation_of_isClosed hDB hAs hdisD hK₁.isClosed hKD (hΩ.inter hV₁)
      (fun x hx => ⟨hKΩ (Or.inr hx), hKV₁ hx⟩)
  exact ⟨O₀, O₁, hO₀, hO₁, hK₀O, hK₁O,
    hO₀sub.trans inter_subset_left, hO₁sub.trans inter_subset_left,
    hVdis.mono (hO₀sub.trans inter_subset_right) (hO₁sub.trans inter_subset_right),
    hO₀A, hO₀B, hO₁B, hO₁A⟩

end DifferentialGeometry.Topology.PiecewiseLinear
