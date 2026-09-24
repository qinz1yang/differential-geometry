/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointSupportedPLEmbeddings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-! # Section34Vertex Edge Pasting -/

open Set Topology Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_section34_vertex_embeddings
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hne : ∀ e, (ends e).1 ≠ (ends e).2)
    (hD : ∀ e, src (.splitDisk e) =
      src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (V K : Section34EdgeIndex 𝒦 𝒦' → Set M)
    (φ₀ φ₁ : Section34EdgeIndex 𝒦 𝒦' → M ≃ M)
    (hV : ∀ e, IsOpen (V e)) (hK : ∀ e, IsClosed (K e)) (hKV : ∀ e, K e ⊆ V e)
    (hdisj : Pairwise (Disjoint on V))
    (hφ₀ : ∀ e, IsPLHomeomorphInto 3 (φ₀ e) (src (.vertexBall (ends e).1)))
    (hφ₁ : ∀ e, IsPLHomeomorphInto 3 (φ₁ e) (src (.vertexBall (ends e).2)))
    (hfix₀ : ∀ e, EqOn (φ₀ e) id (K e)ᶜ) (hfix₁ : ∀ e, EqOn (φ₁ e) id (K e)ᶜ) :
    ∃ Φ : Section34VertexIndex 𝒦 𝒦' → M ≃ M,
      (∀ w, IsPLHomeomorphInto 3 (Φ w) (src (.vertexBall w))) ∧
      (∀ e, EqOn (Φ (ends e).1) (φ₀ e) (V e) ∧
        EqOn (Φ (ends e).2) (φ₁ e) (V e)) ∧
      (∀ e, Φ (ends e).1 '' src (.vertexBall (ends e).1) ∩ V e =
          φ₀ e '' src (.vertexBall (ends e).1) ∩ V e ∧
        Φ (ends e).2 '' src (.vertexBall (ends e).2) ∩ V e =
          φ₁ e '' src (.vertexBall (ends e).2) ∩ V e) ∧
      (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → EqOn (Φ w) id (V e)) ∧
      ∀ w, EqOn (Φ w) id (⋃ (e) (_ : w = (ends e).1 ∨ w = (ends e).2), K e)ᶜ := by
  classical
  have hfin (w : Section34VertexIndex 𝒦 𝒦') :
      {e | w = (ends e).1 ∨ w = (ends e).2}.Finite := by
    have h₀ := finite_splitDisk_of_section34CutFrame hframe (fun e => (ends e).1)
      (fun e => (hD e).subset.trans inter_subset_left) w
    have h₁ := finite_splitDisk_of_section34CutFrame hframe (fun e => (ends e).2)
      (fun e => (hD e).subset.trans inter_subset_right) w
    convert h₀.union h₁ using 1
    ext e
    simp only [mem_ofPred_eq, mem_union, eq_comm]
  let s := fun w => (hfin w).toFinset
  have hs (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') :
      e ∈ s w ↔ w = (ends e).1 ∨ w = (ends e).2 := (hfin w).mem_toFinset
  let ψ := fun (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') =>
    if w = (ends e).1 then φ₀ e else φ₁ e
  have hψ (w) (e) (he : e ∈ s w) : IsPLOn 3 3 (ψ w e) (src (.vertexBall w)) := by
    by_cases hw : w = (ends e).1
    · dsimp only [ψ]
      rw [if_pos hw, hw]
      exact (hφ₀ e).isPLOn
    · have hw' := ((hs w e).mp he).resolve_left hw
      dsimp only [ψ]
      rw [if_neg hw, hw']
      exact (hφ₁ e).isPLOn
  have hψfix (w) (e) : EqOn (ψ w e) id (K e)ᶜ := by
    dsimp [ψ]
    split_ifs
    · exact hfix₀ e
    · exact hfix₁ e
  have hconstruct (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ Φ : M ≃ M, IsPLHomeomorphInto 3 Φ (src (.vertexBall w)) ∧
        (∀ e ∈ s w, EqOn Φ (ψ w e) (V e)) ∧
        (∀ e ∈ s w, Φ '' src (.vertexBall w) ∩ V e = ψ w e '' src (.vertexBall w) ∩ V e) ∧
        EqOn Φ id (⋃ e ∈ s w, K e)ᶜ := by
    have hC : IsPLCellOn 3 (src (.vertexBall w)) (srcBd (.vertexBall w)) :=
      hframe.2.2.2.1 (.vertexBall w)
    obtain ⟨T, -⟩ := hC.isPolyhedralBall
    exact exists_isPL_embedding_of_finite_disjoint_support hC.isCompact T.isPLOn_id
      (s w) V K (ψ w) (fun e _ => hV e) (fun e _ => hK e) (fun e _ => hKV e)
      hdisj (hψ w) (fun e _ => hψfix w e)
  choose Φ hΦ hΦeq hΦimage hΦfix using hconstruct
  refine ⟨Φ, hΦ, ?_, ?_, ?_, ?_⟩
  · intro e
    have h₀ := hΦeq (ends e).1 e ((hs _ _).mpr (Or.inl rfl))
    have h₁ := hΦeq (ends e).2 e ((hs _ _).mpr (Or.inr rfl))
    exact ⟨by simpa only [ψ, if_pos rfl] using h₀,
      by simpa only [ψ, if_neg (hne e).symm] using h₁⟩
  · intro e
    have h₀ := hΦimage (ends e).1 e ((hs _ _).mpr (Or.inl rfl))
    have h₁ := hΦimage (ends e).2 e ((hs _ _).mpr (Or.inr rfl))
    exact ⟨by simpa only [ψ, if_pos rfl] using h₀,
      by simpa only [ψ, if_neg (hne e).symm] using h₁⟩
  · intro e w hw₀ hw₁ x hx
    apply hΦfix w
    intro hxK
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxK
    have hje : j ≠ e := by
      intro he
      exact ((hs w e).mp (he ▸ hj)).elim hw₀ hw₁
    exact Set.disjoint_left.mp (hdisj hje) (hKV j hxj) hx
  · intro w x hx
    apply hΦfix w
    intro hxK
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxK
    exact hx (mem_iUnion₂.mpr ⟨e, (hs w e).mp he, hxe⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
