import DifferentialGeometry.Topology.Circle.Extension
import DifferentialGeometry.Topology.Diffeomorph.SphereGerm
import DifferentialGeometry.Topology.Embedding.Factor
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 1 + 1)]

theorem exists_diffeomorph_eqOn_circle_neighborhood
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hsource : sphere (0 : E) 1 ⊆ F.source)
    (hboundary : MapsTo F (sphere (0 : E) 1) (sphere (0 : E) 1))
    (hside : MapsTo F (closedBall (0 : E) 1 ∩ F.source) (closedBall (0 : E) 1)) :
    ∃ D : E ≃ₘ[ℝ] E, D '' closedBall (0 : E) 1 = closedBall 0 1 ∧
      ∃ V : Set E, IsOpen V ∧ sphere (0 : E) 1 ⊆ V ∧ V ⊆ F.source ∧ EqOn D F V := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ 1
  let S := sphere (0 : E) 1
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, (Fact.out : Module.finrank ℝ E = 1 + 1)]
    norm_num
  let _ : ConnectedSpace S := Subtype.connectedSpace (isConnected_sphere hrank (0 : E) zero_le_one)
  let f : S → E := fun x => F x.val
  have hfimm : Manifold.IsImmersion (𝓡 1) 𝓘(ℝ, E) ∞ f :=
    (isSmoothEmbedding_coe_sphere
      (E := E) (n := 1)).isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      (fun x => F.isLocalDiffeomorphAt _ _ _ (hsource (by
        obtain ⟨y, hy⟩ := x.property
        exact hy ▸ y.property))) (by simp)
  have hf : Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ f :=
    ⟨hfimm, (hfimm.contMDiff.continuous.isClosedEmbedding (fun x y h =>
      Subtype.ext (F.injOn (hsource x.property) (hsource y.property) h))).isEmbedding⟩
  let q : S → S := fun x => ⟨F x.val, hboundary x.property⟩
  have hq : ContMDiff (𝓡 1) (𝓡 1) ∞ q :=
    (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_coe_sphere (E := E) (n := 1)).isImmersion).mpr
      ⟨hf.contMDiff.continuous.subtype_mk _, hf.contMDiff⟩
  have hqemb : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ q :=
    Manifold.IsSmoothEmbedding.of_comp (f := q) (g := Subtype.val) hf (by simp) hq
      (isSmoothEmbedding_coe_sphere (E := E) (n := 1)).contMDiff
  have hqrange : range q = univ := by
    apply IsClopen.eq_univ
    · exact ⟨(isCompact_range hq.continuous).isClosed,
        _root_.Manifold.isOpen_range_of_isSmoothEmbedding
          rfl hqemb⟩
    · exact range_nonempty q
  let Q := hqemb.diffeomorphOfSurjective (range_eq_univ.mp hqrange)
  obtain ⟨C, hC, _, hCball⟩ := EuclideanGeometry.exists_diffeomorph_extension_circle Q
  have hCF (x : E) (hx : x ∈ S) : C x = F x := hC ⟨x, hx⟩
  let G := F.trans C.symm.toPartialDiffeomorph
  have hGs : G.source = F.source := by
    ext x
    change (x ∈ F.source ∧ F x ∈ (univ : Set E)) ↔ x ∈ F.source
    simp only [mem_univ, and_true]
  have hG (x : E) : G x = C.symm (F x) := rfl
  have hSG : S ⊆ G.source := hGs.symm ▸ hsource
  have hGfix : EqOn G id S := by
    intro x hx
    rw [hG, ← hCF x hx, C.symm_apply_apply]
    rfl
  have hGside : MapsTo G (closedBall (0 : E) 1 ∩ G.source) (closedBall (0 : E) 1) := by
    intro x hx
    have hm : F x ∈ C '' closedBall 0 1 := hCball.symm ▸ hside ⟨hx.1, hGs ▸ hx.2⟩
    obtain ⟨y, hy, hyeq⟩ := hm
    rw [hG, ← hyeq, C.symm_apply_apply]
    exact hy
  obtain ⟨V, hV, hSV, hVG, Φ, _, _, _, hΦ, _, hΦball, _⟩ :=
    G.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood zero_lt_one hSG hGfix hGside
      isOpen_univ (subset_univ _)
  refine ⟨(Φ 1).trans C, ?_, V, hV, hSV, hGs ▸ hVG, ?_⟩
  · change (C ∘ Φ 1) '' closedBall 0 1 = closedBall 0 1
    rw [image_comp, hΦball 1 ⟨zero_le_one, le_rfl⟩, hCball]
  · intro x hx
    change C (Φ 1 x) = F x
    rw [hΦ hx, hG, C.apply_symm_apply]

end PartialDiffeomorph
