import DifferentialGeometry.Topology.ThreeManifold.AntipodalQuotientBall
import DifferentialGeometry.Topology.ThreeManifold.BallSphereSides

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by norm_num [Module.finrank_fin_fun]⟩
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := sphere (0 : E3) 1
private abbrev S3 := sphere (0 : E4) 1

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [PreconnectedSpace M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]

theorem exists_ball_or_projective_complement_of_cap_cover
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source)
    (hF : (b '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : E3) 1 ∪ F '' (b '' ball (0 : E3) 1)ᶜ = univ) :
    (∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ G.source ∧
      G '' ball (0 : E3) 1 = (B '' closedBall (0 : E3) 1)ᶜ ∧
      G '' closedBall (0 : E3) 1 = (B '' ball (0 : E3) 1)ᶜ ∧
      G '' sphere (0 : E3) 1 = B '' sphere (0 : E3) 1) ∨
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞,
      closedBall (0 : E3) 1 ⊆ G.source ∧
      (G '' ball (0 : E3) 1)ᶜ ⊆ F.source ∧
      F '' (G '' closedBall (0 : E3) 1)ᶜ = (B '' closedBall (0 : E3) 1)ᶜ ∧
      F '' (G '' ball (0 : E3) 1)ᶜ = (B '' ball (0 : E3) 1)ᶜ ∧
      F '' (G '' sphere (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
  let : PreconnectedSpace S3 := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E4])) 0 1)
  let : ConnectedSpace S3 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E4])) 0 zero_le_one)
  let : ConnectedSpace Z := honto.connectedSpace hp.contMDiff.continuous
  let K := B '' closedBall (0 : E3) 1
  let C := Kᶜ
  let K0 := (b '' ball (0 : E3) 1)ᶜ
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hK0 : IsCompact K0 :=
    (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hb)).isClosed_compl.isCompact
  have hFK0 : IsCompact (F '' K0) :=
    hK0.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hF)
  have hCsub : C ⊆ F '' K0 := by
    intro x hx
    have hh : x ∈ K ∪ F '' K0 := hcover.symm ▸ mem_univ x
    exact hh.resolve_left hx
  have hclsub : closure C ⊆ F '' K0 := closure_minimal hCsub hFK0.isClosed
  have hcompact : IsCompact (closure C) := hFK0.of_isClosed_subset isClosed_closure hclsub
  have hsource : closure C ⊆ F.target := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hclsub hx
    exact F.map_source (hF hy)
  let e : S2 → M := B ∘ Subtype.val
  have he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph B
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hB)
  have hKfront : frontier K = range e := by
    have hh := B.image_frontier_of_isCompact (isCompact_closedBall (0 : E3) 1) hB
    rw [frontier_closedBall _ one_ne_zero] at hh
    rw [← hh, range_comp, Subtype.range_val]
  have hKint : interior K = B '' ball (0 : E3) 1 := by
    have hh := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (closedBall (0 : E3) 1) = interior K at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hCconn : IsConnected C :=
    (DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary
      hK.isClosed (hKint.symm ▸ (nonempty_ball.mpr zero_lt_one).image B) e he hKfront).2
  have hCfront : frontier C = range e := by
    change frontier Kᶜ = range e
    rw [frontier_compl, hKfront]
  have hCclosure : closure C = (B '' ball (0 : E3) 1)ᶜ := by
    change closure Kᶜ = _
    rw [closure_compl, hKint]
  let V := F.symm '' C
  have hCs : C ⊆ F.target := subset_closure.trans hsource
  have hVo : IsOpen V :=
    F.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source hK.isClosed.isOpen_compl hCs
  have hVc : IsConnected V := hCconn.image F.symm
    (F.contMDiffOn_invFun.continuousOn.mono hCs)
  have hVcompact : IsCompact (F.symm '' closure C) :=
    hcompact.image_of_continuousOn (F.contMDiffOn_invFun.continuousOn.mono hsource)
  have hVcl : closure V = F.symm '' closure C :=
    subset_antisymm (closure_minimal (image_mono subset_closure) hVcompact.isClosed)
      ((F.contMDiffOn_invFun.continuousOn.mono hsource).image_closure)
  have hVsource : closure V ⊆ F.source := by
    rw [hVcl]
    rintro x ⟨y, hy, rfl⟩
    exact F.map_target (hsource hy)
  have hVfront : frontier V = F.symm '' frontier C := by
    have hh :=
      (F.symm.toOpenPartialHomeomorph.isImage_image_of_subset_source hCs).frontier.image_eq
    change F.symm '' (F.target ∩ frontier C) = F.source ∩ frontier V at hh
    rw [inter_eq_right.mpr (frontier_subset_closure.trans hsource),
      inter_eq_right.mpr (frontier_subset_closure.trans hVsource)] at hh
    exact hh.symm
  have hFV : F '' V = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (F.right_inv (hCs hz)).symm ▸ hz
    · intro hx
      exact ⟨F.symm x, mem_image_of_mem _ hx, F.right_inv (hCs hx)⟩
  have hFcl : F '' closure V = closure C := by
    rw [hVcl]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (F.right_inv (hsource hz)).symm ▸ hz
    · intro hx
      exact ⟨F.symm x, mem_image_of_mem _ hx, F.right_inv (hsource hx)⟩
  let eZ : S2 → Z := F.symm ∘ e
  have heZ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ eZ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F.symm he
      (hCfront ▸ frontier_subset_closure.trans hsource)
  obtain ⟨G, hG, hGf⟩ :=
    exists_ball_chart_of_antipodal_quotient_sphere_embedding p hp honto hfib eZ heZ
  have hVf : frontier V = G '' sphere (0 : E3) 1 := by
    rw [hVfront, hCfront, ← range_comp, ← hGf]
  have hFf : F '' (G '' sphere (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    rw [← hVf, hVfront, hCfront]
    have hes : range e ⊆ F.target := hCfront ▸ frontier_subset_closure.trans hsource
    have heq : F '' (F.symm '' range e) = range e := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact (F.right_inv (hes hz)).symm ▸ hz
      · intro hx
        exact ⟨F.symm x, mem_image_of_mem _ hx, F.right_inv (hes hx)⟩
    rw [heq, range_comp, Subtype.range_val]
  rcases eq_ball_or_complement_of_connected_sphere_frontier G hG hVo hVc hVf with hball | hcompl
  · left
    have hGc : G '' closedBall (0 : E3) 1 = closure V := by
      rw [← DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph G hG,
        ← hball]
    let Q := G.trans F
    have hQs : closedBall (0 : E3) 1 ⊆ Q.source := by
      intro x hx
      exact ⟨hG hx, hVsource (hGc ▸ mem_image_of_mem G hx)⟩
    refine ⟨Q, hQs, ?_, ?_, ?_⟩
    · change (F ∘ G) '' ball (0 : E3) 1 = C
      rw [image_comp, ← hball, hFV]
    · change (F ∘ G) '' closedBall (0 : E3) 1 = _
      rw [image_comp, hGc, hFcl, hCclosure]
    · change (F ∘ G) '' sphere (0 : E3) 1 = _
      rw [image_comp]
      exact hFf
  · right
    have hGi : interior (G '' closedBall (0 : E3) 1) = G '' ball (0 : E3) 1 := by
      have hh := G.toOpenPartialHomeomorph.image_interior_of_subset_source hG
      change G '' interior (closedBall (0 : E3) 1) = _ at hh
      rw [interior_closedBall _ one_ne_zero] at hh
      exact hh.symm
    have hGc : closure V = (G '' ball (0 : E3) 1)ᶜ := by rw [hcompl, closure_compl, hGi]
    exact ⟨G, hG, hGc ▸ hVsource, hcompl ▸ hFV, hGc ▸ hFcl.trans hCclosure, hFf⟩

end DifferentialGeometry.Topology.ThreeManifold
