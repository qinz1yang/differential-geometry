import DifferentialGeometry.Topology.Manifold.EmbeddedBallShell
import DifferentialGeometry.Topology.Manifold.SphereAnnulusBoundaryMatching
import DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev CI := (𝓡 2).prod (𝓡∂ 1)

private theorem frontier_closed_sdiff_interior_of_subset_interior
    {X : Type*} [TopologicalSpace X] {U K : Set X}
    (hU : IsClosed U) (hK : IsClosed K) (hKr : closure (interior K) = K)
    (hKU : K ⊆ interior U) :
    frontier (U \ interior K) = frontier U ∪ frontier K := by
  have hV : IsClosed (U \ interior K) := hU.sdiff isOpen_interior
  have hVi : interior (U \ interior K) = interior U \ K := by
    rw [sdiff_eq, interior_inter, interior_compl, hKr]
    rfl
  rw [hV.frontier_eq, hVi, hU.frontier_eq, hK.frontier_eq]
  ext x
  constructor
  · rintro ⟨⟨hxU, hxKi⟩, hxV⟩
    by_cases hxUi : x ∈ interior U
    · exact Or.inr ⟨by_contra (fun hxK => hxV ⟨hxUi, hxK⟩), hxKi⟩
    · exact Or.inl ⟨hxU, hxUi⟩
  · rintro (⟨hxU, hxUi⟩ | ⟨hxK, hxKi⟩)
    · exact ⟨⟨hxU, fun hxKi => hxUi (hKU (interior_subset hxKi))⟩, fun h => hxUi h.1⟩
    · exact ⟨⟨interior_subset (hKU hxK), hxKi⟩, fun h => h.2 hxK⟩

private theorem exists_parametrized_embeddedBallShell
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hnested : B '' closedBall (0 : E3) 1 ⊆ ball (0 : E3) 1)
    (f : S2 → E3) (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hfront : B '' sphere (0 : E3) 1 = range f) :
    ∃ (e : PartialEquiv (S2 × unitInterval) E3)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = univ ∧ e.target = closedBall (0 : E3) 1 \ B '' ball (0 : E3) 1 ∧
      ContMDiff CI (𝓡 3) ∞ e ∧ ContMDiffOn (𝓡 3) CI ∞ e.symm e.target ∧
      (∀ z : S2, e (z, 0) = f z) ∧ ∀ z : S2, e (η z, 1) = z.val := by
  let _ : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨e, hes, het, he, hei⟩ := exists_smooth_embeddedBallShell_parametrization
    (n := 2) B zero_lt_one hB hnested v
  have hBint : interior (B '' closedBall (0 : E3) 1) = B '' ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (closedBall (0 : E3) 1) = interior (B '' closedBall (0 : E3) 1) at h
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hKclosed : IsClosed (B '' closedBall (0 : E3) 1) :=
    ((isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)).isClosed
  have hKr : closure (interior (B '' closedBall (0 : E3) 1)) = B '' closedBall (0 : E3) 1 := by
    rw [hBint]
    exact DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB
  have hKf : frontier (B '' closedBall (0 : E3) 1) = range f := by
    rw [← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB,
      frontier_closedBall _ one_ne_zero, hfront]
  have hfrontE : frontier e.target = range f ∪ range (Subtype.val : S2 → E3) := by
    rw [het, ← hBint, frontier_closed_sdiff_interior_of_subset_interior
      isClosed_closedBall hKclosed hKr (by rwa [interior_closedBall _ one_ne_zero]),
      hKf, frontier_closedBall _ one_ne_zero, Subtype.range_val, union_comm]
  obtain ⟨Ψ, η, hzero, hone⟩ := exists_parametrized_sphere_annulus_of_smooth_partial_equiv
    e hes he hei f Subtype.val hf (isSmoothEmbedding_coe_sphere (E := E3) (n := 2)) hfrontE
  let d := Ψ.toEquiv.transPartialEquiv e
  refine ⟨d, η, ?_, het, he.comp Ψ.contMDiff, Ψ.symm.contMDiff.comp_contMDiffOn hei, hzero, hone⟩
  change Ψ ⁻¹' e.source = univ
  rw [hes, preimage_univ]

theorem exists_smooth_nested_ball_shell_with_boundary
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hnested : B '' closedBall (0 : E3) 1 ⊆ C '' ball (0 : E3) 1)
    (f : S2 → M) (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hBf : B '' sphere (0 : E3) 1 = range f) :
    ∃ (e : PartialEquiv (S2 × unitInterval) M)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = univ ∧ e.target = C '' closedBall (0 : E3) 1 \ B '' ball (0 : E3) 1 ∧
      ContMDiff CI (𝓡 3) ∞ e ∧ ContMDiffOn (𝓡 3) CI ∞ e.symm e.target ∧
      (∀ z : S2, e (z, 0) = f z) ∧ ∀ z : S2, e (η z, 1) = C z.val := by
  have hinside : range f ⊆ C '' ball (0 : E3) 1 :=
    hBf ▸ (image_mono sphere_subset_closedBall).trans hnested
  have hftarget : range f ⊆ C.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hinside hz
    exact C.map_source (hC (ball_subset_closedBall hx))
  let fE : S2 → E3 := C.symm ∘ f
  have hfE : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fE :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph C.symm hf hftarget
  let B₀ := B.trans C.symm
  have hBtarget (x : E3) (hx : x ∈ closedBall (0 : E3) 1) : B x ∈ C.target := by
    obtain ⟨y, hy, hyB⟩ := hnested ⟨x, hx, rfl⟩
    exact hyB ▸ C.map_source (hC (ball_subset_closedBall hy))
  have hB₀ : closedBall (0 : E3) 1 ⊆ B₀.source :=
    fun x hx => ⟨hB hx, hBtarget x hx⟩
  have hB₀ball : B₀ '' closedBall (0 : E3) 1 ⊆ ball (0 : E3) 1 := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzB⟩ := hnested ⟨x, hx, rfl⟩
    change C.symm.toPartialEquiv (B x) ∈ ball (0 : E3) 1
    rw [← hzB]
    exact (C.toPartialEquiv.left_inv (hC (ball_subset_closedBall hz))).symm ▸ hz
  have hB₀f : B₀ '' sphere (0 : E3) 1 = range fE := by
    change (C.symm ∘ B) '' sphere (0 : E3) 1 = _
    rw [image_comp, hBf, ← range_comp]
  have hcancel (x : E3) (hx : x ∈ closedBall (0 : E3) 1) : C (B₀ x) = B x :=
    C.right_inv (hBtarget x hx)
  obtain ⟨e₀, η, he₀s, he₀t, he₀, he₀i, he₀zero, he₀one⟩ :=
    exists_parametrized_embeddedBallShell B₀ hB₀ hB₀ball fE hfE hB₀f
  have he₀C : e₀.target ⊆ C.source := by
    rw [he₀t]
    exact fun x hx => hC hx.1
  let e := e₀.trans C.toPartialEquiv
  have hes : e.source = univ := by
    ext p
    constructor
    · exact fun _ => mem_univ _
    · intro _
      have hp : p ∈ e₀.source := he₀s ▸ mem_univ p
      exact ⟨hp, he₀C (e₀.map_source hp)⟩
  have het : e.target = C '' closedBall (0 : E3) 1 \ B '' ball (0 : E3) 1 := by
    ext x
    constructor
    · rintro ⟨hxC, hxe⟩
      rw [he₀t] at hxe
      refine ⟨⟨C.symm x, hxe.1, C.right_inv hxC⟩, ?_⟩
      rintro ⟨y, hy, hByx⟩
      apply hxe.2
      refine ⟨y, hy, ?_⟩
      apply C.toPartialEquiv.injOn
        (hC (ball_subset_closedBall (hB₀ball ⟨y, ball_subset_closedBall hy, rfl⟩)))
        (hC hxe.1)
      exact (hcancel y (ball_subset_closedBall hy)).trans
        (hByx.trans (C.right_inv hxC).symm)
    · rintro ⟨⟨z, hz, rfl⟩, hxB⟩
      refine ⟨C.map_source (hC hz), ?_⟩
      change C.symm (C z) ∈ e₀.target
      change C.toPartialEquiv.symm (C.toPartialEquiv z) ∈ e₀.target
      rw [C.toPartialEquiv.left_inv (hC hz), he₀t]
      refine ⟨hz, ?_⟩
      rintro ⟨y, hy, hB₀yz⟩
      apply hxB
      exact ⟨y, hy, (hcancel y (ball_subset_closedBall hy)).symm.trans (congrArg C hB₀yz)⟩
  have he : ContMDiff CI (𝓡 3) ∞ e := by
    apply contMDiffOn_univ.mp
    exact C.contMDiffOn_toFun.comp he₀.contMDiffOn
      (fun p _ => he₀C (e₀.map_source (he₀s ▸ mem_univ p)))
  have hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target :=
    he₀i.comp (C.contMDiffOn_invFun.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  refine ⟨e, η, hes, het, he, hei, ?_, ?_⟩
  · intro z
    change C (e₀ (z, 0)) = f z
    rw [he₀zero]
    exact C.right_inv (hftarget (mem_range_self z))
  · intro z
    change C (e₀ (η z, 1)) = C z.val
    rw [he₀one]

theorem exists_smooth_ball_shell_of_compact_regular_sphere_frontier
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    {K : Set M} (hK : IsCompact K) (hregular : closure (interior K) = K)
    (hinside : K ⊆ C '' ball (0 : E3) 1)
    (f : S2 → M) (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hfront : frontier K = range f) :
    ∃ (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
      (e : PartialEquiv (S2 × unitInterval) M)
      (β η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' ball (0 : E3) 1 = interior K ∧
      B '' closedBall (0 : E3) 1 = K ∧
      B '' sphere (0 : E3) 1 = range f ∧
      (∀ z : S2, B (β z).val = f z) ∧
      e.source = univ ∧ e.target = C '' closedBall (0 : E3) 1 \ interior K ∧
      ContMDiff CI (𝓡 3) ∞ e ∧ ContMDiffOn (𝓡 3) CI ∞ e.symm e.target ∧
      (∀ z : S2, e (z, 0) = f z) ∧ ∀ z : S2, e (η z, 1) = C z.val := by
  have hneK : K.Nonempty := by
    let z : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
    have hz : f z ∈ closure (interior K) := by
      have hcl : IsClosed K := hregular ▸ isClosed_closure
      rw [hregular]
      exact hcl.frontier_subset (hfront.symm ▸ mem_range_self z)
    exact ⟨f z, hregular ▸ hz⟩
  have hne : (interior K).Nonempty := closure_nonempty_iff.mp (hregular.symm ▸ hneK)
  have hsource : closure (interior K) ⊆ C.target := by
    rw [hregular]
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hinside hz
    exact C.map_source (hC (ball_subset_closedBall hx))
  have hfrontI : frontier (interior K) = range f := by
    rw [frontier, hregular, interior_interior]
    rw [frontier, show closure K = K from (hregular ▸ isClosed_closure).closure_eq] at hfront
    exact hfront
  obtain ⟨B, hB, hBi, hBK, hBf⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_compact_closure_sphere_frontier
      C isOpen_interior hne (hregular.symm ▸ hK) hsource f hf hfrontI
  have hBK' : B '' closedBall (0 : E3) 1 = K := hBK.trans hregular
  obtain ⟨e, η, hes, het, he, hei, hzero, hone⟩ :=
    exists_smooth_nested_ball_shell_with_boundary C hC B hB (hBK'.symm ▸ hinside) f hf hBf
  have hfBtarget : range f ⊆ B.target := by
    rw [← hBf]
    rintro z ⟨w, hw, rfl⟩
    exact B.map_source (hB (sphere_subset_closedBall hw))
  have hfB : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (B.symm ∘ f) :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph B.symm hf hfBtarget
  have hrange : range (B.symm ∘ f) = range (Subtype.val : S2 → E3) := by
    rw [range_comp, ← hBf, Subtype.range_val]
    ext z
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact (B.toPartialEquiv.left_inv (hB (sphere_subset_closedBall hx))).symm ▸ hx
    · intro hz
      refine ⟨B z, ⟨z, hz, rfl⟩, ?_⟩
      exact B.left_inv (hB (sphere_subset_closedBall hz))
  let β := hfB.diffeomorphOfRangeEq (isSmoothEmbedding_coe_sphere (E := E3) (n := 2)) hrange
  refine ⟨B, e, β, η, hB, hBi, hBK', hBf, ?_, hes, ?_, he, hei, hzero, hone⟩
  · intro z
    have hz : (β z).val = B.symm (f z) :=
      hfB.comp_diffeomorphOfRangeEq (isSmoothEmbedding_coe_sphere (E := E3) (n := 2)) hrange z
    rw [hz]
    exact B.right_inv (hfBtarget (mem_range_self z))
  · rw [het, hBi]

end DifferentialGeometry.Topology.Manifold
