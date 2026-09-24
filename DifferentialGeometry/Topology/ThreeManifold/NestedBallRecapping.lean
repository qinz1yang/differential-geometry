import DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.ThreeManifold.RelativeBallReplacement
import DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

open private standardHemisphereChart oppositeHemisphereChart standardHemisphereChart_source
  oppositeHemisphereChart_source hemisphere_complement from
    DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

private def stereographicPartial (p : S3) : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ where
  toPartialEquiv := (stereographic' 3 p).symm.toPartialEquiv
  open_source := (stereographic' 3 p).symm.open_source
  open_target := (stereographic' 3 p).symm.open_target
  contMDiffOn_toFun := (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph p).contMDiff.contMDiffOn
  contMDiffOn_invFun := (DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn p).contMDiffOn

private theorem exists_ball_chart_complement_of_sphere_ball_chart
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' ball (0 : E3) 1 = (C '' closedBall (0 : E3) 1)ᶜ ∧
      B '' closedBall (0 : E3) 1 = (C '' ball (0 : E3) 1)ᶜ ∧
      B '' sphere (0 : E3) 1 = C '' sphere (0 : E3) 1 := by
  let p := C 0
  let A := stereographicPartial p
  have hAt : A.target = {p}ᶜ := by change (stereographic' 3 p).source = {p}ᶜ; simp
  have hCcompact : IsCompact (C '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn (C.contMDiffOn_toFun.continuousOn.mono hC)
  have hCint : interior (C '' closedBall (0 : E3) 1) = C '' ball (0 : E3) 1 := by
    have h := C.toOpenPartialHomeomorph.image_interior_of_subset_source hC
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hclosure : closure (C '' closedBall (0 : E3) 1)ᶜ = (C '' ball (0 : E3) 1)ᶜ := by
    rw [closure_compl, hCint]
  have hp : p ∈ C '' ball (0 : E3) 1 := ⟨0, by simp, rfl⟩
  have hsource : closure (C '' closedBall (0 : E3) 1)ᶜ ⊆ A.target := by
    rw [hclosure, hAt]
    intro z hz hzp
    exact hz (mem_singleton_iff.mp hzp ▸ hp)
  have hne : ((C '' closedBall (0 : E3) 1)ᶜ).Nonempty := by
    by_contra h
    have hall : C '' closedBall (0 : E3) 1 = univ := by
      exact eq_univ_iff_forall.mpr (fun z => not_not.mp (fun hz => h ⟨z, hz⟩))
    have hf := C.image_frontier_of_isCompact (isCompact_closedBall (0 : E3) 1) hC
    rw [frontier_closedBall _ one_ne_zero, hall, frontier_univ] at hf
    have hn : (C '' sphere (0 : E3) 1).Nonempty :=
      ⟨C (EuclideanSpace.single 0 1), EuclideanSpace.single 0 1, by simp, rfl⟩
    rw [hf] at hn
    exact not_nonempty_empty hn
  let f : S2 → S3 := C ∘ Subtype.val
  have hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph C
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hC)
  have hfront : frontier (C '' closedBall (0 : E3) 1)ᶜ = range f := by
    rw [frontier_compl, ← C.image_frontier_of_isCompact (isCompact_closedBall _ _) hC,
      frontier_closedBall _ one_ne_zero, range_comp, Subtype.range_val]
  obtain ⟨B, hB, hBo, hBc, hBf⟩ := exists_ball_chart_of_compact_closure_sphere_frontier
    A hCcompact.isClosed.isOpen_compl hne isClosed_closure.isCompact hsource f hf hfront
  exact ⟨B, hB, hBo, hBc.trans hclosure, by simpa only [f, range_comp, Subtype.range_val] using hBf⟩

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

private theorem exists_ball_chart_of_recapped_sphere_ball_complement
    (C b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hb : closedBall (0 : E3) 1 ⊆ b.source)
    (hG : closedBall (0 : E3) 1 ⊆ G.source)
    (hdis : Disjoint (C '' closedBall (0 : E3) 1) (b '' closedBall (0 : E3) 1))
    (hP : (C '' ball (0 : E3) 1)ᶜ \ b '' ball (0 : E3) 1 ⊆ P.source)
    (hboundary : P '' (b '' sphere (0 : E3) 1) = G '' sphere (0 : E3) 1)
    (hinter : P '' ((C '' ball (0 : E3) 1)ᶜ \ b '' ball (0 : E3) 1) ∩
      G '' closedBall (0 : E3) 1 ⊆ G '' sphere (0 : E3) 1) :
    ∃ (J : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 M ∞)
      (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞),
      (C '' ball (0 : E3) 1)ᶜ ⊆ J.source ∧
      closedBall (0 : E3) 1 ⊆ A.source ∧
      A '' closedBall (0 : E3) 1 =
        P '' ((C '' ball (0 : E3) 1)ᶜ \ b '' ball (0 : E3) 1) ∪ G '' closedBall (0 : E3) 1 ∧
      A '' sphere (0 : E3) 1 = P '' (C '' sphere (0 : E3) 1) ∧
      ∃ O : Set S3, IsOpen O ∧ (C '' ball (0 : E3) 1)ᶜ \ b '' ball (0 : E3) 1 ⊆ O ∧
        O ⊆ P.source ∧ EqOn J P O := by
  let Ω := (C '' ball (0 : E3) 1)ᶜ
  have hΩ : IsCompact Ω :=
    (C.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hC)).isClosed_compl.isCompact
  have hbΩ : b '' closedBall (0 : E3) 1 ⊆ interior Ω := by
    rw [interior_compl, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC]
    exact disjoint_left.mp hdis.symm
  obtain ⟨J, D, hJ, hJimage, _, _, O, hO, hKO, hOP, hJP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement
      b P G hb hG hΩ hbΩ hP hboundary hinter
  obtain ⟨B, hB, _, hBc, hBs⟩ := exists_ball_chart_complement_of_sphere_ball_chart C hC
  let A := B.trans J
  have hA : closedBall (0 : E3) 1 ⊆ A.source := by
    intro z hz
    refine ⟨hB hz, hJ ?_⟩
    change B z ∈ (C '' ball (0 : E3) 1)ᶜ
    exact hBc ▸ mem_image_of_mem B hz
  have hAi : A '' closedBall (0 : E3) 1 = J '' Ω := by
    change (J ∘ B) '' closedBall (0 : E3) 1 = _
    rw [image_comp, hBc]
  have hCboundary : C '' sphere (0 : E3) 1 ⊆ Ω \ b '' ball (0 : E3) 1 := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨v, hv, hvw⟩
      have he := C.toPartialEquiv.injOn (hC (ball_subset_closedBall hv))
        (hC (sphere_subset_closedBall hw)) hvw
      exact (mem_ball_zero_iff.mp (he ▸ hv)).ne (mem_sphere_zero_iff_norm.mp hw)
    · exact fun hz => disjoint_left.mp hdis ⟨w, sphere_subset_closedBall hw, rfl⟩
        (image_mono ball_subset_closedBall hz)
  have hAf : A '' sphere (0 : E3) 1 = P '' (C '' sphere (0 : E3) 1) := by
    change (J ∘ B) '' sphere (0 : E3) 1 = _
    rw [image_comp, hBs]
    exact (hJP.mono (hCboundary.trans hKO)).image_eq
  exact ⟨J, A, hJ, hA, hAi.trans hJimage, hAf, O, hO, hKO, hOP, hJP⟩

end

section

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

omit [T2Space Z] in
theorem exists_ball_chart_of_recapped_nested_ball_shell
    (C B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hG : closedBall (0 : E3) 1 ⊆ G.source)
    (hnested : C '' closedBall (0 : E3) 1 ⊆ B '' ball (0 : E3) 1)
    (hF : B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1 ⊆ F.source)
    (hboundary : F '' (B '' sphere (0 : E3) 1) = G '' sphere (0 : E3) 1)
    (hinter : F '' (B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) ∩
      G '' closedBall (0 : E3) 1 ⊆ G '' sphere (0 : E3) 1) :
    ∃ A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ A.source ∧
      A '' closedBall (0 : E3) 1 =
        F '' (B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) ∪ G '' closedBall (0 : E3) 1 ∧
      A '' sphere (0 : E3) 1 = F '' (C '' sphere (0 : E3) 1) ∧
      ∃ H : PartialDiffeomorph (𝓡 3) (𝓡 3) Z E3 ∞,
        B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1 ⊆ H.source ∧
        (∀ z ∈ B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1, A (H z) = F z) ∧
        ∀ z ∈ C '' sphere (0 : E3) 1, H z ∈ sphere (0 : E3) 1 := by
  let p : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let a := standardHemisphereChart p
  let b := oppositeHemisphereChart p
  have has : a.source = univ := standardHemisphereChart_source p
  have hbs : b.source = univ := oppositeHemisphereChart_source p
  have hab : b '' closedBall (0 : E3) 1 = (a '' ball (0 : E3) 1)ᶜ := hemisphere_complement p
  have hab' : b '' ball (0 : E3) 1 = (a '' closedBall (0 : E3) 1)ᶜ := by
    have h := congrArg interior hab
    have hbi := b.toOpenPartialHomeomorph.image_interior_of_subset_source
      (show closedBall (0 : E3) 1 ⊆ b.source by rw [hbs]; exact subset_univ _)
    change b '' interior (closedBall (0 : E3) 1) = interior (b '' closedBall (0 : E3) 1) at hbi
    rw [interior_closedBall _ one_ne_zero] at hbi
    rw [← hbi, interior_compl,
      DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph a
        (has ▸ subset_univ _)] at h
    exact h
  let L := B.symm.trans a
  let C' := C.trans L
  let P := (a.symm.trans B).trans F
  have hCB (z : E3) (hz : z ∈ closedBall (0 : E3) 1) : C z ∈ B.target := by
    obtain ⟨x, hx, hxc⟩ := hnested ⟨z, hz, rfl⟩
    exact hxc ▸ B.map_source (hB (ball_subset_closedBall hx))
  have hC' : closedBall (0 : E3) 1 ⊆ C'.source :=
    fun z hz => ⟨hC hz, hCB z hz, has ▸ mem_univ _⟩
  have hLC (z : E3) (hz : z ∈ closedBall (0 : E3) 1) :
      B (B.symm (C z)) = C z := B.right_inv (hCB z hz)
  have hC'a : C' '' closedBall (0 : E3) 1 ⊆ a '' ball (0 : E3) 1 := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, hxc⟩ := hnested ⟨z, hz, rfl⟩
    refine ⟨x, hx, ?_⟩
    change a x = a (B.symm (C z))
    rw [← hxc]
    congr 1
    exact (B.left_inv (hB (ball_subset_closedBall hx))).symm
  have hdis : Disjoint (C' '' closedBall (0 : E3) 1) (b '' closedBall (0 : E3) 1) := by
    rw [hab]
    exact disjoint_compl_right.mono_left hC'a
  let S := (C' '' ball (0 : E3) 1)ᶜ \ b '' ball (0 : E3) 1
  have hSa : S ⊆ a '' closedBall (0 : E3) 1 := by
    dsimp only [S]
    rw [hab']
    exact fun x hx => not_not.mp hx.2
  have hcoord (x : S3) (hx : x ∈ S) :
      B (a.symm x) ∈ B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1 := by
    obtain ⟨z, hz, hzx⟩ := hSa hx
    have ha_inv : a.symm x = z := by rw [← hzx]; exact a.left_inv (has ▸ mem_univ _)
    rw [ha_inv]
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwB⟩
    apply hx.1
    refine ⟨w, hw, ?_⟩
    change a (B.symm (C w)) = x
    rw [hwB]
    have hb_inv : B.symm (B z) = z := B.left_inv (hB hz)
    rw [hb_inv]
    exact hzx
  have hPs : S ⊆ P.source := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hSa hx
    have ha_inv : a.symm x = z := by rw [← hzx]; exact a.left_inv (has ▸ mem_univ _)
    refine ⟨⟨?_, ?_⟩, hF (hcoord x hx)⟩
    · exact hzx ▸ a.map_source (has ▸ mem_univ _)
    · change a.symm x ∈ B.source
      rw [ha_inv]
      exact hB hz
  have himage : P '' S = F '' (B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨B (a.symm x), hcoord x hx, rfl⟩
    · rintro ⟨z, ⟨⟨v, hv, hvz⟩, hzC⟩, rfl⟩
      refine ⟨a v, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rintro ⟨w, hw, hwa⟩
          have hvw : B.symm (C w) = v := a.toPartialEquiv.injOn
            (has ▸ mem_univ _) (has ▸ mem_univ _) hwa
          apply hzC
          exact ⟨w, hw, (hLC w (ball_subset_closedBall hw)).symm.trans
            ((congrArg B hvw).trans hvz)⟩
        · rw [hab']
          exact not_not.mpr ⟨v, hv, rfl⟩
      · change F (B (a.symm (a v))) = F z
        have ha_inv : a.symm (a v) = v := a.left_inv (has ▸ mem_univ _)
        rw [ha_inv, hvz]
  have hbface : b '' sphere (0 : E3) 1 = a '' sphere (0 : E3) 1 := by
    have h := congrArg frontier hab
    rw [← b.image_frontier_of_isCompact (isCompact_closedBall _ _) (hbs ▸ subset_univ _),
      frontier_closedBall _ one_ne_zero, frontier_compl,
      DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph a
        (has ▸ subset_univ _)] at h
    exact h
  have hPbs : P '' (b '' sphere (0 : E3) 1) = F '' (B '' sphere (0 : E3) 1) := by
    rw [hbface, image_image, image_image]
    apply image_congr
    intro z hz
    change F (B (a.symm (a z))) = F (B z)
    have ha_inv : a.symm (a z) = z := a.left_inv (has ▸ mem_univ _)
    rw [ha_inv]
  have hPC's : P '' (C' '' sphere (0 : E3) 1) = F '' (C '' sphere (0 : E3) 1) := by
    rw [image_image, image_image]
    apply image_congr
    intro z hz
    change F (B (a.symm (a (B.symm (C z))))) = F (C z)
    have ha_inv : a.symm (a (B.symm (C z))) = B.symm (C z) := a.left_inv (has ▸ mem_univ _)
    rw [ha_inv, hLC z (sphere_subset_closedBall hz)]
  obtain ⟨J, A, _, hA, hAi, hAf, _⟩ := exists_ball_chart_of_recapped_sphere_ball_complement
    C' b P G hC' (hbs ▸ subset_univ _) hG hdis hPs
    (hPbs.trans hboundary) (by rw [himage]; exact hinter)
  have hAi' : A '' closedBall (0 : E3) 1 =
      F '' (B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) ∪ G '' closedBall (0 : E3) 1 := by
    rw [himage] at hAi
    exact hAi
  have hAf' := hAf.trans hPC's
  let H := F.trans A.symm
  have hFHtarget (z : Z) (hz : z ∈ B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) :
      F z ∈ A.target := by
    have hmem : F z ∈ A '' closedBall (0 : E3) 1 := by
      rw [hAi']
      exact Or.inl (mem_image_of_mem F hz)
    obtain ⟨w, hw, heq⟩ := hmem
    exact heq ▸ A.map_source (hA hw)
  refine ⟨A, hA, hAi', hAf', H, ?_, ?_, ?_⟩
  · exact fun z hz => ⟨hF hz, hFHtarget z hz⟩
  · exact fun z hz => A.right_inv (hFHtarget z hz)
  · intro z hz
    obtain ⟨w, hw, heq⟩ := hAf'.symm ▸ mem_image_of_mem F hz
    change A.symm.toPartialEquiv (F z) ∈ sphere (0 : E3) 1
    rw [← heq]
    exact (A.toPartialEquiv.left_inv (hA (sphere_subset_closedBall hw))).symm ▸ hw

end

section

variable {Z M N : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]
  [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N] [T2Space N]

theorem exists_ball_chart_of_recapped_nested_ball_complements
    (C B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hG : closedBall (0 : E3) 1 ⊆ G.source)
    (hF : (C '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hside : (B '' ball (0 : E3) 1)ᶜ ⊆ (C '' closedBall (0 : E3) 1)ᶜ)
    {K : Set M}
    (hKi : F '' (B '' closedBall (0 : E3) 1)ᶜ = interior K)
    (hKf : F '' (B '' sphere (0 : E3) 1) = frontier K)
    (hP : F '' (C '' ball (0 : E3) 1)ᶜ \ interior K ⊆ P.source)
    (hboundary : P '' frontier K = G '' sphere (0 : E3) 1)
    (hinter : P '' (F '' (C '' ball (0 : E3) 1)ᶜ \ interior K) ∩
      G '' closedBall (0 : E3) 1 ⊆ G '' sphere (0 : E3) 1) :
    ∃ (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N ∞)
      (H : PartialDiffeomorph (𝓡 3) (𝓡 3) M E3 ∞),
      closedBall (0 : E3) 1 ⊆ A.source ∧
      A '' closedBall (0 : E3) 1 =
        P '' (F '' (C '' ball (0 : E3) 1)ᶜ \ interior K) ∪ G '' closedBall (0 : E3) 1 ∧
      A '' sphere (0 : E3) 1 = P '' (F '' (C '' sphere (0 : E3) 1)) ∧
      F '' (C '' ball (0 : E3) 1)ᶜ \ interior K ⊆ H.source ∧
      (∀ x ∈ F '' (C '' ball (0 : E3) 1)ᶜ \ interior K, A (H x) = P x) ∧
      ∀ x ∈ F '' (C '' sphere (0 : E3) 1), H x ∈ sphere (0 : E3) 1 := by
  have hnest : C '' closedBall (0 : E3) 1 ⊆ B '' ball (0 : E3) 1 := by
    intro x hx
    by_contra hn
    exact hside hn hx
  have hBcomp : (B '' closedBall (0 : E3) 1)ᶜ ⊆ (C '' ball (0 : E3) 1)ᶜ := by
    intro x hx hxC
    exact hx (image_mono ball_subset_closedBall
      (hnest (image_mono ball_subset_closedBall hxC)))
  have hmodel : F '' (B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) =
      F '' (C '' ball (0 : E3) 1)ᶜ \ interior K := by
    rw [← hKi]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz.2, rfl⟩, ?_⟩
      rintro ⟨y, hy, hyz⟩
      have he := F.toPartialEquiv.injOn (hF (hBcomp hy)) (hF hz.2) hyz
      exact hy (he.symm ▸ hz.1)
    · rintro ⟨⟨z, hz, rfl⟩, hn⟩
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      by_contra hzB
      exact hn ⟨z, hzB, rfl⟩
  have hFP : B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1 ⊆ (F.trans P).source := by
    intro z hz
    exact ⟨hF hz.2, hP (hmodel ▸ mem_image_of_mem F hz)⟩
  have hbound : (F.trans P) '' (B '' sphere (0 : E3) 1) = G '' sphere (0 : E3) 1 := by
    change (P ∘ F) '' (B '' sphere (0 : E3) 1) = _
    rw [image_comp, hKf, hboundary]
  have hFPimage : (F.trans P) '' (B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1) =
      P '' (F '' (C '' ball (0 : E3) 1)ᶜ \ interior K) := by
    change (P ∘ F) '' _ = _
    rw [image_comp, hmodel]
  obtain ⟨A, hA, hAc, hAf, J, hJ, hAJ, hJS⟩ :=
    exists_ball_chart_of_recapped_nested_ball_shell C B (F.trans P) G hC hB hG hnest hFP hbound
      (by rw [hFPimage]; exact hinter)
  let H := F.symm.trans J
  have hcoord (x : M) (hx : x ∈ F '' (C '' ball (0 : E3) 1)ᶜ \ interior K) :
      F.symm x ∈ B '' closedBall (0 : E3) 1 \ C '' ball (0 : E3) 1 := by
    obtain ⟨z, hz, hzx⟩ := hmodel.symm ▸ hx
    rw [← hzx]
    have he : F.symm.toPartialEquiv (F.toPartialEquiv z) = z := F.toPartialEquiv.left_inv (hF hz.2)
    change F.symm.toPartialEquiv (F.toPartialEquiv z) ∈ _
    rw [he]
    exact hz
  refine ⟨A, H, hA, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hFPimage] at hAc
  · change A '' sphere (0 : E3) 1 = (P ∘ F) '' (C '' sphere (0 : E3) 1) at hAf
    rw [image_comp] at hAf
    exact hAf
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hx.1
    exact ⟨hzx ▸ F.map_source (hF hz), hJ (hcoord x hx)⟩
  · intro x hx
    have he := hAJ (F.symm x) (hcoord x hx)
    change A (J (F.symm x)) = P x
    refine he.trans ?_
    change P (F (F.symm x)) = P x
    obtain ⟨z, hz, hzx⟩ := hx.1
    have hcancel : F.toPartialEquiv (F.symm.toPartialEquiv x) = x :=
      F.toPartialEquiv.right_inv (hzx ▸ F.map_source (hF hz))
    rw [hcancel]
  · rintro x ⟨z, hz, rfl⟩
    have hzsource : z ∈ F.source := by
      apply hF
      rintro ⟨w, hw, hwz⟩
      obtain ⟨v, hv, hvz⟩ := hz
      have he := C.toPartialEquiv.injOn (hC (ball_subset_closedBall hw))
        (hC (sphere_subset_closedBall hv)) (hwz.trans hvz.symm)
      exact (mem_ball_zero_iff.mp (he ▸ hw)).ne (mem_sphere_zero_iff_norm.mp hv)
    change J (F.symm (F z)) ∈ sphere (0 : E3) 1
    have he : F.symm.toPartialEquiv (F.toPartialEquiv z) = z := F.toPartialEquiv.left_inv hzsource
    rw [he]
    exact hJS z hz

end

end DifferentialGeometry.Topology.ThreeManifold
