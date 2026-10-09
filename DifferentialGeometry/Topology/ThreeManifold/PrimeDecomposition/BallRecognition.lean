import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.CutCapExistence
import DifferentialGeometry.Topology.ThreeManifold.SmoothUncapping
import DifferentialGeometry.Topology.ThreeManifold.SphereBallAvoidingPoint
import DifferentialGeometry.Topology.ThreeManifold.NestedBallRecapping
import DifferentialGeometry.Topology.Manifold.SphereCollarCoordinates
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent

/-!
# A sphere whose capped side is a `3`-sphere bounds a ball

Let `E` be a spherical cut-cap transition with a single separating tube, and suppose the capped
component on one side is diffeomorphic to `S³`. In that component the cap boundary sphere misses
the cap centre, so the smooth Schoenflies theorem in `S³` gives a ball bounded by it on the core
side; the core neighbourhood partial diffeomorphism of the uncapping construction carries this
ball back to `M`, where it is bounded by the boundary sphere of the tube on that side. A collar
of the middle sphere built from the tube itself supplies the shell between the middle sphere and
that boundary sphere, and recapping the shell with the ball shows that the middle sphere bounds
a ball. This proves `CapSideBallRecognition`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Pointwise

namespace GC.Endpoint

universe u

local notation "E³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1



private def homothetyTwo : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ E³ ∞ :=
  Diffeomorph.toPartialDiffeomorph
    { toFun x := (2 : ℝ) • x
      invFun x := (1 / 2 : ℝ) • x
      left_inv x := by simp [smul_smul]
      right_inv x := by simp [smul_smul]
      contMDiff_toFun := (contDiff_const_smul (2 : ℝ)).contMDiff
      contMDiff_invFun := (contDiff_const_smul (1 / 2 : ℝ)).contMDiff }

private theorem homothetyTwo_apply (x : E³) : homothetyTwo x = (2 : ℝ) • x := rfl

theorem sphereBoundsBall_of_collar_of_ballChart {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace E³ X] {e : S² → X} (c : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e)
    (hc : 1 < c.radius) (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ X ∞)
    (hG : closedBall (0 : E³) 1 ⊆ G.source)
    (hGs : G '' sphere (0 : E³) 1 =
      range fun z => c.toFun (z, ⟨-1, by linarith [c.radius_pos], by linarith⟩))
    (hout : ∀ z (s : ℝ) (hs : -1 < s ∧ s ≤ 0),
      c.toFun (z, ⟨s, by linarith [hs.1], by linarith [hs.2, c.radius_pos]⟩) ∉
        G '' closedBall (0 : E³) 1) :
    SphereBoundsBall e := by
  let v : S² := ⟨EuclideanSpace.single 0 1, by simp⟩
  let F := c.radialPartialDiffeomorph v
  let C : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ E³ ∞ :=
    (Diffeomorph.refl (𝓡 3) E³ ∞).toPartialDiffeomorph
  have hCimg : ∀ s : Set E³, C '' s = s := fun s => image_id s
  have hFr : ∀ (z : S²) (r : ℝ) (h₁ : 1 ≤ r) (h₂ : r ≤ 2),
      F (r • (z : E³)) = c.toFun (z, ⟨1 - r, by linarith [c.radius_pos], by linarith⟩) :=
    fun z r h₁ h₂ => c.radialPartialDiffeomorph_apply v z r (by linarith) _
  have hpolar : ∀ y : E³, y ≠ 0 → ∃ z : S², y = ‖y‖ • (z : E³) := by
    intro y hy
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    refine ⟨⟨‖y‖⁻¹ • y, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · change y = ‖y‖ • ‖y‖⁻¹ • y
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hFs : F '' (homothetyTwo '' sphere (0 : E³) 1) = G '' sphere (0 : E³) 1 := by
    rw [hGs]
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [homothetyTwo_apply, hFr ⟨y, hy⟩ 2 (by norm_num) le_rfl]
      exact congrArg (fun t => c.toFun (⟨y, hy⟩, t)) (Subtype.ext (by norm_num))
    · rintro ⟨z, rfl⟩
      refine ⟨homothetyTwo z, ⟨z, z.2, rfl⟩, ?_⟩
      rw [homothetyTwo_apply, hFr z 2 (by norm_num) le_rfl]
      exact congrArg (fun t => c.toFun (z, t)) (Subtype.ext (by norm_num))
  have hnested : C '' closedBall (0 : E³) 1 ⊆ homothetyTwo '' ball (0 : E³) 1 := by
    rw [hCimg]
    intro x hx
    refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul]
      have := mem_closedBall_zero_iff.mp hx
      norm_num
      linarith
    · rw [homothetyTwo_apply, smul_smul]
      norm_num
  have hF : homothetyTwo '' closedBall (0 : E³) 1 \ C '' ball (0 : E³) 1 ⊆ F.source := by
    rw [hCimg]
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    rw [homothetyTwo_apply] at hy ⊢
    have hx' := mem_closedBall_zero_iff.mp hx
    have hy' : 1 ≤ ‖(2 : ℝ) • x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hy
    rw [norm_smul] at hy'
    rw [c.mem_radialPartialDiffeomorph_source_iff, norm_smul]
    refine ⟨smul_ne_zero two_ne_zero (fun h => absurd hy' (by simp [h])), ?_, ?_⟩ <;>
      norm_num at hy' ⊢ <;> linarith [c.radius_pos]
  have hinter : F '' (homothetyTwo '' closedBall (0 : E³) 1 \ C '' ball (0 : E³) 1) ∩
      G '' closedBall (0 : E³) 1 ⊆ G '' sphere (0 : E³) 1 := by
    rintro _ ⟨⟨_, ⟨⟨x, hx, rfl⟩, hy⟩, rfl⟩, hG'⟩
    rw [hCimg] at hy
    rw [homothetyTwo_apply] at hy hG' ⊢
    have hx' := mem_closedBall_zero_iff.mp hx
    have hy' : 1 ≤ ‖(2 : ℝ) • x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hy
    have hne : (2 : ℝ) • x ≠ 0 := fun h => absurd hy' (by simp [h])
    obtain ⟨z, hz⟩ := hpolar _ hne
    have hle : ‖(2 : ℝ) • x‖ ≤ 2 := by rw [norm_smul]; norm_num; linarith
    set r := ‖(2 : ℝ) • x‖ with hr
    rw [hz, hFr z r hy' hle] at hG' ⊢
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd hG' (hout z _ ⟨by linarith, by linarith⟩)
    · rw [hGs]
      exact ⟨z, congrArg (fun t => c.toFun (z, t))
        (Subtype.ext (show (-1 : ℝ) = 1 - r by linarith))⟩
  obtain ⟨A, hA, -, hAs, -⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_shell
      C homothetyTwo F G (fun _ _ => trivial) (fun _ _ => trivial) hG hnested hF hFs hinter
  refine ⟨A, hA, ?_⟩
  rw [hAs, hCimg]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, (c.radialPartialDiffeomorph_sphere v ⟨y, hy⟩).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, c.radialPartialDiffeomorph_sphere v z⟩




private local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

theorem exists_ballChart_capSide_of_sphere {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) (a : E.tubes.Index) (side : Bool)
    [Subsingleton E.tubes.Index] (hsep : E.cutCapVertex a false ≠ E.cutCapVertex a true)
    (hS : Nonempty ((E.capped.component (E.cutCapVertex a side)).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      standardThreeSphereLift.{u}.Carrier)) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E³ M.Carrier ∞,
      closedBall (0 : E³) 1 ⊆ G.source ∧
      G '' sphere (0 : E³) 1 = range (E.tubes.boundarySphere (a, side)) ∧
      G '' closedBall (0 : E³) 1 ⊆ E.tubes.core := by
  classical
  obtain ⟨D⟩ := hS
  let b : E.tubes.Boundary := (a, side)
  let v : S² := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨F₀, hF₀s, hF₀t, hF₀, hF₀symm⟩ :=
    E.capping.exists_core_neighborhood_partialDiffeomorph (E.tubes.coreBoundarySphere b v)
  let σM : S² → M.Carrier := E.tubes.boundarySphere b
  have hσM : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ σM :=
    E.tubes.toTopological.isSmoothEmbedding_boundarySphere b (E.tubes.smooth b.1)
  let σN : S² → E.capped.Carrier := fun z =>
    E.capping.coreInclusion (E.tubes.coreBoundarySphere b z)
  have hσNeq : σN = F₀ ∘ σM := funext fun z => (hF₀ (E.tubes.coreBoundarySphere b z)).symm
  have hσN : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ σN := by
    rw [hσNeq]
    exact isSmoothEmbedding_comp_partialDiffeomorph F₀ hσM
      (by rintro _ ⟨z, rfl⟩; exact hF₀s (E.tubes.boundarySphere_mem_core b z))
  have hσNcap : ∀ z,
      σN z = E.capping.cap b (sphereToClosedCell ((E.capping.attaching b).symm z)) := by
    intro z
    rw [E.capping.boundary_eq b, Diffeomorph.apply_symm_apply]
  let Kset := ClosedOrientedManifold.componentOpen E.capped (E.cutCapVertex a side)
  have hcapK : ∀ y, E.capping.cap b y ∈ Kset := fun y =>
    E.capRange_subset_componentSet a side ⟨y, rfl⟩
  let σK : S² → Kset := fun z => ⟨σN z, (hσNcap z) ▸ hcapK _⟩
  have hσK : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ σK :=
    Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡 2) (𝓡 3) Kset σK hσN
  let D₀ : Kset ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    D.trans standardThreeSphereLiftDiffeomorph.symm
  let e₃ := D₀ ∘ σK
  have he₃ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₃ :=
    Topology.Manifold.isSmoothEmbedding_diffeomorph_comp (𝓡 2) (𝓡 3) σK hσK D₀
  let c₀ : ClosedCell 3 := ⟨0, by simp⟩
  let pK : Kset := ⟨E.capping.cap b c₀, hcapK c₀⟩
  have hcapinj := (E.capping.cap_embedding b).isEmbedding.injective
  have hnorm : ∀ z, ‖((sphereToClosedCell z : ClosedCell 3) : E³)‖ = 1 := fun z => by
    simp [sphereToClosedCell]
  have hp : D₀ pK ∉ range e₃ := by
    rintro ⟨z, hz⟩
    have h1 : σK z = pK := D₀.injective hz
    have h2 : σN z = E.capping.cap b c₀ := congrArg Subtype.val h1
    rw [hσNcap z] at h2
    have h3 := congrArg (fun y : ClosedCell 3 => ‖(y : E³)‖) (hcapinj h2)
    simp only [hnorm, c₀, norm_zero] at h3
    exact one_ne_zero h3
  obtain ⟨B₃, hB₃, hB₃s, hpB⟩ :=
    ThreeManifold.exists_ball_chart_of_sphere_embedding_avoiding_point e₃ he₃ (D₀ pK) hp
  let hKne : Nonempty Kset := ⟨pK⟩
  let GN := (B₃.trans D₀.symm.toPartialDiffeomorph).trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) Kset hKne)
  have hGNs : closedBall (0 : E³) 1 ⊆ GN.source := fun x hx =>
    ⟨⟨hB₃ hx, trivial⟩, trivial⟩
  have hGNapp : ∀ x, GN x = (D₀.symm (B₃ x) : E.capped.Carrier) := fun x => rfl
  have hGNsph : GN '' sphere (0 : E³) 1 = range σN := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ : B₃ x ∈ range e₃ := hB₃s ▸ ⟨x, hx, rfl⟩
      refine ⟨z, ?_⟩
      rw [hGNapp, ← hz]
      change σN z = (D₀.symm (D₀ (σK z)) : E.capped.Carrier)
      rw [Diffeomorph.symm_apply_apply]
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx, hxz⟩ : e₃ z ∈ B₃ '' sphere (0 : E³) 1 := hB₃s ▸ ⟨z, rfl⟩
      refine ⟨x, hx, ?_⟩
      rw [hGNapp, hxz]
      change (D₀.symm (D₀ (σK z)) : E.capped.Carrier) = σN z
      rw [Diffeomorph.symm_apply_apply]
  have hpN : E.capping.cap b c₀ ∉ GN '' closedBall (0 : E³) 1 := by
    rintro ⟨x, hx, hxp⟩
    rw [hGNapp] at hxp
    have h1 : D₀.symm (B₃ x) = pK := Subtype.ext hxp
    exact hpB ⟨x, hx, by rw [← h1, Diffeomorph.apply_symm_apply]⟩
  have hGNK : GN '' closedBall (0 : E³) 1 ⊆
      ClosedOrientedManifold.componentSet E.capped (E.cutCapVertex a side) := by
    rintro _ ⟨x, -, rfl⟩
    exact (D₀.symm (B₃ x)).2
  let Y : Set E.capped.Carrier := range fun x : ball (0 : E³) 1 =>
    E.capping.cap b ⟨x.1, le_of_lt (mem_ball_zero_iff.mp x.2)⟩
  have hYc : IsPreconnected Y := by
    have : PreconnectedSpace (ball (0 : E³) 1) :=
      Subtype.preconnectedSpace (convex_ball (0 : E³) 1).isPreconnected
    exact isPreconnected_range ((E.capping.cap b).continuous.comp
      (continuous_subtype_val.subtype_mk _))
  have hpY : E.capping.cap b c₀ ∈ Y := ⟨⟨0, mem_ball_self one_pos⟩, rfl⟩
  have hYσ : ∀ y ∈ Y, y ∉ range σN := by
    rintro _ ⟨x, rfl⟩ ⟨z, hz⟩
    rw [hσNcap] at hz
    have h3 := congrArg (fun y : ClosedCell 3 => ‖(y : E³)‖) (hcapinj hz)
    simp only [hnorm] at h3
    have := mem_ball_zero_iff.mp x.2
    change 1 = ‖(x : E³)‖ at h3
    linarith
  have hU₁ : IsOpen (GN '' ball (0 : E³) 1) :=
    GN.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hGNs)
  have hK₂ : IsCompact (GN '' closedBall (0 : E³) 1) :=
    (isCompact_closedBall (0 : E³) 1).image_of_continuousOn
      (GN.contMDiffOn_toFun.continuousOn.mono hGNs)
  have hYsub : Y ⊆ GN '' ball (0 : E³) 1 ∪ (GN '' closedBall (0 : E³) 1)ᶜ := by
    intro y hy
    by_cases h : y ∈ GN '' closedBall (0 : E³) 1
    · left
      obtain ⟨x, hx, rfl⟩ := h
      rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
      · exact ⟨x, mem_ball_zero_iff.mpr hlt, rfl⟩
      · exact absurd (hGNsph ▸ ⟨x, mem_sphere_zero_iff_norm.mpr heq, rfl⟩) (hYσ _ hy)
    · exact Or.inr h
  have hY₂ : Y ⊆ (GN '' closedBall (0 : E³) 1)ᶜ := by
    rcases hYc.subset_or_subset hU₁ hK₂.isClosed.isOpen_compl
      (Set.disjoint_compl_right_iff_subset.mpr (image_mono ball_subset_closedBall)) hYsub with
      h | h
    · exact absurd (image_mono ball_subset_closedBall (h hpY)) hpN
    · exact h
  have hcore : GN '' closedBall (0 : E³) 1 ⊆ range E.capping.coreInclusion := by
    intro y hy
    have hmem : y ∈ range E.capping.coreInclusion ∪ ⋃ b', range (E.capping.cap b') :=
      E.capping.exhaustive ▸ mem_univ y
    rcases hmem with h | h
    · exact h
    · obtain ⟨⟨a', s'⟩, w, rfl⟩ := mem_iUnion.mp h
      obtain rfl : a = a' := Subsingleton.elim _ _
      by_cases hs : s' = side
      · subst hs
        rcases (w.2).lt_or_eq with hlt | heq
        · exact absurd hy (hY₂ ⟨⟨w.1, mem_ball_zero_iff.mpr hlt⟩, rfl⟩)
        · let z : S² := ⟨w.1, mem_sphere_zero_iff_norm.mpr heq⟩
          have hw : w = sphereToClosedCell z := Subtype.ext rfl
          rw [hw, E.capping.boundary_eq]
          exact ⟨_, rfl⟩
      · exfalso
        have h1 := (ClosedOrientedManifold.mem_componentSet _ _ _).mp
          (E.capRange_subset_componentSet a s' ⟨w, rfl⟩)
        have h2 := (ClosedOrientedManifold.mem_componentSet _ _ _).mp (hGNK hy)
        have h3 := h1.symm.trans h2
        cases s' <;> cases side
        · exact hs rfl
        · exact hsep h3
        · exact hsep h3.symm
        · exact hs rfl
  let G := GN.trans F₀.symm
  have hGs : closedBall (0 : E³) 1 ⊆ G.source := fun x hx =>
    ⟨hGNs hx, hF₀t (hcore ⟨x, hx, rfl⟩)⟩
  refine ⟨G, hGs, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ : GN x ∈ range σN := hGNsph ▸ ⟨x, hx, rfl⟩
      refine ⟨z, ?_⟩
      change σM z = F₀.symm (GN x)
      rw [← hz]
      exact (hF₀symm (E.tubes.coreBoundarySphere b z)).symm
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx, hxz⟩ : σN z ∈ GN '' sphere (0 : E³) 1 := hGNsph ▸ ⟨z, rfl⟩
      refine ⟨x, hx, ?_⟩
      change F₀.symm (GN x) = σM z
      rw [hxz]
      exact hF₀symm (E.tubes.coreBoundarySphere b z)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := hcore ⟨x, hx, rfl⟩
    change F₀.symm (GN x) ∈ E.tubes.core
    rw [← hc, hF₀symm]
    exact c.2


private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private def bufferedEquivCollar :
    bufferedCylinder (1 / 2) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯
      (S² × symmetricOpenInterval 3) where
  toFun q := (q.1.1, ⟨q.1.2, by
    have h : -(1 / 2 : ℝ)⁻¹ - 1 < q.1.2 ∧ q.1.2 < (1 / 2 : ℝ)⁻¹ + 1 := q.2
    norm_num at h
    exact h⟩)
  invFun p := ⟨(p.1, p.2.1), by
    have h : -3 < p.2.1 ∧ p.2.1 < 3 := p.2.2
    change -(1 / 2 : ℝ)⁻¹ - 1 < p.2.1 ∧ p.2.1 < (1 / 2 : ℝ)⁻¹ + 1
    norm_num
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (contMDiff_fst.comp contMDiff_subtype_val).prodMk ?_
    exact (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval 3) _).mp
      (contMDiff_snd.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff (bufferedCylinder (1 / 2)) _).mp ?_
    exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)

theorem exists_collar_tubeMiddleSphere {M : ClosedOrientedManifold.{u} 3}
    (T : SphericalTubeSystem M) (a : T.Index) :
    ∃ c : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (tubeMiddleSphere T a), 1 < c.radius ∧
      ∀ z (s : ℝ) (hs : s ∈ symmetricOpenInterval c.radius), |s| ≤ 5 / 4 →
        ∃ h : s ∈ Icc (-2 : ℝ) 2, c.toFun (z, ⟨s, hs⟩) = T.tube a (z, ⟨s, h⟩) := by
  obtain ⟨f, hf, hs, -, heq⟩ := exists_bufferedChart_eqOn_tube (T.tube a) (T.smooth a)
  let c : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (tubeMiddleSphere T a) :=
    { radius := 3
      radius_pos := by norm_num
      neighborhood := hs.image
      toDiffeomorph := bufferedEquivCollar.symm.trans
        (Topology.Manifold.diffeomorphOntoImage f hs hf.injective)
      zero_eq := fun z => heq (z, ⟨0, by norm_num, by norm_num⟩) (by norm_num) (by norm_num) }
  refine ⟨c, by norm_num [c], fun z s hs habs => ?_⟩
  have h₁ := (abs_le.mp habs).1
  have h₂ := (abs_le.mp habs).2
  exact ⟨⟨by linarith, by linarith⟩, heq (z, ⟨s, by linarith, by linarith⟩) h₁ h₂⟩

theorem capSideBallRecognition : CapSideBallRecognition.{u} := by
  intro M Q E a side hsub hsep hS
  obtain ⟨G, hG, hGs, hGc⟩ := exists_ballChart_capSide_of_sphere E a side hsep hS
  obtain ⟨c, hc, hct⟩ := exists_collar_tubeMiddleSphere E.tubes a
  have hband : ∀ z (t : ℝ) (h : t ∈ Icc (-2 : ℝ) 2), -1 < t → t < 1 →
      E.tubes.tube a (z, ⟨t, h⟩) ∉ G '' closedBall (0 : E³) 1 := fun z t h h₁ h₂ hmem =>
    hGc hmem (mem_iUnion.mpr ⟨a, ⟨(z, ⟨t, h⟩), ⟨h₁, h₂⟩, rfl⟩⟩)
  cases side
  · refine sphereBoundsBall_of_collar_of_ballChart c hc G hG ?_ ?_
    · rw [hGs]
      congr 1
      funext z
      obtain ⟨h, hh⟩ := hct z (-1) ⟨by linarith, by linarith⟩ (by norm_num)
      rw [hh]
      rfl
    · intro z s hs
      obtain ⟨h, hh⟩ := hct z s ⟨by linarith [hs.1], by linarith [hs.2]⟩
        (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      rw [hh]
      exact hband z s h hs.1 (by linarith [hs.2])
  · let c' := c.reverse
    have hc' : 1 < c'.radius := hc
    have hct' : ∀ z (s : ℝ) (hs : s ∈ symmetricOpenInterval c'.radius), |s| ≤ 5 / 4 →
        ∃ h : -s ∈ Icc (-2 : ℝ) 2,
          c'.toFun (z, ⟨s, hs⟩) = E.tubes.tube a (z, ⟨-s, h⟩) := by
      intro z s hs habs
      have hs' : -c.radius < s ∧ s < c.radius := hs
      exact hct z (-s) ⟨by linarith [hs'.2], by linarith [hs'.1]⟩ (by rwa [abs_neg])
    refine sphereBoundsBall_of_collar_of_ballChart c' hc' G hG ?_ ?_
    · rw [hGs]
      congr 1
      funext z
      obtain ⟨h, hh⟩ := hct' z (-1) ⟨by linarith, by linarith⟩ (by norm_num)
      rw [hh]
      exact congrArg (fun t => E.tubes.tube a (z, t))
        (Subtype.ext (by norm_num [SphericalTubeSystem.boundaryLevel]))
    · intro z s hs
      obtain ⟨h, hh⟩ := hct' z s ⟨by linarith [hs.1], by linarith [hs.2]⟩
        (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      rw [hh]
      exact hband z (-s) h (by linarith [hs.2]) (by linarith [hs.1])

end GC.Endpoint
