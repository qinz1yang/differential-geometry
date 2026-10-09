import DifferentialGeometry.Topology.ThreeManifold.PairedBallPuncturedAtlas
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DirectSmooth
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Pullback
import DifferentialGeometry.Topology.Manifold.Sigma
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Cover

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment)

def seamCore : TopologicalSpace.Opens (Σ v, PuncturedFactor N endpoint chart v) :=
  ⟨(range (fun z => (⟨endpoint s false, boundaryPoint N endpoint chart hdisj s false z⟩ :
      Σ v, PuncturedFactor N endpoint chart v)) ∪
    range (fun z => (⟨endpoint s true, boundaryPoint N endpoint chart hdisj s true z⟩ :
      Σ v, PuncturedFactor N endpoint chart v)))ᶜ,
    ((isCompact_range (continuous_sigmaMk.comp (continuous_boundaryPoint N endpoint chart hdisj s false))).isClosed.union
      (isCompact_range (continuous_sigmaMk.comp (continuous_boundaryPoint N endpoint chart hdisj s true))).isClosed).isOpen_compl⟩

def seamCoreInclusion : seamCore N endpoint chart hdisj s → Quot (seamRel N endpoint chart hdisj s a) :=
  fun x => Quot.mk _ x.val

include hdisj in
private theorem radial_not_mem_holes (e : E) (b : Bool)
    (z : sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ Icc 1 2) :
    flagMap N endpoint chart (e, b) (r • z.val) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 := by
  intro hx
  obtain ⟨p, v, hv, heq⟩ := mem_iUnion.mp hx
  have hrad : r • z.val ∈ closedBall (0 : E3) 2 := by
    rw [mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2
  by_cases hp : p = (e, b)
  · subst p
    have hh : (chart e b).chart v = (chart e b).chart (r • z.val) := eq_of_heq (Sigma.mk.inj heq).2
    have hvsrc := (chart e b).toBallChart.ball_subset_source hv
    have he := (chart e b).chart.injOn hvsrc ((chart e b).closedBall_subset_source hrad) hh
    rw [he, mem_ball, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])] at hv
    exact (not_lt_of_ge hr.1) hv
  · exact disjoint_left.mp (hdisj hp)
      ⟨v, ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hv, heq⟩
      ⟨r • z.val, hrad, rfl⟩

def radialPoint (e : E) (b : Bool) (z : sphere (0 : E3) 1)
    (r : ℝ) (hr : r ∈ Icc 1 2) : PuncturedFactor N endpoint chart (endpoint e b) :=
  ⟨(chart e b).chart (r • z.val), radial_not_mem_holes N endpoint chart hdisj e b z r hr⟩

theorem radialPoint_one (e : E) (b : Bool) (z : sphere (0 : E3) 1) :
    radialPoint N endpoint chart hdisj e b z 1 (by norm_num) =
      boundaryPoint N endpoint chart hdisj e b z := by
  apply Subtype.ext
  change (chart e b).chart ((1 : ℝ) • z.val) = (chart e b).chart z.val
  rw [one_smul]

def seamChart (p : SelfAttachment.directSeamDomain) : Quot (seamRel N endpoint chart hdisj s a) :=
  if ht : 0 ≤ p.val.2 then
    Quot.mk _ ⟨endpoint s false,
      radialPoint N endpoint chart hdisj s false p.val.1 (1 + p.val.2)
        ⟨by linarith, by linarith [p.property.2.2]⟩⟩
  else
    Quot.mk _ ⟨endpoint s true,
      radialPoint N endpoint chart hdisj s true (a.val p.val.1) (1 - p.val.2)
        ⟨by linarith, by linarith [p.property.2.1]⟩⟩

theorem seamChart_zero (z : SelfAttachment.Sphere (n := 3)) :
    seamChart N endpoint chart hdisj s a ⟨(z, 0), mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ =
      Quot.mk _ ⟨endpoint s false, boundaryPoint N endpoint chart hdisj s false z⟩ := by
  rw [seamChart, dite_eq_left le_rfl]
  apply congrArg (Quot.mk _)
  apply congrArg (Sigma.mk (endpoint s false))
  apply Subtype.ext
  change (chart s false).chart ((1 + 0 : ℝ) • z.val) = (chart s false).chart z.val
  simp only [add_zero, one_smul]

theorem seam_local_maps_cover (q : Quot (seamRel N endpoint chart hdisj s a)) :
    (∃ x, seamCoreInclusion N endpoint chart hdisj s a x = q) ∨
      ∃ z, seamChart N endpoint chart hdisj s a
        ⟨(z, 0), mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ = q := by
  induction q using Quot.inductionOn with
  | h x =>
    by_cases hx : x ∈ seamCore N endpoint chart hdisj s
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · right
      have hx' : x ∈ range (fun z => (⟨endpoint s false, boundaryPoint N endpoint chart hdisj s false z⟩ :
          Σ v, PuncturedFactor N endpoint chart v)) ∪
        range (fun z => (⟨endpoint s true, boundaryPoint N endpoint chart hdisj s true z⟩ :
          Σ v, PuncturedFactor N endpoint chart v)) := not_not.mp hx
      rcases hx' with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨z, seamChart_zero N endpoint chart hdisj s a z⟩
      · refine ⟨a.val.symm z, ?_⟩
        rw [seamChart_zero]
        apply Quot.sound
        refine ⟨a.val.symm z, Or.inl ⟨rfl, ?_⟩⟩
        rw [a.val.apply_symm_apply]

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2)
      (flagMap N endpoint chart q '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2))
  (s : E) (a : BoundaryAttachment)

theorem mem_seamCore_iff (x : Σ v, PuncturedFactor N endpoint chart v) :
    x ∈ seamCore N endpoint chart hdisj s ↔
      (⟨x.fst, x.snd.val⟩ : Σ v, (N v).Carrier) ∉
        flagMap N endpoint chart (s, false) '' closedBall 0 1 ∪
          flagMap N endpoint chart (s, true) '' closedBall 0 1 := by
  have heq (b : Bool) :
      x ∈ range (fun z => (⟨endpoint s b, boundaryPoint N endpoint chart hdisj s b z⟩ :
        Σ v, PuncturedFactor N endpoint chart v)) ↔
        (⟨x.fst, x.snd.val⟩ : Σ v, (N v).Carrier) ∈ flagMap N endpoint chart (s, b) '' closedBall 0 1 := by
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, sphere_subset_closedBall z.property, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hge : 1 ≤ ‖y‖ := by
        by_contra h
        exact x.snd.property (mem_iUnion.mpr ⟨(s, b), y, mem_ball_zero_iff.mpr (not_le.mp h), hyx⟩)
      let z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        ⟨y, mem_sphere_zero_iff_norm.mpr (le_antisymm (mem_closedBall_zero_iff.mp hy) hge)⟩
      refine ⟨z, ?_⟩
      have hi : Function.Injective (fun q : Σ v, PuncturedFactor N endpoint chart v =>
          (⟨q.fst, q.snd.val⟩ : Σ v, (N v).Carrier)) := by
        rintro ⟨v, p⟩ ⟨w, q⟩ h
        have hv : v = w := congrArg Sigma.fst h
        subst w
        exact congrArg (Sigma.mk v) (Subtype.ext (eq_of_heq (Sigma.mk.inj h).2))
      exact hi hyx
  exact not_congr (or_congr (heq false) (heq true))

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment)

theorem range_seamCoreInclusion_union_range_seamChart :
    range (seamCoreInclusion N endpoint chart hdisj s a) ∪
      range (seamChart N endpoint chart hdisj s a) = univ := by
  apply eq_univ_of_forall
  intro q
  rcases seam_local_maps_cover N endpoint chart hdisj s a q with h | ⟨z, hz⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, hz⟩

variable [∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v)]

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 3) Y]

variable [ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a))]

theorem isLocalDiffeomorph_seamQuotient_of_comp_local_maps
    (hcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (seamCoreInclusion N endpoint chart hdisj s a))
    (hseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a))
    (f : Quot (seamRel N endpoint chart hdisj s a) → Y)
    (hfcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (f ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hfseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (f ∘ seamChart N endpoint chart hdisj s a)) :
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ f :=
  DifferentialGeometry.isLocalDiffeomorph_of_comp_cover _ _
    (range_seamCoreInclusion_union_range_seamChart N endpoint chart hdisj s a)
    hcore hseam f hfcore hfseam

def seamDiffeomorphOfLocalMaps
    (h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ Y)
    (hcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (seamCoreInclusion N endpoint chart hdisj s a))
    (hseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a))
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (h ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (h ∘ seamChart N endpoint chart hdisj s a)) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a)) Y ∞ :=
  (isLocalDiffeomorph_seamQuotient_of_comp_local_maps N endpoint chart hdisj s a
    hcore hseam h hhcore hhseam).diffeomorphOfBijective h.bijective

theorem seamDiffeomorphOfLocalMaps_apply
    (h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ Y)
    (hcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (seamCoreInclusion N endpoint chart hdisj s a))
    (hseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a))
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (h ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (h ∘ seamChart N endpoint chart hdisj s a))
    (x : Quot (seamRel N endpoint chart hdisj s a)) :
    seamDiffeomorphOfLocalMaps N endpoint chart hdisj s a h hcore hseam hhcore hhseam x = h x := rfl

omit [ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a))] in
theorem exists_smooth_seam_atlas_of_comp_local_maps [IsManifold (𝓡∂ 3) ∞ Y]
    (h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ Y)
    (hhcore : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (h ∘ seamCoreInclusion N endpoint chart hdisj s a))
    (hhseam : IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (h ∘ seamChart N endpoint chart hdisj s a)) :
    ∃ C : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := C
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a)) Y ∞,
          ∀ x, D x = h x := by
  let C := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := EuclideanHalfSpace 3) h
  let _ := C
  let _ := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡∂ 3) (n := ∞) h
  refine ⟨C, inferInstance, ?_, ?_,
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡∂ 3) (n := ∞) h, fun _ => rfl⟩
  · exact isLocalDiffeomorph_pullback_of_comp h _ hhcore
  · exact isLocalDiffeomorph_pullback_of_comp h _ hhseam

end DifferentialGeometry.Topology.PairedBallGluing
