import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereRegion
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCircleFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereEdge

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the adapted rim charts

Part B of the circle kind of the S³ inhabitant: the rim charts ADAPTED to the actual rows (lead
decision 02:45; review 49 B.5: the final rim parametrisation need not be a pre-compiled one), over
the adapted corner charts of `sphereCircleRegion`:

  `circRim b e (θ, v) = J(k_{b,e}(v), θ)`  (`J = sphereCircleChart`),

and the rim chart layer `sphereRimLayer : RimChartLayer sphereW sphereEdgeLayer sphereCircleRegion`
for the ACCEPTED handles of `sphereEdgeLayer` (handle `h` = `cycleS3Handle (finTwoEquiv h)`), with
`handleCorner h e = (finTwoEquiv h, e)`: source `rimBox 2` in the rim coordinates, the projection
is the corner chart (`rim_proj` by construction), the rim at `(0, 0)` is the end rim of the
handle, pairwise disjoint targets. The compiled `cycleRimChart` is NOT used (its base trace is not
adapted to the edge height `‖w‖²`, see `state-FC39-CIRC-B.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc

/-- The plane corner chart followed by `(ψ, r) ↦ ℝ²`. -/
def circPlaneE2 (σ σ' : Bool) : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) E2 ∞ :=
  (circPlaneChart σ σ').trans circEquivPD

/-- **The adapted rim chart** of the corner `(b, e)`: `(θ, v) ↦ J(k_{b,e}(v), θ)`. -/
def circRim (b e : Bool) : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (𝓡 3)
    (Circle × (ℝ × ℝ)) sphereW.Carrier ∞ :=
  ((Diffeomorph.prodComm (𝓡 1) 𝓘(ℝ, ℝ × ℝ) Circle (ℝ × ℝ) ∞).toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod (circPlaneE2 b (b ^^ e))
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph)).trans sphereCircleChart

theorem circRim_apply (b e : Bool) (p : Circle × (ℝ × ℝ)) :
    circRim b e p =
      sphereCircleChart (sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) p.2), p.1) :=
  rfl

theorem circRim_chart_source (b e : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    (sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) p.2), p.1) ∈ sphereCircleChart.source := by
  rw [sphereCircleChart_source]
  exact ⟨circPlaneMap_mem_base hp, mem_univ _⟩

theorem mem_circRim_source (b e : Bool) {p : Circle × (ℝ × ℝ)} :
    p ∈ (circRim b e).source ↔ p.2 ∈ rimBox 2 := by
  change (p ∈ univ ∧ (p.2 ∈ rimBox 2 ∧ circPlaneMap b (b ^^ e) p.2 ∈ univ) ∧ p.1 ∈ univ) ∧
    (sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) p.2), p.1) ∈ sphereCircleChart.source ↔ _
  constructor
  · intro hp
    exact hp.1.2.1.1
  · intro hp
    exact ⟨⟨mem_univ _, ⟨hp, mem_univ _⟩, mem_univ _⟩, circRim_chart_source b e hp⟩

theorem mem_circRim_target {b e : Bool} {x : sphereW.Carrier} :
    x ∈ (circRim b e).target ↔ x ∈ sphereCircleChart.target ∧
      sphereCircleEquiv (sphereCircleChart.symm x).1 ∈ circPlaneTarget b (b ^^ e) := by
  change x ∈ sphereCircleChart.target ∧
    ((((sphereCircleChart.symm x).1 ∈ univ ∧
      sphereCircleEquiv (sphereCircleChart.symm x).1 ∈ circPlaneTarget b (b ^^ e)) ∧
        (sphereCircleChart.symm x).2 ∈ univ) ∧ Prod.swap (sphereCircleChart.symm x) ∈ univ) ↔ _
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.1.1.2⟩
  · intro hx
    exact ⟨hx.1, ⟨⟨mem_univ _, hx.2⟩, mem_univ _⟩, mem_univ _⟩

/-- **The projection of the rim chart is the corner chart.** -/
theorem circRim_proj (b e : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    ∃ hx : circRim b e p ∈ sphereCircleDomain,
      sphereCircleProj ⟨circRim b e p, hx⟩ = circCornerChart b e p.2 := by
  refine ⟨sphereCircleChart_mem_domain (circRim_chart_source b e hp), Subtype.ext ?_⟩
  rw [circCornerChart_val b e hp]
  exact sphereCircleProj_chart (circRim_chart_source b e hp)

/-- The rim targets of two different corners are disjoint. -/
theorem circRim_disjoint {b e b' e' : Bool} (h : (b, e) ≠ (b', e')) :
    Disjoint (circRim b e).target (circRim b' e').target := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  rw [mem_circRim_target] at hx hx'
  have hne : (b, b ^^ e) ≠ (b', b' ^^ e') := by
    intro h'
    apply h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    rw [h1] at h2
    have aux : ∀ c f f' : Bool, (c ^^ f) = (c ^^ f') → f = f' := by decide
    exact Prod.ext h1 (aux _ _ _ h2)
  exact Set.disjoint_left.1 (circPlaneTarget_disjoint hne) hx.2 hx'.2

/-! ## The rim at the corner centre is the handle end rim -/

theorem cycleHandleRadius_iccEnd_CIRCB (e : Bool) :
    cycleHandleRadius (iccEnd e : ℝ) = circEndVal e := by
  cases e
  · change cycleHandleRadius 0 = 1
    rw [cycleHandleRadius_inner (by norm_num)]
    norm_num
  · change cycleHandleRadius 1 = 4
    rw [cycleHandleRadius_outer (by norm_num)]
    norm_num

theorem cycleHandleRadius_one_sub_iccEnd_CIRCB (e : Bool) :
    cycleHandleRadius (1 - (iccEnd e : ℝ)) = circEndVal (!e) := by
  cases e
  · change cycleHandleRadius (1 - 0) = 4
    rw [sub_zero, cycleHandleRadius_outer (by norm_num)]
    norm_num
  · change cycleHandleRadius (1 - 1) = 1
    rw [sub_self, cycleHandleRadius_inner (by norm_num)]
    norm_num

theorem unitOf_planeOfCircle_CIRCB (θ : Circle) :
    unitOf (Complex.orthonormalBasisOneI.repr.symm (planeOfCircle θ)) = θ := by
  rw [planeOfCircle, LinearIsometryEquiv.symm_apply_apply]
  apply Circle.ext
  rw [coe_unitOf (Circle.coe_ne_zero θ), Circle.norm_coe, inv_one, one_smul]

/-- The rim chart at the centre. -/
theorem circRim_center (b e : Bool) (θ : Circle) :
    circRim b e (θ, (0, 0)) =
      sphereCircleChart (sphereCircleEquiv.symm (circEndVal b, circEndVal (b ^^ e)), θ) := by
  rw [circRim_apply]
  simp only [circPlaneMap, circCornerInv_zero]

/-- **The rim of the rim chart at `(0, 0)` is the end rim of the handle.** -/
theorem circRim_label (b e : Bool) :
    circRim b e '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => (cycleS3Handle b).map (x, iccEnd e)) '' diskRim := by
  ext z
  constructor
  · rintro ⟨⟨θ, v⟩, hv, rfl⟩
    change v = (0, 0) at hv
    subst hv
    rw [circRim_center]
    cases b
    · refine ⟨⟨planeOfCircle θ, (planeOfCircle_norm_CIRCA θ).le⟩,
        diskRim_iff_FC39P0b.2 (planeOfCircle_norm_CIRCA θ), ?_⟩
      change cycleHandleChart false (planeOfCircle θ, (iccEnd e : ℝ)) = _
      rw [cycleHandleChart_false_eq_circle, planeOfCircle_norm_CIRCA,
        cycleHandleRadius_iccEnd_CIRCB, unitOf_planeOfCircle_CIRCB]
      cases e <;> rfl
    · refine ⟨⟨planeOfCircle (circleAntipode_CIRCA θ),
        (planeOfCircle_norm_CIRCA _).le⟩, diskRim_iff_FC39P0b.2 (planeOfCircle_norm_CIRCA _), ?_⟩
      have hw : planeOfCircle (circleAntipode_CIRCA θ) ≠ 0 := by
        intro h0
        have := planeOfCircle_norm_CIRCA (circleAntipode_CIRCA θ)
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      change cycleHandleChart true (planeOfCircle (circleAntipode_CIRCA θ), (iccEnd e : ℝ)) = _
      rw [cycleHandleChart_true_eq_circle hw, planeOfCircle_norm_CIRCA,
        cycleHandleRadius_one_sub_iccEnd_CIRCB, unitOf_planeOfCircle_CIRCB,
        circleAntipode_antipode_CIRCA]
      norm_num [circEndVal]
  · rintro ⟨x, hx, rfl⟩
    have hn : ‖x.val‖ = 1 := diskRim_iff_FC39P0b.1 hx
    have hw : x.val ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    change cycleHandleChart b (x.val, (iccEnd e : ℝ)) ∈ _
    cases b
    · rw [cycleHandleChart_false_eq_circle, hn, cycleHandleRadius_iccEnd_CIRCB]
      refine ⟨(unitOf (Complex.orthonormalBasisOneI.repr.symm x.val), (0, 0)), rfl, ?_⟩
      rw [circRim_center]
      cases e <;> rfl
    · rw [cycleHandleChart_true_eq_circle hw, hn, cycleHandleRadius_one_sub_iccEnd_CIRCB]
      refine ⟨(circleAntipode_CIRCA (unitOf (Complex.orthonormalBasisOneI.repr.symm x.val)),
        (0, 0)), rfl, ?_⟩
      rw [circRim_center]
      norm_num [circEndVal]

/-! ## The rim chart layer -/

/-- The corner of the end `e` of the handle `h`: `(finTwoEquiv h, e)`. -/
def sphereHandleCorner (h : Fin 2) (e : Bool) : Fin 4 :=
  circCornerEquiv (finTwoEquiv h, e)

theorem sphereHandleCorner_bijective :
    Bijective fun hb : Fin 2 × Bool => sphereHandleCorner hb.1 hb.2 :=
  ((Equiv.prodCongr finTwoEquiv (Equiv.refl Bool)).trans circCornerEquiv).bijective

theorem circCorner_sphereHandleCorner (h : Fin 2) (e : Bool) :
    circCorner (sphereHandleCorner h e) = circCornerChart (finTwoEquiv h) e := by
  rw [circCorner, sphereHandleCorner, Equiv.symm_apply_apply]

/-- **The rim chart layer of the S³ configuration**: the adapted rim charts over the adapted corner
charts, for the accepted handles of `sphereEdgeLayer`. -/
def sphereRimLayer : RimChartLayer sphereW sphereEdgeLayer sphereCircleRegion where
  handleCorner := sphereHandleCorner
  handleCorner_bijective := sphereHandleCorner_bijective
  rimChart h e := circRim (finTwoEquiv h) e
  rim_source h e _ := mem_circRim_source _ _
  rim_proj h e p hp := by
    have hp' := (mem_circRim_source _ _).1 hp
    obtain ⟨hx, hproj⟩ := circRim_proj (finTwoEquiv h) e hp'
    refine ⟨hx, ?_⟩
    exact hproj.trans
      (congrArg (fun φ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) sphereCircleBaseOpens ∞ =>
        φ p.2) (circCorner_sphereHandleCorner h e).symm)
  rim_label h e := circRim_label (finTwoEquiv h) e
  rim_disjoint h e h' e' hne := circRim_disjoint (fun heq => hne (by
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    rw [finTwoEquiv.injective h1, h2]))

theorem sphereRimLayer_rimChart (h : Fin 2) (e : Bool) :
    sphereRimLayer.rimChart h e = circRim (finTwoEquiv h) e :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
