import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSum
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CollarAbsorption

set_option autoImplicit false
noncomputable section
open Set Metric

namespace DifferentialGeometry.Topology.SelfAttachment

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable (M : ConnectedClosedOrientedManifold.{u} 3)
  (p q : OrientedBallChart M.toClosedOrientedManifold)
  (hpq : Disjoint (p.chart '' closedBall 0 2) (q.chart '' closedBall 0 2))

theorem exists_orientedBallChart_family_complement_homeomorph {ι : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (hep : ∀ i x, x ∈ closedBall (0 : E3) 2 → (e i).chart x ∉ p.chart '' closedBall 0 2)
    (heq : ∀ i x, x ∈ closedBall (0 : E3) 2 → (e i).chart x ∉ q.chart '' closedBall 0 2)
    (he : Pairwise fun i j => Disjoint ((e i).chart '' closedBall (0 : E3) 2)
      ((e j).chart '' closedBall (0 : E3) 2)) :
    ∃ s : SmoothSelfAttachment p q hpq boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
        s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold,
    ∃ b : ι → OrientedBallChart (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ,
          (b i).chart x = F.val (coreInclusion p.toBallChart q.toBallChart hpq
            boundaryAttachment.val.toHomeomorph ⟨(e i).chart x, hx⟩)) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' closedBall (0 : E3) 2)
        ((b j).chart '' closedBall (0 : E3) 2)) ∧
      ∃ H : Quot (fun x y : {x : p.toBallChart.DoublePunctured q.toBallChart //
          x.val ∉ ⋃ i, (e i).chart '' ball (0 : E3) 1} =>
          directRel p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph x.val
              y.val) ≃ₜ
        {x : (connectedSum M sphereTwoTimesCircleLift).Carrier //
          x ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1},
        (∀ x, (H (Quot.mk _ x)).val = F.val (coreToBand p.toBallChart q.toBallChart hpq
          boundaryAttachment.val.toHomeomorph x.val)) ∧
        (∀ i z (_ : z ∈ closedBall (0 : E3) 2)
          (hx : (e i).chart z ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ)
          (hu : (e i).chart z ∉ ⋃ j, (e j).chart '' ball (0 : E3) 1),
          (H (Quot.mk _ ⟨⟨(e i).chart z, hx⟩, hu⟩)).val = (b i).chart z) := by
  obtain ⟨s, F, hF⟩ := exists_smoothSelfAttachment_orientedDiffeomorph_retaining_charts M p q hpq
  have havoid (i : ι) (x : E3) (hx : x ∈ closedBall (0 : E3) 2) :
      (e i).chart x ∉ p.chart '' closedBall 0 1 ∪ q.chart '' closedBall 0 1 := by
    rintro (hp | hq)
    · exact hep i x hx ((image_mono (closedBall_subset_closedBall (by norm_num))) hp)
    · exact heq i x hx ((image_mono (closedBall_subset_closedBall (by norm_num))) hq)
  obtain ⟨b, hb⟩ := hF e havoid
  let U : Set (p.toBallChart.DoublePunctured q.toBallChart) :=
    {x | x.val ∈ ⋃ i, (e i).chart '' ball (0 : E3) 1}
  have hU : IsOpen U := (isOpen_iUnion fun i => (e i).toBallChart.isOpen_chart_image_ball).preimage
    continuous_subtype_val
  have hball : ball (0 : E3) 1 ⊆ closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hUp (x : p.toBallChart.DoublePunctured q.toBallChart) (hx : x ∈ U) :
      x.val ∉ p.chart '' closedBall (0 : E3) 2 := by
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    exact hzx ▸ hep i z (hball hz)
  have hUq (x : p.toBallChart.DoublePunctured q.toBallChart) (hx : x ∈ U) :
      x.val ∉ q.chart '' closedBall (0 : E3) 2 := by
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    exact hzx ▸ heq i z (hball hz)
  let H₀ := directBandComplementHomeomorph p.toBallChart q.toBallChart hpq
    boundaryAttachment.val.toHomeomorph U hU hUp hUq
  have hmem (y : Quotient p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph) :
      y ∈ coreInclusion p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph '' U ↔
      F.val y ∈ ⋃ i, (b i).chart '' ball (0 : E3) 1 := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
      obtain ⟨hz', hbz⟩ := hb i z (hball hz)
      refine mem_iUnion.mpr ⟨i, z, hz, ?_⟩
      exact hbz.trans (congrArg F.val (congrArg
        (coreInclusion p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph)
          (Subtype.ext hzx)))
    · intro hy
      obtain ⟨i, z, hz, hzy⟩ := mem_iUnion.mp hy
      obtain ⟨hz', hbz⟩ := hb i z (hball hz)
      refine ⟨⟨(e i).chart z, hz'⟩, mem_iUnion.mpr ⟨i, z, hz, rfl⟩, ?_⟩
      exact F.val.injective (hbz.symm.trans hzy)
  let H₁ := F.val.toHomeomorph.subtype
    (p := fun y => y ∉ coreInclusion p.toBallChart q.toBallChart hpq
      boundaryAttachment.val.toHomeomorph '' U)
    (q := fun y => y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1)
    (fun y => not_congr (hmem y))
  let H := H₀.trans H₁
  refine ⟨s, F, b, hb, ?_, H, fun _ => rfl, ?_⟩
  · intro i j hij
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ ⟨w, hw, hwx⟩
    obtain ⟨hz', hbz⟩ := hb i z hz
    obtain ⟨hw', hbw⟩ := hb j w hw
    have hco := F.val.injective (hbz.symm.trans ((hzx.trans hwx.symm).trans hbw))
    have hev := congrArg Subtype.val
      (coreInclusion_injective p.toBallChart q.toBallChart hpq
          boundaryAttachment.val.toHomeomorph hco)
    exact disjoint_left.mp (he hij) ⟨z, hz, hev⟩ ⟨w, hw, rfl⟩
  · intro i z hz hx hu
    change F.val (coreToBand p.toBallChart q.toBallChart hpq
      boundaryAttachment.val.toHomeomorph ⟨(e i).chart z, hx⟩) = _
    obtain ⟨hx', hbz⟩ := hb i z hz
    exact (congrArg F.val (coreToBand_of_not_mem_chart_image p.toBallChart q.toBallChart hpq
      boundaryAttachment.val.toHomeomorph ⟨(e i).chart z, hx⟩ (hep i z hz) (heq i z
          hz))).trans hbz.symm

end DifferentialGeometry.Topology.SelfAttachment
