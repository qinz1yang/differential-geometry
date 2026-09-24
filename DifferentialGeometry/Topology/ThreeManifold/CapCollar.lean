import DifferentialGeometry.Topology.ThreeManifold.CapShell
import DifferentialGeometry.Topology.Manifold.ClosedBall.Collar

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private local instance capClosedCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
private local instance capClosedCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem exists_capCollar (b : T.Boundary) :
    ∃ d : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) ((C.cap b) ∘ sphereToClosedCell),
      ∃ hwidth : d.radius ≤ 1 / 2,
        (∀ p : S2 × symmetricOpenInterval d.radius, ∀ hp : 0 ≤ p.2.val,
          d.toFun p = C.cap b ⟨(1 - p.2.val) • p.1.val, by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (by linarith [p.2.property.2] : 0 < 1 - p.2.val),
              norm_eq_of_mem_sphere, mul_one]
            linarith⟩) ∧
        (∀ z, d.toFun (z, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩) =
          C.coreInclusion (T.coreBoundarySphere b (C.attaching b z))) ∧
        (∀ p : S2 × symmetricOpenInterval d.radius, 0 < p.2.val →
          d.toFun p = C.capShellMap b
            ((if b.2 then p.1 else -p.1), 4 * (1 - p.2.val))) ∧
        ∀ (x : T.core) (hx : C.coreInclusion x ∈ d.neighborhood),
          ((d.toDiffeomorph.symm ⟨C.coreInclusion x, hx⟩).2 : ℝ) ≤ 0 := by
  obtain ⟨d, hwidth, hd⟩ :=
    Manifold.exists_smoothTwoSidedCollar_of_closedCell_embedding (C.cap b) (C.cap_embedding b)
  refine ⟨d, hwidth, hd, ?_, ?_, ?_⟩
  · intro z
    exact (d.toFun_zero z).trans (C.boundary_eq b z)
  · intro p hp
    have hr : 4 * (1 - p.2.val) ∈ Ioo (0 : ℝ) 4 := by
      constructor <;> nlinarith [p.2.property.2]
    erw [hd p hp.le, C.capShellMap_eq_cap b _ hr]
    apply congrArg (C.cap b)
    apply Subtype.ext
    dsimp only
    cases b.2 with
    | true =>
      change (1 - p.2.val) • p.1.val = (1 / 4 : ℝ) • ((4 * (1 - p.2.val)) • p.1.val)
      rw [smul_smul]
      congr 1
      ring
    | false =>
      change (1 - p.2.val) • p.1.val = (-(1 / 4 : ℝ)) • ((4 * (1 - p.2.val)) • (-p.1.val))
      simp only [smul_neg, neg_smul, neg_neg]
      rw [smul_smul]
      congr 1
      ring
  · intro x hx
    let q := d.toDiffeomorph.symm ⟨C.coreInclusion x, hx⟩
    have hq : d.toFun q = C.coreInclusion x :=
      congrArg Subtype.val (d.toDiffeomorph.apply_symm_apply ⟨C.coreInclusion x, hx⟩)
    by_contra hnot
    have hpos : 0 < q.2.val := lt_of_not_ge hnot
    have heq := (hd q hpos.le).symm.trans hq
    let y : ClosedCell 3 := ⟨(1 - q.2.val) • q.1.val, by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith [q.2.property.2] : 0 < 1 - q.2.val),
        norm_eq_of_mem_sphere, mul_one]
      linarith⟩
    have hy : ‖y.val‖ < 1 := by
      change ‖(1 - q.2.val) • q.1.val‖ < 1
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith [q.2.property.2] : 0 < 1 - q.2.val),
        norm_eq_of_mem_sphere, mul_one]
      linarith
    have hboth : C.cap b y ∈ range C.coreInclusion ∩ range (C.cap b) :=
      ⟨⟨x, heq.symm⟩, ⟨y, rfl⟩⟩
    rw [C.core_cap_intersection b] at hboth
    obtain ⟨z, hz⟩ := hboth
    have hcap : C.cap b (sphereToClosedCell ((C.attaching b).symm z)) = C.cap b y := by
      rw [C.boundary_eq b ((C.attaching b).symm z), Diffeomorph.apply_symm_apply]
      exact hz
    have hn := congrArg (fun y : ClosedCell 3 => ‖y.val‖)
      ((C.cap_embedding b).isEmbedding.injective hcap)
    have hz1 : ‖(sphereToClosedCell ((C.attaching b).symm z)).val‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ((C.attaching b).symm z).property
    rw [hz1] at hn
    exact (ne_of_lt hy) hn.symm

end DifferentialGeometry.Topology.SphericalCapping
