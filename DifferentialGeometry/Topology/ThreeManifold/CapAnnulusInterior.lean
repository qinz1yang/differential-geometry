import DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import DifferentialGeometry.Topology.Manifold.ClosedBall.BallChart
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

set_option autoImplicit false
noncomputable section

open Set Metric Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "PI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2
private local instance sphereDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem exists_capInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    ∃ φ : _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N.Carrier ∞,
      φ.source = ball 0 1 ∧
      φ.target = (C.cap b ∘ B) '' {x : ClosedCell 3 | ‖x.val‖ < 1} ∧
      ∀ (x : E3) (hx : ‖x‖ < 1), φ x = C.cap b (B ⟨x, hx.le⟩) :=
  Manifold.exists_partialDiffeomorph_of_closedCell_embedding (C.cap b ∘ B)
    (Manifold.isSmoothEmbedding_diffeomorph_precomp (C.cap b) (C.cap_embedding b) B)

def capInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N.Carrier ∞ :=
  (C.exists_capInteriorChart b B).choose

@[simp] theorem capInteriorChart_source (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    (C.capInteriorChart b B).source = ball 0 1 :=
  (C.exists_capInteriorChart b B).choose_spec.1

@[simp] theorem capInteriorChart_target (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    (C.capInteriorChart b B).target = (C.cap b ∘ B) '' {x : ClosedCell 3 | ‖x.val‖ < 1} :=
  (C.exists_capInteriorChart b B).choose_spec.2.1

theorem capInteriorChart_apply (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) {x : E3} (hx : ‖x‖ < 1) :
    C.capInteriorChart b B x = C.cap b (B ⟨x, hx.le⟩) :=
  (C.exists_capInteriorChart b B).choose_spec.2.2 x hx

private theorem norm_sphere_smul (q : Sphere × ℝ) (hq : 0 < q.2) :
    ‖q.2 • q.1.val‖ = q.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, norm_eq_of_mem_sphere, mul_one]

def capAnnulusInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere) :
    _root_.PartialDiffeomorph PI (𝓡 3) (Sphere × ℝ) N.Carrier ∞ :=
  (Manifold.spherePolarChart (n := 2) v).trans (C.capInteriorChart b B)

@[simp] theorem capAnnulusInteriorChart_source (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere) :
    (C.capAnnulusInteriorChart b B v).source = {q | q.2 ∈ Ioo (0 : ℝ) 1} := by
  change {q : Sphere × ℝ | 0 < q.2} ∩ (Manifold.spherePolarChart (n := 2) v) ⁻¹'
    (C.capInteriorChart b B).source = _
  rw [C.capInteriorChart_source]
  ext q
  constructor
  · rintro ⟨h0,h1⟩
    exact ⟨h0, by simpa only [mem_preimage, Manifold.spherePolarChart_apply,
      mem_ball_zero_iff, norm_sphere_smul q h0] using h1⟩
  · rintro ⟨h0,h1⟩
    refine ⟨h0, ?_⟩
    change q.2 • q.1.val ∈ ball (0 : E3) 1
    rwa [mem_ball_zero_iff, norm_sphere_smul q h0]

theorem capAnnulusInteriorChart_apply (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere)
    (q : Sphere × ℝ) (hq : q.2 ∈ Ioo (0 : ℝ) 1) :
    C.capAnnulusInteriorChart b B v q = C.cap b (B ⟨q.2 • q.1.val, by
      rw [norm_sphere_smul q hq.1]
      exact hq.2.le⟩) :=
  by
    change C.capInteriorChart b B (q.2 • q.1.val) = _
    exact C.capInteriorChart_apply b B (by rw [norm_sphere_smul q hq.1]; exact hq.2)

theorem isLocalDiffeomorphAt_capAnnulusInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere)
    {q : Sphere × ℝ} (hq : q.2 ∈ Ioo (0 : ℝ) 1) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞ (C.capAnnulusInteriorChart b B v) q :=
  (C.capAnnulusInteriorChart b B v).isLocalDiffeomorphAt _ _ ∞ (by
    rw [C.capAnnulusInteriorChart_source]
    exact hq)

theorem cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall
    (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x)
    (x : ClosedCell 3) (hx : 1 / 4 < ‖x.val‖) :
    C.cap b (B x) ∉ ⋃ b', (C.capBallChart b').chart '' closedBall (0 : E3) 1 := by
  intro h
  obtain ⟨b', y, hy, heq⟩ := mem_iUnion.mp h
  let r : ℝ := if b'.2 then 1 / 4 else -(1 / 4)
  have habs : |r| = 1 / 4 := by dsimp only [r]; cases b'.2 <;> norm_num
  have hyn : ‖r • y‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, habs]
    have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    linarith
  let z : ClosedCell 3 := ⟨r • y, by linarith⟩
  have hz : ‖z.val‖ ≤ 1 / 4 := hyn
  have hc : (C.capBallChart b').chart y = C.cap b' z :=
    C.capBallChart_apply b' y (by change ‖r • y‖ < 1; linarith)
  have hcaps : C.cap b' z = C.cap b (B x) := hc.symm.trans heq
  by_cases hb : b' = b
  · subst b'
    have hzx : z = B x := (C.cap_embedding b).isEmbedding.injective hcaps
    have hxz : x = z := B.injective (hzx.symm.trans (hsmall z hz).symm)
    rw [hxz] at hx
    exact not_lt_of_ge hz hx
  · exact Set.disjoint_left.mp (C.cap_disjoint hb) ⟨z,hcaps⟩ ⟨B x,rfl⟩

theorem capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall
    (b : T.Boundary) (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (v : Sphere)
    (q : Sphere × ℝ) (hq : q.2 ∈ Ioo (1 / 4 : ℝ) 1) :
    C.capAnnulusInteriorChart b B v q ∉
      ⋃ b', (C.capBallChart b').chart '' closedBall (0 : E3) 1 := by
  have hq0 : 0 < q.2 := lt_trans (by norm_num) hq.1
  rw [C.capAnnulusInteriorChart_apply b B v q ⟨hq0,hq.2⟩]
  apply C.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall b B.toHomeomorph hsmall
  change 1 / 4 < ‖q.2 • q.1.val‖
  rw [norm_sphere_smul q hq0]
  exact hq.1

end DifferentialGeometry.Topology.SphericalCapping
