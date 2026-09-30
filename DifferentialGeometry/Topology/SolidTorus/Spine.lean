import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Topology.Homotopy.ConvexProduct

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

def IsSpine (S J : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (φ : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ S)
    (p : EuclideanSpace ℝ (Fin 2)),
    p ∈ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
    J = Subtype.val '' (φ '' {q | (q.1 : EuclideanSpace ℝ (Fin 2)) = p})

private abbrev DiskModel := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
private abbrev CircleModel := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

open Classical in
theorem IsSpine.exists_homotopyEquiv_leftInverse
    {S J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsSpine S J) (hJS : J ⊆ S) :
    ∃ (e : S ≃ₕ J), Function.LeftInverse e
      (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) := by
  obtain ⟨φ, p, hp, hJset⟩ := hJ
  let p' : DiskModel := ⟨p, interior_subset hp⟩
  let i : C(J, S) :=
    ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let j : CircleModel ≃ₜ J :=
    { toFun := fun q =>
        ⟨(φ (p', q) : EuclideanSpace ℝ (Fin 3)), by
          rw [hJset]
          exact ⟨φ (p', q), ⟨(p', q), rfl, rfl⟩, rfl⟩⟩
      invFun := fun y =>
        (φ.symm (⟨(y : EuclideanSpace ℝ (Fin 3)), hJS y.property⟩ : S)).2
      left_inv := by
        intro q
        apply Subtype.ext
        change ((φ.symm (φ (p', q))).2 : EuclideanSpace ℝ (Fin 2)) = q
        exact congrArg Subtype.val (congrArg Prod.snd (φ.symm_apply_apply (p', q)))
      right_inv := by
        intro y
        let ys : S := ⟨(y : EuclideanSpace ℝ (Fin 3)), hJS y.property⟩
        have hy : (y : EuclideanSpace ℝ (Fin 3)) ∈
            Subtype.val '' (φ '' {q | q.1 = p}) := hJset ▸ y.property
        obtain ⟨z, ⟨q, hq, hqφ⟩, hyz⟩ := hy
        have hzy : z = ys := by
          apply Subtype.ext
          exact hyz
        have hqeq : q = φ.symm ys := by
          apply φ.injective
          rw [φ.apply_symm_apply]
          exact hqφ.trans hzy
        have hqp : q.1 = p' := Subtype.ext hq
        have harg : (p', (φ.symm ys).2) = q := by
          apply Prod.ext
          · exact hqp.symm
          · exact (congrArg Prod.snd hqeq).symm
        apply Subtype.ext
        change (φ (p', (φ.symm ys).2) : EuclideanSpace ℝ (Fin 3)) = y
        rw [harg]
        exact (congrArg Subtype.val hqφ).trans hyz }
  let e₁ : S ≃ₕ (DiskModel × CircleModel) := φ.symm.toHomotopyEquiv
  let e₂ : (DiskModel × CircleModel) ≃ₕ (CircleModel × DiskModel) :=
    (Homeomorph.prodComm DiskModel CircleModel).toHomotopyEquiv
  let e₃ : (CircleModel × DiskModel) ≃ₕ CircleModel :=
    DifferentialGeometry.HomotopyEquiv.productConvex CircleModel
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) p'
  let e₄ : CircleModel ≃ₕ J := j.toHomotopyEquiv
  let e := e₁.trans (e₂.trans (e₃.trans e₄))
  refine ⟨e, ?_⟩
  intro x
  have hx : (x : EuclideanSpace ℝ (Fin 3)) ∈
      Subtype.val '' (φ '' {q | q.1 = p}) := hJset ▸ x.property
  obtain ⟨y, ⟨q, hq, hqφ⟩, hxy⟩ := hx
  have hqeq : q = φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hJS x.property⟩ : S) := by
    apply φ.injective
    rw [φ.apply_symm_apply]
    exact hqφ.trans (Subtype.ext hxy)
  have hqp : q.1 = p' := Subtype.ext hq
  simp only [ContinuousMap.coe_mk]
  apply Subtype.ext
  change (φ (p', (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hJS x.property⟩ : S)).2) :
      EuclideanSpace ℝ (Fin 3)) = x
  have harg : (p', (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hJS x.property⟩ : S)).2) = q := by
    apply Prod.ext
    · exact hqp.symm
    · exact (congrArg Prod.snd hqeq).symm
  rw [harg]
  exact (congrArg Subtype.val hqφ).trans hxy

end DifferentialGeometry.Topology.PiecewiseLinear
