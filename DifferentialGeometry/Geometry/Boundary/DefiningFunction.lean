import DifferentialGeometry.Geometry.Operator.Operators

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Boundary

theorem frontier_levelSet_annulus_subset
    {X : Type*} [TopologicalSpace X]
    {rho : X → Real} (hrho : Continuous rho) {r R : Real} :
    frontier {x | r ≤ rho x ∧ rho x ≤ R} ⊆
      {x | rho x = r ∨ rho x = R} := by
  intro x hx
  let K : Set X := {y | r ≤ rho y ∧ rho y ≤ R}
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const hrho).inter
      (isClosed_le hrho continuous_const)
  have hxK : x ∈ K := by
    have hxcl : x ∈ closure K := frontier_subset_closure hx
    rwa [hKclosed.closure_eq] at hxcl
  by_contra hboundary
  change ¬ (rho x = r ∨ rho x = R) at hboundary
  rw [not_or] at hboundary
  have hrx : r < rho x :=
    lt_of_le_of_ne hxK.1 (Ne.symm hboundary.1)
  have hxR : rho x < R :=
    lt_of_le_of_ne hxK.2 hboundary.2
  let U : Set X := {y | r < rho y} ∩ {y | rho y < R}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const hrho).inter
      (isOpen_lt hrho continuous_const)
  have hUK : U ⊆ K := by
    intro y hy
    exact ⟨hy.1.le, hy.2.le⟩
  have hxU : x ∈ U := ⟨hrx, hxR⟩
  have hxint : x ∈ interior K := interior_maximal hUK hUopen hxU
  exact (mem_frontier_iff_notMem_interior hxK).mp hx hxint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def levelSetOutwardNormal
    (g : SmoothRiemannianMetric I M) (rho : M → Real) (x : M) :
    TangentSpace I x :=
  if 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x) then
    (Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x)))⁻¹ •
        gradientFun (I := I) g rho x
  else
    0

theorem levelSetOutwardNormal_eq
    (g : SmoothRiemannianMetric I M) (rho : M → Real) (x : M)
    (hgrad : 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x)) :
    levelSetOutwardNormal (I := I) g rho x =
      (Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x)))⁻¹ •
          gradientFun (I := I) g rho x := by
  unfold levelSetOutwardNormal
  rw [if_pos hgrad]

theorem levelSetOutwardNormal_unit
    (g : SmoothRiemannianMetric I M) (rho : M → Real) (x : M)
    (hgrad : 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x)) :
    g.inner x (levelSetOutwardNormal (I := I) g rho x)
      (levelSetOutwardNormal (I := I) g rho x) = 1 := by
  let q := g.inner x (gradientFun (I := I) g rho x)
    (gradientFun (I := I) g rho x)
  have hq : 0 < q := hgrad
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsqrt_ne : Real.sqrt q ≠ 0 := ne_of_gt hsqrt
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  rw [levelSetOutwardNormal_eq (I := I) g rho x hgrad]
  change g.inner x ((Real.sqrt q)⁻¹ • gradientFun (I := I) g rho x)
      ((Real.sqrt q)⁻¹ • gradientFun (I := I) g rho x) = 1
  rw [map_smul, ContinuousLinearMap.map_smul]
  change (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = 1
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) =
    q / (Real.sqrt q * Real.sqrt q) by field_simp]
  rw [hsq]
  exact div_self (ne_of_gt hq)

theorem inner_levelSetOutwardNormal_neg
    (g : SmoothRiemannianMetric I M) (rho f : M → Real) (x : M)
    (hgrad : 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x))
    (hneg : g.inner x (gradientFun (I := I) g f x)
      (gradientFun (I := I) g rho x) < 0) :
    g.inner x (gradientFun (I := I) g f x)
      (levelSetOutwardNormal (I := I) g rho x) < 0 := by
  rw [levelSetOutwardNormal_eq (I := I) g rho x hgrad,
    ContinuousLinearMap.map_smul]
  change (Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
    (gradientFun (I := I) g rho x)))⁻¹ *
      g.inner x (gradientFun (I := I) g f x)
        (gradientFun (I := I) g rho x) < 0
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (Real.sqrt_pos.mpr hgrad)) hneg

end DifferentialGeometry.Geometry.Boundary
