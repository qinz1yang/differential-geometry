import DifferentialGeometry.Topology.Manifold.HalfClosedIntervalSmoothMaps
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold

theorem contMDiff_halfClosedInterval_inclusion {a b c : ℝ}
    (hab : a < b) (hac : a < c) (hbc : b ≤ c) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := halfClosedIntervalChartedSpace hab
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico a c) := halfClosedIntervalChartedSpace hac
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (fun p : Ico a b => (⟨p.val, p.property.1, p.property.2.trans_le hbc⟩ : Ico a c)) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := halfClosedIntervalChartedSpace hab
  exact contMDiff_halfClosedInterval_of_val (𝓡∂ 1) hac _
    (isSmoothEmbedding_halfClosedInterval_inclusion hab).contMDiff

theorem mfderiv_halfClosedInterval_inclusion_bijective {a b c : ℝ}
    (hab : a < b) (hac : a < c) (hbc : b ≤ c) (p : Ico a b) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := halfClosedIntervalChartedSpace hab
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico a c) := halfClosedIntervalChartedSpace hac
    Bijective (mfderiv (𝓡∂ 1) (𝓡∂ 1)
      (fun q : Ico a b => (⟨q.val, q.property.1, q.property.2.trans_le hbc⟩ : Ico a c)) p) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := halfClosedIntervalChartedSpace hab
  let : IsManifold (𝓡∂ 1) ∞ (Ico a b) := halfClosedInterval_isManifold hab
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico a c) := halfClosedIntervalChartedSpace hac
  let : IsManifold (𝓡∂ 1) ∞ (Ico a c) := halfClosedInterval_isManifold hac
  let j : Ico a b → Ico a c := fun q => ⟨q.val, q.property.1, q.property.2.trans_le hbc⟩
  have hj : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ j := contMDiff_halfClosedInterval_inclusion hab hac hbc
  have he : extChartAt (𝓡∂ 1) (j p) ∘ j = extChartAt (𝓡∂ 1) p := by
    funext q
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (extChartAt (𝓡∂ 1) (j p) (j q)) 0 = (extChartAt (𝓡∂ 1) p q) 0
    rw [halfClosedInterval_extChartAt_apply hac, halfClosedInterval_extChartAt_apply hab]
  have hc := mfderiv_comp p
    ((contMDiffAt_extChartAt (I := 𝓡∂ 1) (x := j p) (n := ∞)).mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp))
  rw [he] at hc
  have hi : Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) j p) := by
    intro v w hv
    apply (isInvertible_mfderiv_extChartAt (I := 𝓡∂ 1) (mem_extChartAt_source p)).injective
    rw [hc]
    exact congrArg (mfderiv (𝓡∂ 1) (𝓡 1) (extChartAt (𝓡∂ 1) (j p)) (j p)) hv
  let D : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv (𝓡∂ 1) (𝓡∂ 1) j p
  exact D.toLinearMap.linearEquivOfInjective hi rfl |>.bijective
end DifferentialGeometry.Topology.Manifold
