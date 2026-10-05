import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCornerIndependent
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCorePairs
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallRegular

/-!
The actual handle, ball, and deep core form the genuine global defining family on the whole base.
Their active depth, native pair independence, and true corner centers satisfy the original contract.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

def loopDefining (l : Fin 3) : loopCircleBase → ℝ :=
  ![loopHandleDefining, loopBallDefining, loopCoreDefining] l

theorem loopDefining_smooth (l : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (loopDefining l) := by
  fin_cases l
  · exact loopHandleDefining_smooth
  · exact loopBallDefining_smooth
  · exact loopCoreDefining_smooth

theorem loopDefining_regular (l : Fin 3) (z : loopCircleBase) (hz : loopDefining l z = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (loopDefining l) z ≠ 0 := by
  fin_cases l
  · exact loopHandleDefining_regular z hz
  · exact loopBallDefining_regular z hz
  · exact loopCoreDefining_regular z hz

theorem loopDefining_depth (z : loopCircleBase) :
    (Finset.univ.filter fun l : Fin 3 => loopDefining l z = 0).card ≤ 2 := by
  classical
  by_cases hc : loopCoreDefining z = 0
  · have hs : (Finset.univ.filter fun l : Fin 3 => loopDefining l z = 0) ⊆ {2} := by
      intro l hl
      have hz := (Finset.mem_filter.mp hl).2
      fin_cases l
      · exact False.elim (loopCoreHandle_no_common z hc hz)
      · exact False.elim (loopCoreBall_no_common z hc hz)
      · simp
    exact (Finset.card_le_card hs).trans (by decide)
  · have hs : (Finset.univ.filter fun l : Fin 3 => loopDefining l z = 0) ⊆ {0, 1} := by
      intro l hl
      have hz := (Finset.mem_filter.mp hl).2
      fin_cases l
      · simp
      · simp
      · exact False.elim (hc hz)
    exact (Finset.card_le_card hs).trans (by decide)

theorem loopDefining_independent (z : loopCircleBase) (l l' : Fin 3) (hne : l ≠ l')
    (hl : loopDefining l z = 0) (hl' : loopDefining l' z = 0) :
    Function.Surjective fun w : TangentSpace (𝓡 2) z =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (loopDefining l) z w,
       mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (loopDefining l') z w) := by
  fin_cases l <;> fin_cases l'
  · exact False.elim (hne rfl)
  · exact loopHandleBall_independent z hl hl'
  · exact False.elim (loopCoreHandle_no_common z hl' hl)
  · exact loopBallHandle_independent z hl hl'
  · exact False.elim (hne rfl)
  · exact False.elim (loopCoreBall_no_common z hl' hl)
  · exact False.elim (loopCoreHandle_no_common z hl hl')
  · exact False.elim (loopCoreBall_no_common z hl hl')
  · exact False.elim (hne rfl)

theorem loopDefining_corner_center (z : loopCircleBase) (l l' : Fin 3) (hne : l ≠ l')
    (hl : loopDefining l z = 0) (hl' : loopDefining l' z = 0) :
    ∃ b : Bool, z = loopBaseCorner b (0, 0) := by
  fin_cases l <;> fin_cases l'
  · exact False.elim (hne rfl)
  · exact loopHandleBall_common_center z hl hl'
  · exact False.elim (loopCoreHandle_no_common z hl' hl)
  · exact loopHandleBall_common_center z hl' hl
  · exact False.elim (hne rfl)
  · exact False.elim (loopCoreBall_no_common z hl' hl)
  · exact False.elim (loopCoreHandle_no_common z hl hl')
  · exact False.elim (loopCoreBall_no_common z hl hl')
  · exact False.elim (hne rfl)

theorem loopDefining_chart_first (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopDefining 0 (loopBaseCorner b v) = -v.1 := loopHandleDefining_rim b hv

theorem loopDefining_chart_second (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopDefining 1 (loopBaseCorner b v) = -v.2 := loopBallDefining_rim b hv

theorem loopDefining_chart_other (b : Bool) (l : Fin 3) (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    {v : ℝ × ℝ} (hv : v ∈ rimBox 2) : loopDefining l (loopBaseCorner b v) < 0 := by
  fin_cases l
  · exact False.elim (hl0 rfl)
  · exact False.elim (hl1 rfl)
  · exact loopCoreDefining_corner b hv

end GC.GraphManifold.Assembly
