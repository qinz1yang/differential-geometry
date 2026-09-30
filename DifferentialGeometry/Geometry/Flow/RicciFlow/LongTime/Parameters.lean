import DifferentialGeometry.Geometry.Collapse.Parameters

set_option autoImplicit false
namespace GC.LongTime

def lateDerivativeOrder : ℕ := 20

theorem staticDerivativeOrder_le_lateDerivativeOrder :
    DifferentialGeometry.Geometry.Collapse.staticDerivativeOrder ≤ lateDerivativeOrder := by decide

end GC.LongTime
