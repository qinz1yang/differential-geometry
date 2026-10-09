import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenCompatP6HC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBodyProducerA6K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelCtimeSelA6K

/-!
# KCONS 助手（O-CH11-KCONS，后缀 `_KC`）

`hRQ_of_hQsrho_KC`：kernel 行 `hRQ : R ≤ c·Qs` ⇐ hgap 的 `R ≤ ρ̃(Tn)⁻²`（`hQρ`）与新增合取
`hQsρ : ρ(Tno)⁻² ≤ Qs`，经 `neckRadius_rescale_inv_sq_P6X` 与 `c·Tn = Tno`。PROVED，无新前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **`hRQ` 助手（`_KC`，PROVED）**。 -/
theorem hRQ_of_hQsrho_KC (q : CutoffParameters) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (Tn Tno R Qs : ℕ → ℝ) (hcT : ∀ n, c n * Tn n = Tno n)
    (hQρ : ∀ n, R n ≤ ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (hQsρ : ∀ n, (q.neckRadius (Tno n) ^ 2)⁻¹ ≤ Qs n) :
    ∀ n, R n ≤ c n * Qs n := fun n => by
  have h := hQρ n
  rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q, hcT n] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hQsρ n) (hc n).le)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
