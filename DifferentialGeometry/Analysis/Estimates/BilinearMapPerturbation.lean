import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DifferentialGeometry
namespace HCGCompactness

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

theorem bilinPerturb {B : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} (v w : E') :
    |B (A v) (A w) - B v w| ≤
      ‖B‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖) := by
  have hsplit : B (A v) (A w) - B v w
      = B ((A - ContinuousLinearMap.id Real E') v) (A w)
        + B v ((A - ContinuousLinearMap.id Real E') w) := by
    simp only [sub_apply, ContinuousLinearMap.coe_id', id_eq, map_sub, sub_apply]
    abel
  rw [hsplit]
  have h1 : |B ((A - ContinuousLinearMap.id Real E') v) (A w)| ≤
      ‖B‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
    calc
      |B ((A - ContinuousLinearMap.id Real E') v) (A w)|
          ≤ ‖B‖ * ‖(A - ContinuousLinearMap.id Real E') v‖ * ‖A w‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
            gcongr
            · exact ContinuousLinearMap.le_opNorm _ v
            · exact ContinuousLinearMap.le_opNorm A w
  have h2 : |B v ((A - ContinuousLinearMap.id Real E') w)| ≤
      ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖w‖) := by
    calc
      |B v ((A - ContinuousLinearMap.id Real E') w)|
          ≤ ‖B‖ * ‖v‖ * ‖(A - ContinuousLinearMap.id Real E') w‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖w‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ w
  calc
    |B ((A - ContinuousLinearMap.id Real E') v) (A w)
        + B v ((A - ContinuousLinearMap.id Real E') w)|
        ≤ |B ((A - ContinuousLinearMap.id Real E') v) (A w)|
          + |B v ((A - ContinuousLinearMap.id Real E') w)| := abs_add_le _ _
    _ ≤ ‖B‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖v‖) * (‖A‖ * ‖w‖)
        + ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id Real E'‖ * ‖w‖) := add_le_add h1 h2
    _ = ‖B‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) *
        (‖v‖ * ‖w‖) := by ring

theorem quadPerturbTri {B₀ B₁ : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} (v : E') :
    |B₁ (A v) (A v) - B₀ v v| ≤
      (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖v‖) := by
  have h1 := bilinPerturb (B := B₁) (A := A) v v
  have h2 : |B₁ v v - B₀ v v| ≤ ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := by
    have : B₁ v v - B₀ v v = (B₁ - B₀) v v := by
      simp [sub_apply]
    rw [this, ← Real.norm_eq_abs]
    calc
      ‖(B₁ - B₀) v v‖ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm₂ _ v v
      _ = ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := by ring
  calc
    |B₁ (A v) (A v) - B₀ v v|
        = |(B₁ (A v) (A v) - B₁ v v) + (B₁ v v - B₀ v v)| := by ring_nf
    _ ≤ |B₁ (A v) (A v) - B₁ v v| + |B₁ v v - B₀ v v| := abs_add_le _ _
    _ ≤ ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) * (‖v‖ * ‖v‖)
        + ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := add_le_add h1 h2
    _ = (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖v‖) := by ring

theorem bilinPerturbTri {B₀ B₁ : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} (v w : E') :
    |B₁ (A v) (A w) - B₀ v w| ≤
      (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖w‖) := by
  have h1 := bilinPerturb (B := B₁) (A := A) v w
  have h2 : |B₁ v w - B₀ v w| ≤ ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := by
    have hsub : B₁ v w - B₀ v w = (B₁ - B₀) v w := by
      simp [sub_apply]
    rw [hsub, ← Real.norm_eq_abs]
    calc
      ‖(B₁ - B₀) v w‖ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm₂ _ v w
      _ = ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := by ring
  calc
    |B₁ (A v) (A w) - B₀ v w|
        = |(B₁ (A v) (A w) - B₁ v w) + (B₁ v w - B₀ v w)| := by ring_nf
    _ ≤ |B₁ (A v) (A w) - B₁ v w| + |B₁ v w - B₀ v w| := abs_add_le _ _
    _ ≤ ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖)
        + ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := add_le_add h1 h2
    _ = (‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) *
        (‖v‖ * ‖w‖) := by ring

theorem quadPerturbNeumann {B₀ B₁ : E' →L[Real] E' →L[Real] Real}
    {A : E' →L[Real] E'} {ε : Real}
    (hA : ‖A - ContinuousLinearMap.id Real E'‖ ≤ ε) (v : E') :
    |B₁ (A v) (A v) - B₀ v v| ≤
      (‖B₁‖ * ε * (2 + ε) + ‖B₁ - B₀‖) * (‖v‖ * ‖v‖) := by
  refine (quadPerturbTri v).trans ?_
  have hAle : ‖A‖ ≤ 1 + ε := by
    calc
      ‖A‖ = ‖ContinuousLinearMap.id Real E' +
          (A - ContinuousLinearMap.id Real E')‖ := by
            congr 1
            abel
      _ ≤ ‖ContinuousLinearMap.id Real E'‖ +
          ‖A - ContinuousLinearMap.id Real E'‖ := norm_add_le _ _
      _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hA
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hcoef : ‖B₁‖ * ‖A - ContinuousLinearMap.id Real E'‖ * (1 + ‖A‖) ≤
      ‖B₁‖ * ε * (2 + ε) := by
    have h2 : (1 : Real) + ‖A‖ ≤ 2 + ε := by linarith [hAle]
    gcongr
  gcongr

end HCGCompactness
end DifferentialGeometry
