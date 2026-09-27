import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Algebra.Torsor.Basic

namespace LinearIsometryEquiv

variable {R E F : Type*} [Semiring R]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R F]

instance instMulAction : MulAction (F ≃ₗᵢ[R] F) (E ≃ₗᵢ[R] F) where
  smul g p := p.trans g
  one_smul _ := trans_refl _
  mul_smul _ _ _ := rfl

@[simp]
theorem isometry_smul_apply (g : F ≃ₗᵢ[R] F) (p : E ≃ₗᵢ[R] F) (v : E) :
    (g • p) v = g (p v) := rfl

theorem isometry_smul_def (g : F ≃ₗᵢ[R] F) (p : E ≃ₗᵢ[R] F) : g • p = p.trans g := rfl

instance instSDiv : SDiv (F ≃ₗᵢ[R] F) (E ≃ₗᵢ[R] F) where
  sdiv p q := q.symm.trans p

instance instTorsor [Nonempty (E ≃ₗᵢ[R] F)] :
    Torsor (F ≃ₗᵢ[R] F) (E ≃ₗᵢ[R] F) where
  sdiv_smul' p q := by
    ext v
    exact congrArg p (q.symm_apply_apply v)
  smul_sdiv' g p := by
    ext v
    exact congrArg g (p.apply_symm_apply v)

theorem sdiv_def (p q : E ≃ₗᵢ[R] F) :
    p /ₛ q = q.symm.trans p := rfl

@[simp]
theorem sdiv_apply (p q : E ≃ₗᵢ[R] F) (v : F) :
    (p /ₛ q) v = p (q.symm v) := rfl

variable {E' : Type*} [SeminormedAddCommGroup E'] [Module R E']

theorem trans_isometry_smul (e : E ≃ₗᵢ[R] E') (g : F ≃ₗᵢ[R] F) (p : E' ≃ₗᵢ[R] F) :
    e.trans (g • p) = g • e.trans p := rfl

theorem trans_sdiv (e : E ≃ₗᵢ[R] E') (p q : E' ≃ₗᵢ[R] F) :
    e.trans p /ₛ e.trans q = p /ₛ q := by
  ext v
  exact congrArg p (e.apply_symm_apply (q.symm v))

end LinearIsometryEquiv
