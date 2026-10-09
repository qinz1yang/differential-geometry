import Mathlib.Topology.Algebra.MulAction
import Mathlib.GroupTheory.GroupAction.Defs

namespace MulAction

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [ContinuousSMul G X] in
private theorem section_inv_mul_mem_stabilizer (o : X) (s : X → G)
    (hs : ∀ x, s x • o = x) (g : G) : (s (g • o))⁻¹ * g ∈ stabilizer G o := by
  rw [mem_stabilizer_iff, mul_smul]
  calc
    (s (g • o))⁻¹ • (g • o) = (s (g • o))⁻¹ • (s (g • o) • o) :=
      congrArg (fun x => (s (g • o))⁻¹ • x) (hs (g • o)).symm
    _ = o := inv_smul_smul _ _

def orbitSectionHomeomorph (o : X) (s : X → G) (hs : ∀ x, s x • o = x)
    (hc : Continuous s) : X × stabilizer G o ≃ₜ G where
  toFun z := s z.1 * z.2
  invFun g := (g • o, ⟨(s (g • o))⁻¹ * g, section_inv_mul_mem_stabilizer o s hs g⟩)
  left_inv := by
    rintro ⟨x, k⟩
    have hk : (k : G) • o = o := k.property
    have hx : (s x * (k : G)) • o = x := by rw [mul_smul, hk, hs]
    apply Prod.ext
    · exact hx
    · apply Subtype.ext
      change (s ((s x * (k : G)) • o))⁻¹ * (s x * (k : G)) = (k : G)
      rw [hx, inv_mul_cancel_left]
  right_inv g := by
    change s (g • o) * ((s (g • o))⁻¹ * g) = g
    exact mul_inv_cancel_left _ _
  continuous_toFun := (hc.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (continuous_id.smul continuous_const).prodMk
    (((hc.comp (continuous_id.smul continuous_const)).inv.mul continuous_id).subtype_mk _)

@[simp]
theorem orbitSectionHomeomorph_apply (o : X) (s : X → G) (hs : ∀ x, s x • o = x)
    (hc : Continuous s) (x : X) (k : stabilizer G o) :
    orbitSectionHomeomorph o s hs hc (x, k) = s x * k := rfl

end MulAction
