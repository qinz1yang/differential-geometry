import Batteries.Tactic.Alias
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry

variable {𝕜 B EB HB F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, NormedAddCommGroup (V b)] [∀ b, NormedSpace 𝕜 (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

theorem contMDiff_fiberInclusion (b : B) {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, V b) (IB.prod 𝓘(𝕜, F)) n (TotalSpace.mk b : V b → TotalSpace F V) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  exact (VectorBundle.continuousLinearEquivAt 𝕜 F V b).contDiff.contMDiff.contMDiffAt

def vectorBundleFiberDiffeomorph [Subsingleton B] (b : B) {n : ℕ∞ω} :
    V b ≃ₘ^n⟮𝓘(𝕜, V b), IB.prod 𝓘(𝕜, F)⟯ TotalSpace F V := by
  let e : V b ≃ TotalSpace F V := Equiv.ofBijective (TotalSpace.mk b)
    ⟨TotalSpace.mk_injective b, by
      rintro ⟨x, v⟩
      cases Subsingleton.elim x b
      exact ⟨v, rfl⟩⟩
  refine ⟨e, contMDiff_fiberInclusion b, ?_⟩
  intro p
  have hc := (Bundle.contMDiffAt_totalSpace.mp
    (contMDiffAt_id : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (id : TotalSpace F V → TotalSpace F V) p)).2
  have hpb : p.proj = b := Subsingleton.elim _ _
  dsimp only [id] at hc
  rw [hpb] at hc
  have hs := (VectorBundle.continuousLinearEquivAt 𝕜 F V b).symm.contDiff.contMDiff.contMDiffAt.comp p hc
  convert hs using 1
  ext q
  apply (VectorBundle.continuousLinearEquivAt 𝕜 F V b).injective
  dsimp only [Function.comp_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change (trivializationAt F V b (e (e.symm q))).2 = _
  rw [e.apply_symm_apply]

@[simp]
theorem vectorBundleFiberDiffeomorph_apply [Subsingleton B] (b : B) {n : ℕ∞ω} (v : V b) :
    vectorBundleFiberDiffeomorph (IB := IB) (F := F) (n := n) b v = TotalSpace.mk b v :=
  rfl

@[simp]
theorem vectorBundleFiberDiffeomorph_symm_mk [Subsingleton B] (b : B) {n : ℕ∞ω} (v : V b) :
    (vectorBundleFiberDiffeomorph (IB := IB) (F := F) (n := n) b).symm (TotalSpace.mk b v) = v :=
  (vectorBundleFiberDiffeomorph (IB := IB) (F := F) (n := n) b).symm_apply_apply v

end DifferentialGeometry

namespace DifferentialGeometry.Geometry

alias contMDiff_fiberInclusion := DifferentialGeometry.contMDiff_fiberInclusion
@[reducible] alias vectorBundleFiberDiffeomorph := DifferentialGeometry.vectorBundleFiberDiffeomorph
alias vectorBundleFiberDiffeomorph_apply := DifferentialGeometry.vectorBundleFiberDiffeomorph_apply
alias vectorBundleFiberDiffeomorph_symm_mk := DifferentialGeometry.vectorBundleFiberDiffeomorph_symm_mk

end DifferentialGeometry.Geometry
