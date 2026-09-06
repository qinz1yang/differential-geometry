import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_perp_basis
    (g : SmoothRiemannianMetric I M) (p : M) (u : TangentSpace I p)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hu : 0 < g.inner p u u) :
    ∃ B : Module.Basis (Option (Fin (Module.finrank Real E - 1))) Real E,
      B none = (u : E) ∧ ∀ i, B (some i) = (v i : E) := by
  classical
  let _ : FiniteDimensional ℝ (TangentSpace I p) := by
    change FiniteDimensional ℝ E
    infer_instance
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  let φ : TangentSpace I p →ₗ[Real] Real := (g.inner p u).toLinearMap
  have hVker : Set.range v ⊆ LinearMap.ker φ := by
    rintro y ⟨i, rfl⟩
    change g.inner p u (v i) = 0
    exact hperp i
  have hZspan : u ∉ Submodule.span Real (Set.range v) := by
    intro hmem
    have hker : u ∈ LinearMap.ker φ := (Submodule.span_le.2 hVker) hmem
    have hzero : g.inner p u u = 0 := hker
    exact hu.ne' hzero
  have hWLI : LinearIndependent Real
      (fun o : Option (Fin (Module.finrank Real E - 1)) =>
        Option.casesOn' o u v) := hv.option hZspan
  have hdim : 0 < Module.finrank Real (TangentSpace I p) :=
    Module.finrank_pos_iff.mpr ⟨u, 0, hu_ne⟩
  have hcardW : Fintype.card (Option (Fin (Module.finrank Real E - 1))) =
      Module.finrank Real (TangentSpace I p) := by
    rw [Fintype.card_option, Fintype.card_fin]
    exact Nat.sub_add_cancel hdim
  let b : Module.Basis (Option (Fin (Module.finrank Real E - 1))) Real
      (TangentSpace I p) :=
    basisOfLinearIndependentOfCardEqFinrank hWLI hcardW
  have hb : ∀ o, b o = Option.casesOn' o u v :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hWLI hcardW)
  refine ⟨b, ?_, ?_⟩
  · exact hb none
  · intro i; exact hb (some i)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
