import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.LocalTrivialization
import DifferentialGeometry.Bundle.SmoothSubbundle.Defs
import DifferentialGeometry.Bundle.Hom.Regularity
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
variable [FiberBundle F V] [VectorBundle ℝ F V]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
variable [IsContMDiffRiemannianBundle I n F V]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [ContMDiffVectorBundle n F V I] in
private theorem contMDiffOn_conj_coframe {U : Set M} {q : ∀ x, V x ≃ₗᵢ[ℝ] G}
    (hq : ∀ w : G, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => TotalSpace.mk' F x ((q x).symm w)) U) (A : G →L[ℝ] G) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x ((q x).symm.conjStarAlgEquiv A)) U := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  have hinv := ContinuousLinearMap.contMDiffOn_bundle_apply_of_pointwise
    (φ := fun x => (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap) hq
  have hforw := LinearIsometryEquiv.contMDiffOn_coframe_to hq
  have hA : ContMDiff (I.prod 𝓘(ℝ, G)) (I.prod 𝓘(ℝ, G)) n
      (fun p : M × G => (p.1, A p.2)) :=
    contMDiff_fst.prodMk (A.contMDiff.comp contMDiff_snd)
  have hmap : ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (fun v : TotalSpace F V => TotalSpace.mk' F v.proj
        ((q v.proj).symm (A (q v.proj v.2)))) (TotalSpace.proj ⁻¹' U) :=
    hinv.comp (hA.comp_contMDiffOn hforw) (fun v hv => ⟨hv, mem_univ _⟩)
  exact ContMDiffOn.clm_bundle_of_map
    (φ := fun x => (q x).symm.conjStarAlgEquiv A) hmap

private theorem map_selfAdjoint_conj
    {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
    (e : P ≃ₗᵢ[ℝ] Q) :
    (selfAdjoint.submodule ℝ (P →L[ℝ] P)).map
      e.conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap =
      selfAdjoint.submodule ℝ (Q →L[ℝ] Q) := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    have hB' : IsSelfAdjoint B := hB
    have hmap : IsSelfAdjoint (e.conjStarAlgEquiv B) := hB'.map e.conjStarAlgEquiv
    exact hmap
  · intro hA
    have hA' : IsSelfAdjoint A := hA
    have hmap : IsSelfAdjoint (e.conjStarAlgEquiv.symm A) :=
      hA'.map e.conjStarAlgEquiv.symm
    refine ⟨e.conjStarAlgEquiv.symm A, hmap, ?_⟩
    exact e.conjStarAlgEquiv.apply_symm_apply A

namespace Bundle

def selfAdjointSubbundle :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    ContMDiffVectorSubbundle (I := I) (F := F →L[ℝ] F)
      (V := fun x => V x →L[ℝ] V x) (n := n) := by
  letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  let G := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))
  let b := Module.finBasis ℝ (selfAdjoint.submodule ℝ (G →L[ℝ] G))
  refine ⟨fun x => selfAdjoint.submodule ℝ (V x →L[ℝ] V x),
    Module.finrank ℝ (selfAdjoint.submodule ℝ (G →L[ℝ] G)), ?_⟩
  intro x₀
  let p₀ : V x₀ ≃ₗᵢ[ℝ] G :=
    ((stdOrthonormalBasis ℝ (V x₀)).reindex
      (finCongr (VectorBundle.finrank_eq ℝ F V x₀))).repr
  obtain ⟨U, hU, hx₀, q, _, hq⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe_to (I := I) (F := F) (n := n) x₀ p₀
  let s := fun i x => (q x).symm.conjStarAlgEquiv (b i : G →L[ℝ] G)
  refine ⟨U, s, hU, hx₀, ?_, ?_, ?_⟩
  · intro x hx
    exact (b.linearIndependent.map' (selfAdjoint.submodule ℝ (G →L[ℝ] G)).subtype
      (Submodule.ker_subtype _)).map' (q x).symm.conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr (q x).symm.conjStarAlgEquiv.injective)
  · intro x hx
    have hb : Submodule.span ℝ (range (fun i => (b i : G →L[ℝ] G))) =
        selfAdjoint.submodule ℝ (G →L[ℝ] G) := by
      rw [show (fun i => (b i : G →L[ℝ] G)) =
        (selfAdjoint.submodule ℝ (G →L[ℝ] G)).subtype ∘ b from rfl,
        Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
    change Submodule.span ℝ
      (range ((q x).symm.conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap ∘
        (fun i => (b i : G →L[ℝ] G)))) = _
    rw [Set.range_comp, ← Submodule.map_span, hb, map_selfAdjoint_conj]
  · intro i
    exact contMDiffOn_conj_coframe hq (b i)

@[simp]
theorem selfAdjointSubbundle_fiber (x : M) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    (selfAdjointSubbundle (I := I) (F := F) (V := V) (n := n)).fiber x =
      selfAdjoint.submodule ℝ (V x →L[ℝ] V x) := rfl

end Bundle
