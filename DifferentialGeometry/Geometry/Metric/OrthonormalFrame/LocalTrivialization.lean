import DifferentialGeometry.Bundle.OrthonormalFrame
import DifferentialGeometry.Bundle.Hom.Pointwise
import Mathlib.Topology.VectorBundle.FiniteDimensional

noncomputable section

open Bundle Filter Set
open scoped Topology BigOperators InnerProductSpace Manifold ContDiff

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

def linearIsometryEquivAt (x : B) : V x ≃ₗᵢ[ℝ] F := by
  letI := VectorBundle.finiteDimensional ℝ F V x
  exact ((stdOrthonormalBasis ℝ (V x)).reindex
    (finCongr (VectorBundle.finrank_eq ℝ F V x))).repr.trans
      (stdOrthonormalBasis ℝ F).repr.symm

end FiberBundle

namespace LinearIsometryEquiv

section Sum

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

private theorem continuousOn_sum_sections
    {ι : Type*} {U : Set B} {e : ι → ∀ x, V x} (s : Finset ι) (c : ι → ℝ)
    (he : ∀ i ∈ s, ContinuousOn (fun x => (⟨x, e i x⟩ : TotalSpace F V)) U) :
    ContinuousOn (fun x => (⟨x, ∑ i ∈ s, c i • e i x⟩ : TotalSpace F V)) U := by
  intro x hx
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨continuousWithinAt_id, ?_⟩
  let t := trivializationAt F V x
  have hcoord (i : ι) (hi : i ∈ s) :
      ContinuousWithinAt (fun y => t.continuousLinearMapAt ℝ y (e i y)) U x := by
    have h := (he i hi x hx)
    rw [FiberBundle.continuousWithinAt_totalSpace] at h
    have h := h.2
    apply h.congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [Filter.mem_inf_of_left (t.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V x))] with y hy
    exact t.continuousLinearMapAt_apply_of_mem ℝ hy _
  have hsum : ContinuousWithinAt
      (fun y => ∑ i ∈ s, c i • t.continuousLinearMapAt ℝ y (e i y)) U x :=
    tendsto_finsetSum s (fun i hi => (hcoord i hi).const_smul (c i))
  apply hsum.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [Filter.mem_inf_of_left (t.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V x))] with y hy
  change (t ⟨y, ∑ i ∈ s, c i • e i y⟩).2 = _
  rw [← t.continuousLinearMapAt_apply_of_mem ℝ hy]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (t.continuousLinearMapAt ℝ y).map_smul (c i) (e i y))


end Sum

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

private theorem exists_coframe_of_orthonormal_sections
    {U : Set B} {e : Fin (Module.finrank ℝ F) → ∀ x, V x}
    (he : ∀ x ∈ U, Orthonormal ℝ (fun i => e i x)) :
    ∃ q : ∀ x, V x ≃ₗᵢ[ℝ] F, ∀ x ∈ U, ∀ w : F,
      (q x).symm w = ∑ i, (stdOrthonormalBasis ℝ F).repr w i • e i x := by
  classical
  let b := stdOrthonormalBasis ℝ F
  have hsp (x : B) (hx : x ∈ U) :
      ⊤ ≤ Submodule.span ℝ (range (fun i => e i x)) := by
    let := VectorBundle.finiteDimensional ℝ F V x
    exact ((he x hx).linearIndependent.span_eq_top_of_card_eq_finrank'
      ((Fintype.card_fin _).trans (VectorBundle.finrank_eq ℝ F V x).symm)).ge
  let q : ∀ x, V x ≃ₗᵢ[ℝ] F := fun x =>
    if hx : x ∈ U then (OrthonormalBasis.mk (he x hx) (hsp x hx)).repr.trans b.repr.symm
    else FiberBundle.linearIsometryEquivAt V x
  refine ⟨q, ?_⟩
  intro x hx w
  dsimp only [q]
  rw [dif_pos hx]
  change (OrthonormalBasis.mk (he x hx) (hsp x hx)).repr.symm (b.repr w) = _
  rw [← (OrthonormalBasis.mk (he x hx) (hsp x hx)).sum_repr_symm]
  simp only [OrthonormalBasis.coe_mk]
  rfl


theorem exists_continuous_coframe (x₀ : B) (p₀ : V x₀ ≃ₗᵢ[ℝ] F)
    [IsContinuousRiemannianBundle F V] :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧
      ∃ q : ∀ x, V x ≃ₗᵢ[ℝ] F,
        q x₀ = p₀ ∧ ∀ w : F,
          ContinuousOn (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U := by
  classical
  let b := stdOrthonormalBasis ℝ F
  obtain ⟨U, hU, hx₀, e, he, ho, hx⟩ :=
    exists_continuous_orthonormal_sections (F := F) x₀ (fun i => p₀.symm (b i))
      (p₀.symm.toLinearIsometry.orthonormal_comp_iff.mpr b.orthonormal)
  obtain ⟨q, hq⟩ := exists_coframe_of_orthonormal_sections ho
  refine ⟨U, hU, hx₀, q, ?_, ?_⟩
  · have hs : (q x₀).symm = p₀.symm := by
      ext w
      rw [hq x₀ hx₀]
      simp only [hx, ← map_smul, ← map_sum]
      exact congrArg p₀.symm (b.sum_repr w)
    exact congrArg (fun p : F ≃ₗᵢ[ℝ] V x₀ => p.symm) hs
  · intro w
    have h := continuousOn_sum_sections (F := F) Finset.univ (fun i => b.repr w i)
      (fun i _ => he i)
    exact h.congr (fun x hx => TotalSpace.mk_inj.mpr (hq x hx w))




section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H B]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n F V] [ContMDiffVectorBundle n F V I]

theorem exists_contMDiff_coframe (x₀ : B) (p₀ : V x₀ ≃ₗᵢ[ℝ] F) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧
      ∃ q : ∀ x, V x ≃ₗᵢ[ℝ] F,
        q x₀ = p₀ ∧ ∀ w : F,
          ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
            (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U := by
  classical
  let b := stdOrthonormalBasis ℝ F
  obtain ⟨U, hU, hx₀, e, he, ho, hx⟩ :=
    exists_contMDiff_orthonormal_sections (F := F) (I := I) (m := n)
      x₀ (fun i => p₀.symm (b i))
      (p₀.symm.toLinearIsometry.orthonormal_comp_iff.mpr b.orthonormal)
  obtain ⟨q, hq⟩ := exists_coframe_of_orthonormal_sections ho
  refine ⟨U, hU, hx₀, q, ?_, ?_⟩
  · have hs : (q x₀).symm = p₀.symm := by
      ext w
      rw [hq x₀ hx₀]
      simp only [hx, ← map_smul, ← map_sum]
      exact congrArg p₀.symm (b.sum_repr w)
    exact congrArg (fun p : F ≃ₗᵢ[ℝ] V x₀ => p.symm) hs
  · intro w
    have h : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
        (fun x => (⟨x, ∑ i, b.repr w i • e i x⟩ : TotalSpace F V)) U :=
      ContMDiffOn.sum_section (s := Finset.univ)
        (fun i _ => (contMDiffOn_const (c := b.repr w i)).smul_section (he i))
    exact h.congr (fun x hx => TotalSpace.mk_inj.mpr (hq x hx w))

omit [ContMDiffVectorBundle n F V I] in
theorem contMDiffOn_coframe {U : Set B} {q : ∀ x, V x ≃ₗᵢ[ℝ] F}
    (hq : ∀ w : F, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U) :
    ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (fun v : TotalSpace F V => (v.proj, q v.proj v.2)) (TotalSpace.proj ⁻¹' U) := by
  classical
  let b := stdOrthonormalBasis ℝ F
  have he (i) : ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (fun v : TotalSpace F V => (⟨v.proj, (q v.proj).symm (b i)⟩ : TotalSpace F V))
      (TotalSpace.proj ⁻¹' U) :=
    (hq (b i)).comp (Bundle.contMDiffOn_proj V) (fun _ hv => hv)
  have hv : ContMDiffOn (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) n
      (fun v : TotalSpace F V => ∑ i, inner ℝ ((q v.proj).symm (b i)) v.2 • b i)
      (TotalSpace.proj ⁻¹' U) := by
    intro v hv
    apply ContMDiffWithinAt.sum
    intro i _
    exact ((he i v hv).inner_bundle contMDiffWithinAt_id).smul contMDiffWithinAt_const
  have heq (v : TotalSpace F V) : q v.proj v.2 =
      ∑ i, inner ℝ ((q v.proj).symm (b i)) v.2 • b i := by
    rw [← b.sum_repr (q v.proj v.2)]
    apply Finset.sum_congr rfl
    intro i _
    rw [b.repr_apply_apply]
    congr 1
    simpa only [apply_symm_apply] using
      (q v.proj).inner_map_map ((q v.proj).symm (b i)) v.2
  exact (Bundle.contMDiffOn_proj V).prodMk (hv.congr (fun v _ => heq v))

theorem exists_contMDiff_coframe_trivialization (x₀ : B) (p₀ : V x₀ ≃ₗᵢ[ℝ] F) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ q : ∀ x, V x ≃ₗᵢ[ℝ] F,
      q x₀ = p₀ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
        (fun z : B × F => (⟨z.1, (q z.1).symm z.2⟩ : TotalSpace F V)) (U ×ˢ univ) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
        (fun v : TotalSpace F V => (v.proj, q v.proj v.2)) (TotalSpace.proj ⁻¹' U) := by
  obtain ⟨U, hU, hx₀, q, hq₀, hq⟩ := exists_contMDiff_coframe (I := I) (n := n) x₀ p₀
  refine ⟨U, hU, hx₀, q, hq₀, ?_, contMDiffOn_coframe hq⟩
  exact ContinuousLinearMap.contMDiffOn_bundle_apply_of_pointwise
    (φ := fun x => (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap) hq

end Smooth

end LinearIsometryEquiv
