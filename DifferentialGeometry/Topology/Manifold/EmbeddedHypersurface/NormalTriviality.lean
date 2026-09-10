import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.NormalBundle
import DifferentialGeometry.Bundle.PositiveSection
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Collar

set_option autoImplicit false
noncomputable section
open Set Bundle Filter DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

private theorem continuous_covector_of_continuous_apply
    {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (V : B → Type*) [∀ x, AddCommGroup (V x)]
    [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    (ν : ∀ x : B, V x →L[ℝ] ℝ)
    (hν : Continuous (fun z : TotalSpace F V ↦ ν z.proj z.snd)) :
    Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
      (E := fun x : B ↦ V x →L[ℝ] ℝ) x (ν x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
  refine ⟨continuousAt_id, ?_⟩
  apply continuousAt_clm_apply.mpr
  intro v
  let a := trivializationAt F V x
  have hx : x ∈ a.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hW : ContinuousAt (fun y ↦ (⟨y, a.symm y v⟩ : TotalSpace F V)) x :=
    (a.continuousOn_symm.comp (continuous_id.prodMk
      (continuous_const (y := v))).continuousOn
      (fun y hy ↦ ⟨hy, mem_univ v⟩)).continuousAt (a.open_baseSet.mem_nhds hx)
  apply (hν.continuousAt.comp hW).congr_of_eventuallyEq
  filter_upwards [a.open_baseSet.mem_nhds hx] with y hy
  rw [ContinuousLinearMap.inCoordinates_eq
    (E' := Bundle.Trivial B ℝ) (y₀ := x) (y := y) hy (mem_univ y)]
  change ν y (a.symm y v) =
    ν y ((a.continuousLinearEquivAt ℝ y hy).symm v)
  rfl

private instance pullbackAddCommGroup {B B' : Type*} (f : B' → B) (V : B → Type*)
    [∀ b, AddCommGroup (V b)] (x : B') : AddCommGroup ((f *ᵖ V) x) :=
  inferInstanceAs (AddCommGroup (V (f x)))

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ S] [IsManifold J ∞ M]

omit [I.Boundaryless] [J.Boundaryless] in
theorem exists_contMDiff_transverse_of_normalTrivialization {e : S → M}
    [T2Space S] [SigmaCompactSpace S] (he : ContMDiff I J ∞ e)
    (t : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (normalSpace I J e) → S))
    [t.IsLinear ℝ] (ht : t.baseSet = Set.univ) :
    ∃ V : ∀ s, TangentSpace J (e s),
      ContMDiff I J.tangent ∞ (fun s ↦ (⟨e s, V s⟩ : TangentBundle J M)) ∧
      (∀ s, 0 < normalTrivializationCovector I J e t ht s (V s)) ∧
      (∀ s, V s ≠ 0) ∧ ∀ s, V s ∉ (mfderiv I J e s).range := by
  let f : ContMDiffMap I J S M ∞ := ⟨e, he⟩
  let T := f *ᵖ (TangentSpace J (M := M))
  let ν : ∀ s : S, T s →L[ℝ] ℝ := normalTrivializationCovector I J e t ht
  have hν : Continuous (fun s ↦ TotalSpace.mk' (MorseModel (m + 1) →L[ℝ] ℝ)
      (E := fun s : S ↦ T s →L[ℝ] ℝ) s (ν s)) :=
    continuous_covector_of_continuous_apply T ν
      (continuous_normalTrivializationCovector_apply I J e t ht)
  obtain ⟨V, hV, hpos⟩ := DifferentialGeometry.VectorBundle.exists_contMDiff_section_covector_pos I T ν hν
    (normalTrivializationCovector_ne_zero I J e t ht)
  refine ⟨V, ?_, hpos, ?_, ?_⟩
  · intro x
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨he x, (Bundle.contMDiffAt_totalSpace.mp (hV x)).2⟩
  · intro s hs
    change V s = (0 : T s) at hs
    have hz : ν s (V s) = 0 := hs ▸ (ν s).map_zero
    exact (ne_of_gt (hpos s)) hz
  · intro s hs
    have hz : ν s (V s) = 0 := by
      change V s ∈ (normalTrivializationCovector I J e t ht s).ker
      rw [ker_normalTrivializationCovector]
      exact hs
    exact (ne_of_gt (hpos s)) hz

theorem nonempty_smoothTwoSidedCollar_of_normalTrivialization {e : S → M}
    [T2Space M] [SigmaCompactSpace M]
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e))
    (t : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (normalSpace I J e) → S))
    [t.IsLinear ℝ] (ht : t.baseSet = Set.univ) :
    Nonempty (SmoothTwoSidedCollar I J e) := by
  let : T2Space S := he.isEmbedding.t2Space
  let : CompactSpace S := isCompact_univ_iff.mp
    (he.isEmbedding.isCompact_iff.mpr (by simpa using hK))
  obtain ⟨V, hV, _, _, htrans⟩ :=
    exists_contMDiff_transverse_of_normalTrivialization I J he.contMDiff t ht
  exact nonempty_smoothTwoSidedCollar I J he hK V hV.continuous htrans

end DifferentialGeometry.Manifold.EmbeddedHypersurface
