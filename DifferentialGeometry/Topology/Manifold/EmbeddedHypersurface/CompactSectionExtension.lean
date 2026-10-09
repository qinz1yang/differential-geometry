import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.LocalAmbientSectionExtension
import DifferentialGeometry.Topology.Manifold.CompactCutoff

set_option autoImplicit false

open Bundle Filter Function Manifold Set Topology
open scoped Bundle Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold J ∞ A]

/-- A compactly supported field along the open part of an embedded compact domain extends
to an ambient field with prescribed support. It agrees at every point of the open part
and vanishes on the rest of the compact domain. No boundary charts on that domain are needed. -/
theorem exists_ambientSection_on_compact_domain
    {K : Set B} (hK : IsCompact K) (U : TopologicalSpace.Opens B)
    (hUK : (U : Set B) ⊆ K) {f : B → A}
    (hf : _root_.Topology.IsEmbedding (fun x : K ↦ f x))
    (C : SmoothEmbeddingRealNormalAtlas I J ∞ (fun x : U ↦ f x))
    (s : ∀ x : U, TangentSpace J (f x))
    (hs : ContMDiff I J.tangent ∞ (fun x : U ↦ (⟨f x, s x⟩ : TangentBundle J A)))
    (hsupport : IsCompact (closure {x : U | s x ≠ 0}))
    {O : Set A} (hO : IsOpen O)
    (hsO : ∀ x ∈ closure {x : U | s x ≠ 0}, f x ∈ O) :
    ∃ X : ∀ a : A, TangentSpace J a,
      ContMDiff J J.tangent ∞ (fun a ↦ (⟨a, X a⟩ : TangentBundle J A)) ∧
      HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ x : U, X (f x) = s x) ∧ ∀ x ∈ K \ (U : Set B), X (f x) = 0 := by
  classical
  have hfcont : ContinuousOn f K :=
    continuousOn_iff_continuous_domRestrict.mpr hf.continuous
  have hinjK : Set.InjOn f K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (@hf.injective ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  have hinjU : Injective (fun x : U ↦ f x) := by
    intro x y hxy
    exact Subtype.ext (hinjK (hUK x.property) (hUK y.property) hxy)
  let Q : Set A := (fun x : U ↦ f x) '' closure {x : U | s x ≠ 0}
  have hQ : IsCompact Q := hsupport.image C.contMDiff.continuous
  have hQO : Q ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsO x hx
  let R : Set A := f '' (K \ (U : Set B))
  have hR : IsCompact R :=
    (hK.diff U.isOpen).image_of_continuousOn (hfcont.mono sdiff_subset)
  have hQR : ∀ a ∈ Q, a ∉ R := by
    rintro a ⟨x, hx, hxa⟩ ⟨y, hy, hya⟩
    have hxy : (x : B) = y := hinjK (hUK x.property) hy.1 (hxa.trans hya.symm)
    exact hy.2 (hxy ▸ x.property)
  let s₀ : U → F := fun x ↦ s x
  let v₀ : A → F := fun a ↦
    if h : ∃ x : U, f x = a then s₀ (Classical.choose h) else 0
  let v (a : A) : TangentSpace J a := v₀ a
  have hv (x : U) : v (f x) = s x := by
    change v₀ (f x) = s₀ x
    have hex : ∃ y : U, f y = f x := ⟨x, rfl⟩
    dsimp only [v₀]
    rw [dite_eq_left hex]
    exact congrArg s₀ (hinjU (Classical.choose_spec hex))
  have hvzero {a : A} (ha : a ∉ Q) : v a = 0 := by
    change v₀ a = 0
    dsimp only [v₀]
    split_ifs with h
    · by_contra hne
      exact ha ⟨Classical.choose h, subset_closure hne, Classical.choose_spec h⟩
    · rfl
  have hlocal : ∀ a ∈ f '' K, ∃ V ∈ nhds a, ∃ l : ∀ b, TangentSpace J b,
      ContMDiffOn J J.tangent ∞ (fun b ↦ (⟨b, l b⟩ : TangentBundle J A)) V ∧
      ∀ b ∈ V, b ∈ f '' K → l b = v b := by
    intro a ha
    by_cases haQ : a ∈ Q
    · obtain ⟨x, hx, hxa⟩ := haQ
      obtain ⟨V, hV, hxV, l, hl, heq⟩ := C.exists_local_ambientSection hinjU s hs x
      refine ⟨V \ R, (IsOpen.sdiff hV hR.isClosed).mem_nhds
        ⟨hxa ▸ hxV, hQR a ⟨x, hx, hxa⟩⟩,
        l, hl.mono sdiff_subset, ?_⟩
      rintro _ hb ⟨y, hyK, rfl⟩
      have hyU : y ∈ U := by
        by_contra hn
        exact hb.2 ⟨y, ⟨hyK, hn⟩, rfl⟩
      exact (heq ⟨y, hyU⟩ hb.1).trans (hv ⟨y, hyU⟩).symm
    · refine ⟨Qᶜ, hQ.isClosed.isOpen_compl.mem_nhds haQ, (fun _ ↦ 0), ?_, ?_⟩
      · exact (contMDiff_zeroSection ℝ (TangentSpace J : A → Type _)).contMDiffOn
      · intro b hb _
        exact (hvzero hb).symm
  obtain ⟨S, _, hS⟩ :=
    exists_contMDiffSection_eqOn_of_isCompact_of_local (I := J)
      (TangentSpace J : A → Type _) (hK.image_of_continuousOn hfcont) v hlocal
  obtain ⟨X, hX, hXc, hXO, hXS, hscale⟩ :=
    exists_compactSupport_vectorField_eq_near S.contMDiff hQ hO hQO
  refine ⟨X, hX, hXc, hXO, ?_, ?_⟩
  · intro x
    have hSx : S (f x) = s x := (hS (f x) ⟨x, hUK x.property, rfl⟩).trans (hv x)
    by_cases hxQ : f x ∈ Q
    · exact (hXS.self_of_nhdsSet hxQ).trans hSx
    · have hsx : s x = 0 := (hv x).symm.trans (hvzero hxQ)
      obtain ⟨b, _, hb⟩ := hscale (f x)
      rw [hb, hSx, hsx, smul_zero]
  · intro x hx
    have hxQ : f x ∉ Q := fun h ↦ hQR (f x) h ⟨x, hx, rfl⟩
    have hSx : S (f x) = 0 := (hS (f x) ⟨x, hx.1, rfl⟩).trans (hvzero hxQ)
    obtain ⟨b, _, hb⟩ := hscale (f x)
    rw [hb, hSx, smul_zero]

end DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas
