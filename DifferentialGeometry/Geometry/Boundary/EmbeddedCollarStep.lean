import DifferentialGeometry.Geometry.Boundary.LiftedChart
import DifferentialGeometry.Topology.Manifold.ProductCollarStep

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_uniform_smooth_step_of_embedded_product_collar :
    ∃ C : ℝ, 0 < C ∧ ∀
    {E H W F G M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [T2Space W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] (L : ModelWithCorners ℝ E' H')
    [TopologicalSpace N] [ChartedSpace H' N] [CompactSpace N],
    ∀ ι : W → M, ContMDiff I J ∞ ι →
    IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
    Module.finrank ℝ E = Module.finrank ℝ F →
    ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮L.prod 𝓘(ℝ), J⟯ V)
    (l r : ℝ) (hlr : l < r) (hcollar : (univ : Set N) ×ˢ Icc l r ⊆ O),
    let e : N × Icc l r → M := fun x ↦
      Φ ⟨(x.1, (x.2 : ℝ)), hcollar ⟨mem_univ _, x.2.property⟩⟩
    let q : M → ℝ := Subtype.val.extend
      (fun y : V ↦ ((Φ.symm y : O) : N × ℝ).2) (fun _ ↦ 0)
    (∀ x, e x ∈ interior (range ι)) →
    ∀ P Q : Set W, IsClosed P → IsClosed Q → Disjoint P Q →
    P ∪ ι ⁻¹' range e ∪ Q = univ →
    P ∩ ι ⁻¹' range e ⊆ ι ⁻¹' range (fun p : N ↦ e (p, ⟨l, le_rfl, hlr.le⟩)) →
    Q ∩ ι ⁻¹' range e ⊆ ι ⁻¹' range (fun p : N ↦ e (p, ⟨r, hlr.le, le_rfl⟩)) →
    ∀ a b : ℝ, l < a → a < b → b < r →
      let K := ι ⁻¹' (e '' {x | a ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b})
      ∃ (β : ℝ → ℝ) (θ : W → ℝ),
        ContDiff ℝ ∞ β ∧ Monotone β ∧ ContMDiff I 𝓘(ℝ) ∞ θ ∧
        (∀ w, θ w ∈ Icc (0 : ℝ) 1) ∧
        (∀ w ∈ P, θ w = 0) ∧ (∀ w ∈ Q, θ w = 1) ∧
        (∀ w x, ι w = e x → θ w = β (x.2 : ℝ)) ∧
        (∀ t, t ≤ a → β t = 0) ∧ (∀ t, b ≤ t → β t = 1) ∧
        IsCompact K ∧ (∀ w ∉ K, θ w = 0 ∨ θ w = 1) ∧
        (∀ w ∉ K, mvfderiv I θ w = 0) ∧
        ∀ w (v : TangentSpace I w),
          |mvfderiv I θ w v| ≤ (C / (b - a)) * |mvfderiv I (q ∘ ι) w v| := by
  obtain ⟨C, hC, hstep⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_uniform_smooth_step_of_product_collar
  refine ⟨C, hC, ?_⟩
  intro E H W F G M E' H' N _ _ _ _ I _ _ _ _ _ _ _ _ _ J _ _ _ _ _ _ L _ _ _
  specialize hstep (N := N) (M := W) L I
  intro ι hι hemb hinj hdim O V Φ l r hlr hcollar e q hinternal
    P Q hP hQ hPQ hcover hleft hright a b hla hab hbr K
  obtain ⟨U, hUO, Z, Ψ, hU, hZ, hΨ⟩ :=
    exists_lifted_chart_of_interior_range ι hι hemb hinj hdim O V Φ
  have hcollarU : (univ : Set N) ×ˢ Icc l r ⊆ U := by
    rintro x ⟨_, hx⟩
    exact (hU ⟨x, hcollar ⟨mem_univ _, hx⟩⟩).mpr (hinternal (x.1, ⟨x.2, hx⟩))
  let eW : N × Icc l r → W := fun x ↦
    Ψ ⟨(x.1, (x.2 : ℝ)), hcollarU ⟨mem_univ _, x.2.property⟩⟩
  let qW : W → ℝ := Subtype.val.extend
    (fun z : Z ↦ ((Ψ.symm z : U) : N × ℝ).2) (fun _ ↦ 0)
  have heW (x : N × Icc l r) : ι (eW x) = e x := hΨ _
  have hrange : range eW = ι ⁻¹' range e := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (heW x).symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, hemb.injective ((heW x).trans hx)⟩
  have hcoverW : P ∪ range eW ∪ Q = univ := by rwa [hrange]
  have hleftW : P ∩ range eW ⊆ range (fun p : N ↦ eW (p, ⟨l, le_rfl, hlr.le⟩)) := by
    intro w hw
    obtain ⟨p, hp⟩ := hleft ⟨hw.1, hrange ▸ hw.2⟩
    exact ⟨p, hemb.injective ((heW _).trans hp)⟩
  have hrightW : Q ∩ range eW ⊆ range (fun p : N ↦ eW (p, ⟨r, hlr.le, le_rfl⟩)) := by
    intro w hw
    obtain ⟨p, hp⟩ := hright ⟨hw.1, hrange ▸ hw.2⟩
    exact ⟨p, hemb.injective ((heW _).trans hp)⟩
  have hK : eW '' {x | a ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b} = K := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (heW x).symm⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, hemb.injective ((heW x).trans he)⟩
  obtain ⟨β, θ, hβ, hmono, hθ, h01, hzero, hone, hformula, hβzero, hβone,
      hcompact, hbinary, hoff, hbound⟩ :=
    hstep U Z Ψ l r hlr hcollarU P Q hP hQ hPQ hcoverW hleftW hrightW a b hla hab hbr
  have hqeq (z : Z) : qW z = q (ι z) := by
    have hz : ι (z : W) ∈ V := by
      have h : (z : W) ∈ (Z : Set W) := z.property
      rw [hZ] at h
      exact h.1
    have hcomm := hΨ (Ψ.symm z)
    rw [Ψ.apply_symm_apply] at hcomm
    have hφ : Φ (TopologicalSpace.Opens.inclusion hUO (Ψ.symm z)) =
        (⟨ι (z : W), hz⟩ : V) := Subtype.ext hcomm.symm
    have hinverse : Φ.symm ⟨ι (z : W), hz⟩ =
        TopologicalSpace.Opens.inclusion hUO (Ψ.symm z) := by
      rw [← hφ, Φ.symm_apply_apply]
    change Function.extend (Subtype.val : Z → W)
      (fun z : Z ↦ ((Ψ.symm z : U) : N × ℝ).2) (fun _ ↦ 0) (z : W) =
      Function.extend (Subtype.val : V → M)
        (fun y : V ↦ ((Φ.symm y : O) : N × ℝ).2) (fun _ ↦ 0)
          (Subtype.val (⟨ι (z : W), hz⟩ : V))
    rw [Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply, hinverse]
  refine ⟨β, θ, hβ, hmono, hθ, h01, hzero, hone, ?_, hβzero, hβone,
    hK ▸ hcompact, hK ▸ hbinary, hK ▸ hoff, ?_⟩
  · intro w x hx
    have hw : w = eW x := hemb.injective (hx.trans (heW x).symm)
    rw [hw]
    exact hformula x
  · intro w v
    by_cases hw : w ∈ K
    · have hwZ : w ∈ Z := by
        rw [← hK] at hw
        obtain ⟨x, _, rfl⟩ := hw
        exact (Ψ ⟨(x.1, (x.2 : ℝ)), hcollarU ⟨mem_univ _, x.2.property⟩⟩).property
      have hlocal : qW =ᶠ[𝓝 w] q ∘ ι :=
        Filter.eventually_of_mem (Z.isOpen.mem_nhds hwZ) (fun y hy ↦ hqeq ⟨y, hy⟩)
      have hd : mvfderiv I qW w v = mvfderiv I (q ∘ ι) w v := by
        change (show ℝ from mfderiv I 𝓘(ℝ) qW w v) =
          (show ℝ from mfderiv I 𝓘(ℝ) (q ∘ ι) w v)
        rw [hlocal.mfderiv_eq]
        rfl
      exact hd ▸ hbound w v
    · have hz := hoff w (by rwa [hK])
      rw [hz]
      simp only [zero_apply, abs_zero]
      exact mul_nonneg (div_nonneg hC.le (sub_pos.mpr hab).le) (abs_nonneg _)

end DifferentialGeometry.Geometry.Boundary
