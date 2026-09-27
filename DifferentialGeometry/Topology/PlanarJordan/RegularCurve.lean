import DifferentialGeometry.Topology.Manifold.RegularLevel.Tangent
import DifferentialGeometry.Topology.Manifold.CircleComponents
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import DifferentialGeometry.Topology.Manifold.RegularZero.Coordinates
import DifferentialGeometry.Analysis.Calculus.LocalExtrema
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter Manifold Schoenflies
open scoped ContDiff Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem dual_apply_two (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (v : Fin 2 → ℝ) :
    L v = v 0 * L ![1, 0] + v 1 * L ![0, 1] := by
  have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv, map_add, map_smul, map_smul]
  rfl

private theorem rotated_dual_mem_ker (L : (Fin 2 → ℝ) →L[ℝ] ℝ) :
    L ![-L ![0, 1], L ![1, 0]] = 0 := by
  rw [dual_apply_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem rotated_dual_ne_zero (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    (![-L ![0, 1], L ![1, 0]] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Pi.zero_apply, neg_eq_zero] at h0
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
  apply hL
  ext v
  rw [dual_apply_two, h0, h1]
  simp

private theorem exists_circle_embedding_regular_level_fin_two
    {f : (Fin 2 → ℝ) → ℝ} {U : Set (Fin 2 → ℝ)} {a : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hc : IsCompact {x | x ∈ U ∧ f x = a})
    (hconn : IsConnected {x | x ∈ U ∧ f x = a})
    (hr : ∀ x ∈ U, f x = a → fderiv ℝ f x ≠ 0) :
    ∃ γ : AddCircle (1 : ℝ) → (Fin 2 → ℝ),
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ γ ∧
        range γ = {x | x ∈ U ∧ f x = a} := by
  let O : TopologicalSpace.Opens (Fin 2 → ℝ) := ⟨U, hU⟩
  let g : O → ℝ := fun x => f x.val
  have hg : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ g := by
    intro x
    exact contMDiffAt_subtype_iff.mpr
      ((hf.contDiffAt (hU.mem_nhds x.property)).contMDiffAt)
  have hdg (x : O) : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) g x = fderiv ℝ f x.val := by
    rw [DifferentialGeometry.mfderiv_restrict_open, mfderiv_eq_fderiv]
  have hgr (x : O) (hx : g x = a) : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) g x ≠ 0 := by
    rw [hdg]
    exact hr x.val x.property hx
  let V : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
    fun x => ![-fderiv ℝ f x ![0, 1], fderiv ℝ f x ![1, 0]]
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hV : ContDiffOn ℝ ∞ V U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (hdf.clm_apply contDiffOn_const).neg
    · exact hdf.clm_apply contDiffOn_const
  have hVO : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (𝓘(ℝ, Fin 2 → ℝ)).tangent ∞
      (fun x : O => (⟨x, V x.val⟩ : TangentBundle 𝓘(ℝ, Fin 2 → ℝ) O)) :=
    DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens O
      (contMDiffOn_vectorSpace_iff_contDiffOn.mpr hV)
  let _ := DifferentialGeometry.Manifold.RegularLevel.levelChartedSpace
    𝓘(ℝ, Fin 2 → ℝ) hg hgr
  let _ := DifferentialGeometry.Manifold.RegularLevel.levelIsManifold
    𝓘(ℝ, Fin 2 → ℝ) hg hgr
  let L := {x : O // g x = a}
  have hinc := DifferentialGeometry.Manifold.RegularLevel.isSmoothEmbedding_level_inclusion
    𝓘(ℝ, Fin 2 → ℝ) hg hgr
  obtain ⟨W, hW, hpush⟩ := DifferentialGeometry.Manifold.RegularLevel.exists_contMDiff_tangent_field
    𝓘(ℝ, Fin 2 → ℝ) hg hgr (fun x : O => V x.val) hVO (fun x _ => by
      rw [hdg]
      exact rotated_dual_mem_ker (fderiv ℝ f x.val))
  have hWne (x : L) : W x ≠ 0 := by
    intro hz
    apply rotated_dual_ne_zero (fderiv ℝ f x.val.val) (hr _ x.val.property x.property)
    change V x.val.val = 0
    rw [← hpush, hz, map_zero]
    rfl
  have himage : (fun x : L => x.val.val) '' (univ : Set L) =
      {x | x ∈ U ∧ f x = a} := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact ⟨y.val.property, y.property⟩
    · rintro ⟨hx, hf⟩
      exact ⟨⟨⟨x, hx⟩, hf⟩, mem_univ _, rfl⟩
  have hind : Topology.IsInducing (fun x : L => x.val.val) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  let : CompactSpace L := isCompact_univ_iff.mp (hind.isCompact_iff.mpr (himage ▸ hc))
  let : PreconnectedSpace L :=
    preconnectedSpace_iff_univ.mpr (hind.isPreconnected_image.mp (himage ▸ hconn.isPreconnected))
  obtain ⟨x, hxU, hxf⟩ := hconn.nonempty
  obtain ⟨γ, hγ, hrange⟩ := DifferentialGeometry.Topology.Manifold.exists_circle_embedding_connectedComponent
    (I := 𝓘(ℝ, MorseModel 1)) (by simp [MorseModel]) W hW hWne (⟨⟨x, hxU⟩, hxf⟩ : L)
  have hj : IsSmoothEmbedding 𝓘(ℝ, MorseModel 1) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun x : L => x.val.val) := (IsSmoothEmbedding.of_opens O).comp hinc (by simp)
  refine ⟨(fun x : L => x.val.val) ∘ γ, hj.comp hγ (by simp), ?_⟩
  rw [range_comp, hrange, PreconnectedSpace.connectedComponent_eq_univ]
  exact himage

theorem exists_circle_embedding_of_isCompact_isConnected_regular_level
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : Module.finrank ℝ E = 2) {f : E → ℝ} {U : Set E} {a : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hc : IsCompact {x | x ∈ U ∧ f x = a})
    (hconn : IsConnected {x | x ∈ U ∧ f x = a})
    (hr : ∀ x ∈ U, f x = a → fderiv ℝ f x ≠ 0) :
    ∃ γ : AddCircle (1 : ℝ) → E,
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ ∧
        range γ = {x | x ∈ U ∧ f x = a} := by
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  let e : (Fin 2 → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim.symm)
  have hg : ContDiffOn ℝ ∞ (f ∘ e) (e ⁻¹' U) :=
    hf.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hgr (x : Fin 2 → ℝ) (hx : x ∈ e ⁻¹' U) (hfx : (f ∘ e) x = a) :
      fderiv ℝ (f ∘ e) x ≠ 0 := by
    rw [fderiv_comp x ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      e.differentiableAt, e.fderiv]
    intro hz
    apply hr (e x) hx hfx
    ext v
    have hzv := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (e.symm v)) hz
    simpa using hzv
  obtain ⟨γ, hγ, hrange⟩ := exists_circle_embedding_regular_level_fin_two
    (hU.preimage e.continuous) hg (e.toHomeomorph.isCompact_preimage.mpr hc)
      (e.toHomeomorph.isConnected_preimage.mpr hconn) hgr
  have he : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, E) ∞ e := e.contDiff.contMDiff
  have hsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (e ∘ γ) := he.comp hγ.contMDiff
  have himm : IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (e ∘ γ) := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hsm
    intro x
    rw [mfderiv_comp x (he.mdifferentiableAt (by simp))
      (hγ.contMDiff.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, e.fderiv]
    exact e.injective.comp ((hγ.isImmersion.isImmersionAt x).injective_mfderiv (by simp))
  refine ⟨e ∘ γ, ⟨himm, e.toHomeomorph.isEmbedding.comp hγ.isEmbedding⟩, ?_⟩
  rw [range_comp, hrange]
  ext x
  constructor
  · rintro ⟨y, ⟨hyU, hyf⟩, rfl⟩
    exact ⟨hyU, hyf⟩
  · rintro ⟨hxU, hxf⟩
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simpa using And.intro hxU hxf


private theorem exists_neighborhood_inside_iff_pos_or_neg_of_regular_defining_function
    {C U : Set Plane} {a : Plane} {f : Plane → ℝ}
    (hC : IsSeparating C) (hU : IsOpen U) (haC : a ∈ C) (haU : a ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hzero : ∀ x ∈ U, x ∈ C ↔ f x = 0)
    (hr : fderiv ℝ f a ≠ 0) :
    ∃ V : Set Plane, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      (∀ x ∈ V, fderiv ℝ f x ≠ 0) ∧
      ((∀ x ∈ V, x ∈ inside C ↔ 0 < f x) ∨
        (∀ x ∈ V, x ∈ inside C ↔ f x < 0)) := by
  have hfa : f a = 0 := (hzero a haU).mp haC
  have hcont := (hf.contDiffAt (hU.mem_nhds haU)).continuousAt_fderiv (by simp)
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp
    (hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hr))
  have hsurj : Function.Surjective (fderiv ℝ f a) := by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hr
    have hv' : (fderiv ℝ f a) v ≠ 0 := by simpa using hv
    intro t
    refine ⟨(t / (fderiv ℝ f a) v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv']
  obtain ⟨Φ, haΦ, hΦsub, hΦfst, hΦa⟩ :=
    DifferentialGeometry.Manifold.RegularZero.exists_coordinates (by simp)
      (hU.inter hW) (hf.mono inter_subset_left) ⟨haU, haW⟩ hsurj
  have hΦa0 : Φ a = 0 := by
    apply Prod.ext
    · simpa [hfa] using hΦfst a
    · exact hΦa
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Φ.open_target (Φ a) (Φ.map_source haΦ)
  rw [hΦa0] at hball
  let K := (fderiv ℝ f a).ker
  let S : Set (ℝ × K) := Ioo (-ε) ε ×ˢ Metric.ball (0 : K) ε
  have hS : IsOpen S := isOpen_Ioo.prod Metric.isOpen_ball
  have hSt : S ⊆ Φ.target := by
    intro z hz
    apply hball
    rw [← ball_prod_same]
    refine ⟨?_, hz.2⟩
    simpa only [Metric.mem_ball, Real.dist_eq, Prod.fst_zero, sub_zero, abs_lt, mem_Ioo] using hz.1
  have h0S : (0 : ℝ × K) ∈ S := ⟨⟨neg_neg_of_pos hε, hε⟩, Metric.mem_ball_self hε⟩
  let V := Φ.symm '' S
  have hVo : IsOpen V := Φ.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source hS hSt
  have haV : a ∈ V := ⟨Φ a, hΦa0.symm ▸ h0S, Φ.left_inv haΦ⟩
  have hVsource : V ⊆ Φ.source := by
    rintro x ⟨z, hz, rfl⟩
    exact Φ.map_target (hSt hz)
  have hVsub : V ⊆ U := fun _ hx => (hΦsub (hVsource hx)).1
  have himage (P : Set ℝ) (hP : P ⊆ Ioo (-ε) ε) :
      V ∩ {x | f x ∈ P} = Φ.symm '' (P ×ˢ Metric.ball (0 : K) ε) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hfz⟩
      refine ⟨z, ⟨?_, hz.2⟩, rfl⟩
      have h := congrArg Prod.fst (Φ.right_inv (hSt hz))
      rw [hΦfst] at h
      rwa [← h]
    · rintro ⟨z, hz, rfl⟩
      have hzS : z ∈ S := ⟨hP hz.1, hz.2⟩
      refine ⟨⟨z, hzS, rfl⟩, ?_⟩
      have h := congrArg Prod.fst (Φ.right_inv (hSt hzS))
      rw [hΦfst] at h
      change f (Φ.symm z) ∈ P
      exact h.symm ▸ hz.1
  have hpos : IsPreconnected (V ∩ {x | 0 < f x}) := by
    have heq : V ∩ {x | 0 < f x} = V ∩ {x | f x ∈ Ioo 0 ε} := by
      ext x
      constructor
      · rintro ⟨hx, hp⟩
        obtain ⟨z, hz, rfl⟩ := hx
        have heq := congrArg Prod.fst (Φ.right_inv (hSt hz))
        rw [hΦfst] at heq
        exact ⟨⟨z, hz, rfl⟩, hp, heq ▸ hz.1.2⟩
      · exact fun hx => ⟨hx.1, hx.2.1⟩
    rw [heq, himage (Ioo 0 ε) (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)]
    exact (isPreconnected_Ioo.prod (convex_ball (0 : K) ε).isPreconnected).image Φ.symm
      (Φ.symm.toOpenPartialHomeomorph.continuousOn.mono (fun z hz =>
        hSt ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩))
  have hneg : IsPreconnected (V ∩ {x | f x < 0}) := by
    have heq : V ∩ {x | f x < 0} = V ∩ {x | f x ∈ Ioo (-ε) 0} := by
      ext x
      constructor
      · rintro ⟨hx, hp⟩
        obtain ⟨z, hz, rfl⟩ := hx
        have heq := congrArg Prod.fst (Φ.right_inv (hSt hz))
        rw [hΦfst] at heq
        exact ⟨⟨z, hz, rfl⟩, heq ▸ hz.1.1, hp⟩
      · exact fun hx => ⟨hx.1, hx.2.2⟩
    rw [heq, himage (Ioo (-ε) 0) (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩)]
    exact (isPreconnected_Ioo.prod (convex_ball (0 : K) ε).isPreconnected).image Φ.symm
      (Φ.symm.toOpenPartialHomeomorph.continuousOn.mono (fun z hz =>
        hSt ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩))
  refine ⟨V, hVo, haV, hVsub, fun x hx => hWsub (hΦsub (hVsource hx)).2, ?_⟩
  exact hC.local_side_sign hVo haC haV f (fun x hx => hzero x (hVsub hx)) hpos hneg

theorem exists_signed_regular_defining_function
    {C U : Set Plane} {a : Plane} {f : Plane → ℝ}
    (hC : IsSeparating C) (hU : IsOpen U) (haC : a ∈ C) (haU : a ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hzero : ∀ x ∈ U, x ∈ C ↔ f x = 0)
    (hr : fderiv ℝ f a ≠ 0) :
    ∃ V : Set Plane, ∃ g : Plane → ℝ,
      IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ (g = f ∨ g = -f) ∧
      ContDiffOn ℝ ∞ g V ∧ (∀ x ∈ V, fderiv ℝ g x ≠ 0) ∧
      (∀ x ∈ V, x ∈ C ↔ g x = 0) ∧
      (∀ x ∈ V, x ∈ inside C ↔ 0 < g x) := by
  obtain ⟨V, hVo, haV, hVU, hreg, hsign⟩ :=
    exists_neighborhood_inside_iff_pos_or_neg_of_regular_defining_function
      hC hU haC haU hf hzero hr
  rcases hsign with hp | hn
  · exact ⟨V, f, hVo, haV, hVU, Or.inl rfl, hf.mono hVU, hreg,
      fun x hx => hzero x (hVU hx), hp⟩
  · refine ⟨V, -f, hVo, haV, hVU, Or.inr rfl, (hf.mono hVU).neg, ?_, ?_, ?_⟩
    · intro x hx
      rw [fderiv_neg, neg_ne_zero]
      exact hreg x hx
    · intro x hx
      simpa only [Pi.neg_apply, neg_eq_zero] using hzero x (hVU hx)
    · intro x hx
      simpa only [Pi.neg_apply, neg_pos] using hn x hx


theorem exists_neighborhood_inside_iff_pos_of_regular_defining_function
    {C U : Set Plane} {a : Plane} {f : Plane → ℝ}
    (hC : IsSeparating C) (hU : IsOpen U) (haC : a ∈ C) (haU : a ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hzero : ∀ x ∈ U, x ∈ C ↔ f x = 0)
    (hr : fderiv ℝ f a ≠ 0)
    (ha : a ∈ closure (outside C ∩ {x | f x < 0})) :
    ∃ V : Set Plane, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      (∀ x ∈ V, fderiv ℝ f x ≠ 0) ∧
      (∀ x ∈ V, x ∈ inside C ↔ 0 < f x) ∧
      (∀ x ∈ V, x ∈ closure (inside C) ↔ 0 ≤ f x) := by
  obtain ⟨V, g, hVopen, haV, hsub, hchoice, hgs, hgr, hgzero, hgin⟩ :=
    exists_signed_regular_defining_function hC hU haC haU hf hzero hr
  have hgf : g = f := by
    rcases hchoice with h | h
    · exact h
    · obtain ⟨x, hxV, hxout, hxneg⟩ := mem_closure_iff.mp ha V hVopen haV
      have hxin := (hgin x hxV).mpr (by simpa [h] using neg_pos.mpr (show f x < 0 from hxneg))
      exact (Set.disjoint_left.mp disjoint_inside_outside hxin hxout).elim
  subst g
  refine ⟨V, hVopen, haV, hsub, hgr, hgin, ?_⟩
  intro x hx
  rw [(IsRegionOf.inside C).closure_eq hC, mem_union, hgin x hx,
    hzero x (hsub hx)]
  exact ⟨fun h => h.elim le_of_lt (fun h => h.ge), fun h => h.eq_or_lt.elim
    (fun h => Or.inr h.symm) Or.inl⟩


private theorem exists_regular_defining_function_of_signed_finite_cover
    {ι : Type*} [Finite ι] {C : Set Plane} (hC : IsClosed C)
    (U : ι → Set Plane) (hU : ∀ i, IsOpen (U i)) (hcover : C ⊆ ⋃ i, U i)
    (f : ι → Plane → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hzero : ∀ i x, x ∈ U i → (x ∈ C ↔ f i x = 0))
    (hsign : ∀ i x, x ∈ U i → (x ∈ inside C ↔ 0 < f i x))
    (hr : ∀ i x, x ∈ U i → fderiv ℝ (f i) x ≠ 0) :
    ∃ G : Plane → ℝ, ∃ W : Set Plane,
      ContDiff ℝ ∞ G ∧ IsOpen W ∧ C ⊆ W ∧
      (∀ x ∈ W, x ∈ C ↔ G x = 0) ∧ (∀ x ∈ C, fderiv ℝ G x ≠ 0) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Plane) hC U hU hcover
  let G : Plane → ℝ := fun x => ∑ i, ρ i x * f i x
  let W : Set Plane := {x | 0 < ∑ i, ρ i x}
  have hterms (i : ι) : ContDiff ℝ ∞ (fun x => ρ i x * f i x) := by
    simpa only [smul_eq_mul] using
      (ρ.contMDiff_smul (n := ⊤) (fun x hx =>
        ((hf i).contDiffAt ((hU i).mem_nhds (hρ i hx))).contMDiffAt)).contDiff
  have hG : ContDiff ℝ ∞ G := ContDiff.sum (fun i _ => hterms i)
  have hWo : IsOpen W := isOpen_lt continuous_const
    (continuous_finsetSum _ (fun i _ => (ρ i).contMDiff.continuous))
  have hCW : C ⊆ W := by
    intro x hx
    change 0 < ∑ i, ρ i x
    have h : (∑ i, ρ i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    rw [h]
    exact zero_lt_one
  have hUm (i : ι) {x : Plane} (hx : ρ i x ≠ 0) : x ∈ U i :=
    hρ i (subset_tsupport _ hx)
  have hGzero {x : Plane} (hx : x ∈ C) : G x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : ρ i x = 0
    · rw [hi, zero_mul]
    · rw [(hzero i x (hUm i hi)).mp hx, mul_zero]
  have hGsign {x : Plane} (hxW : x ∈ W) (hxC : x ∉ C) : G x ≠ 0 := by
    obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => ρ.nonneg i x)).mp hxW
    by_cases hxI : x ∈ inside C
    · have hnonneg (i : ι) : 0 ≤ ρ i x * f i x := by
        by_cases hi : ρ i x = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_nonneg (ρ.nonneg i x) ((hsign i x (hUm i hi)).mp hxI).le
      have hpos : 0 < G x := Finset.sum_pos' (fun i _ => hnonneg i)
        ⟨j, Finset.mem_univ j, mul_pos hj ((hsign j x (hUm j hj.ne')).mp hxI)⟩
      exact hpos.ne'
    · have hneg (i : ι) (hi : ρ i x ≠ 0) : f i x < 0 := by
        have hne : f i x ≠ 0 := fun hz => hxC ((hzero i x (hUm i hi)).mpr hz)
        have hnp : ¬0 < f i x := fun hp => hxI ((hsign i x (hUm i hi)).mpr hp)
        exact lt_of_le_of_ne (le_of_not_gt hnp) hne
      have hnonpos (i : ι) : ρ i x * f i x ≤ 0 := by
        by_cases hi : ρ i x = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_nonpos_of_nonneg_of_nonpos (ρ.nonneg i x) (hneg i hi).le
      have hlt : G x < 0 := Finset.sum_neg' (fun i _ => hnonpos i)
        ⟨j, Finset.mem_univ j, mul_neg_of_pos_of_neg hj (hneg j hj.ne')⟩
      exact hlt.ne
  refine ⟨G, W, hG, hWo, hCW, ?_, ?_⟩
  · intro x hx
    exact ⟨hGzero, fun hz => by_contra fun hn => hGsign hx hn hz⟩
  · intro x hx
    obtain ⟨j, hj⟩ := ρ.exists_pos_of_mem hx
    have hxj : x ∈ U j := hUm j hj.ne'
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp (hr j x hxj)
    have hv' : fderiv ℝ (f j) x v ≠ 0 := by simpa using hv
    obtain ⟨v, hv⟩ : ∃ v, 0 < fderiv ℝ (f j) x v := by
      rcases lt_or_gt_of_ne hv' with hn | hp
      · exact ⟨-v, by simpa only [map_neg] using neg_pos.mpr hn⟩
      · exact ⟨v, hp⟩
    have hderpos (i : ι) (hi : ρ i x ≠ 0) : 0 < fderiv ℝ (f i) x v := by
      have hxi := hUm i hi
      apply ((hf j).contDiffAt ((hU j).mem_nhds hxj)).differentiableAt (by simp)
        |>.hasFDerivAt.apply_pos_of_eventually_nonneg
          (((hf i).contDiffAt ((hU i).mem_nhds hxi)).differentiableAt (by simp)).hasFDerivAt
          ((hzero j x hxj).mp hx) ((hzero i x hxi).mp hx) (hr i x hxi) ?_ hv
      filter_upwards [(hU j).mem_nhds hxj, (hU i).mem_nhds hxi] with y hyj hyi
      exact fun hy => ((hsign i y hyi).mp ((hsign j y hyj).mpr hy)).le
    have hder (i : ι) : fderiv ℝ (fun y => ρ i y * f i y) x v =
        ρ i x * fderiv ℝ (f i) x v := by
      by_cases hi : x ∈ tsupport (ρ i)
      · have hfi := ((hf i).contDiffAt ((hU i).mem_nhds (hρ i hi))).differentiableAt (by simp)
        have hρi := (ρ i).contMDiff.contDiff.differentiable (by simp) x
        rw [fderiv_fun_mul hρi hfi]
        simp only [add_apply, smul_apply, smul_eq_mul,
          (hzero i x (hρ i hi)).mp hx, zero_mul, add_zero]
      · have hρzero := notMem_tsupport_iff_eventuallyEq.mp hi
        have hprod : (fun y => ρ i y * f i y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [hρzero] with y hy
          simp only [hy, Pi.zero_apply, zero_mul]
        rw [hprod.fderiv_eq, fderiv_const_apply, image_eq_zero_of_notMem_tsupport hi]
        simp
    have hsum : fderiv ℝ G x v = ∑ i, ρ i x * fderiv ℝ (f i) x v := by
      rw [show G = fun y => ∑ i, ρ i y * f i y from rfl,
        fderiv_fun_sum (fun i _ => (hterms i).differentiable (by simp) x)]
      simp only [sum_apply, hder]
    have hpos : 0 < fderiv ℝ G x v := by
      rw [hsum]
      apply Finset.sum_pos'
      · intro i _
        by_cases hi : ρ i x = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_nonneg (ρ.nonneg i x) (hderpos i hi).le
      · exact ⟨j, Finset.mem_univ j, mul_pos hj (hderpos j hj.ne')⟩
    intro hz
    simp only [hz, zero_apply, lt_self_iff_false] at hpos


theorem exists_circle_embedding_of_local_regular_defining_functions
    {C : Set Plane} (hC : IsJordanCurve C)
    (hreg : ∀ a ∈ C, ∃ U : Set Plane, ∃ f : Plane → ℝ,
      IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
        (∀ x ∈ U, x ∈ C ↔ f x = 0) ∧ fderiv ℝ f a ≠ 0) :
    ∃ γ : AddCircle (1 : ℝ) → Plane,
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ ∧ range γ = C := by
  classical
  have hlocal (a : C) : ∃ V : Set Plane, ∃ g : Plane → ℝ,
      IsOpen V ∧ a.val ∈ V ∧ ContDiffOn ℝ ∞ g V ∧
      (∀ x ∈ V, fderiv ℝ g x ≠ 0) ∧
      (∀ x ∈ V, x ∈ C ↔ g x = 0) ∧ (∀ x ∈ V, x ∈ inside C ↔ 0 < g x) := by
    obtain ⟨U, f, hU, haU, hf, hzero, hr⟩ := hreg a.val a.property
    obtain ⟨V, g, hV, haV, _, _, hg, hrg, hzg, hsg⟩ :=
      exists_signed_regular_defining_function (jordan_curve_theorem hC) hU a.property haU hf hzero hr
    exact ⟨V, g, hV, haV, hg, hrg, hzg, hsg⟩
  choose U f hU hmem hf hr hzero hsign using hlocal
  have hcover : C ⊆ ⋃ a, U a := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hC.isCompact.elim_finite_subcover U hU hcover
  have hfinite : C ⊆ ⋃ a : s, U a.val := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨haS, hxU⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a, haS⟩, hxU⟩
  obtain ⟨G, W, hG, hW, hCW, hzeroW, hGreg⟩ :=
    exists_regular_defining_function_of_signed_finite_cover hC.isClosed (fun a : s => U a.val)
      (fun a => hU a.val) hfinite (fun a : s => f a.val) (fun a => hf a.val)
      (fun a => hzero a.val) (fun a => hsign a.val) (fun a => hr a.val)
  have hlevel : {x | x ∈ W ∧ G x = 0} = C := by
    ext x
    exact ⟨fun hx => (hzeroW x hx.1).mpr hx.2,
      fun hx => ⟨hCW hx, (hzeroW x (hCW hx)).mp hx⟩⟩
  obtain ⟨γ, hγ, hγrange⟩ := exists_circle_embedding_of_isCompact_isConnected_regular_level
    (by simp [Plane]) hW hG.contDiffOn (hlevel.symm ▸ hC.isCompact)
      (hlevel.symm ▸ hC.isConnected) (fun x hx hxG => hGreg x ((hzeroW x hx).mpr hxG))
  exact ⟨γ, hγ, hγrange.trans hlevel⟩


end DifferentialGeometry.Topology.PlanarJordan
