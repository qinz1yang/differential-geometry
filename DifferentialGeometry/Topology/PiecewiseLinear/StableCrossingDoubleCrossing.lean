/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingNormalizer
import DifferentialGeometry.Topology.PiecewiseLinear.NormalCrossingTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isPLHomeomorphOn_univ_of_affineEquiv (T : E ≃ᵃ[ℝ] F) :
    IsPLHomeomorphOn T univ univ := by
  refine ⟨bijOn_univ.mpr T.bijective, isPiecewiseAffineOn_of_affine T.toAffineMap isOpen_univ,
    (isPiecewiseAffineOn_of_affine T.symm.toAffineMap isOpen_univ).congr fun y _ => ?_⟩
  have hex : ∃ x ∈ (univ : Set E), T x = y := ⟨T.symm y, mem_univ _, T.apply_symm_apply y⟩
  apply T.injective
  rw [Function.invFunOn_eq hex]
  exact (T.apply_symm_apply y).symm

omit [FiniteDimensional ℝ F] in
theorem isPLHomeomorphOn_image_of_eqOn_comp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] {P : Set E} (hP : IsPolyhedron P) {f : E → G}
    {g : E → F} {k : F → G} (hg : IsPiecewiseAffineOn g P) (hk : IsPiecewiseAffineOn k univ)
    (hfg : EqOn f (k ∘ g) P) (hinj : InjOn f P) : IsPLHomeomorphOn f P (f '' P) := by
  have hkg : IsPiecewiseAffineOn (k ∘ g) P := by
    have hcomp := hk.comp hg
    rwa [preimage_univ, inter_univ] at hcomp
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP (hkg.congr hfg) hinj.bijOn_image

end General

section Topological

theorem eventually_inter_preimage_singleton_subset_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {K V : Set X} (hK : IsCompact K) {g : X → Y}
    (hg : ContinuousOn g K) {y : Y} (hV : ∀ x ∈ K, g x = y → V ∈ 𝓝[K] x) :
    ∀ᶠ w in 𝓝 y, K ∩ g ⁻¹' {w} ⊆ V := by
  set W : Set X := {x | V ∈ 𝓝[K] x}
  have hWo : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    have hx' : V ∈ 𝓝[K] x := hx
    obtain ⟨U, hU, hUV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hx'
    obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.mp hU
    refine Filter.mem_of_superset (hO.mem_nhds hxO) fun x' hx' => ?_
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨O, hO.mem_nhds hx', fun z hz => hUV ⟨hOU hz.1, hz.2⟩⟩
  have hc : IsCompact (g '' (K \ W)) :=
    (hK.diff hWo).image_of_continuousOn (hg.mono sdiff_subset)
  have hy : y ∉ g '' (K \ W) := by
    rintro ⟨x, ⟨hxK, hxW⟩, hxy⟩
    exact hxW (hV x hxK hxy)
  filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hy] with w hw
  rintro x ⟨hxK, hxw⟩
  have hxW : x ∈ W := by
    by_contra hxW
    exact hw ⟨x, ⟨hxK, hxW⟩, hxw⟩
  exact mem_of_mem_nhdsWithin hxK hxW

theorem eventually_mem_image_iff_of_graph {X Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {Sh : Set X} {π : Y → Z} {G : Z → Y} {Hh : Set Z} {y₀ : Y}
    (hπ : ContinuousAt π y₀) (hGπ : ∀ q, π (G q) = q) (hgraph : ∀ x ∈ Sh, G (π (f x)) = f x)
    (hhalf : ∀ x ∈ Sh, π (f x) ∈ Hh) (hnhds : (π ∘ f) '' Sh ∈ 𝓝[Hh] (π y₀)) :
    ∀ᶠ z in 𝓝 y₀, z ∈ f '' Sh ↔ z ∈ range G ∧ π z ∈ Hh := by
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  filter_upwards [hπ.preimage_mem_nhds hU] with z hz
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨π (f x), hgraph x hx⟩, hhalf x hx⟩
  · rintro ⟨⟨q, rfl⟩, hq⟩
    rw [mem_preimage, hGπ] at hz
    rw [hGπ] at hq
    obtain ⟨x, hx, hxq⟩ := hUsub ⟨hz, hq⟩
    refine ⟨x, hx, ?_⟩
    rw [← hgraph x hx]
    exact congrArg G hxq

end Topological

section NormalForm

variable {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {a b : ℝ × ℝ → ℝ}
  {H : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ)}

theorem exists_normalForm_of_two_graphs (hH : IsPLHomeomorphOn H univ univ)
    (hHt : ∀ p, (H p).2.2 = p.2.2)
    (hHa : H '' range (fun q : ℝ × ℝ => (a q, q.1, q.2)) = {p | p.1 = 0})
    (hHb : H '' range (fun q : ℝ × ℝ => (q.1, b q, q.2)) = {p | p.2.1 = 0})
    {y₀ : EuclideanSpace ℝ (Fin 3)} (hy₀a : A y₀ ∈ range (fun q : ℝ × ℝ => (a q, q.1, q.2)))
    (hy₀b : A y₀ ∈ range (fun q : ℝ × ℝ => (q.1, b q, q.2))) :
    ∃ (k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (P Q : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
      (τ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      IsPLHomeomorphOn k univ univ ∧ k y₀ = 0 ∧ Module.finrank ℝ P = 2 ∧
        Module.finrank ℝ Q = 2 ∧ Module.finrank ℝ (P ⊓ Q : Submodule ℝ _) = 1 ∧ P ⊔ Q = ⊤ ∧
        (∃ w ∈ P ⊓ Q, τ w = 1) ∧
        (∀ z, k z ∈ P ↔ A z ∈ range (fun q : ℝ × ℝ => (a q, q.1, q.2))) ∧
        (∀ z, k z ∈ Q ↔ A z ∈ range (fun q : ℝ × ℝ => (q.1, b q, q.2))) ∧
        ∀ z, τ (k z) = (A z).2.2 - (A y₀).2.2 := by
  set L := A.linear
  set p₀ := H (A y₀) with hp₀
  let T : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-p₀)).trans L.symm.toAffineEquiv
  let k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := T ∘ H ∘ A
  have hk : IsPLHomeomorphOn k univ univ :=
    ((isPLHomeomorphOn_univ_of_affineEquiv A).trans hH).trans
      (isPLHomeomorphOn_univ_of_affineEquiv T)
  have hLk : ∀ z, L (k z) = -p₀ + H (A z) := by
    intro z
    change L (L.symm (-p₀ +ᵥ H (A z))) = -p₀ + H (A z)
    rw [LinearEquiv.apply_symm_apply, vadd_eq_add]
  have hp₀a : p₀.1 = 0 := by
    have hmem : p₀ ∈ H '' range (fun q : ℝ × ℝ => (a q, q.1, q.2)) := ⟨A y₀, hy₀a, rfl⟩
    rw [hHa] at hmem
    exact hmem
  have hp₀b : p₀.2.1 = 0 := by
    have hmem : p₀ ∈ H '' range (fun q : ℝ × ℝ => (q.1, b q, q.2)) := ⟨A y₀, hy₀b, rfl⟩
    rw [hHb] at hmem
    exact hmem
  let φu : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ (ℝ × ℝ)).comp L.toLinearMap
  let φv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp ((LinearMap.snd ℝ ℝ (ℝ × ℝ)).comp L.toLinearMap)
  let τ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ ℝ ℝ).comp ((LinearMap.snd ℝ ℝ (ℝ × ℝ)).comp L.toLinearMap)
  have hφu : ∀ z, φu z = (L z).1 := fun _ => rfl
  have hφv : ∀ z, φv z = (L z).2.1 := fun _ => rfl
  have hτ : ∀ z, τ z = (L z).2.2 := fun _ => rfl
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hφu0 : φu ≠ 0 := by
    intro h0
    have h1 := LinearMap.congr_fun h0 (L.symm (1, 0, 0))
    rw [hφu, LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at h1
    exact one_ne_zero h1
  have hφv0 : φv ≠ 0 := by
    intro h0
    have h1 := LinearMap.congr_fun h0 (L.symm (0, 1, 0))
    rw [hφv, LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at h1
    exact one_ne_zero h1
  have hP2 : Module.finrank ℝ (LinearMap.ker φu) = 2 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφu0
    rw [hdim] at h1
    omega
  have hQ2 : Module.finrank ℝ (LinearMap.ker φv) = 2 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφv0
    rw [hdim] at h1
    omega
  have hwP : L.symm (0, 1, 0) ∈ LinearMap.ker φu := by
    rw [LinearMap.mem_ker, hφu, LinearEquiv.apply_symm_apply]
  have hsup : LinearMap.ker φu ⊔ LinearMap.ker φv = ⊤ :=
    sup_ker_eq_top_of_apply_ne_zero (LinearMap.ker φu) φv hwP (by
      rw [hφv, LinearEquiv.apply_symm_apply]
      exact one_ne_zero)
  have hinf : Module.finrank ℝ (LinearMap.ker φu ⊓ LinearMap.ker φv : Submodule ℝ _) = 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker φu) (LinearMap.ker φv)
    rw [hsup, finrank_top, hdim, hP2, hQ2] at h1
    omega
  refine ⟨k, LinearMap.ker φu, LinearMap.ker φv, τ, hk, ?_, hP2, hQ2, hinf, hsup, ?_, ?_, ?_, ?_⟩
  · apply L.injective
    rw [hLk, map_zero, hp₀, neg_add_cancel]
  · refine ⟨L.symm (0, 0, 1), Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, hφu, LinearEquiv.apply_symm_apply]
    · rw [LinearMap.mem_ker, hφv, LinearEquiv.apply_symm_apply]
    · rw [hτ, LinearEquiv.apply_symm_apply]
  · intro z
    rw [LinearMap.mem_ker, hφu, hLk, Prod.fst_add, Prod.fst_neg, hp₀a, neg_zero, zero_add,
      ← H.injective.mem_set_image, hHa]
    rfl
  · intro z
    rw [LinearMap.mem_ker, hφv, hLk, Prod.snd_add, Prod.snd_neg, Prod.fst_add, Prod.fst_neg,
      hp₀b, neg_zero, zero_add, ← H.injective.mem_set_image, hHb]
    rfl
  · intro z
    rw [hτ, hLk]
    simp only [Prod.snd_add, Prod.snd_neg, hp₀, hHt]
    ring

end NormalForm

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem hasPLNormalDoubleCrossingAt_chart_of_isStableCrossingBlock [T2Space M]
    (D : SingularTwoCell M) {BdM : Set M} (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock (⇑D) D.domain ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet (⇑D) D.domain)
    (hyB : y ∈ innerChartBlock ec A r tlo) :
    HasPLNormalDoubleCrossingAt (⇑ec ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' ec.source)
      (⇑ec '' (ec.source ∩ BdM)) (ec y) := by
  obtain ⟨hr0, hη, hLa, hLb, hmar, -, -, hside, hpre, hdisj, hgA, hgB, hplA, hplB, hnbA, hnbB,
    hLipa, hLipb, hpa, hpb⟩ := id h
  have htlo : tlo ≤ 0 := by
    rcases hside with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]
      linarith
    · exact le_of_eq e
  have hyC : y ∈ chartBlock ec A r tlo := chartBlock_mono_of_half ec A hr0.le htlo hyB
  have hysrc : y ∈ ec.source := hyC.1
  obtain ⟨⟨xa, hxaA, hxay⟩, ⟨xb, hxbB, hxby⟩⟩ :=
    sheets_nonempty_of_isStableCrossingBlock h hy hyC
  have hxay' : D xa = y := hxay
  have hxby' : D xb = y := hxby
  set f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) := ⇑ec ∘ ⇑D with hf
  set πA : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ := fun z => ((A z).2.1, (A z).2.2) with hπAdef
  set πB : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ := fun z => ((A z).1, (A z).2.2) with hπBdef
  set GA : ℝ × ℝ → EuclideanSpace ℝ (Fin 3) := fun q => A.symm (a q, q.1, q.2) with hGAdef
  set GB : ℝ × ℝ → EuclideanSpace ℝ (Fin 3) := fun q => A.symm (q.1, b q, q.2) with hGBdef
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hπA : Continuous πA := hAc.snd.fst.prodMk hAc.snd.snd
  have hπB : Continuous πB := hAc.fst.prodMk hAc.snd.snd
  have hGAπ : ∀ q, πA (GA q) = q := fun q => by
    simp only [hπAdef, hGAdef, AffineEquiv.apply_symm_apply, Prod.mk.eta]
  have hGBπ : ∀ q, πB (GB q) = q := fun q => by
    simp only [hπBdef, hGBdef, AffineEquiv.apply_symm_apply, Prod.mk.eta]
  have hSsub : ∀ x ∈ SA ∪ SB, x ∈ D.domain ∧ D x ∈ chartBlock ec A r tlo := fun x hx => by
    rw [← hpre] at hx
    exact hx
  have hgraphA : ∀ x ∈ SA, GA (πA (f x)) = f x := fun x hx => by
    apply A.injective
    simp only [hGAdef, hπAdef, AffineEquiv.apply_symm_apply]
    exact Prod.ext (hgA x hx).symm rfl
  have hgraphB : ∀ x ∈ SB, GB (πB (f x)) = f x := fun x hx => by
    apply A.injective
    simp only [hGBdef, hπBdef, AffineEquiv.apply_symm_apply]
    exact Prod.ext rfl (Prod.ext (hgB x hx).symm rfl)
  have hhalfA : ∀ x ∈ SA, πA (f x) ∈ blockHalfPlane tlo := fun x hx => by
    intro htz
    have hC := (hSsub x (Or.inl hx)).2.2.2.2.1
    rw [htz] at hC
    exact hC
  have hhalfB : ∀ x ∈ SB, πB (f x) ∈ blockHalfPlane tlo := fun x hx => by
    intro htz
    have hC := (hSsub x (Or.inr hx)).2.2.2.2.1
    rw [htz] at hC
    exact hC
  have hinjA : InjOn f SA := fun x hx x' hx' hxx => hplA.bijOn.injOn hx hx' (congrArg πA hxx)
  have hinjB : InjOn f SB := fun x hx x' hx' hxx => hplB.bijOn.injOn hx hx' (congrArg πB hxx)
  have hdomP : IsPolyhedron D.domain := D.isPLBall_domain.isPolyhedron
  have hxaI : D xa ∈ innerChartBlock ec A r tlo := by rw [hxay']; exact hyB
  have hxbI : D xb ∈ innerChartBlock ec A r tlo := by rw [hxby']; exact hyB
  obtain ⟨hSAnb, hQAnb⟩ := hnbA xa hxaA hxaI
  obtain ⟨hSBnb, hQBnb⟩ := hnbB xb hxbB hxbI
  have hxadom : xa ∈ D.domain := (hSsub xa (Or.inl hxaA)).1
  have hxbdom : xb ∈ D.domain := (hSsub xb (Or.inr hxbB)).1
  obtain ⟨A', hA'poly, hA'sub, hA'nb⟩ :=
    hdomP.isLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin hxadom hSAnb
  obtain ⟨B', hB'poly, hB'sub, hB'nb⟩ :=
    hdomP.isLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin hxbdom hSBnb
  have hA'SA : A' ⊆ SA := fun x hx => (hA'sub hx).2
  have hB'SB : B' ⊆ SB := fun x hx => (hB'sub hx).2
  have hxaA' : xa ∈ A' := mem_of_mem_nhdsWithin hxadom hA'nb
  have hxbB' : xb ∈ B' := mem_of_mem_nhdsWithin hxbdom hB'nb
  have hfxa : f xa = ec y := by rw [hf, Function.comp_apply, hxay']
  have hfxb : f xb = ec y := by rw [hf, Function.comp_apply, hxby']
  have hSAP : SA ⊆ D.domain ∩ ⇑D ⁻¹' ec.source := fun x hx =>
    ⟨(hSsub x (Or.inl hx)).1, (hSsub x (Or.inl hx)).2.1⟩
  have hSBP : SB ⊆ D.domain ∩ ⇑D ⁻¹' ec.source := fun x hx =>
    ⟨(hSsub x (Or.inr hx)).1, (hSsub x (Or.inr hx)).2.1⟩
  have hA'nbP : A' ∈ 𝓝[D.domain ∩ ⇑D ⁻¹' ec.source] xa := nhdsWithin_mono xa inter_subset_left hA'nb
  have hB'nbP : B' ∈ 𝓝[D.domain ∩ ⇑D ⁻¹' ec.source] xb := nhdsWithin_mono xb inter_subset_left hB'nb
  have hGA : IsPiecewiseAffineOn GA univ :=
    (hpa.prod_mk (isPiecewiseAffineOn_of_affine (AffineMap.id ℝ (ℝ × ℝ)) isOpen_univ)).affine_comp
      A.symm.toAffineMap
  have hGB : IsPiecewiseAffineOn GB univ := by
    have hfst : IsPiecewiseAffineOn (fun q : ℝ × ℝ => q.1) univ :=
      isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ ℝ).toAffineMap isOpen_univ
    have hsnd : IsPiecewiseAffineOn (fun q : ℝ × ℝ => q.2) univ :=
      isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
    exact (hfst.prod_mk (hpb.prod_mk hsnd)).affine_comp A.symm.toAffineMap
  have hplA' : IsPLHomeomorphOn f A' (f '' A') :=
    isPLHomeomorphOn_image_of_eqOn_comp hA'poly
      (hplA.isPiecewiseAffineOn.mono_of_isPolyhedron hA'poly hA'SA) hGA
      (fun x hx => (hgraphA x (hA'SA hx)).symm) (hinjA.mono hA'SA)
  have hplB' : IsPLHomeomorphOn f B' (f '' B') :=
    isPLHomeomorphOn_image_of_eqOn_comp hB'poly
      (hplB.isPiecewiseAffineOn.mono_of_isPolyhedron hB'poly hB'SB) hGB
      (fun x hx => (hgraphB x (hB'SB hx)).symm) (hinjB.mono hB'SB)
  have hnA : (πA ∘ f) '' A' ∈ 𝓝[blockHalfPlane tlo] (πA (ec y)) := by
    have hA'SAnb : A' ∈ 𝓝[SA] xa :=
      nhdsWithin_mono xa (fun x hx => (hSsub x (Or.inl hx)).1) hA'nb
    have hcont := hplA.isPiecewiseAffineOn_invFunOn.continuousOn
    have htend : Filter.Tendsto (Function.invFunOn (blockSheetProjA ec A ⇑D) SA)
        (𝓝[blockSheetProjA ec A ⇑D '' SA] (blockSheetProjA ec A ⇑D xa)) (𝓝[SA] xa) := by
      have h1 := (hcont _ (hplA.bijOn.mapsTo hxaA)).tendsto_nhdsWithin
        hplA.bijOn.surjOn.mapsTo_invFunOn
      rwa [hplA.bijOn.invOn_invFunOn.1 hxaA] at h1
    have h1 : blockSheetProjA ec A ⇑D '' A' ∈
        𝓝[blockSheetProjA ec A ⇑D '' SA] (blockSheetProjA ec A ⇑D xa) := by
      filter_upwards [htend hA'SAnb, self_mem_nhdsWithin] with q hq hqQ
      exact ⟨_, hq, hplA.bijOn.invOn_invFunOn.2 hqQ⟩
    have hpt : πA (ec y) = blockSheetProjA ec A ⇑D xa := by
      rw [← hfxa]
      rfl
    rw [hpt]
    exact nhdsWithin_le_of_mem hQAnb h1
  have hnB : (πB ∘ f) '' B' ∈ 𝓝[blockHalfPlane tlo] (πB (ec y)) := by
    have hB'SBnb : B' ∈ 𝓝[SB] xb :=
      nhdsWithin_mono xb (fun x hx => (hSsub x (Or.inr hx)).1) hB'nb
    have hcont := hplB.isPiecewiseAffineOn_invFunOn.continuousOn
    have htend : Filter.Tendsto (Function.invFunOn (blockSheetProjB ec A ⇑D) SB)
        (𝓝[blockSheetProjB ec A ⇑D '' SB] (blockSheetProjB ec A ⇑D xb)) (𝓝[SB] xb) := by
      have h1 := (hcont _ (hplB.bijOn.mapsTo hxbB)).tendsto_nhdsWithin
        hplB.bijOn.surjOn.mapsTo_invFunOn
      rwa [hplB.bijOn.invOn_invFunOn.1 hxbB] at h1
    have h1 : blockSheetProjB ec A ⇑D '' B' ∈
        𝓝[blockSheetProjB ec A ⇑D '' SB] (blockSheetProjB ec A ⇑D xb) := by
      filter_upwards [htend hB'SBnb, self_mem_nhdsWithin] with q hq hqQ
      exact ⟨_, hq, hplB.bijOn.invOn_invFunOn.2 hqQ⟩
    have hpt : πB (ec y) = blockSheetProjB ec A ⇑D xb := by
      rw [← hfxb]
      rfl
    rw [hpt]
    exact nhdsWithin_le_of_mem hQBnb h1
  have hkeyA : ∀ᶠ z in 𝓝 (ec y), z ∈ f '' A' ↔ z ∈ range GA ∧ πA z ∈ blockHalfPlane tlo :=
    eventually_mem_image_iff_of_graph hπA.continuousAt hGAπ (fun x hx => hgraphA x (hA'SA hx))
      (fun x hx => hhalfA x (hA'SA hx)) hnA
  have hkeyB : ∀ᶠ z in 𝓝 (ec y), z ∈ f '' B' ↔ z ∈ range GB ∧ πB z ∈ blockHalfPlane tlo :=
    eventually_mem_image_iff_of_graph hπB.continuousAt hGBπ (fun x hx => hgraphB x (hB'SB hx))
      (fun x hx => hhalfB x (hB'SB hx)) hnB
  have hrA : ∀ z, z ∈ range GA ↔ A z ∈ range (fun q : ℝ × ℝ => (a q, q.1, q.2)) := fun z =>
    ⟨fun ⟨q, hq⟩ => ⟨q, by rw [← hq]; simp only [hGAdef, AffineEquiv.apply_symm_apply]⟩,
      fun ⟨q, hq⟩ => ⟨q, by
        simp only [hGAdef]
        rw [← A.symm_apply_apply z, ← hq]⟩⟩
  have hrB : ∀ z, z ∈ range GB ↔ A z ∈ range (fun q : ℝ × ℝ => (q.1, b q, q.2)) := fun z =>
    ⟨fun ⟨q, hq⟩ => ⟨q, by rw [← hq]; simp only [hGBdef, AffineEquiv.apply_symm_apply]⟩,
      fun ⟨q, hq⟩ => ⟨q, by
        simp only [hGBdef]
        rw [← A.symm_apply_apply z, ← hq]⟩⟩
  obtain ⟨Hn, hHpl, hHt, hHa, hHb⟩ :=
    exists_pl_homeomorph_two_graphs_to_coordinate_planes_of_lipschitz hpa hpb hη hLa hLb hmar
      hLipa hLipb
  have hya : A (ec y) ∈ range (fun q : ℝ × ℝ => (a q, q.1, q.2)) := by
    rw [← hrA, ← hfxa, ← hgraphA xa hxaA]
    exact mem_range_self _
  have hyb : A (ec y) ∈ range (fun q : ℝ × ℝ => (q.1, b q, q.2)) := by
    rw [← hrB, ← hfxb, ← hgraphB xb hxbB]
    exact mem_range_self _
  obtain ⟨k, P, Q, τ, hk, hk0, hP2, hQ2, hinf, hsup, hw, hPiff, hQiff, hτ⟩ :=
    exists_normalForm_of_two_graphs hHpl hHt hHa hHb hya hyb
  have hfib0 : ∀ᶠ w in 𝓝 y, D.domain ∩ ⇑D ⁻¹' {w} ⊆ A' ∪ B' := by
    refine eventually_inter_preimage_singleton_subset_of_isCompact hdomP.isCompact D.continuousOn ?_
    intro x hx hxy
    have hxAB : x ∈ SA ∪ SB := by
      rw [← hpre]
      refine ⟨hx, ?_⟩
      rw [mem_preimage, hxy]
      exact hyC
    have hfx : f x = ec y := by rw [hf, Function.comp_apply, hxy]
    rcases hxAB with hxA | hxB
    · have hxe : x = xa := hinjA hxA hxaA (hfx.trans hfxa.symm)
      rw [hxe]
      exact Filter.mem_of_superset hA'nb subset_union_left
    · have hxe : x = xb := hinjB hxB hxbB (hfx.trans hfxb.symm)
      rw [hxe]
      exact Filter.mem_of_superset hB'nb subset_union_right
  have hfib : ∀ᶠ z in 𝓝 (ec y), (D.domain ∩ ⇑D ⁻¹' ec.source) ∩ (⇑ec ∘ ⇑D) ⁻¹' {z} ⊆ A' ∪ B' := by
    have ht : Filter.Tendsto ec.symm (𝓝 (ec y)) (𝓝 y) := by
      have hc := (ec.continuousAt_symm (ec.map_source hysrc)).tendsto
      rwa [ec.left_inv hysrc] at hc
    filter_upwards [ht.eventually hfib0] with z hz
    rintro x ⟨⟨hxdom, hxsrc⟩, hxz⟩
    apply hz
    refine ⟨hxdom, ?_⟩
    have hxz' : ec (D x) = z := hxz
    change D x = ec.symm z
    rw [← hxz', ec.left_inv hxsrc]
  have hdisj' : Disjoint A' B' := hdisj.mono hA'SA hB'SB
  have hA'P : A' ⊆ D.domain ∩ ⇑D ⁻¹' ec.source := hA'SA.trans hSAP
  have hB'P : B' ⊆ D.domain ∩ ⇑D ⁻¹' ec.source := hB'SB.trans hSBP
  have hBd : ec y ∈ ⇑ec '' (ec.source ∩ BdM) ↔ y ∈ BdM := mem_image_source_inter_iff ec BdM hysrc
  have hcrossI : (∀ᶠ z in 𝓝 (ec y), πA z ∈ blockHalfPlane tlo ∧ πB z ∈ blockHalfPlane tlo) →
      HasPLCrossingAt (f '' A') (f '' B') (ec y) := fun hev =>
    ⟨univ, univ, k, P, Q, 0, 0, isOpen_univ, isOpen_univ, mem_univ _, hk, hk0, hP2, hQ2, hinf,
      hsup, Or.inl rfl, Or.inl rfl, Or.inl rfl, by
        filter_upwards [hkeyA, hkeyB, hev] with z hzA hzB hz
        refine ⟨?_, ?_⟩
        · rw [hzA, hPiff, ← hrA]
          simp only [hz.1, and_true, LinearMap.zero_apply, le_refl]
        · rw [hzB, hQiff, ← hrB]
          simp only [hz.2, and_true, LinearMap.zero_apply, le_refl]⟩
  rcases hside with ⟨htr, hdisBd⟩ | ⟨ht0, hAℓ, -⟩
  · have hyBd : y ∉ BdM := fun hyb => disjoint_left.mp hdisBd hyC hyb
    have hhalf : ∀ p : ℝ × ℝ, p ∈ blockHalfPlane tlo := fun p => by
      intro htz
      rw [htr] at htz
      linarith
    exact Or.inr ⟨fun hmem => hyBd (hBd.mp hmem), xa, xb, A', B', hxaA', hxbB', hfxa, hfxb,
      hA'P, hB'P, hdisj', hA'nbP, hB'nbP, hplA', hplB',
      hcrossI (Filter.Eventually.of_forall fun z => ⟨hhalf _, hhalf _⟩), hfib⟩
  · subst ht0
    have hyt : (A (ec y)).2.2 = ℓ (ec y) := hAℓ (ec y)
    by_cases hy0 : ℓ (ec y) = 0
    · have hyt0 : (A (ec y)).2.2 = 0 := hyt.trans hy0
      refine Or.inl ⟨hBd.mpr ((hBdchart y hysrc).mpr hy0), {z | 0 ≤ τ (k z)}, xa, xb, A', B',
        hxaA', hxbB', hfxa, hfxb, hA'P, hB'P, hdisj', hA'nbP, hB'nbP, hplA', hplB',
        ⟨univ, univ, k, P, Q, τ, isOpen_univ, isOpen_univ, mem_univ _, hk, hk0, hP2, hQ2, hinf,
          hsup, hw, ?_⟩, hfib⟩
      filter_upwards [hkeyA, hkeyB] with z hzA hzB
      refine ⟨Iff.rfl, ?_, ?_⟩
      · rw [hzA, hPiff, ← hrA, hτ, hyt0, sub_zero]
        simp only [blockHalfPlane, mem_ofPred_eq, hπAdef, true_implies]
      · rw [hzB, hQiff, ← hrB, hτ, hyt0, sub_zero]
        simp only [blockHalfPlane, mem_ofPred_eq, hπBdef, true_implies]
    · have hyBd : y ∉ BdM := fun hyb => hy0 ((hBdchart y hysrc).mp hyb)
      have hpos : 0 < (A (ec y)).2.2 := by
        have hge : (0 : ℝ) ≤ (A (ec y)).2.2 := hyC.2.2.2.1
        rw [hyt] at hge ⊢
        exact lt_of_le_of_ne hge (Ne.symm hy0)
      have hev : ∀ᶠ z in 𝓝 (ec y), 0 < (A z).2.2 :=
        (hAc.snd.snd.tendsto (ec y)).eventually (lt_mem_nhds hpos)
      have hmemHalf : ∀ p : ℝ × ℝ, 0 ≤ p.2 → p ∈ blockHalfPlane 0 := fun p hp => by
        intro _
        exact hp
      exact Or.inr ⟨fun hmem => hyBd (hBd.mp hmem), xa, xb, A', B', hxaA', hxbB', hfxa, hfxb,
        hA'P, hB'P, hdisj', hA'nbP, hB'nbP, hplA', hplB',
        hcrossI (hev.mono fun z hz => ⟨hmemHalf _ hz.le, hmemHalf _ hz.le⟩), hfib⟩

theorem hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock [T2Space M] (D : SingularTwoCell M)
    {BdM : Set M} (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock (⇑D) D.domain ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet (⇑D) D.domain)
    (hyB : y ∈ innerChartBlock ec A r tlo) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e.source)
        (⇑e '' (e.source ∩ BdM)) (e y) := by
  let _ := hℓ
  exact exists_crossing_chart_mem_atlas
    (hasPLNormalDoubleCrossingAt_chart_of_isStableCrossingBlock D ec ℓ hBdchart h hy hyB)
    D.continuousOn hec hyB.1

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
