/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.InwardPushStages
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialZero
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section ModelBridge

theorem isPLOn_iff_isPiecewiseAffineOn {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} : IsPLOn n m f s ↔ IsPiecewiseAffineOn f s := by
  have hchart : chartAt (EuclideanSpace ℝ (Fin m)) (0 : EuclideanSpace ℝ (Fin m)) =
      OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin m)) := chartAt_self_eq
  have he : OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin m)) ∈
      (plGroupoid m).maximalAtlas (EuclideanSpace ℝ (Fin m)) := by
    rw [← hchart]
    exact StructureGroupoid.chart_mem_maximalAtlas (plGroupoid m) 0
  have hmap : MapsTo f s (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin m))).source := by
    intro x _
    simp
  rw [isPLOn_iff_isPiecewiseAffineOn_comp_chart _ he hmap]
  exact ⟨fun h => h.congr fun _ _ => rfl, fun h => h.congr fun _ _ => rfl⟩

end ModelBridge

section Conjugation

variable {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_isPLHomeomorphInto_of_isPLHomeomorphOn {P Q : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M₁} {v : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hv : IsPLHomeomorphInto 3 v Q)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} (hH : IsPLHomeomorphOn H P Q) :
    IsPLHomeomorphInto 3 (v ∘ H ∘ Function.invFunOn u P) (u '' P) ∧
      (v ∘ H ∘ Function.invFunOn u P) '' (u '' P) = v '' Q := by
  set p : M₁ → EuclideanSpace ℝ (Fin 3) := Function.invFunOn u P with hp
  have hleft : LeftInvOn p u P := hu.injOn.leftInvOn_invFunOn
  have hpmaps : MapsTo p (u '' P) P := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hleft hx]
    exact hx
  have hppl : IsPLOn 3 3 p (u '' P) := hu.isPLOn_inverse hleft
  have hHpl : IsPLOn 3 3 H P := isPLOn_iff_isPiecewiseAffineOn.mpr hH.isPiecewiseAffineOn
  have hcomp1 : IsPLOn 3 3 (H ∘ p) (u '' P) := IsPLOn.comp_of_mapsTo hHpl hppl hpmaps
  have hHmaps : MapsTo (H ∘ p) (u '' P) Q := fun y hy => hH.bijOn.mapsTo (hpmaps hy)
  have hfpl : IsPLOn 3 3 (v ∘ H ∘ p) (u '' P) :=
    IsPLOn.comp_of_mapsTo hv.isPLOn hcomp1 hHmaps
  have hval : ∀ x ∈ P, (v ∘ H ∘ p) (u x) = v (H x) := by
    intro x hx
    simp only [Function.comp_apply, hleft hx]
  have himage : (v ∘ H ∘ p) '' (u '' P) = v '' Q := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hval x hx]
      exact ⟨H x, hH.bijOn.mapsTo hx, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hH.bijOn.surjOn hq
      exact ⟨u x, ⟨x, hx, rfl⟩, hval x hx⟩
  have hinj : InjOn (v ∘ H ∘ p) (u '' P) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    rw [hval x hx, hval y hy] at hxy
    exact congrArg u
      (hH.bijOn.injOn hx hy (hv.injOn (hH.bijOn.mapsTo hx) (hH.bijOn.mapsTo hy) hxy))
  refine ⟨⟨hfpl, hinj, fun y hy => ⟨u ∘ Function.invFunOn H P ∘ Function.invFunOn v Q, ?_, ?_⟩⟩,
    himage⟩
  · rw [himage]
    have hvinv : IsPLOn 3 3 (Function.invFunOn v Q) (v '' Q) :=
      hv.isPLOn_inverse hv.injOn.leftInvOn_invFunOn
    have hvmaps : MapsTo (Function.invFunOn v Q) (v '' Q) Q := by
      rintro _ ⟨q, hq, rfl⟩
      rw [hv.injOn.leftInvOn_invFunOn hq]
      exact hq
    have hHinv : IsPLOn 3 3 (Function.invFunOn H P) Q :=
      isPLOn_iff_isPiecewiseAffineOn.mpr hH.isPiecewiseAffineOn_invFunOn
    have hstep : IsPLOn 3 3 (Function.invFunOn H P ∘ Function.invFunOn v Q) (v '' Q) :=
      IsPLOn.comp_of_mapsTo hHinv hvinv hvmaps
    have hstepmaps : MapsTo (Function.invFunOn H P ∘ Function.invFunOn v Q) (v '' Q) P :=
      fun z hz => hH.bijOn.surjOn.mapsTo_invFunOn (hvmaps hz)
    exact (IsPLOn.comp_of_mapsTo hu.isPLOn hstep hstepmaps) y (himage ▸ hy)
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, hleft hx,
      hv.injOn.leftInvOn_invFunOn (hH.bijOn.mapsTo hx), hH.bijOn.invOn_invFunOn.1 hx]

theorem isPLHomeomorphOn_conj {P₀ P Q₀ Q : Set (EuclideanSpace ℝ (Fin 3))} {D : Set M₁}
    {u : EuclideanSpace ℝ (Fin 3) → M₁} {v : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hv : IsPLHomeomorphInto 3 v Q)
    (hP₀ : IsPolyhedron P₀) (hP₀P : P₀ ⊆ P) (hP₀ne : P₀.Nonempty)
    (hQ₀ : IsPolyhedron Q₀) (hQ₀Q : Q₀ ⊆ Q) {g : M₁ → M₂} (hg : IsPLHomeomorphInto 3 g D)
    (hD : u '' P₀ ⊆ D) (hgim : g '' (u '' P₀) = v '' Q₀) :
    IsPLHomeomorphOn (Function.invFunOn v Q ∘ g ∘ u) P₀ Q₀ := by
  obtain ⟨x₀, hx₀⟩ := hP₀ne
  have hM₁ : Nonempty M₁ := ⟨u x₀⟩
  set q : M₂ → EuclideanSpace ℝ (Fin 3) := Function.invFunOn v Q with hq
  set b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := q ∘ g ∘ u with hb
  have hvleft : LeftInvOn q v Q := hv.injOn.leftInvOn_invFunOn
  have hgleft : LeftInvOn (Function.invFunOn g D) g D := hg.injOn.leftInvOn_invFunOn
  have huP₀ : IsPLOn 3 3 u P₀ := hu.isPLOn.mono_of_isPolyhedron hP₀ hP₀P
  have hvQ₀ : IsPLOn 3 3 v Q₀ := hv.isPLOn.mono_of_isPolyhedron hQ₀ hQ₀Q
  have hpre : ∀ x ∈ P₀, ∃ y ∈ Q₀, g (u x) = v y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgim.subset ⟨u x, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨y, hy, hxy.symm⟩
  have hbval : ∀ x ∈ P₀, ∀ y ∈ Q₀, g (u x) = v y → b x = y := by
    intro x hx y hy hxy
    simp only [hb, Function.comp_apply, hxy]
    exact hvleft (hQ₀Q hy)
  have hbmaps : MapsTo b P₀ Q₀ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hpre x hx
    rw [hbval x hx y hy hxy]
    exact hy
  have hbinj : InjOn b P₀ := by
    intro x hx y hy hxy
    obtain ⟨z, hz, hxz⟩ := hpre x hx
    obtain ⟨t, ht, hyt⟩ := hpre y hy
    have hzt : z = t := by
      rw [← hbval x hx z hz hxz, ← hbval y hy t ht hyt, hxy]
    have : g (u x) = g (u y) := by rw [hxz, hyt, hzt]
    exact hu.injOn (hP₀P hx) (hP₀P hy) (hg.injOn (hD ⟨x, hx, rfl⟩) (hD ⟨y, hy, rfl⟩) this)
  have hbsurj : SurjOn b P₀ Q₀ := by
    intro y hy
    obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := hgim.symm.subset ⟨y, hy, rfl⟩
    exact ⟨x, hx, hbval x hx y hy hz⟩
  have hbbij : BijOn b P₀ Q₀ := ⟨hbmaps, hbinj, hbsurj⟩
  have hgu : IsPLOn 3 3 (g ∘ u) P₀ :=
    IsPLOn.comp_of_mapsTo hg.isPLOn huP₀ fun x hx => hD ⟨x, hx, rfl⟩
  have hgumaps : MapsTo (g ∘ u) P₀ (v '' Q) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hpre x hx
    exact ⟨y, hQ₀Q hy, hxy.symm⟩
  have hbpl : IsPiecewiseAffineOn b P₀ :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (hv.isPLOn_inverse hvleft) hgu hgumaps)
  have hcv : MapsTo v Q₀ (g '' D) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hgim.symm.subset ⟨y, hy, rfl⟩
    exact ⟨z, hD hz, hzy⟩
  have hcstep : IsPLOn 3 3 (Function.invFunOn g D ∘ v) Q₀ :=
    IsPLOn.comp_of_mapsTo (hg.isPLOn_inverse hgleft) hvQ₀ hcv
  have hcval : ∀ y ∈ Q₀, ∃ x ∈ P₀, (Function.invFunOn g D ∘ v) y = u x := by
    intro y hy
    obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := hgim.symm.subset ⟨y, hy, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [Function.comp_apply, ← hz]
    exact hgleft (hD ⟨x, hx, rfl⟩)
  have hcmaps : MapsTo (Function.invFunOn g D ∘ v) Q₀ (u '' P) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hcval y hy
    exact ⟨x, hP₀P hx, hxy.symm⟩
  have hcpl : IsPiecewiseAffineOn (Function.invFunOn u P ∘ Function.invFunOn g D ∘ v) Q₀ :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hcstep hcmaps)
  refine ⟨hbbij, hbpl, hcpl.congr ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hcval y hy
  have hleftx : Function.invFunOn u P (u x) = x := hu.injOn.leftInvOn_invFunOn (hP₀P hx)
  have hcy : (Function.invFunOn u P ∘ Function.invFunOn g D ∘ v) y = x := by
    simp only [Function.comp_apply] at hxy ⊢
    rw [hxy, hleftx]
  rw [hcy]
  refine hbinj (hbbij.surjOn.mapsTo_invFunOn hy) hx ?_
  rw [hbbij.invOn_invFunOn.2 hy]
  obtain ⟨z, hz, hxz⟩ := hpre x hx
  have hbx : b x = z := hbval x hx z hz hxz
  have hzy : z = y := by
    have hgux : g (u x) = v y := by
      have h1 : Function.invFunOn g D (v y) = u x := by
        simp only [Function.comp_apply] at hxy
        exact hxy
      obtain ⟨z', ⟨x', hx', rfl⟩, hz'⟩ := hgim.symm.subset ⟨y, hy, rfl⟩
      have h2 : Function.invFunOn g D (v y) = u x' := by
        rw [← hz']
        exact hgleft (hD ⟨x', hx', rfl⟩)
      rw [h1] at h2
      rw [h2, hz']
    rw [hxz] at hgux
    exact hv.injOn (hQ₀Q hz) (hQ₀Q hy) hgux
  rw [hbx, hzy]

end Conjugation

section CellExtension

variable {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_isPLHomeomorphInto_extension_of_cell {d : ℕ} (hd : 0 < d)
    {P Q : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3)}
    {s : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) P)
    (hs : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) Q)
    {u : EuclideanSpace ℝ (Fin 3) → M₁} {v : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hv : IsPLHomeomorphInto 3 v Q)
    {D : Set M₁} {g : M₁ → M₂} (hg : IsPLHomeomorphInto 3 g D)
    (hD : u '' (r '' stdSimplexBoundary d) ⊆ D)
    (hgim : g '' (u '' (r '' stdSimplexBoundary d)) = v '' (s '' stdSimplexBoundary d)) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f (u '' P) ∧ f '' (u '' P) = v '' Q ∧
      EqOn f g (u '' (r '' stdSimplexBoundary d)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hbsub : stdSimplexBoundary (n + 1) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) := fun x hx => hx.1
  have hPsphere : IsPLSphere n (r '' stdSimplexBoundary (n + 1)) :=
    hr.isPLSphere_image_stdSimplexBoundary
  have hQsphere : IsPLSphere n (s '' stdSimplexBoundary (n + 1)) :=
    hs.isPLSphere_image_stdSimplexBoundary
  have hP₀P : r '' stdSimplexBoundary (n + 1) ⊆ P := by
    rw [← hr.image_eq]
    exact image_mono hbsub
  have hQ₀Q : s '' stdSimplexBoundary (n + 1) ⊆ Q := by
    rw [← hs.image_eq]
    exact image_mono hbsub
  have hb := isPLHomeomorphOn_conj hu hv hPsphere.isPolyhedron hP₀P hPsphere.nonempty
    hQsphere.isPolyhedron hQ₀Q hg hD hgim
  obtain ⟨H, hH, hHb⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hr hs hb
  obtain ⟨hf, hfim⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hv hH
  refine ⟨_, hf, hfim, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxP : x ∈ P := hP₀P hx
  have hval : (v ∘ H ∘ Function.invFunOn u P) (u x) = v (H x) := by
    simp only [Function.comp_apply, hu.injOn.leftInvOn_invFunOn hxP]
  rw [hval, hHb hx]
  simp only [Function.comp_apply]
  obtain ⟨y, hy, hxy⟩ := hgim.subset ⟨u x, ⟨x, hx, rfl⟩, rfl⟩
  rw [← hxy]
  exact congrArg v (hv.injOn.leftInvOn_invFunOn (hQ₀Q hy))

theorem exists_isPLHomeomorphOn_of_stdSimplex_dim_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {d : ℕ} (hd : d = 0) {P : Set E} {Q : Set F}
    {r : (Fin (d + 1) → ℝ) → E} {s : (Fin (d + 1) → ℝ) → F}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) P)
    (hs : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) Q) :
    ∃ H : E → F, IsPLHomeomorphOn H P Q := by
  subst hd
  set c : Fin (0 + 1) → ℝ := Pi.single 0 1 with hc
  have hcmem : c ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (0 + 1)) := Convexity.StdSimplex.single_mem_coordinateSet ℝ 0
  have hunique : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (0 + 1)), x = c := by
    intro x hx
    have h1 : ∑ i, x i = 1 := hx.2
    have h2 : ∑ i, c i = 1 := hcmem.2
    rw [Fin.sum_univ_one] at h1 h2
    funext i
    induction i using Fin.cases with
    | zero => rw [h1, h2]
    | succ j => exact j.elim0
  have hP : P = {r c} := by
    rw [← hr.image_eq]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [hunique x hx]
      rfl
    · rintro _ rfl
      exact ⟨c, hcmem, rfl⟩
  have hQ : Q = {s c} := by
    rw [← hs.image_eq]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [hunique x hx]
      rfl
    · rintro _ rfl
      exact ⟨c, hcmem, rfl⟩
  refine ⟨fun _ => s c, ?_⟩
  rw [hP, hQ]
  have hbij : BijOn (fun _ : E => s c) ({r c} : Set E) {s c} :=
    ⟨fun _ _ => rfl, fun x hx y hy _ => hx.trans hy.symm, fun y hy => ⟨r c, rfl, hy.symm⟩⟩
  refine ⟨hbij, ?_, ?_⟩
  · exact (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.const ℝ E (s c))
      (isHPolytope_singleton (r c))).congr fun _ _ => rfl
  · refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.const ℝ F (r c))
      (isHPolytope_singleton (s c))).congr ?_
    intro y hy
    exact hbij.surjOn.mapsTo_invFunOn hy

end CellExtension

section Assembly

universe u

variable {Λ : Type u} {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [TopologicalSpace M₂] [T2Space M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] [Nonempty M₂]

omit [T2Space M₁] [T2Space M₂] in
theorem exists_isPLHomeomorphInto_row (dim : Λ → ℕ) (sourceCell : Λ → Set M₁)
    (targetCell : Λ → Set M₂) (d : ℕ) (fcell : Λ → M₁ → M₂)
    (hSc : ∀ l, IsClosed (sourceCell l)) (hTc : ∀ l, IsClosed (targetCell l))
    (hcell : ∀ l, dim l ≤ d → IsPLHomeomorphInto 3 (fcell l) (sourceCell l))
    (hcellim : ∀ l, dim l ≤ d → fcell l '' sourceCell l = targetCell l)
    (hagree : ∀ l m, dim l ≤ d → dim m ≤ d →
      EqOn (fcell l) (fcell m) (sourceCell l ∩ sourceCell m))
    (hmeet : ∀ l m, dim l ≤ d → dim m ≤ d →
      fcell l '' (sourceCell l ∩ sourceCell m) = targetCell l ∩ targetCell m)
    (hLFs : ∀ x ∈ ⋃ l, sourceCell l, ∃ U ∈ 𝓝 x, {l | (sourceCell l ∩ U).Nonempty}.Finite)
    (hLFt : ∀ y ∈ ⋃ l, targetCell l, ∃ V ∈ 𝓝 y, {l | (targetCell l ∩ V).Nonempty}.Finite) :
    ∃ g : M₁ → M₂, IsPLHomeomorphInto 3 g (⋃ l, ⋃ (_ : dim l ≤ d), sourceCell l) ∧
      (∀ l, dim l ≤ d → g '' sourceCell l = targetCell l) ∧
      ∀ l, dim l ≤ d → EqOn g (fcell l) (sourceCell l) := by
  classical
  have hSunion : (∅ : Set M₁) ∪ ⋃ i : {l : Λ // dim l ≤ d}, sourceCell i.1 =
      ⋃ l, ⋃ (_ : dim l ≤ d), sourceCell l := by
    rw [empty_union, iUnion_subtype]
  have hlocs : ∀ x ∈ (∅ : Set M₁) ∪ ⋃ i : {l : Λ // dim l ≤ d}, sourceCell i.1,
      ∃ U ∈ 𝓝 x, {i : {l : Λ // dim l ≤ d} | (sourceCell i.1 ∩ U).Nonempty}.Finite := by
    intro x hx
    have hxu : x ∈ ⋃ l, sourceCell l := by
      rcases hx with hx | hx
      · exact absurd hx (notMem_empty x)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.1, hi⟩
    obtain ⟨U, hU, hfin⟩ := hLFs x hxu
    refine ⟨U, hU, ?_⟩
    have heq : {i : {l : Λ // dim l ≤ d} | (sourceCell i.1 ∩ U).Nonempty} =
        Subtype.val ⁻¹' {l | (sourceCell l ∩ U).Nonempty} := rfl
    rw [heq]
    exact Set.Finite.preimage Subtype.val_injective.injOn hfin
  have hloct : ∀ y ∈ (∅ : Set M₂) ∪ ⋃ i : {l : Λ // dim l ≤ d}, targetCell i.1,
      ∃ V ∈ 𝓝 y, {i : {l : Λ // dim l ≤ d} | (targetCell i.1 ∩ V).Nonempty}.Finite := by
    intro y hy
    have hyu : y ∈ ⋃ l, targetCell l := by
      rcases hy with hy | hy
      · exact absurd hy (notMem_empty y)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨i.1, hi⟩
    obtain ⟨V, hV, hfin⟩ := hLFt y hyu
    refine ⟨V, hV, ?_⟩
    have heq : {i : {l : Λ // dim l ≤ d} | (targetCell i.1 ∩ V).Nonempty} =
        Subtype.val ⁻¹' {l | (targetCell l ∩ V).Nonempty} := rfl
    rw [heq]
    exact Set.Finite.preimage Subtype.val_injective.injOn hfin
  obtain ⟨G, hG, -, hGS, -⟩ :=
    exists_isPLHomeomorphInto_union_of_locallyFinite_pieces (A := (∅ : Set M₁))
      (B := (∅ : Set M₂)) (S := fun i : {l : Λ // dim l ≤ d} => sourceCell i.1)
      (T := fun i : {l : Λ // dim l ≤ d} => targetCell i.1)
      (F₀ := fun _ => Classical.arbitrary M₂)
      (f := fun i : {l : Λ // dim l ≤ d} => fcell i.1)
      isClosed_empty isClosed_empty (fun i => hSc i.1) (fun i => hTc i.1)
      (isPLHomeomorphInto_empty _) (image_empty _) (fun i => hcell i.1 i.2)
      (fun i => hcellim i.1 i.2) (fun i x hx => absurd hx.1 (notMem_empty x))
      (fun i => by rw [empty_inter, image_empty, empty_inter])
      (fun i j => hagree i.1 j.1 i.2 j.2) (fun i j => hmeet i.1 j.1 i.2 j.2) hlocs hloct
  refine ⟨G, by rwa [hSunion] at hG, fun l hl => ?_, fun l hl => hGS ⟨l, hl⟩⟩
  rw [image_congr (hGS ⟨l, hl⟩), hcellim l hl]

theorem exists_isPLHomeomorphInto_of_labelledCells (dim : Λ → ℕ) (face : Λ → Set Λ)
    (P Q : Λ → Set (EuclideanSpace ℝ (Fin 3)))
    (r : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (s : (l : Λ) → (Fin (dim l + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (u : Λ → EuclideanSpace ℝ (Fin 3) → M₁) (v : Λ → EuclideanSpace ℝ (Fin 3) → M₂)
    (sourceCell : Λ → Set M₁) (targetCell : Λ → Set M₂) (hdim : ∀ l, dim l ≤ 3)
    (hr : ∀ l, IsPLHomeomorphOn (r l) (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim l + 1))) (P l))
    (hs : ∀ l, IsPLHomeomorphOn (s l) (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim l + 1))) (Q l))
    (hu : ∀ l, IsPLHomeomorphInto 3 (u l) (P l))
    (hv : ∀ l, IsPLHomeomorphInto 3 (v l) (Q l))
    (hsourceCell : ∀ l, sourceCell l = u l '' P l)
    (htargetCell : ∀ l, targetCell l = v l '' Q l)
    (hfaceDim : ∀ l m, m ∈ face l → m = l ∨ dim m < dim l)
    (hsourceBoundary : ∀ l, u l '' (r l '' stdSimplexBoundary (dim l)) =
      ⋃ m ∈ face l \ {l}, sourceCell m)
    (htargetBoundary : ∀ l, v l '' (s l '' stdSimplexBoundary (dim l)) =
      ⋃ m ∈ face l \ {l}, targetCell m)
    (hsourceInter : ∀ l m, sourceCell l ∩ sourceCell m = ⋃ k ∈ face l ∩ face m, sourceCell k)
    (htargetInter : ∀ l m, targetCell l ∩ targetCell m = ⋃ k ∈ face l ∩ face m, targetCell k)
    (hLFs : ∀ x ∈ ⋃ l, sourceCell l, ∃ U ∈ 𝓝 x, {l | (sourceCell l ∩ U).Nonempty}.Finite)
    (hLFt : ∀ y ∈ ⋃ l, targetCell l, ∃ V ∈ 𝓝 y, {l | (targetCell l ∩ V).Nonempty}.Finite) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f (⋃ l, sourceCell l) ∧
      ∀ l, f '' sourceCell l = targetCell l := by
  classical
  have hSc : ∀ l, IsClosed (sourceCell l) := by
    intro l
    rw [hsourceCell l]
    exact (((IsPLBall.isPolyhedron ⟨r l, hr l⟩).isCompact).image_of_continuousOn
      (hu l).continuousOn).isClosed
  have hTc : ∀ l, IsClosed (targetCell l) := by
    intro l
    rw [htargetCell l]
    exact (((IsPLBall.isPolyhedron ⟨s l, hs l⟩).isCompact).image_of_continuousOn
      (hv l).continuousOn).isClosed
  have hlowdim : ∀ (d : ℕ) (l m k : Λ), dim l ≤ d + 1 → dim m ≤ d + 1 → l ≠ m →
      k ∈ face l ∩ face m → dim k ≤ d := by
    intro d l m k hl hm hne hk
    rcases hfaceDim l k hk.1 with h1 | h1
    · rcases hfaceDim m k hk.2 with h2 | h2
      · exact absurd (h1.symm.trans h2) hne
      · omega
    · omega
  have hinterSubS : ∀ l m : Λ, l ≠ m → dim l ≤ dim m →
      sourceCell l ∩ sourceCell m ⊆ u m '' (r m '' stdSimplexBoundary (dim m)) := by
    intro l m hne hle
    rw [hsourceInter l m, hsourceBoundary m]
    refine iUnion₂_subset fun k hk => ?_
    have hkm : k ≠ m := by
      intro hkm
      rcases hfaceDim l k hk.1 with h | h
      · exact hne (h.symm.trans hkm)
      · rw [hkm] at h
        omega
    exact subset_biUnion_of_mem ⟨hk.2, hkm⟩
  have key : ∀ d : ℕ, ∃ fc : Λ → M₁ → M₂,
      (∀ l, dim l ≤ d → IsPLHomeomorphInto 3 (fc l) (sourceCell l)) ∧
      (∀ l, dim l ≤ d → fc l '' sourceCell l = targetCell l) ∧
      (∀ l m, dim l ≤ d → dim m ≤ d → EqOn (fc l) (fc m) (sourceCell l ∩ sourceCell m)) ∧
      (∀ l m, dim l ≤ d → dim m ≤ d →
        fc l '' (sourceCell l ∩ sourceCell m) = targetCell l ∩ targetCell m) := by
    intro d
    induction d with
    | zero =>
        have hfe : ∀ l m : Λ, dim l ≤ 0 → dim m ≤ 0 → l ≠ m → face l ∩ face m = ∅ := by
          intro l m hl hm hne
          rw [eq_empty_iff_forall_notMem]
          intro k hk
          have h1 : k = l := (hfaceDim l k hk.1).resolve_right (by omega)
          have h2 : k = m := (hfaceDim m k hk.2).resolve_right (by omega)
          exact hne (h1.symm.trans h2)
        have hemptyS : ∀ l m : Λ, dim l ≤ 0 → dim m ≤ 0 → l ≠ m →
            sourceCell l ∩ sourceCell m = ∅ := by
          intro l m hl hm hne
          rw [hsourceInter l m, hfe l m hl hm hne]
          simp
        have hemptyT : ∀ l m : Λ, dim l ≤ 0 → dim m ≤ 0 → l ≠ m →
            targetCell l ∩ targetCell m = ∅ := by
          intro l m hl hm hne
          rw [htargetInter l m, hfe l m hl hm hne]
          simp
        have hzero : ∀ l, ∃ F : M₁ → M₂, dim l ≤ 0 →
            IsPLHomeomorphInto 3 F (sourceCell l) ∧ F '' sourceCell l = targetCell l := by
          intro l
          by_cases hl : dim l ≤ 0
          · obtain ⟨H, hH⟩ := exists_isPLHomeomorphOn_of_stdSimplex_dim_zero
              (d := dim l) (Nat.le_zero.mp hl) (hr l) (hs l)
            obtain ⟨hA, hB⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn (hu l) (hv l) hH
            refine ⟨v l ∘ H ∘ Function.invFunOn (u l) (P l), fun _ => ⟨?_, ?_⟩⟩
            · rw [hsourceCell l]
              exact hA
            · rw [hsourceCell l, htargetCell l]
              exact hB
          · exact ⟨fun _ => Classical.arbitrary M₂, fun h => absurd h hl⟩
        choose F hF using hzero
        refine ⟨F, fun l hl => (hF l hl).1, fun l hl => (hF l hl).2, ?_, ?_⟩
        · intro l m hl hm
          by_cases hlm : l = m
          · subst hlm
            exact fun x _ => rfl
          · rw [hemptyS l m hl hm hlm]
            exact fun x hx => absurd hx (notMem_empty x)
        · intro l m hl hm
          by_cases hlm : l = m
          · subst hlm
            rw [inter_self, inter_self]
            exact (hF _ hl).2
          · rw [hemptyS l m hl hm hlm, hemptyT l m hl hm hlm, image_empty]
    | succ d ih =>
        obtain ⟨fcold, hold1, hold2, hold3, hold4⟩ := ih
        obtain ⟨g, hg, hgim, hgeq⟩ := exists_isPLHomeomorphInto_row dim sourceCell targetCell d
          fcold hSc hTc hold1 hold2 hold3 hold4 hLFs hLFt
        have hfacelow : ∀ l m : Λ, dim l = d + 1 → m ∈ face l \ {l} → dim m ≤ d := by
          intro l m hl hm
          rcases hfaceDim l m hm.1 with h | h
          · exact absurd (mem_singleton_iff.mpr h) hm.2
          · omega
        have hbdA : ∀ l, dim l = d + 1 → u l '' (r l '' stdSimplexBoundary (dim l)) ⊆
            ⋃ k, ⋃ (_ : dim k ≤ d), sourceCell k := by
          intro l hl
          rw [hsourceBoundary l]
          refine iUnion₂_subset fun m hm => fun x hx => ?_
          exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hfacelow l m hl hm, hx⟩⟩
        have hbdim : ∀ l, dim l = d + 1 →
            g '' (u l '' (r l '' stdSimplexBoundary (dim l))) =
              v l '' (s l '' stdSimplexBoundary (dim l)) := by
          intro l hl
          rw [hsourceBoundary l, htargetBoundary l, image_iUnion₂]
          exact iUnion₂_congr fun m hm => hgim m (hfacelow l m hl hm)
        have hnew : ∀ l, ∃ F : M₁ → M₂, dim l = d + 1 →
            IsPLHomeomorphInto 3 F (sourceCell l) ∧ F '' sourceCell l = targetCell l ∧
              EqOn F g (u l '' (r l '' stdSimplexBoundary (dim l))) := by
          intro l
          by_cases hl : dim l = d + 1
          · obtain ⟨F, hF1, hF2, hF3⟩ := exists_isPLHomeomorphInto_extension_of_cell
              (d := dim l) (by omega) (hr l) (hs l) (hu l) (hv l) hg (hbdA l hl) (hbdim l hl)
            refine ⟨F, fun _ => ⟨?_, ?_, hF3⟩⟩
            · rw [hsourceCell l]
              exact hF1
            · rw [hsourceCell l, htargetCell l]
              exact hF2
          · exact ⟨fun _ => Classical.arbitrary M₂, fun h => absurd h hl⟩
        choose Fnew hFnew using hnew
        set fcell : Λ → M₁ → M₂ := fun l => if dim l ≤ d then fcold l else Fnew l with hfcell
        have hfc1 : ∀ l, dim l ≤ d → fcell l = fcold l := fun l hl => by
          simp only [hfcell, ite_eq_left hl]
        have hfc2 : ∀ l, ¬ dim l ≤ d → fcell l = Fnew l := fun l hl => by
          simp only [hfcell, ite_eq_right hl]
        have hemb : ∀ l, dim l ≤ d + 1 → IsPLHomeomorphInto 3 (fcell l) (sourceCell l) := by
          intro l hl
          by_cases hd : dim l ≤ d
          · rw [hfc1 l hd]
            exact hold1 l hd
          · rw [hfc2 l hd]
            exact (hFnew l (by omega)).1
        have himg : ∀ l, dim l ≤ d + 1 → fcell l '' sourceCell l = targetCell l := by
          intro l hl
          by_cases hd : dim l ≤ d
          · rw [hfc1 l hd]
            exact hold2 l hd
          · rw [hfc2 l hd]
            exact (hFnew l (by omega)).2.1
        have hglue : ∀ l m : Λ, dim l ≤ d + 1 → dim m ≤ d + 1 → l ≠ m →
            EqOn (fcell l) g (sourceCell l ∩ sourceCell m) := by
          intro l m hl hm hne x hx
          by_cases hd : dim l ≤ d
          · rw [hfc1 l hd]
            exact (hgeq l hd hx.1).symm
          · rw [hfc2 l hd]
            refine (hFnew l (by omega)).2.2 ?_
            rw [inter_comm] at hx
            exact hinterSubS m l (Ne.symm hne) (by omega) hx
        refine ⟨fcell, hemb, himg, ?_, ?_⟩
        · intro l m hl hm
          by_cases hlm : l = m
          · subst hlm
            exact fun x _ => rfl
          · intro x hx
            rw [hglue l m hl hm hlm hx]
            refine (hglue m l hm hl (Ne.symm hlm) ?_).symm
            rw [inter_comm]
            exact hx
        · intro l m hl hm
          by_cases hlm : l = m
          · subst hlm
            rw [inter_self, inter_self]
            exact himg _ hl
          · rw [image_congr (hglue l m hl hm hlm), hsourceInter l m, htargetInter l m,
              image_iUnion₂]
            exact iUnion₂_congr fun k hk => hgim k (hlowdim d l m k hl hm hlm hk)
  obtain ⟨fc, hfc1, hfc2, hfc3, hfc4⟩ := key 3
  obtain ⟨g, hg, hgim, -⟩ := exists_isPLHomeomorphInto_row dim sourceCell targetCell 3 fc
    hSc hTc hfc1 hfc2 hfc3 hfc4 hLFs hLFt
  have huniv : (⋃ l, ⋃ (_ : dim l ≤ 3), sourceCell l) = ⋃ l, sourceCell l := by
    refine Subset.antisymm (iUnion₂_subset fun l _ => subset_iUnion _ l) ?_
    refine iUnion_subset fun l x hx => ?_
    exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr ⟨hdim l, hx⟩⟩
  exact ⟨g, huniv ▸ hg, fun l => hgim l (hdim l)⟩

end Assembly

end DifferentialGeometry.Topology.PiecewiseLinear
