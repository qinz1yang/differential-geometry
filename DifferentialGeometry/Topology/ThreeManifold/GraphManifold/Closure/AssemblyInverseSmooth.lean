import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.InverseSmooth
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Inverse smoothness at boundary points

`contMDiffOn_of_leftInverse_of_bijective_mfderiv`: a smooth map between manifolds (with boundary
or corners allowed on both sides) which maps an open set bijectively onto an open set, with
continuous inverse and bijective differential at every point, has a smooth inverse. The proof
reduces in charts to `contDiffOn_of_leftInverse_of_invertible`, which works on relatively open
chart images (sets with unique differentials): the easy half of the inverse function theorem
within sets (`HasFDerivWithinAt.of_local_left_inverse`), continuity of inversion, and the bootstrap
`contDiffOn_infty_of_inverse_pair` (`SmoothApproximation/Boundary/InverseSmooth.lean:31`). No
open-set inverse function theorem is used, so boundary points are covered. Used by B2-side
(`AssemblyHalfCollar.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly


/-- **Euclidean inverse smoothness on sets with unique differentials.** A smooth map `f`, bijective
from `S` onto `T` with continuous inverse `g` and invertible derivative within `S` at every point,
has a smooth inverse on `T`. Covers half-space chart images (boundary points); the open-set
inverse function theorem is not used. -/
theorem contDiffOn_of_leftInverse_of_invertible
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T)
    {f : E → F} {g : F → E} (hf : ContDiffOn ℝ ∞ f S) (hg : ContinuousOn g T)
    (hfS : MapsTo f S T) (hgT : MapsTo g T S)
    (hfg : ∀ y ∈ T, f (g y) = y) (hgf : ∀ x ∈ S, g (f x) = x)
    (hinv : ∀ x ∈ S, ∃ e : E ≃L[ℝ] F, (e : E →L[ℝ] F) = fderivWithin ℝ f S x) :
    ContDiffOn ℝ ∞ g T := by
  have hderiv : ∀ y ∈ T, HasFDerivWithinAt g
      (ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) T y := by
    intro y hy
    obtain ⟨e, he⟩ := hinv (g y) (hgT hy)
    have hf' : HasFDerivWithinAt f (e : E →L[ℝ] F) S (g y) := by
      rw [he]
      exact ((hf.differentiableOn (by simp)) (g y) (hgT hy)).hasFDerivWithinAt
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact hf'.of_local_left_inverse ((hg y hy).tendsto_nhdsWithin hgT) hy
      (eventually_nhdsWithin_of_forall hfg)
  have hdiff : DifferentiableOn ℝ g T := fun y hy => (hderiv y hy).differentiableWithinAt
  have heq : ∀ y ∈ T, fderivWithin ℝ g T y =
      ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y)) :=
    fun y hy => (hderiv y hy).fderivWithin (hT y hy)
  have hcontD : ContinuousOn (fun x => fderivWithin ℝ f S x) S :=
    hf.continuousOn_fderivWithin hS (by simp)
  have hcont : ContinuousOn (fun y => fderivWithin ℝ g T y) T := by
    refine ContinuousOn.congr (f := fun y =>
      ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) ?_ heq
    intro y hy
    obtain ⟨e, he⟩ := hinv (g y) (hgT hy)
    have hinvc : ContinuousAt (ContinuousLinearMap.inverse : (E →L[ℝ] F) → (F →L[ℝ] E))
        (fderivWithin ℝ f S (g y)) := by
      rw [← he]
      exact (contDiffAt_map_inverse (n := 0) e).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (g := ContinuousLinearMap.inverse)
      (f := fun y => fderivWithin ℝ f S (g y)) hinvc ((hcontD.comp hg hgT) y hy)
  have hg1 : ContDiffOn ℝ 1 g T := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderivWithin hT]
    exact ⟨hdiff, by simp, contDiffOn_zero.mpr hcont⟩
  exact DifferentialGeometry.Topology.Manifold.SmoothApproximation.contDiffOn_infty_of_inverse_pair
    hS hT hf hg1 hfS hgT hfg hgf

/-- **Manifold inverse smoothness, boundary points included.** Let `f` be smooth on an open set
`A`, mapping it bijectively onto an open set `B` with continuous inverse `g`, and with bijective
differential at every point of `A`. Then `g` is smooth on `B`. Manifolds with boundary are allowed
on both sides (a boundary point of `M` may go to an interior point of `N` only if `B` fails to be
open, which is excluded). Route: chart reduction to
`contDiffOn_of_leftInverse_of_invertible` on relatively open chart images. -/
theorem contMDiffOn_of_leftInverse_of_bijective_mfderiv
    {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    {f : M → N} {g : N → M} {A : Set M} {B : Set N} (hA : IsOpen A) (hB : IsOpen B)
    (hf : ContMDiffOn I J ∞ f A) (hfA : MapsTo f A B) (hgB : MapsTo g B A)
    (hfg : ∀ y ∈ B, f (g y) = y) (hgf : ∀ x ∈ A, g (f x) = x) (hg : ContinuousOn g B)
    (hbij : ∀ x ∈ A, Bijective (mfderiv I J f x)) : ContMDiffOn J I ∞ g B := by
  intro y hy
  have hx : g y ∈ A := hgB hy
  have hfy : f (g y) = y := hfg y hy
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [contMDiffAt_iff]
  refine ⟨hg.continuousAt (hB.mem_nhds hy), ?_⟩
  set φ := extChartAt I (g y) with hφ
  set ψ := extChartAt J y with hψ
  let F' : E → F := ψ ∘ f ∘ φ.symm
  let G' : F → E := φ ∘ g ∘ ψ.symm
  have hO : IsOpen (A ∩ f ⁻¹' ψ.source) :=
    hf.continuousOn.isOpen_inter_preimage hA (isOpen_extChartAt_source y)
  let S1 : Set E := φ.target ∩ φ.symm ⁻¹' (A ∩ f ⁻¹' ψ.source)
  have hS1nhds : ∀ u ∈ S1, S1 ∈ 𝓝[range I] u := by
    intro u hu
    refine inter_mem (extChartAt_target_mem_nhdsWithin_of_mem hu.1)
      (mem_nhdsWithin_of_mem_nhds ?_)
    have hsrc : φ.symm u ∈ φ.source := φ.map_target hu.1
    have h := extChartAt_preimage_mem_nhds' hsrc (hO.mem_nhds hu.2)
    rwa [φ.right_inv hu.1] at h
  have hS1sub : S1 ⊆ range I := fun u hu => extChartAt_target_subset_range _ hu.1
  have hS1 : UniqueDiffOn ℝ S1 := fun u hu => by
    have h := (I.uniqueDiffOn u (hS1sub hu)).inter' (hS1nhds u hu)
    rwa [inter_eq_right.mpr hS1sub] at h
  have hF1 : ContDiffOn ℝ ∞ F' S1 := (contMDiffOn_iff.mp hf).2 (g y) y
  let D : E → E →L[ℝ] F := fun u => fderivWithin ℝ F' S1 u
  have hDc : ContinuousOn D S1 := hF1.continuousOn_fderivWithin hS1 (by simp)
  let Ω : Set (E →L[ℝ] F) := range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hΩ : IsOpen Ω := ContinuousLinearEquiv.isOpen
  have hu₀ : φ (g y) ∈ S1 := by
    refine ⟨mem_extChartAt_target _, ?_⟩
    change φ.symm (φ (g y)) ∈ A ∩ f ⁻¹' ψ.source
    rw [φ.left_inv (mem_extChartAt_source _)]
    exact ⟨hx, by rw [mem_preimage, hfy]; exact mem_extChartAt_source y⟩
  have hmd : MDifferentiableAt I J f (g y) :=
    (hf.contMDiffAt (hA.mem_nhds hx)).mdifferentiableAt (by simp)
  have hDu₀ : D (φ (g y)) = mfderiv I J f (g y) := by
    rw [hmd.mfderiv]
    have hw : writtenInExtChartAt I J (g y) f = F' := by
      simp only [writtenInExtChartAt, hfy]
      rfl
    rw [hw]
    exact (fderivWithin_of_mem_nhdsWithin (hS1nhds _ hu₀) (I.uniqueDiffOn _ (hS1sub hu₀))
      ((hF1.differentiableOn (by simp)) _ hu₀)).symm
  have hDΩ : D (φ (g y)) ∈ Ω := by
    rw [hDu₀]
    refine ⟨(LinearEquiv.ofBijective (mfderiv I J f (g y)).toLinearMap
      (hbij (g y) hx)).toContinuousLinearEquiv, ?_⟩
    ext v
    rfl
  let S0 : Set E := S1 ∩ D ⁻¹' Ω
  have hS0rel : ∀ u ∈ S0, S0 ∈ 𝓝[S1] u := fun u hu =>
    inter_mem self_mem_nhdsWithin ((hDc u hu.1).preimage_mem_nhdsWithin (hΩ.mem_nhds hu.2))
  have hS0nhds : ∀ u ∈ S0, S0 ∈ 𝓝[range I] u := fun u hu =>
    nhdsWithin_le_of_mem (hS1nhds u hu.1) (hS0rel u hu)
  have hS0sub : S0 ⊆ range I := fun u hu => hS1sub hu.1
  have hS0 : UniqueDiffOn ℝ S0 := fun u hu => by
    have h := (I.uniqueDiffOn u (hS0sub hu)).inter' (hS0nhds u hu)
    rwa [inter_eq_right.mpr hS0sub] at h
  have hF0 : ContDiffOn ℝ ∞ F' S0 := hF1.mono inter_subset_left
  have hinv0 : ∀ u ∈ S0, ∃ e : E ≃L[ℝ] F, (e : E →L[ℝ] F) = fderivWithin ℝ F' S0 u := by
    intro u hu
    obtain ⟨e, he⟩ := hu.2
    refine ⟨e, ?_⟩
    rw [he]
    exact fderivWithin_of_mem_nhdsWithin (hS0rel u hu) (hS1 u hu.1)
      ((hF0.differentiableOn (by simp)) u hu)
  let T0 : Set F := F' '' S0
  have hT0nhds : ∀ u ∈ S0, T0 ∈ 𝓝[range J] (F' u) := by
    intro u hu
    have hx' : φ.symm u ∈ φ.source := φ.map_target hu.1.1
    have hA' : φ.symm u ∈ A := hu.1.2.1
    have hψ' : f (φ.symm u) ∈ ψ.source := hu.1.2.2
    have hφS0 : φ.source ∩ φ ⁻¹' S0 ∈ 𝓝 (φ.symm u) := by
      refine inter_mem ((isOpen_extChartAt_source (g y)).mem_nhds hx') ?_
      have h := hS0nhds u hu
      rw [← φ.right_inv hu.1.1, ← map_extChartAt_nhds' hx'] at h
      exact h
    have hgy' : g (f (φ.symm u)) = φ.symm u := hgf _ hA'
    have hBy' : f (φ.symm u) ∈ B := hfA hA'
    have hNy : B ∩ ψ.source ∩ g ⁻¹' (φ.source ∩ φ ⁻¹' S0) ∈ 𝓝 (f (φ.symm u)) := by
      refine inter_mem (inter_mem (hB.mem_nhds hBy')
        ((isOpen_extChartAt_source y).mem_nhds hψ')) ?_
      apply (hg.continuousAt (hB.mem_nhds hBy')).preimage_mem_nhds
      rw [hgy']
      exact hφS0
    have himg : ψ '' (B ∩ ψ.source ∩ g ⁻¹' (φ.source ∩ φ ⁻¹' S0)) ⊆ T0 := by
      rintro _ ⟨y'', ⟨⟨hy''B, hy''ψ⟩, hy''φ, hy''S0⟩, rfl⟩
      refine ⟨φ (g y''), hy''S0, ?_⟩
      change ψ (f (φ.symm (φ (g y'')))) = ψ y''
      rw [φ.left_inv hy''φ, hfg y'' hy''B]
    have hmap := map_extChartAt_nhds' (I := J) hψ'
    have hmem : ψ '' (B ∩ ψ.source ∩ g ⁻¹' (φ.source ∩ φ ⁻¹' S0)) ∈
        𝓝[range J] (ψ (f (φ.symm u))) := by
      rw [← hmap]
      exact image_mem_map hNy
    exact mem_of_superset hmem himg
  have hT0sub : T0 ⊆ ψ.target := by
    rintro _ ⟨u, hu, rfl⟩
    exact ψ.map_source hu.1.2.2
  have hT0 : UniqueDiffOn ℝ T0 := by
    rintro _ ⟨u, hu, rfl⟩
    have hr : T0 ⊆ range J := fun v hv => extChartAt_target_subset_range _ (hT0sub hv)
    have h := (J.uniqueDiffOn (F' u) (hr ⟨u, hu, rfl⟩)).inter' (hT0nhds u hu)
    rwa [inter_eq_right.mpr hr] at h
  have hGF : ∀ u ∈ S0, G' (F' u) = u := by
    intro u hu
    change φ (g (ψ.symm (ψ (f (φ.symm u))))) = u
    rw [ψ.left_inv hu.1.2.2, hgf _ hu.1.2.1, φ.right_inv hu.1.1]
  have hG0 : ContinuousOn G' T0 := by
    refine (continuousOn_extChartAt (g y)).comp (hg.comp
      ((continuousOn_extChartAt_symm y).mono hT0sub) ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩
      change ψ.symm (ψ (f (φ.symm u))) ∈ B
      rw [ψ.left_inv hu.1.2.2]
      exact hfA hu.1.2.1
    · rintro _ ⟨u, hu, rfl⟩
      change g (ψ.symm (ψ (f (φ.symm u)))) ∈ φ.source
      rw [ψ.left_inv hu.1.2.2, hgf _ hu.1.2.1]
      exact φ.map_target hu.1.1
  have hG : ContDiffOn ℝ ∞ G' T0 :=
    contDiffOn_of_leftInverse_of_invertible hS0 hT0 hF0 hG0 (mapsTo_image F' S0)
      (by rintro _ ⟨u, hu, rfl⟩; rw [hGF u hu]; exact hu)
      (by rintro _ ⟨u, hu, rfl⟩; rw [hGF u hu]) hGF hinv0
  have hyF : F' (φ (g y)) = ψ y := by
    change ψ (f (φ.symm (φ (g y)))) = ψ y
    rw [φ.left_inv (mem_extChartAt_source _), hfy]
  have hyT : ψ y ∈ T0 := ⟨φ (g y), ⟨hu₀, hDΩ⟩, hyF⟩
  have hnhds := hT0nhds (φ (g y)) ⟨hu₀, hDΩ⟩
  rw [hyF] at hnhds
  exact (hG.contDiffWithinAt hyT).mono_of_mem_nhdsWithin hnhds

end GC.GraphManifold.Assembly
