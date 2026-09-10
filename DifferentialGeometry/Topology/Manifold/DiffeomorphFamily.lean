import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import DifferentialGeometry.Topology.Manifold.InverseFunction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

noncomputable section
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {ι : Type*}

def diffeomorphList (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (l : List ι) (t : ι → ℝ) : M ≃ₘ⟮I, I⟯ M :=
  l.foldr (fun i e ↦ (d i (t i)).trans e) (Diffeomorph.refl I M ∞)

@[simp]
theorem diffeomorphList_zero (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (hzero : ∀ i, d i 0 = Diffeomorph.refl I M ∞) (l : List ι) :
    diffeomorphList d l 0 = Diffeomorph.refl I M ∞ := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (d i 0).trans (diffeomorphList d l 0) = _
    rw [hzero, ih]
    rfl

theorem diffeomorphList_single [DecidableEq ι]
    (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (hzero : ∀ i, d i 0 = Diffeomorph.refl I M ∞)
    (l : List ι) (hl : l.Nodup) (i : ι) (r : ℝ) :
    diffeomorphList d l (Pi.single i r) =
      if i ∈ l then d i r else Diffeomorph.refl I M ∞ := by
  classical
  induction l with
  | nil => simp [diffeomorphList]
  | cons j l ih =>
    have hn := List.nodup_cons.mp hl
    change (d j ((Pi.single i r : ι → ℝ) j)).trans
      (diffeomorphList d l (Pi.single i r)) = _
    rw [ih hn.2]
    by_cases hij : j = i
    · subst j
      simp [hn.1]
    · simp [hzero, hij, Ne.symm hij]

variable [Fintype ι]

theorem contMDiff_diffeomorphList (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ d i p.1 p.2)) (l : List ι) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod I) I ∞
      (fun p : (ι → ℝ) × M ↦ diffeomorphList d l p.1 p.2) := by
  induction l with
  | nil => exact contMDiff_snd
  | cons i l ih =>
    have ht : ContMDiff (𝓘(ℝ, ι → ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : (ι → ℝ) × M ↦ p.1 i) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff.comp
        contMDiff_fst
    exact ih.comp (contMDiff_fst.prodMk ((hd i).comp (ht.prodMk contMDiff_snd)))

theorem contMDiff_diffeomorphList_symm (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ (d i p.1).symm p.2)) (l : List ι) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod I) I ∞
      (fun p : (ι → ℝ) × M ↦ (diffeomorphList d l p.1).symm p.2) := by
  induction l with
  | nil => exact contMDiff_snd
  | cons i l ih =>
    have ht : ContMDiff (𝓘(ℝ, ι → ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : (ι → ℝ) × M ↦ p.1 i) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff.comp
        contMDiff_fst
    exact (hd i).comp (ht.prodMk ih)

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_diffeomorphList_single [DecidableEq ι]
    (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (hzero : ∀ i, d i 0 = Diffeomorph.refl I M ∞)
    (hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ d i p.1 p.2))
    (l : List ι) (hl : l.Nodup) (i : ι) (hi : i ∈ l) (x : M) :
    mfderiv 𝓘(ℝ, ι → ℝ) I (fun t ↦ diffeomorphList d l t x) 0 (Pi.single i 1) =
      mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ d i r x) 0 (1 : ℝ) := by
  let g : (ι → ℝ) → M := fun t ↦ diffeomorphList d l t x
  have hg : ContMDiff 𝓘(ℝ, ι → ℝ) I ∞ g :=
    (contMDiff_diffeomorphList d hd l).comp (contMDiff_id.prodMk contMDiff_const)
  have he : g ∘ (fun r : ℝ ↦ (Pi.single i r : ι → ℝ)) = (fun r ↦ d i r x) := by
    funext r
    simp [g, diffeomorphList_single d hzero l hl i r, hi]
  have hc := (hasFDerivAt_single (𝕜 := ℝ) (i := i) (E := fun _ : ι ↦ ℝ) 0).hasMFDerivAt
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ι → ℝ))
    (I'' := I) 0 ((hg _).mdifferentiableAt (by simp)) hc.mdifferentiableAt
  rw [he] at hchain
  rw [hc.mfderiv] at hchain
  have hz : (Pi.single i (0 : ℝ) : ι → ℝ) = 0 := Pi.single_zero i
  rw [hz] at hchain
  have hv := congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) hchain
  change mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ d i r x) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, ι → ℝ) I g 0
      ((ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) (1 : ℝ)) at hv
  have hs : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) (1 : ℝ) =
      (Pi.single i 1 : ι → ℝ) := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [hs] at hv
  exact hv.symm

theorem isLocalDiffeomorphAt_diffeomorphList_of_basis
    [I.Boundaryless] [IsManifold I ∞ M]
    (d : ι → ℝ → M ≃ₘ⟮I, I⟯ M)
    (hzero : ∀ i, d i 0 = Diffeomorph.refl I M ∞)
    (hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ d i p.1 p.2))
    (l : List ι) (hl : l.Nodup) (hmem : ∀ i, i ∈ l)
    (x : M) (b : Module.Basis ι ℝ E)
    (hb : ∀ i, mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ d i r x) 0 (1 : ℝ) = b i) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) I ∞ (fun t ↦ diffeomorphList d l t x) 0 := by
  classical
  let g : (ι → ℝ) → M := fun t ↦ diffeomorphList d l t x
  have hg : ContMDiff 𝓘(ℝ, ι → ℝ) I ∞ g :=
    (contMDiff_diffeomorphList d hd l).comp (contMDiff_id.prodMk contMDiff_const)
  let A := b.equivFunL.symm
  have hA : mfderiv 𝓘(ℝ, ι → ℝ) I g 0 = (A : (ι → ℝ) →L[ℝ] E) := by
    have hlin : (mfderiv 𝓘(ℝ, ι → ℝ) I g 0).toLinearMap = A.toLinearEquiv.toLinearMap := by
      apply (Pi.basisFun ℝ ι).ext
      intro i
      change mfderiv 𝓘(ℝ, ι → ℝ) I g 0 (Pi.single i 1) = A (Pi.single i 1)
      rw [mfderiv_diffeomorphList_single d hzero hd l hl i (hmem i) x, hb]
      exact (Basis.equivFun_symm_single b i).symm
    exact ContinuousLinearMap.ext (fun v ↦ LinearMap.congr_fun hlin v)
  apply isLocalDiffeomorphAt_of_hasMFDerivAt_equiv g hg 0 A
  rw [← hA]
  exact ((hg 0).mdifferentiableAt (by simp)).hasMFDerivAt

end Poincare.Topology.Manifold
