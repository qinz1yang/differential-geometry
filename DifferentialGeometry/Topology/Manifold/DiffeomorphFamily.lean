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

namespace DifferentialGeometry.Topology.Manifold

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

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem eqOn_symm_of_eqOn_compl {Φ : Diffeomorph I I M M ∞} {K : Set M}
    (h : Set.EqOn Φ id Kᶜ) : Set.EqOn Φ.symm id Kᶜ := by
  intro x hx
  have h1 : Φ x = x := h hx
  calc Φ.symm x = Φ.symm (Φ x) := by rw [h1]
    _ = x := Φ.symm_apply_apply x

end DifferentialGeometry.Topology.Manifold

section

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem mem_of_mem_of_fixes_compl {ι : Type*} {U : ι → Set M}
    {i : ι} {D : Diffeomorph I I M M ∞} {y : M}
    (hfix : ∀ z ∉ U i, D z = z ∧ D.symm z = z) (hy : y ∈ U i) : D y ∈ U i := by
  by_contra hc
  have h2 : D.symm (D y) = D y := (hfix (D y) hc).2
  have h3 : D y = y := h2 ▸ Diffeomorph.symm_apply_apply D y
  exact hc (h3.symm ▸ hy)

theorem diffeomorphList_diagonal_apply_eq_of_forall_notMem {ι : Type*}
    (d : ι → ℝ → Diffeomorph I I M M ∞) (U : ι → Set M)
    (hfix : ∀ i t x, x ∉ U i → d i t x = x ∧ (d i t).symm x = x)
    (l : List ι) (t : ι → ℝ) {y : M} (hy : ∀ i ∈ l, y ∉ U i) :
    diffeomorphList d l t y = y := by
  revert hy
  induction l with
  | nil => intro hy; rfl
  | cons a rest ih =>
    intro hy
    change diffeomorphList d rest t ((d a (t a)) y) = y
    rw [(hfix a (t a) y (hy a (List.mem_cons.mpr (Or.inl rfl)))).1]
    exact ih (fun i hi ↦ hy i (List.mem_cons.mpr (Or.inr hi)))

theorem diffeomorphList_diagonal_one_apply_eq_of_disjoint_support {ι : Type*}
    (d : ι → ℝ → Diffeomorph I I M M ∞) (U : ι → Set M)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hfix : ∀ i t x, x ∉ U i → d i t x = x ∧ (d i t).symm x = x)
    (l : List ι) (hl : l.Nodup) {i : ι} (hi : i ∈ l) {y : M}
    (hy : ∀ j ∈ l, j ≠ i → y ∉ U j) :
    diffeomorphList d l (fun _ ↦ (1 : ℝ)) y = d i 1 y := by
  revert hl hi hy
  induction l with
  | nil => intro hl hi hy; exact absurd hi (by simp)
  | cons a rest ih =>
    intro hl hi hy
    have hn := List.nodup_cons.mp hl
    change diffeomorphList d rest (fun _ ↦ (1 : ℝ)) ((d a 1) y) = d i 1 y
    by_cases hai : a = i
    · rw [← hai] at hy ⊢
      refine diffeomorphList_diagonal_apply_eq_of_forall_notMem d U hfix rest
        (fun _ ↦ (1 : ℝ)) ?_
      intro j hj
      have hja : j ≠ a := fun h ↦ hn.1 (h ▸ hj)
      by_cases hya : y ∈ U a
      · exact Set.disjoint_left.mp (hdisj a j (Ne.symm hja))
          (mem_of_mem_of_fixes_compl (hfix a 1) hya)
      · rw [(hfix a 1 y hya).1]
        exact hy j (List.mem_cons.mpr (Or.inr hj)) hja
    · rw [(hfix a 1 y (hy a (List.mem_cons.mpr (Or.inl rfl)) hai)).1]
      have hinew : i ∈ rest := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hai
        · exact h
      exact ih hn.2 hinew (fun j hj hji ↦ hy j (List.mem_cons.mpr (Or.inr hj)) hji)

variable {ι : Type*} [Fintype ι]

theorem diffeomorphList_univ_diagonal_zero (d : ι → ℝ → Diffeomorph I I M M ∞)
    (hzero : ∀ i, d i 0 = Diffeomorph.refl I M ∞) :
    diffeomorphList d (Finset.univ : Finset ι).toList (fun _ ↦ (0 : ℝ)) =
      Diffeomorph.refl I M ∞ :=
  diffeomorphList_zero d hzero _

theorem contMDiff_diffeomorphList_univ_diagonal (d : ι → ℝ → Diffeomorph I I M M ∞)
    (hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ d i p.1 p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M ↦
        diffeomorphList d (Finset.univ : Finset ι).toList (fun _ ↦ q.1) q.2) := by
  have hdiag : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ι → ℝ) ∞
      (fun q : ℝ × M ↦ (fun _ : ι ↦ q.1 : ι → ℝ)) := by
    rw [contMDiff_pi_space]
    exact fun _ ↦ contMDiff_fst
  exact (contMDiff_diffeomorphList d hd _).comp (hdiag.prodMk contMDiff_snd)

theorem contMDiff_diffeomorphList_univ_diagonal_symm (d : ι → ℝ → Diffeomorph I I M M ∞)
    (hdi : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ (d i p.1).symm p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M ↦
        (diffeomorphList d (Finset.univ : Finset ι).toList (fun _ ↦ q.1)).symm q.2) := by
  have hdiag : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ι → ℝ) ∞
      (fun q : ℝ × M ↦ (fun _ : ι ↦ q.1 : ι → ℝ)) := by
    rw [contMDiff_pi_space]
    exact fun _ ↦ contMDiff_fst
  exact (contMDiff_diffeomorphList_symm d hdi _).comp (hdiag.prodMk contMDiff_snd)

end DifferentialGeometry.Topology.Manifold

end
