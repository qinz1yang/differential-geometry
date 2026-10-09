import DifferentialGeometry.Analysis.Calculus.Inverse.LocalSubmersion
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace DifferentialGeometry.Topology.Manifold
universe u v

theorem exists_local_zero_slice_charts
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (s : Set H) (n k : ℕ) (hdim : ∀ _ : s, Module.finrank ℝ H = n+k)
    (F : s → Type v)
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    [∀ x, FiniteDimensional ℝ (F x)]
    (hF : ∀ x, Module.finrank ℝ (F x) = n)
    (U : s → Set H) (hU : ∀ x, IsOpen (U x)) (hx : ∀ x : s, (x : H) ∈ U x)
    (f : ∀ x : s, H → F x)
    (hf : ∀ x, ContDiffOn ℝ ∞ (f x) (U x))
    (hsurj : ∀ x : s, Function.Surjective (fderiv ℝ (f x) (x : H)))
    (hzero : ∀ x : s, ∀ y ∈ U x, y ∈ s ↔ f x y = 0) :
    ∃ e : s → OpenPartialHomeomorph H ((Fin n → ℝ) × (Fin k → ℝ)),
      ∀ x : s, (x : H) ∈ (e x).source ∧ (e x).source ⊆ U x ∧
        ContDiffOn ℝ ∞ (e x) (e x).source ∧
        ContDiffOn ℝ ∞ (e x).symm (e x).target ∧
        ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = 0 := by
  classical
  let _ : CompleteSpace H := FiniteDimensional.complete ℝ H
  have hlocal (x : s) :
      ∃ e : OpenPartialHomeomorph H ((Fin n → ℝ) × (Fin k → ℝ)),
        (x : H) ∈ e.source ∧ e.source ⊆ U x ∧
          ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
          ∀ y ∈ e.source, y ∈ s ↔ (e y).1 = 0 := by
    let D : H →L[ℝ] F x := fderiv ℝ (f x) (x : H)
    have hsplit : D.HasRightInverse :=
      ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional (hsurj x)
    have hdf : HasFDerivAt (f x) D (x : H) :=
      ((hf x).contDiffAt ((hU x).mem_nhds (hx x))).differentiableAt (by simp) |>.hasFDerivAt
    obtain ⟨b,hxb,hbU,hb,hbi,hfirst,_hinv⟩ :=
      DifferentialGeometry.Analysis.exists_localProjection_of_hasRightInverse
        (hf x) (hU x) (hx x) hdf hsplit
    let split : H ≃L[ℝ] (F x × D.ker) := ContinuousLinearEquiv.equivOfRightInverse
      D hsplit.rightInverse hsplit.rightInverse_rightInverse
    have hker : Module.finrank ℝ D.ker = k := by
      have hh := split.toLinearEquiv.finrank_eq
      rw [Module.finrank_prod, hF x, hdim x] at hh
      omega
    let a : F x ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq
      (by rw [hF x, Module.finrank_fin_fun])
    let q : D.ker ≃L[ℝ] (Fin k → ℝ) := ContinuousLinearEquiv.ofFinrankEq
      (by rw [hker, Module.finrank_fin_fun])
    let T := a.prodCongr q
    let e : OpenPartialHomeomorph H ((Fin n → ℝ) × (Fin k → ℝ)) :=
      OpenPartialHomeomorph.trans b T.toHomeomorph.toOpenPartialHomeomorph
    have hesource : e.source ⊆ b.source := fun _ hy => hy.1
    have hex : (x : H) ∈ e.source := ⟨hxb, Set.mem_univ _⟩
    have he : ContDiffOn ℝ ∞ e e.source :=
      T.contDiff.comp_contDiffOn (hb.mono hesource)
    have hei : ContDiffOn ℝ ∞ e.symm e.target :=
      hbi.comp T.symm.contDiff.contDiffOn (fun _ hy => hy.2)
    refine ⟨e,hex,hesource.trans hbU,he,hei,?_⟩
    intro y hy
    rw [hzero x y (hbU (hesource hy))]
    change f x y = 0 ↔ a (b y).1 = 0
    rw [hfirst y]
    constructor
    · intro hz
      rw [hz,map_zero]
    · intro hz
      apply a.injective
      simpa only [map_zero] using hz
  choose e he using hlocal
  exact ⟨e,he⟩

end DifferentialGeometry.Topology.Manifold
