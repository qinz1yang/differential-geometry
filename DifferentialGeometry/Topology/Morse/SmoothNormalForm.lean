import DifferentialGeometry.Topology.Morse.RelativePerturbationChart
import DifferentialGeometry.Topology.Morse.NormalForm.Manifold
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment
open scoped Manifold ContDiff Topology

namespace Poincare.Morse

private def smoothAffineDiffeomorph {n : ℕ} (a : MorseModel n)
    (L : MorseModel n ≃ₗ[ℝ] MorseModel n) :
    Diffeomorph 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (MorseModel n) (MorseModel n) ∞ where
  toEquiv := (L.toContinuousLinearEquiv.toHomeomorph.trans (addHomeo n a)).toEquiv
  contMDiff_toFun := by
    change ContMDiff _ _ ∞ (fun y : MorseModel n ↦ a + L y)
    exact (contDiff_const.add L.toContinuousLinearEquiv.contDiff).contMDiff
  contMDiff_invFun := by
    change ContMDiff _ _ ∞ (fun y : MorseModel n ↦ L.symm (y - a))
    exact (L.symm.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff

private def smoothReindexDiffeomorph {n : ℕ} (σ : Fin n ≃ Fin n) :
    Diffeomorph 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (MorseModel n) (MorseModel n) ∞ where
  toEquiv := (reindexHomeo σ).toEquiv
  contMDiff_toFun := by
    apply contMDiff_iff_contDiff.mpr
    change ContDiff ℝ ∞ (fun y : MorseModel n ↦ fun i ↦ y (σ.symm i))
    fun_prop
  contMDiff_invFun := by
    apply contMDiff_iff_contDiff.mpr
    change ContDiff ℝ ∞ (fun y : MorseModel n ↦ fun i ↦ y (σ i))
    fun_prop

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [IsManifold I ∞ M]

theorem exists_interior_morse_normal_form (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (p : M) (hp : I.IsInteriorPoint p) (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (fun y ↦ f ((extChartAt I p).symm y))
      (extChartAt I p p)) = k) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, MorseModel n) I (MorseModel n) M ∞,
      0 ∈ χ.source ∧ χ 0 = p ∧
      (∀ y ∈ χ.source, f (χ y) = morseNormalForm hk (f p) y) ∧
      ∀ x ∈ χ.target, I.IsInteriorPoint x := by
  let c := Poincare.Manifold.interiorChart I ∞ p
  have hpc : p ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I ∞ p).mpr hp
  let z := c p
  obtain ⟨W, F, hW, hzW, hWsub, hF⟩ :=
    exists_contDiff_interiorChart_extensions (g := fun _ : Unit ↦ f) (fun _ ↦ hf) hp
  let g := F ()
  have hg : ContDiff ℝ ∞ g := (hF ()).1
  have heq : g =ᶠ[𝓝 z] fun y ↦ f (c.symm y) := by
    filter_upwards [hW.mem_nhds hzW] with y hy
    exact (hF ()).2.2.2 hy
  have hgcrit : fderiv ℝ g z = 0 := by
    rw [heq.fderiv_eq, fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff hf c
      (c.map_source hpc)]
    have hcp : c.symm.toPartialEquiv (c.toPartialEquiv p) = p := c.left_inv hpc
    rw [hcp]
    exact hnd.1
  have hQ : chartHessianAt g z =
      chartHessianAt (fun y ↦ f ((extChartAt I p).symm y)) (extChartAt I p p) := by
    have hh := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    ext u
    change (fderiv ℝ (fderiv ℝ g) z u) u = _
    rw [hh]
    rfl
  have hgnd : (QuadraticMap.associated (R := ℝ) (chartHessianAt g z)).SeparatingLeft :=
    hQ.symm ▸ hnd.2
  have hlemma := morse_lemma_smooth 𝓘(ℝ, MorseModel n) g z
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq, PartialEquiv.refl_target] at hlemma
  obtain ⟨ψ, hψsrc, hψtgt, hψ0, _, _, ⟨v, hv, h0v, hψv, hψiv⟩, w, hw, hsig, L, hnormal⟩ :=
    hlemma hg.contDiffOn hgcrit hgnd
  have hcard : {i : Fin n | w i < 0}.ncard = k := hsig.trans (hQ ▸ hindex)
  obtain ⟨σ, hσneg, hσpos⟩ := exists_reindexEquiv hk w hw hcard
  let ψr := ψ.restrOpen (ψ.target ∩ v) (ψ.open_target.inter hv)
  let ψd : PartialDiffeomorph 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
      (MorseModel n) (MorseModel n) ∞ := {
    toPartialEquiv := ψr.toPartialEquiv
    open_source := ψr.open_source
    open_target := ψr.open_target
    contMDiffOn_toFun := hψv.contMDiffOn.mono (fun _ hy ↦ hy.2.2)
    contMDiffOn_invFun := hψiv.contMDiffOn.mono (fun y hy ↦ by
      refine ⟨ψ.symm y, hy.2.2, ?_⟩
      exact ψ.right_inv hy.1) }
  let a := smoothAffineDiffeomorph z L.symm
  let cr := c.symm.toOpenPartialHomeomorph.restrOpen W hW
  let cd : PartialDiffeomorph 𝓘(ℝ, MorseModel n) I (MorseModel n) M ∞ := {
    toPartialEquiv := cr.toPartialEquiv
    open_source := cr.open_source
    open_target := cr.open_target
    contMDiffOn_toFun := c.symm.contMDiffOn.mono inter_subset_left
    contMDiffOn_invFun := c.contMDiffOn.mono inter_subset_left }
  let T := smoothReindexDiffeomorph σ
  let χ := ((T.toPartialDiffeomorph.trans ψd).trans a.toPartialDiffeomorph).trans cd
  have hT0 : T 0 = 0 := by ext i; rfl
  have ha0 : a 0 = z := by
    change z + L.symm 0 = z
    rw [map_zero, add_zero]
  have hχsrc0 : (0 : MorseModel n) ∈ χ.source := by
    change ((0 ∈ Set.univ ∧ T 0 ∈ ψ.source ∩ (ψ.target ∩ v)) ∧
      ψ (T 0) ∈ Set.univ) ∧ a (ψ (T 0)) ∈ c.target ∩ W
    rw [hT0, hψ0, ha0]
    exact ⟨⟨⟨mem_univ _, hψsrc, hψtgt, h0v⟩, mem_univ _⟩, c.map_source hpc, hzW⟩
  have hχ0 : χ 0 = p := by
    change c.symm (a (ψ (T 0))) = p
    rw [hT0, hψ0, ha0]
    exact c.left_inv hpc
  refine ⟨χ, hχsrc0, hχ0, ?_, ?_⟩
  · intro y hy
    have hymem : T y ∈ ψ.target := hy.1.1.2.2.1
    have hyW : a (ψ (T y)) ∈ W := hy.2.2
    have hn := hnormal (T y) hymem
    have hga : g (a (ψ (T y))) = f (χ y) := (hF ()).2.2.2 hyW
    have hgz : g z = f p := (heq.eq_of_nhds).trans (congrArg f (c.left_inv hpc))
    change g (a (ψ (T y))) = _ at hn
    rw [hga, hgz] at hn
    rw [hn]
    change f p + 1 / 2 * (∑ i : Fin n, w i * (y (σ.symm i)) * y (σ.symm i)) = _
    have hsum : (∑ i : Fin n, w i * (y (σ.symm i)) * y (σ.symm i)) =
        ∑ i : Fin n, w i * (y (σ.symm i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum, w_sum_reindexed hk w σ hσneg hσpos]
    rfl
  · intro x hx
    have hxc : x ∈ c.source := hx.1.1
    exact Poincare.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞ (by simp) hxc

end Poincare.Morse
