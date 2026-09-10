import DifferentialGeometry.Analysis.Calculus.Inverse.TransverseImmersion
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace Poincare.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_localInverse_of_one_sided_transverse_family
    {f : E × ℝ → F} {ι : E → F} {V : Set E} {p : E} {ρ : ℝ} {v : F}
    (hV : IsOpen V) (hp : p ∈ V) (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ Icc 0 ρ))
    (hzero : ∀ x ∈ V, f (x, 0) = ι x)
    (hinj : Function.Injective (fderiv ℝ ι p))
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ F)
    (hderiv : HasDerivWithinAt (fun t ↦ f (p, t)) v (Icc 0 ρ) 0)
    (htransverse : v ∉ range (fderiv ℝ ι p)) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) F,
      (p, 0) ∈ e.source ∧ e.source ⊆ V ×ˢ Ioo (-ρ) ρ ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, 0 ≤ z.2 → e z = f z := by
  obtain ⟨gext, W₀, hW₀, hgext, hext⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
    (fun t x ↦ f (x, t)) ρ hρ V p (by simpa only [hV.interior_eq] using hp)
    (hf.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz ↦ ⟨hz.2, hz.1⟩))
  obtain ⟨W, hWW₀, hW, hpW⟩ := mem_nhds_iff.mp hW₀
  let g : E × ℝ → F := fun z ↦ gext z.2 z.1
  let D := (W ∩ V) ×ˢ Ioo (-ρ) ρ
  have hD : IsOpen D := (hW.inter hV).prod isOpen_Ioo
  have hpD : (p, (0 : ℝ)) ∈ D := ⟨⟨hpW, hp⟩, neg_neg_of_pos hρ, hρ⟩
  have hg : ContDiffOn ℝ ∞ g D :=
    hgext.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun z hz ↦ ⟨mem_univ _, hWW₀ hz.1.1⟩)
  have hgeq : ∀ x ∈ W, ∀ t ∈ Icc 0 ρ, g (x, t) = f (x, t) :=
    fun x hx t ht ↦ hext t ht x (hWW₀ hx)
  have hgzero : ∀ x, (x, 0) ∈ D → g (x, 0) = ι x := by
    intro x hx
    rw [hgeq x hx.1.1 0 ⟨le_rfl, hρ.le⟩, hzero x hx.1.2]
  have hgd : HasDerivAt (fun t ↦ g (p, t)) (fderiv ℝ g (p, 0) (0, 1)) 0 :=
    ((hg.contDiffAt (hD.mem_nhds hpD)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 p).prodMk (hasDerivAt_id 0))
  have hgdWithin : HasDerivWithinAt (fun t ↦ g (p, t)) v (Icc 0 ρ) 0 :=
    hderiv.congr (fun t ht ↦ hgeq p hpW t ht) (hgeq p hpW 0 ⟨le_rfl, hρ.le⟩)
  have ht : deriv (fun t ↦ g (p, t)) 0 = v := by
    rw [hgd.deriv]
    exact (hgd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hρ 0 ⟨le_rfl, hρ.le⟩)).symm.trans
      (hgdWithin.derivWithin (uniqueDiffOn_Icc hρ 0 ⟨le_rfl, hρ.le⟩))
  obtain ⟨e, hpe, heD, he, hi, heq⟩ := exists_localInverse_of_transverse_family hg hD hpD hgzero
    hinj hdim (by rwa [ht])
  refine ⟨e, hpe, (fun z hz ↦ ⟨(heD hz).1.2, (heD hz).2⟩), he, hi, ?_⟩
  intro z hz ht
  rw [heq]
  exact hgeq z.1 (heD hz).1.1 z.2 ⟨ht, (heD hz).2.2.le⟩

end Poincare.Analysis
