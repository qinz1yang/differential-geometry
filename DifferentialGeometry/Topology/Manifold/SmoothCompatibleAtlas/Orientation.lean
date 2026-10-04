import DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas.Defs
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.Algebra.Module.Determinant

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem det_clm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S T : E →L[ℝ] E) :
    (S.comp T).det = S.det * T.det :=
  LinearMap.det_comp (S : E →ₗ[ℝ] E) (T : E →ₗ[ℝ] E)

theorem det_clm_comp_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S T : E →L[ℝ] E)
    (hS : 0 < S.det) (hT : 0 < T.det) : 0 < (S.comp T).det := by
  rw [det_clm_comp S T]
  exact mul_pos hS hT

theorem det_fderiv_homeomorph_symm_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E ≃ₜ E) {r : ℕ} (hr : 1 ≤ r) (hg : ContDiff ℝ r g) (hgs : ContDiff ℝ r g.symm)
    (hdet : ∀ x, 0 < (fderiv ℝ g x).det) (u : E) : 0 < (fderiv ℝ g.symm u).det := by
  have hr0 : ((r : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (fderiv ℝ g (g.symm u)).comp (fderiv ℝ g.symm u) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp u (hg.differentiable hr0 (g.symm u)) (hgs.differentiable hr0 u),
      g.self_comp_symm, fderiv_id]
  have h2 : (fderiv ℝ g (g.symm u)).det * (fderiv ℝ g.symm u).det = 1 := by
    rw [← det_clm_comp, h1]
    exact LinearMap.det_id
  have h3 : 0 < (fderiv ℝ g (g.symm u)).det * (fderiv ℝ g.symm u).det := by
    rw [h2]
    exact zero_lt_one
  exact pos_of_mul_pos_right h3 (hdet (g.symm u)).le

theorem det_fderiv_symm_trans_trans_homeomorph_pos {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (p q : OpenPartialHomeomorph X E) (gp gq : E ≃ₜ E)
    {r : ℕ} (hr : 1 ≤ r) (hpq : ContDiffOn ℝ r (p.symm.trans q) (p.symm.trans q).source)
    (hpos : ∀ u ∈ (p.symm.trans q).source, 0 < (fderiv ℝ (p.symm.trans q) u).det)
    (hgp : ContDiff ℝ r gp.symm) (hgq : ContDiff ℝ r gq)
    (hdetp : ∀ x, 0 < (fderiv ℝ gp.symm x).det) (hdetq : ∀ x, 0 < (fderiv ℝ gq x).det) :
    ∀ u ∈ ((p.trans gp.toOpenPartialHomeomorph).symm.trans
        (q.trans gq.toOpenPartialHomeomorph)).source,
      0 < (fderiv ℝ ((p.trans gp.toOpenPartialHomeomorph).symm.trans
        (q.trans gq.toOpenPartialHomeomorph)) u).det := by
  intro u hu
  have hr0 : ((r : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨⟨-, h1⟩, h2, -⟩ := hu
  have h1' : gp.symm u ∈ p.target := h1
  have h2' : p.symm (gp.symm u) ∈ q.source := h2
  have hmem : gp.symm u ∈ (p.symm.trans q).source := ⟨h1', h2'⟩
  have hT : DifferentiableAt ℝ (p.symm.trans q) (gp.symm u) :=
    (hpq.contDiffAt ((p.symm.trans q).open_source.mem_nhds hmem)).differentiableAt hr0
  have hdp : DifferentiableAt ℝ gp.symm u := hgp.differentiable hr0 u
  change 0 < (fderiv ℝ (gq ∘ ((p.symm.trans q) ∘ gp.symm)) u).det
  rw [fderiv_comp u (hgq.differentiable hr0 _) (hT.comp u hdp), fderiv_comp u hT hdp]
  exact det_clm_comp_pos _ _ (hdetq _) (det_clm_comp_pos _ _ (hpos _ hmem) (hdetp u))

theorem SmoothCompatibleAtlas.det_fderiv_transition_pos {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] (A : SmoothCompatibleAtlas E X ι)
    (φ : ι → OpenPartialHomeomorph X E) {r : ℕ} (hr : 1 ≤ r)
    (hφ : ∀ i j, ContDiffOn ℝ r ((φ i).symm.trans (φ j)) ((φ i).symm.trans (φ j)).source)
    (hpos : ∀ i j, ∀ u ∈ ((φ i).symm.trans (φ j)).source,
      0 < (fderiv ℝ ((φ i).symm.trans (φ j)) u).det)
    (g : ι → E ≃ₜ E) (hchart : ∀ i, A.chart i = (φ i).trans (g i).toOpenPartialHomeomorph)
    (hreg : ∀ i, ContDiff ℝ r (g i) ∧ ContDiff ℝ r (g i).symm)
    (hdet : ∀ i x, 0 < (fderiv ℝ (g i) x).det) :
    ∀ i j, ∀ u ∈ ((A.chart i).symm.trans (A.chart j)).source,
      0 < (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) u).det := by
  intro i j
  rw [hchart i, hchart j]
  exact det_fderiv_symm_trans_trans_homeomorph_pos (φ i) (φ j) (g i) (g j) hr (hφ i j)
    (hpos i j) (hreg i).2 (hreg j).1
    (det_fderiv_homeomorph_symm_pos (g i) hr (hreg i).1 (hreg i).2 (hdet i)) (hdet j)

end DifferentialGeometry.Topology.Manifold
