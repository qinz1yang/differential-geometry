import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.Algebra.Structures


namespace Tensor0SBundle

noncomputable section

open Bundle
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma chartGramFamilyDet_jointContMDiffOn
    {U : Set ℝ} (x₀ : M) (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hGram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).det)
      (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hexp :
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).det)
        = (fun p : ℝ × M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 (σ i) i) := by
    funext p
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact hGram (σ i) i

private lemma chartGramFamilyAdjugate_jointContMDiffOn
    {U : Set ℝ} (x₀ : M) (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hGram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).adjugate i j)
      (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hexp :
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).adjugate i j)
        = (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).updateRow j
              (Pi.single i (1 : ℝ))).det) := by
    funext p
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 :
      (fun p : ℝ × M =>
          ((chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).updateRow j
            (Pi.single i (1 : ℝ))).det)
        = (fun p : ℝ × M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k, (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).updateRow j
                    (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext p
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq :
        (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).updateRow j
          (Pi.single i (1 : ℝ)) (σ k) k)
          = (fun _ : ℝ × M =>
              (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i (1 : ℝ)) k) := by
      funext p
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).updateRow j
          (Pi.single i (1 : ℝ)) (σ k) k)
          = (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 (σ k) k) := by
      funext p
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact hGram (σ k) k

private lemma chartInvGramFamily_jointContMDiffOn
    {U : Set ℝ} (x₀ : M) (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hGram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartInvGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
      (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hcongr : ∀ p ∈ U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet,
      chartInvGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j
        = ((chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).det)⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).adjugate i j := by
    intro p _
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).det •
            (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).adjugate) i j = _
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_
    (chartGramFamilyAdjugate_jointContMDiffOn (I := I) x₀ g_fam hGram i j)
  intro p hp
  have hdet_pos := chartGramMatrix_det_pos (I := I) (g_fam p.1) x₀ hp.2
  have hdet_ne : (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).det ≠ 0 := ne_of_gt hdet_pos
  have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
      (chartGramMatrix (I := I) (g_fam p.1) x₀ p.2).det := contDiffAt_inv _ hdet_ne
  have h_at := (chartGramFamilyDet_jointContMDiffOn (I := I) x₀ g_fam hGram) p hp
  exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt p h_at

theorem normSq0S_jointContMDiffOn
    (g_fam : ℝ → SmoothRiemannianMetric I M) (s : ℕ)
    (T : ℝ → (x : M) → Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x)
    {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ {Idx : Type} [Fintype Idx] (frame : Idx → (x : M) → TangentSpace I x)
        {u : Set M}, IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u →
      ∀ i j : Idx, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (g_fam p.1).inner p.2 (frame i p.2) (frame j p.2)) (U ×ˢ u))
    (hT : ∀ {Idx : Type} [Fintype Idx] (frame : Idx → (x : M) → TangentSpace I x)
        {u : Set M}, IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u →
      ∀ m : Fin s → Idx, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun a => frame (m a) p.2)) (U ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (I := I) (g_fam p.1) p.2 s (T p.1 p.2))
      (U ×ˢ (Set.univ : Set M)) := by
  classical
  apply contMDiffOn_of_locally_contMDiffOn
  rintro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, -⟩ := hp
  set e := trivializationAt E (TangentSpace I) x₀ with he
  refine ⟨U ×ˢ e.baseSet, hU.prod e.open_baseSet, ⟨ht₀, ?_⟩, ?_⟩
  · exact mem_baseSet_trivializationAt E (TangentSpace I) x₀
  · have hframe0 : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
        (e.localFrame (chartModelBasis E)) e.baseSet :=
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
    have hbridge : ∀ {y : M}, y ∈ e.baseSet → ∀ k,
        e.localFrame (chartModelBasis E) k y = chartBasisVecFiber (I := I) x₀ k y := by
      intro y hy k
      rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hy]
      rfl
    have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
        (chartBasisVecFiber (I := I) x₀) e.baseSet :=
      hframe0.congr (fun k y hy => hbridge hy k)
    have hGram : ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (U ×ˢ e.baseSet) :=
      fun i j => hg (chartBasisVecFiber (I := I) x₀) hframe i j
    have hInv : ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => chartInvGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (U ×ˢ e.baseSet) :=
      fun i j => chartInvGramFamily_jointContMDiffOn (I := I) x₀ g_fam hGram i j
    have hTcomp : ∀ m : Fin s → Fin (Module.finrank ℝ E),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => T p.1 p.2 (fun a => chartBasisVecFiber (I := I) x₀ (m a) p.2))
          (U ×ˢ e.baseSet) :=
      fun m => hT (chartBasisVecFiber (I := I) x₀) hframe m
    have hRHS : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          ∑ I0 : Fin s → Fin (Module.finrank ℝ E),
            ∑ J0 : Fin s → Fin (Module.finrank ℝ E),
              (∏ a : Fin s, chartInvGramMatrix (I := I) (g_fam p.1) x₀ p.2 (I0 a) (J0 a)) *
                  T p.1 p.2 (fun a => chartBasisVecFiber (I := I) x₀ (I0 a) p.2) *
                    T p.1 p.2 (fun a => chartBasisVecFiber (I := I) x₀ (J0 a) p.2))
        (U ×ˢ e.baseSet) := by
      refine contMDiffOn_finset_sum (fun I0 _ => ?_)
      refine contMDiffOn_finset_sum (fun J0 _ => ?_)
      refine ContMDiffOn.mul (ContMDiffOn.mul ?_ (hTcomp I0)) (hTcomp J0)
      exact contMDiffOn_finset_prod (fun a _ => hInv (I0 a) (J0 a))
    have key : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => normSq0S (I := I) (g_fam p.1) p.2 s (T p.1 p.2))
        (U ×ˢ e.baseSet) := by
      refine hRHS.congr ?_
      intro p hp
      obtain ⟨-, hy⟩ := hp
      have hinv : MetricInverseInBasis (I := I) (g_fam p.1) p.2
          (chartBasisFamily (I := I) x₀ hy)
          (fun i j => chartInvGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j) := by
        have hgram : ∀ a b : Fin (Module.finrank ℝ E),
            (g_fam p.1).inner p.2 (chartBasisFamily (I := I) x₀ hy a)
                (chartBasisFamily (I := I) x₀ hy b)
              = chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 a b := by
          intro a b
          simp only [chartBasisFamily_apply, chartGramMatrix_apply]
        intro a b
        refine ⟨?_, ?_⟩
        · simp only [hgram]
          rw [← Matrix.mul_apply,
            chartInvGramMatrix_mul_chartGramMatrix (I := I) (g_fam p.1) x₀ hy,
            Matrix.one_apply]
        · simp only [hgram]
          rw [← Matrix.mul_apply,
            chartGramMatrix_mul_chartInvGramMatrix (I := I) (g_fam p.1) x₀ hy,
            Matrix.one_apply]
      rw [normSq0S_eq_coord (I := I) (g_fam p.1) p.2 s (chartBasisFamily (I := I) x₀ hy)
        (fun i j => chartInvGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j) hinv (T p.1 p.2)]
      unfold coordInner0S
      simp only [tensor0SComponent_apply, chartBasisFamily_apply]
    exact key.mono Set.inter_subset_right

theorem chartGram_jointContMDiffOn_of_metricFamilySmoothOn
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
      (D.regular ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (e.localFrame (chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  have hbridge : ∀ {y : M}, y ∈ e.baseSet → ∀ k,
      e.localFrame (chartModelBasis E) k y = chartBasisVecFiber (I := I) x₀ k y := by
    intro y hy k
    rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hy]
    rfl
  have hcomp := hG.frameCompSmooth (e.localFrame (chartModelBasis E)) hframe i j
  refine hcomp.congr ?_
  intro p hp
  simp only [chartGramMatrix_apply, hbridge hp.2 i, hbridge hp.2 j]

end

end Tensor0SBundle
