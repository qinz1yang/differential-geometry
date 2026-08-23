import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue

noncomputable section

set_option autoImplicit false

open Set Function Bundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_of_isOpen {U : Set E} (hU : IsOpen U) (u : E → ℝ)
    (q : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ U) :
    partialDeriv (E := E) q u y = fderivWithin ℝ u U y ((chartModelBasis E) q) := by
  rw [partialDeriv, fderivWithin_of_isOpen hU hy]

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDerivWithin
    (Ψ : ℝ → E → ℝ) (q : Fin (Module.finrank ℝ E))
    {S : Set ℝ} {U : Set E} (hU : IsOpen U) {s₀ : ℝ} {y₀ : E}
    (hs : s₀ ∈ S) (hy : y₀ ∈ U)
    (hΨ : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => Ψ r.1 r.2) (S ×ˢ U) (s₀, y₀)) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) q (fun y => Ψ p.1 y) p.2) (S ×ˢ U) (s₀, y₀) := by
  have hmem : ((s₀, y₀) : ℝ × E) ∈ S ×ˢ U := ⟨hs, hy⟩
  have hst : S ×ˢ U ⊆ (fun p : ℝ × E => p.2) ⁻¹' U := fun p hp => hp.2
  have hf : ContDiffWithinAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y))
      ((S ×ˢ U) ×ˢ U) (((s₀, y₀) : ℝ × E), (fun p : ℝ × E => p.2) (s₀, y₀)) := by
    have huncurry : (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y)) =
        (fun r : ℝ × E => Ψ r.1 r.2) ∘ (fun z : (ℝ × E) × E => (z.1.1, z.2)) := by
      funext z; rfl
    rw [huncurry]
    refine hΨ.comp (((s₀, y₀) : ℝ × E), y₀)
      (((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffWithinAt) ?_
    rintro z ⟨⟨hz1, -⟩, hz2⟩
    exact ⟨hz1, hz2⟩
  have hg : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => p.2) (S ×ˢ U) (s₀, y₀) := contDiffWithinAt_snd
  have hk : ContDiffWithinAt ℝ ∞ (fun _ : ℝ × E => (chartModelBasis E) q) (S ×ˢ U) (s₀, y₀) :=
    contDiffWithinAt_const
  have hfd := hf.fderivWithin_apply hg hk hU.uniqueDiffOn (le_refl _) hmem hst
  exact hfd.congr (fun p hp => partialDeriv_of_isOpen hU _ q hp.2)
    (partialDeriv_of_isOpen hU _ q hy)

section GenTower

variable (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)

def GenJointGramOn (S : Set ℝ) : Prop :=
  (∀ (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}, s₀ ∈ S →
      y₀ ∈ interior (extChartAt I α).target →
      ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2)
        (S ×ˢ interior (extChartAt I α).target) (s₀, y₀)) ∧
  (∀ {s₀ : ℝ}, s₀ ∈ S →
      ∀ {x : M}, x ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      0 < (chartGramMatrix (I := I) (gfam s₀) α x).det)

omit [NeZero (Module.finrank ℝ E)] in
theorem genJointGramOn_of_gen {S : Set ℝ}
    (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S) :
    GenJointGramOn (I := I) gfam α S := by
  refine ⟨fun i j _ _ hs hy => (hG.1 i j hs hy).contDiffWithinAt, ?_⟩
  intro s₀ hs x hx
  exact hG.2 hs hx

omit [NeZero (Module.finrank ℝ E)] in
theorem invGramWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  classical
  have hGentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2) a b)
        (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
    intro a b
    have := hG.1 a b hs hy
    simpa only [chartGramOnE_def] using this
  have hdet : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
        ((extChartAt I α).symm p.2)).det)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
    have hdet_eq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ kk, chartGramMatrix (I := I) (gfam p.1) α
              ((extChartAt I α).symm p.2) (σ kk) kk) := by
      funext p; rw [Matrix.det_apply]; simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffWithinAt.sum (fun σ _ => ?_)
    refine contDiffWithinAt_const.mul ?_
    exact contDiffWithinAt_prod (fun kk _ => hGentry (σ kk) kk)
  have hx_base : (extChartAt I α).symm y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hy_t : y₀ ∈ (extChartAt I α).target := interior_subset hy
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_t
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have hdet_ne : (chartGramMatrix (I := I) (gfam (s₀, y₀).1) α
      ((extChartAt I α).symm (s₀, y₀).2)).det ≠ 0 := ne_of_gt (hG.2 hs hx_base)
  have hadj : ∀ kk ll : Fin (Module.finrank ℝ E),
      ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll)
        (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
    intro kk ll
    have hexp : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ m, (chartGramMatrix (I := I) (gfam p.1) α
                ((extChartAt I α).symm p.2)).updateRow ll
                (Pi.single kk (1 : ℝ)) (σ m) m) := by
      funext p; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
    rw [hexp]
    refine ContDiffWithinAt.sum (fun σ _ => ?_)
    refine contDiffWithinAt_const.mul ?_
    refine contDiffWithinAt_prod (fun m _ => ?_)
    by_cases hσm : σ m = ll
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun _ : ℝ × E => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) kk
            (1 : ℝ)) m) := by
        funext p; rw [hσm, Matrix.updateRow_self]
      rw [heq]; exact contDiffWithinAt_const
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2) (σ m) m) := by
        funext p; rw [Matrix.updateRow_ne hσm]
      rw [heq]; exact hGentry (σ m) m
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) =
      (fun p : ℝ × E => ((chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det)⁻¹ *
        (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate k l) := by
    funext p
    rw [chartInvGramOnE_def]
    change (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2))⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2)).det •
            (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiffAt_inv _ hdet_ne).comp_contDiffWithinAt (s₀, y₀) hdet).mul (hadj k l)

omit [NeZero (Module.finrank ℝ E)] in
theorem bracketWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (i j l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) i (fun y => chartGramOnE (I := I) (gfam r.1) α l j y) r.2 +
          partialDeriv (E := E) j (fun y => chartGramOnE (I := I) (gfam r.1) α l i y) r.2 -
          partialDeriv (E := E) l (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) := by
    funext r; rw [gramBracket]
  rw [heq]
  exact ((partialDerivWithin (fun s y => chartGramOnE (I := I) (gfam s) α l j y) i
      isOpen_interior hs hy (hG.1 l j hs hy)).add
    (partialDerivWithin (fun s y => chartGramOnE (I := I) (gfam s) α l i y) j
      isOpen_interior hs hy (hG.1 l i hs hy))).sub
    (partialDerivWithin (fun s y => chartGramOnE (I := I) (gfam s) α i j y) l
      isOpen_interior hs hy (hG.1 i j hs hy))

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) =
      (fun r : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α k l r.2 *
          gramBracket (I := I) (gfam r.1) α i j l r.2) := by
    funext r; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine contDiffWithinAt_const.mul (ContDiffWithinAt.sum (fun l _ => ?_))
  exact (invGramWithin (I := I) gfam α hG k l hs hy).mul
    (bracketWithin (I := I) gfam α hG i j l hs hy)

omit [NeZero (Module.finrank ℝ E)] in
theorem partChristWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (m i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartChristoffel (I := I) (gfam r.1) α i j k y) r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) :=
  partialDerivWithin (fun s y => chartChristoffel (I := I) (gfam s) α i j k y) m
    isOpen_interior hs hy (christoffelWithin (I := I) gfam α hG i j k hs hy)

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) j (fun y => chartChristoffel (I := I) (gfam r.1) α i k l y) r.2 -
          partialDeriv (E := E) k (fun y => chartChristoffel (I := I) (gfam r.1) α i j l y) r.2 +
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) (gfam r.1) α j m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i k m r.2 -
              chartChristoffel (I := I) (gfam r.1) α k m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i j m r.2))) := by
    funext r; rw [chartRiemannTensor_def]
  rw [heq]
  refine ((partChristWithin (I := I) gfam α hG j i k l hs hy).sub
    (partChristWithin (I := I) gfam α hG k i j l hs hy)).add ?_
  refine ContDiffWithinAt.sum (fun m _ => ?_)
  exact ((christoffelWithin (I := I) gfam α hG j m l hs hy).mul
      (christoffelWithin (I := I) gfam α hG i k m hs hy)).sub
    ((christoffelWithin (I := I) gfam α hG k m l hs hy).mul
      (christoffelWithin (I := I) gfam α hG i j m hs hy))

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) =
      (fun r : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (gfam r.1) α i j k j r.2) := by
    funext r; rw [chartRicciTensor_def]
  rw [heq]
  exact ContDiffWithinAt.sum (fun j _ => riemannWithin (I := I) gfam α hG i j k j hs hy)

omit [NeZero (Module.finrank ℝ E)] in
theorem partRiemWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (m i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m
          (fun y => chartRiemannTensor (I := I) (gfam r.1) α i j k l y) r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) :=
  partialDerivWithin (fun s y => chartRiemannTensor (I := I) (gfam s) α i j k l y) m
    isOpen_interior hs hy (riemannWithin (I := I) gfam α hG i j k l hs hy)

omit [NeZero (Module.finrank ℝ E)] in
theorem partRicciWithin {S : Set ℝ} (hG : GenJointGramOn (I := I) gfam α S)
    (m i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartRicciTensor (I := I) (gfam r.1) α i k y) r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) :=
  partialDerivWithin (fun s y => chartRicciTensor (I := I) (gfam s) α i k y) m
    isOpen_interior hs hy (ricciWithin (I := I) gfam α hG i k hs hy)

omit [NeZero (Module.finrank ℝ E)] in
theorem christWithin_of_open {S : Set ℝ} (hS : IsOpen S) (hG : GenJointGramOn (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) (s₀, y₀) :=
  (christoffelWithin (I := I) gfam α hG i j k hs hy).contDiffAt
    ((hS.prod isOpen_interior).mem_nhds ⟨hs, hy⟩)

omit [NeZero (Module.finrank ℝ E)] in
theorem riemWithin_of_open {S : Set ℝ} (hS : IsOpen S) (hG : GenJointGramOn (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) (s₀, y₀) :=
  (riemannWithin (I := I) gfam α hG i j k l hs hy).contDiffAt
    ((hS.prod isOpen_interior).mem_nhds ⟨hs, hy⟩)

end GenTower

section Consumer

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem genGramOn_of_field (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    GenJointGramOn (I := I) g α J := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    set e := trivializationAt E (TangentSpace I) α with he
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hsubset : (extChartAt I α).target ⊆ (extChartAt I α).symm ⁻¹' e.baseSet := by
      intro y hy'
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy'
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rw [he, trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => p.1) (J ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞
        (fun p : ℝ × E => p.2) (J ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
    have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
        (J ×ˢ interior (extChartAt I α).target) (extChartAt I α).target :=
      fun p hp => interior_subset hp.2
    have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
        (fun p : ℝ × E => (extChartAt I α).symm p.2)
        (J ×ˢ interior (extChartAt I α).target) :=
      hsymm.comp hsnd hmaps2
    have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
        (J ×ˢ interior (extChartAt I α).target) :=
      hσ1.prodMk hσ2
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g p.1) α i j p.2)
        (J ×ˢ interior (extChartAt I α).target) := by
      refine ((hgram i j).comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
      intro p _
      rfl
    exact hcomp.contDiffOn (s₀, y₀) ⟨hs, hy⟩
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (g s₀) α hx

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] in
theorem jointOnMWithin (α : M) (F : ℝ → E → ℝ) {J : Set ℝ} {t : ℝ} {x : M}
    (hF : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => F r.1 r.2)
      (J ×ˢ interior (extChartAt I α).target) (t, extChartAt I α x))
    (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) := by
  have hchart : ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (fun y : M => extChartAt I α y)
      (chartAt H α).source x :=
    (contMDiffOn_extChartAt (I := I) (x := α) (n := ∞)) x hx
  have hmapsSnd : Set.MapsTo (fun p : ℝ × M => p.2) (J ×ˢ (chartAt H α).source)
      (chartAt H α).source := fun p hp => hp.2
  have hchartComp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => extChartAt I α p.2) (J ×ˢ (chartAt H α).source) (t, x) :=
    hchart.comp ((t, x) : ℝ × M) contMDiffWithinAt_snd hmapsSnd
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × M => (p.1, extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) := by
    have h : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M => (p.1, extChartAt I α p.2))
        (J ×ˢ (chartAt H α).source) (t, x) :=
      contMDiffWithinAt_fst.prodMk hchartComp
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hmapsΦ : Set.MapsTo (fun p : ℝ × M => (p.1, extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (J ×ˢ interior (extChartAt I α).target) := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    have hsrc : p.2 ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hp2
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hsrc)
  simpa only [Function.comp_def] using
    hF.contMDiffWithinAt.comp ((t, x) : ℝ × M) hΦ hmapsΦ

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem chart_mem_interior (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    extChartAt I α x ∈ interior (extChartAt I α).target := by
  have hsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
    ((extChartAt I α).map_source hsrc)

omit [NeZero (Module.finrank ℝ E)] in
theorem christWithinM (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : GenJointGramOn (I := I) g α J) (i j k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) α i j k (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  jointOnMWithin (I := I) α (fun s y => chartChristoffel (I := I) (g s) α i j k y)
    (christoffelWithin (I := I) g α hG i j k ht (chart_mem_interior (I := I) α hx)) hx

omit [NeZero (Module.finrank ℝ E)] in
theorem riemWithinM (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : GenJointGramOn (I := I) g α J) (i j k l : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) α i j k l (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  jointOnMWithin (I := I) α (fun s y => chartRiemannTensor (I := I) (g s) α i j k l y)
    (riemannWithin (I := I) g α hG i j k l ht (chart_mem_interior (I := I) α hx)) hx

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciWithinM (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : GenJointGramOn (I := I) g α J) (i k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartRicciTensor (I := I) (g p.1) α i k (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  jointOnMWithin (I := I) α (fun s y => chartRicciTensor (I := I) (g s) α i k y)
    (ricciWithin (I := I) g α hG i k ht (chart_mem_interior (I := I) α hx)) hx

omit [NeZero (Module.finrank ℝ E)] in
theorem partRiemWithinM (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : GenJointGramOn (I := I) g α J) (m i j k l : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        partialDeriv (E := E) m
          (fun y => chartRiemannTensor (I := I) (g p.1) α i j k l y) (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  jointOnMWithin (I := I) α
    (fun s y =>
      partialDeriv (E := E) m (fun z => chartRiemannTensor (I := I) (g s) α i j k l z) y)
    (partRiemWithin (I := I) g α hG m i j k l ht (chart_mem_interior (I := I) α hx)) hx

omit [NeZero (Module.finrank ℝ E)] in
theorem partRicciWithinM (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : GenJointGramOn (I := I) g α J) (m i k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        partialDeriv (E := E) m
          (fun y => chartRicciTensor (I := I) (g p.1) α i k y) (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  jointOnMWithin (I := I) α
    (fun s y => partialDeriv (E := E) m (fun z => chartRicciTensor (I := I) (g s) α i k z) y)
    (partRicciWithin (I := I) g α hG m i k ht (chart_mem_interior (I := I) α hx)) hx

private theorem icc_subset_ico {a b c : ℝ} (hcb : c < b) : Icc a c ⊆ Ico a b :=
  fun _ hx => ⟨hx.1, lt_of_le_of_lt hx.2 hcb⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem slabBase_nhdsWithin (x₀ : M) (a c t : ℝ) :
    Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈
      𝓝[Icc a c ×ˢ (univ : Set M)] ((t, x₀) : ℝ × M) := by
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hset : (Icc a c ×ˢ (univ : Set M)) ∩
      ((fun p : ℝ × M => p.2) ⁻¹' (trivializationAt E (TangentSpace I) x₀).baseSet)
      = Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    ext p
    simp [Set.mem_prod]
  have hopen : ((fun p : ℝ × M => p.2) ⁻¹'
      (trivializationAt E (TangentSpace I) x₀).baseSet) ∈ 𝓝 ((t, x₀) : ℝ × M) :=
    (((trivializationAt E (TangentSpace I) x₀).open_baseSet.preimage
      continuous_snd)).mem_nhds hx₀
  have := inter_mem_nhdsWithin (Icc a c ×ˢ (univ : Set M)) (a := ((t, x₀) : ℝ × M)) hopen
  rwa [hset] at this

omit [NeZero (Module.finrank ℝ E)] in
theorem christSlabCont (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) x₀ i j k (extChartAt I x₀ p.2))
      (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hG := genGramOn_of_field (I := I) g x₀ hgram
  have hsub : Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ⊆
      Ico a b ×ˢ (chartAt H x₀).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact Set.prod_mono (icc_subset_ico hcb) (Set.Subset.refl _)
  intro p hp
  exact ((christWithinM (I := I) g x₀ hG i j k (hsub hp).1
    (hsub hp).2).continuousWithinAt).mono hsub

omit [NeZero (Module.finrank ℝ E)] in
theorem riemSlabCont (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) x₀ i j k l (extChartAt I x₀ p.2))
      (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hG := genGramOn_of_field (I := I) g x₀ hgram
  have hsub : Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ⊆
      Ico a b ×ˢ (chartAt H x₀).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact Set.prod_mono (icc_subset_ico hcb) (Set.Subset.refl _)
  intro p hp
  exact ((riemWithinM (I := I) g x₀ hG i j k l (hsub hp).1
    (hsub hp).2).continuousWithinAt).mono hsub

omit [NeZero (Module.finrank ℝ E)] in
theorem christSlabContAt (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ Icc a c) :
    ContinuousWithinAt
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) x₀ i j k (extChartAt I x₀ p.2))
      (Icc a c ×ˢ (univ : Set M)) (t, x₀) := by
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hbase := christSlabCont (I := I) g hcb x₀ hgram i j k (t, x₀) ⟨ht, hx₀⟩
  exact hbase.mono_of_mem_nhdsWithin (slabBase_nhdsWithin (I := I) x₀ a c t)

omit [NeZero (Module.finrank ℝ E)] in
theorem riemSlabContAt (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ Icc a c) :
    ContinuousWithinAt
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) x₀ i j k l (extChartAt I x₀ p.2))
      (Icc a c ×ˢ (univ : Set M)) (t, x₀) := by
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hbase := riemSlabCont (I := I) g hcb x₀ hgram i j k l (t, x₀) ⟨ht, hx₀⟩
  exact hbase.mono_of_mem_nhdsWithin (slabBase_nhdsWithin (I := I) x₀ a c t)

end Consumer

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
