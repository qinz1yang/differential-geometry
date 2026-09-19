import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeAffine
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => EuclideanSpace ℝ (Fin (d + 1))

private def spaceTimeEquiv : X ≃L[ℝ] ℝ × E :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x 0, WithLp.toLp 2 (fun i => x i.succ))
      invFun := fun p => WithLp.toLp 2 (Fin.cons p.1 p.2)
      left_inv := by
        intro x
        ext i
        cases i using Fin.cases <;> rfl
      right_inv := by
        intro p
        ext i <;> rfl
      map_add' := by
        intro x y
        ext i <;> rfl
      map_smul' := by
        intro a x
        ext i <;> rfl }

private theorem spaceTimeEquiv_measurePreserving :
    MeasurePreserving (spaceTimeEquiv (d := d)) volume
      ((volume : Measure ℝ).prod (volume : Measure E)) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin d))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (d + 1))))
  have heq : (Prod.map id (WithLp.toLp 2) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0) ∘ WithLp.ofLp) =
      spaceTimeEquiv (d := d) := by
    funext x
    apply Prod.ext
    · rfl
    · ext i
      change x (Fin.succAbove 0 i) = x i.succ
      simp
  rwa [heq] at h

private theorem spaceTimeEquiv_single_zero :
    spaceTimeEquiv (EuclideanSpace.single (0 : Fin (d + 1)) 1) = (1, (0 : E)) := by
  ext i <;> simp [spaceTimeEquiv]

private theorem spaceTimeEquiv_single_succ (i : Fin d) :
    spaceTimeEquiv (EuclideanSpace.single i.succ 1) = (0, EuclideanSpace.single i 1) := by
  ext j <;> simp [spaceTimeEquiv]

private theorem spaceTimeEquiv_restrict_measurePreserving (J : Set ℝ) (Ω : Set E) :
    MeasurePreserving (spaceTimeEquiv (d := d))
      (volume.restrict (spaceTimeEquiv ⁻¹' (J ×ˢ Ω)))
      ((volume.restrict J).prod (volume.restrict Ω)) := by
  have h := spaceTimeEquiv_measurePreserving.restrict_preimage_emb
    (spaceTimeEquiv (d := d)).toHomeomorph.isClosedEmbedding.measurableEmbedding (J ×ˢ Ω)
  rwa [← Measure.prod_restrict] at h

private theorem hasWeakPartialDeriv_comp_spaceTimeEquiv
    {J : Set ℝ} {Ω : Set E} {U V : ℝ × E → ℝ} (i : Fin (d + 1))
    (h : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, U p * fderiv ℝ φ p (spaceTimeEquiv (EuclideanSpace.single i 1))
        ∂(volume.restrict J).prod (volume.restrict Ω)) =
        -∫ p, V p * φ p ∂(volume.restrict J).prod (volume.restrict Ω)) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => V (spaceTimeEquiv x))
      (fun x => U (spaceTimeEquiv x)) (spaceTimeEquiv ⁻¹' (J ×ˢ Ω)) := by
  apply weak_deriv_comp_affineEquiv (spaceTimeEquiv (d := d)).toContinuousAffineEquiv
    (μ := volume) (ν := (volume : Measure ℝ).prod (volume : Measure E))
    (EuclideanSpace.single i 1)
  intro φ hφ hφc hφs
  have hlinear : (spaceTimeEquiv (d := d)).toContinuousAffineEquiv.toAffineEquiv.linear
      (EuclideanSpace.single i 1) = spaceTimeEquiv (EuclideanSpace.single i 1) := rfl
  simpa only [hlinear, ← Measure.prod_restrict] using h φ hφ hφc hφs

private theorem memWkp_comp_spaceTimeEquiv_of_mixed_weak_partial_trees
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (N : ℕ)
    (P : ℕ → ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p ((volume.restrict J).prod (volume.restrict Ω)))
    (hPw : ∀ k ≤ N, ∀ m < N, ∀ β i, ∀ᵐ t ∂volume.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω)
    (hPt : ∀ k < N, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ x, P k 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (1, 0)
        ∂(volume.restrict J).prod (volume.restrict Ω)) =
        -∫ x, P (k + 1) 0 (fun i => Fin.elim0 i) x * φ x
          ∂(volume.restrict J).prod (volume.restrict Ω)) :
    MemWkp N p (fun x => P 0 0 (fun i => Fin.elim0 i) (spaceTimeEquiv x))
      (spaceTimeEquiv ⁻¹' (J ×ˢ Ω)) := by
  let e := spaceTimeEquiv (d := d)
  have hO : IsOpen (e ⁻¹' (J ×ˢ Ω)) := (hJ.prod hΩ).preimage e.continuous
  have hmem (k m β) : MemLp (fun x => P k m β (e x)) p (volume.restrict (e ⁻¹' (J ×ˢ Ω))) :=
    (Lp.memLp (P k m β)).comp_measurePreserving (spaceTimeEquiv_restrict_measurePreserving J Ω)
  have htime (k) (hk : k < N) := integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees N
    (1 : ℝ) (fun m β x => P k m β x) (fun m β x => P (k + 1) m β x)
    (fun m _ β => (Lp.memLp (P k m β)).locallyIntegrable hp)
    (fun m _ β => (Lp.memLp (P (k + 1) m β)).locallyIntegrable hp)
    (hPw k (by omega)) (hPw (k + 1) (by omega)) (hPt k hk)
  have hnode : ∀ r k m β, k + r ≤ N → m + r ≤ N →
      MemWkp r p (fun x => P k m β (e x)) (e ⁻¹' (J ×ˢ Ω)) := by
    intro r
    induction r with
    | zero =>
      intro k m β hk hm
      exact hmem k m β
    | succ r ih =>
      intro k m β hk hm
      let D : Fin (d + 1) → X → ℝ := Fin.cases
        (fun x => P (k + 1) m β (e x))
        (fun i x => P k (m + 1) (Fin.cons i β) (e x))
      apply memWkp_succ_of_hasWeakPartialDeriv hp hO (hmem k m β) (g := D)
      · intro i
        cases i using Fin.cases with
        | zero => exact ih (k + 1) m β (by omega) (by omega)
        | succ i => exact ih k (m + 1) (Fin.cons i β) (by omega) (by omega)
      · intro i
        cases i using Fin.cases with
        | zero =>
          apply hasWeakPartialDeriv_comp_spaceTimeEquiv
          rw [spaceTimeEquiv_single_zero]
          exact htime k (by omega) m (by omega) β
        | succ i =>
          apply hasWeakPartialDeriv_comp_spaceTimeEquiv
          rw [spaceTimeEquiv_single_succ]
          intro φ hφ hφc hφs
          exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
            ((Lp.memLp (P k m β)).locallyIntegrable hp)
            ((Lp.memLp (P k (m + 1) (Fin.cons i β))).locallyIntegrable hp) i
            (hPw k (by omega) m (by omega) β i) φ hφ hφc
            (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  exact hnode N 0 0 (fun i => Fin.elim0 i) (by omega) (by omega)

theorem exists_contDiffOn_ae_eq_of_mixed_weak_partial_trees
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω) (U : ℝ × E → ℝ)
    (h : ∀ N : ℕ, ∃ P : ℕ → ∀ m : ℕ, (Fin m → Fin d) →
        Lp ℝ 2 ((volume.restrict J).prod (volume.restrict Ω)),
      (P 0 0 (fun i => Fin.elim0 i) =ᵐ[(volume.restrict J).prod (volume.restrict Ω)] U) ∧
      (∀ k ≤ N, ∀ m < N, ∀ β i, ∀ᵐ t ∂volume.restrict J, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω) ∧
      ∀ k < N, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ J ×ˢ Ω →
        (∫ x, P k 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (1, 0)
          ∂(volume.restrict J).prod (volume.restrict Ω)) =
          -∫ x, P (k + 1) 0 (fun i => Fin.elim0 i) x * φ x
            ∂(volume.restrict J).prod (volume.restrict Ω)) :
    ∃ u : ℝ × E → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (J ×ˢ Ω) ∧
      U =ᵐ[(volume.restrict J).prod (volume.restrict Ω)] u := by
  let e := spaceTimeEquiv (d := d)
  have hO : IsOpen (e ⁻¹' (J ×ˢ Ω)) := (hJ.prod hΩ).preimage e.continuous
  have hν := spaceTimeEquiv_restrict_measurePreserving J Ω
  have hsob (N : ℕ) : MemWkp N 2 (fun x => U (e x)) (e ⁻¹' (J ×ˢ Ω)) := by
    obtain ⟨P, hP, hPw, hPt⟩ := h N
    have hp : 1 ≤ (2 : ℝ≥0∞) := by norm_num
    have hreg := memWkp_comp_spaceTimeEquiv_of_mixed_weak_partial_trees hJ hΩ hp N P hPw hPt
    exact (MemWkp_congr_ae hp hO (hν.quasiMeasurePreserving.ae hP)).mp hreg
  obtain ⟨v, hv, huv⟩ := EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two hO hsob
  refine ⟨fun p => v (e.symm p), ?_, ?_⟩
  · exact hv.comp e.symm.contDiff.contDiffOn (fun p hp => by
      change e (e.symm p) ∈ J ×ˢ Ω
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp)
  · have hνsymm := MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv hν
    filter_upwards [hνsymm.quasiMeasurePreserving.ae huv] with p hp
    change U (e (e.symm p)) = v (e.symm p) at hp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

theorem contDiffOn_of_continuousOn_of_mixed_weak_partial_trees
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω) (U : ℝ × E → ℝ)
    (hU : ContinuousOn U (J ×ˢ Ω))
    (h : ∀ N : ℕ, ∃ P : ℕ → ∀ m : ℕ, (Fin m → Fin d) →
        Lp ℝ 2 ((volume.restrict J).prod (volume.restrict Ω)),
      (P 0 0 (fun i => Fin.elim0 i) =ᵐ[(volume.restrict J).prod (volume.restrict Ω)] U) ∧
      (∀ k ≤ N, ∀ m < N, ∀ β i, ∀ᵐ t ∂volume.restrict J, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω) ∧
      ∀ k < N, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ J ×ˢ Ω →
        (∫ x, P k 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (1, 0)
          ∂(volume.restrict J).prod (volume.restrict Ω)) =
          -∫ x, P (k + 1) 0 (fun i => Fin.elim0 i) x * φ x
            ∂(volume.restrict J).prod (volume.restrict Ω)) :
    ContDiffOn ℝ (⊤ : ℕ∞) U (J ×ˢ Ω) := by
  obtain ⟨u, hu, hUu⟩ := exists_contDiffOn_ae_eq_of_mixed_weak_partial_trees hJ hΩ U h
  rw [Measure.prod_restrict] at hUu
  exact hu.congr (Measure.eqOn_open_of_ae_eq hUu (hJ.prod hΩ) hU hu.continuousOn)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
