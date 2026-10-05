import DifferentialGeometry.Geometry.Metric.Isometry.TransitionSubconvergence

/-!
# LFR13 with arbitrary ellipticity

Both metrics are scaled to normalize only their lower bound. The condition number remains
in the first derivative bound, and a finite envelope propagates it through the accepted
connection recurrence. Constants precede all metrics, maps and domains; bounded images
then give native finite-order subconvergence on every compact overlap.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness.MetricIsometry
variable {E : Type*} [normedE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]

open private isom_next_le isom_second_on isomNextBudget postBilin preBilin raisedKoszulOp from
DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds

private def ellipticJetEnvelope (D R : ℝ) : ℕ → ℝ
  | 0 => max 1 R
  | n + 1 => max (ellipticJetEnvelope D R n)
      (isomNextBudget (E0 := E) D (ellipticJetEnvelope D R n) n)

private theorem one_le_ellipticJetEnvelope (D R : ℝ) (n : ℕ) :
    1 ≤ ellipticJetEnvelope (E := E) D R n := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n hn => exact hn.trans (le_max_left _ _)

omit finiteE in
private theorem first_jet_bound_of_ellipticity (lam capLam : ℝ)
    (hlam : 0 < lam) (horder : lam ≤ capLam)
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E)
    (hupper : ∀ v, B v v ≤ capLam * ‖v‖ ^ 2)
    (hlower : ∀ v, lam * ‖v‖ ^ 2 ≤ C v v)
    (hiso : ∀ v, C (L v) (L v) = B v v) : ‖L‖ ≤ Real.sqrt (capLam / lam) := by
  have hcap : 0 ≤ capLam := hlam.le.trans horder
  have hratio : 0 ≤ capLam / lam := div_nonneg hcap hlam.le
  apply ContinuousLinearMap.opNorm_le_bound L (Real.sqrt_nonneg _)
  intro v
  have hquad := (hlower (L v)).trans ((hiso v).trans_le (hupper v))
  apply le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt hratio, div_mul_eq_mul_div, le_div_iff₀ hlam]
  nlinarith

omit finiteE in
private theorem scaled_metric_jet_bound (c A D : ℝ) (hc : 0 ≤ c)
    (hD : 1 ≤ D) (hAD : c * A ≤ D)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) {q : ℕ} (hq : 1 ≤ q)
    (hbound : ∀ x ∈ U, ‖iteratedFDeriv ℝ q B x‖ ≤ A) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ q (fun y => c • B y) x‖ ≤ D ^ q := by
  rw [iteratedFDeriv_const_smul_apply'
    (((hB x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact WithTop.coe_le_coe.mpr le_top)),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact ((mul_le_mul_of_nonneg_left (hbound x hx) hc).trans hAD).trans
    (le_self_pow₀ hD (by omega))

theorem exists_transition_jet_bound_of_ellipticity (K : ℕ) (lam capLam A : ℝ)
    (hlam : 0 < lam) (hlamcapLam : lam ≤ capLam) :
    ∃ M : ℝ, ∀ (H G : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (τ : ℕ → E → E)
      (U V : Set E), IsOpen U → IsOpen V →
      (∀ i, ContDiffOn ℝ ∞ (H i) U) → (∀ i, ContDiffOn ℝ ∞ (G i) V) →
      (∀ i, ContDiffOn ℝ ∞ (τ i) U) → (∀ i, MapsTo (τ i) U V) →
      (∀ i, ∀ x ∈ U, ∀ u v : E,
        H i x u v = G i (τ i x) (fderiv ℝ (τ i) x u) (fderiv ℝ (τ i) x v)) →
      (∀ i, ∀ y ∈ V, ∀ a b : E, G i y a b = G i y b a) →
      (∀ i, ∀ x ∈ U, ∀ v : E, lam * ‖v‖ ^ 2 ≤ H i x v v ∧
        H i x v v ≤ capLam * ‖v‖ ^ 2) →
      (∀ i, ∀ y ∈ V, ∀ v : E, lam * ‖v‖ ^ 2 ≤ G i y v v) →
      (∀ i q, 1 ≤ q → q ≤ K → ∀ x ∈ U, ‖iteratedFDeriv ℝ q (H i) x‖ ≤ A) →
      (∀ i q, 1 ≤ q → q ≤ K → ∀ y ∈ V, ‖iteratedFDeriv ℝ q (G i) y‖ ≤ A) →
      ∀ i r, 1 ≤ r → r ≤ K + 1 → ∀ x ∈ U, ‖iteratedFDeriv ℝ r (τ i) x‖ ≤ M
 := by
  let c : ℝ := 1 / (2 * lam)
  let D : ℝ := max 1 (c * |A|)
  let R : ℝ := Real.sqrt (capLam / lam)
  have hc : 0 < c := by dsimp [c]; positivity
  have hclam : c * lam = 1 / 2 := by dsimp [c]; field_simp
  have hD : 1 ≤ D := le_max_left _ _
  have hAD : c * A ≤ D :=
    (mul_le_mul_of_nonneg_left (le_abs_self A) hc.le).trans (le_max_right _ _)
  refine ⟨ellipticJetEnvelope (E := E) D R K, ?_⟩
  intro H G τ U V hU hV hH hG hτ hmap hiso hGsymm hHell hGell hHb hGb i r hr hrK x hx
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun y => c • H i y
  let C : E → E →L[ℝ] E →L[ℝ] ℝ := fun y => c • G i y
  have hB : ContDiffOn ℝ ∞ B U := (hH i).const_smul c
  have hC : ContDiffOn ℝ ∞ C V := (hG i).const_smul c
  have hBLower : ∀ y ∈ U, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B y v v := by
    intro y hy v
    have ht := mul_le_mul_of_nonneg_left (hHell i y hy v).1 hc.le
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ c * H i y v v
    simpa only [← mul_assoc, hclam] using ht
  have hCLower : ∀ y ∈ V, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ C y v v := by
    intro y hy v
    have ht := mul_le_mul_of_nonneg_left (hGell i y hy v) hc.le
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ c * G i y v v
    simpa only [← mul_assoc, hclam] using ht
  have hScaledIso : ∀ y ∈ U, ∀ u v : E,
      B y u v = C (τ i y) (fderiv ℝ (τ i) y u) (fderiv ℝ (τ i) y v) := by
    intro y hy u v
    change c * H i y u v = c * G i (τ i y) (fderiv ℝ (τ i) y u) (fderiv ℝ (τ i) y v)
    rw [hiso i y hy]
  have hCsymm : ∀ y ∈ V, ∀ u v : E, C y u v = C y v u := by
    intro y hy u v
    change c * G i y u v = c * G i y v u
    rw [hGsymm i y hy]
  have hDB : ∀ q, 1 ≤ q → q ≤ K → ‖iteratedFDeriv ℝ q B x‖ ≤ D ^ q := by
    intro q hq hqK
    exact scaled_metric_jet_bound c A D hc.le hD hAD (H i) hU (hH i) hq
      (hHb i q hq hqK) hx
  have hDC : ∀ q, 1 ≤ q → q ≤ K → ‖iteratedFDeriv ℝ q C (τ i x)‖ ≤ D ^ q := by
    intro q hq hqK
    exact scaled_metric_jet_bound c A D hc.le hD hAD (G i) hV (hG i) hq
      (hGb i q hq hqK) (hmap i hx)
  have hfirst : ‖iteratedFDeriv ℝ 1 (τ i) x‖ ≤ R := by
    rw [norm_iteratedFDeriv_one]
    exact first_jet_bound_of_ellipticity lam capLam hlam hlamcapLam (H i x) (G i (τ i x))
      (fderiv ℝ (τ i) x) (fun v => (hHell i x hx v).2) (hGell i (τ i x) (hmap i hx))
      (fun v => (hiso i x hx v v).symm)
  have hclaim : ∀ n, n ≤ K → ∀ j, 1 ≤ j → j ≤ n + 1 →
      ‖iteratedFDeriv ℝ j (τ i) x‖ ≤ ellipticJetEnvelope (E := E) D R n := by
    intro n
    induction n with
    | zero =>
      intro hn j hj hjn
      have hj1 : j = 1 := by omega
      subst j
      exact hfirst.trans (le_max_right _ _)
    | succ n ih =>
      intro hn j hj hjn
      by_cases hprev : j ≤ n + 1
      · exact (ih (by omega) j hj hprev).trans (le_max_left _ _)
      · have hjnext : j = n + 2 := by omega
        subst j
        have hsecond := isom_second_on B C (τ i) U V hU hV
          (hB.of_le (by exact WithTop.coe_le_coe.mpr le_top))
          (hC.of_le (by exact WithTop.coe_le_coe.mpr le_top))
          ((hτ i).of_le (by exact WithTop.coe_le_coe.mpr le_top)) (hmap i) hScaledIso
          hCsymm hBLower hCLower
        have heq : fderiv ℝ (fderiv ℝ (τ i)) =ᶠ[𝓝 x] fun y =>
            postBilin (fderiv ℝ (τ i) y) (raisedKoszulOp (B y) (fderiv ℝ B y)) -
            preBilin (raisedKoszulOp (C (τ i y)) (fderiv ℝ C (τ i y))) (fderiv ℝ (τ i) y) := by
          filter_upwards [hU.mem_nhds hx] with y hy
          exact hsecond y hy
        have hnext := isom_next_le B C (τ i) x n D (ellipticJetEnvelope (E := E) D R n)
          (((hB x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact WithTop.coe_le_coe.mpr le_top))
          (((hC (τ i x) (hmap i hx)).contDiffAt (hV.mem_nhds (hmap i hx))).of_le
            (by exact WithTop.coe_le_coe.mpr le_top))
          (((hτ i x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact WithTop.coe_le_coe.mpr le_top))
          (by filter_upwards [hU.mem_nhds hx] with y hy v; exact hBLower y hy v)
          (by filter_upwards [hV.mem_nhds (hmap i hx)] with y hy v; exact hCLower y hy v)
          (fun q hq hqn => hDB q hq (by omega))
          (fun q hq hqn => hDC q hq (by omega))
          (fun q hq hqn => (ih (by omega) q hq hqn).trans
            (le_self_pow₀ (one_le_ellipticJetEnvelope D R n) (by omega))) heq
        exact hnext.trans (le_max_right _ _)
  exact hclaim K le_rfl r hr hrK

theorem exists_transition_cK_subseq_of_ellipticity (K : ℕ) (lam capLam : ℝ)
    (hlam : 0 < lam) (hlamcapLam : lam ≤ capLam)
    (H G : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (τ : ℕ → E → E) {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hVb : ∃ Z : ℝ, ∀ y ∈ V, ‖y‖ ≤ Z)
    (hH : ∀ i, ContDiffOn ℝ ∞ (H i) U) (hG : ∀ i, ContDiffOn ℝ ∞ (G i) V)
    (hτ : ∀ i, ContDiffOn ℝ ∞ (τ i) U) (hmap : ∀ i, MapsTo (τ i) U V)
    (hiso : ∀ i, ∀ x ∈ U, ∀ u v : E,
      H i x u v = G i (τ i x) (fderiv ℝ (τ i) x u) (fderiv ℝ (τ i) x v))
    (hGsymm : ∀ i, ∀ y ∈ V, ∀ a b : E, G i y a b = G i y b a)
    (hHell : ∀ i, ∀ x ∈ U, ∀ v : E, lam * ‖v‖ ^ 2 ≤ H i x v v ∧
      H i x v v ≤ capLam * ‖v‖ ^ 2)
    (hGell : ∀ i, ∀ y ∈ V, ∀ v : E, lam * ‖v‖ ^ 2 ≤ G i y v v)
    {A : ℝ} (hHb : ∀ i q, 1 ≤ q → q ≤ K → ∀ x ∈ U, ‖iteratedFDeriv ℝ q (H i) x‖ ≤ A)
    (hGb : ∀ i q, 1 ≤ q → q ≤ K → ∀ y ∈ V, ‖iteratedFDeriv ℝ q (G i) y‖ ≤ A) :
    ∃ (φ : ℕ → ℕ) (τinf : E → E), StrictMono φ ∧ ContDiffOn ℝ K τinf U ∧
      ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S K (fun k => τ (φ k)) τinf
 := by
  obtain ⟨M, hM⟩ := exists_transition_jet_bound_of_ellipticity (E := E) K lam capLam A
    hlam hlamcapLam
  have hbound := hM H G τ U V hU hV hH hG hτ hmap hiso hGsymm hHell hGell hHb hGb
  obtain ⟨Z, hZ⟩ := hVb
  have hbdd : ∀ r, r ≤ K + 1 → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ B : ℝ, ∀ i, ∀ x ∈ S, ‖iteratedFDeriv ℝ r (τ i) x‖ ≤ B := by
    intro r hr S hS hSU
    clear hS
    by_cases hr0 : r = 0
    · subst r
      refine ⟨Z, ?_⟩
      intro i x hx
      rw [norm_iteratedFDeriv_zero]
      exact hZ (τ i x) (hmap i (hSU hx))
    · refine ⟨M, ?_⟩
      intro i x hx
      exact hbound i r (by omega) hr x (hSU hx)
  obtain ⟨φ, τinf, hφ, hreg, hconv⟩ := exists_cP_subseq_on_of_le (K + 1) (by omega)
    hU τ (fun i => (hτ i).of_le (by exact WithTop.coe_le_coe.mpr le_top)) hbdd
  exact ⟨φ, τinf, hφ, by simpa only [Nat.add_sub_cancel] using hreg,
    by simpa only [Nat.add_sub_cancel] using hconv⟩

end DifferentialGeometry.CheegerGromovCompactness.MetricIsometry
