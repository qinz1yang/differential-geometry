import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_mul_of_finite_weak_partial_trees
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (A Y : ∀ n : ℕ, (Fin n → Fin d) → E → ℝ)
    (hA : ∀ n ≤ K, ∀ α, MemLp (A n α) ∞ (volume.restrict Ω))
    (hY : ∀ n ≤ K, ∀ α, MemLp (Y n α) p (volume.restrict Ω))
    (hAsmooth : ∀ n < K, ∀ α, ContDiffOn ℝ (⊤ : ℕ∞) (A n α) Ω)
    (hDA : ∀ n < K, ∀ α i,
      A (n + 1) (Fin.cons i α) =ᵐ[volume.restrict Ω]
        fun x => fderiv ℝ (A n α) x (EuclideanSpace.single i 1))
    (hYweak : ∀ n < K, ∀ α i,
      DeGiorgi.HasWeakPartialDeriv i (Y (n + 1) (Fin.cons i α)) (Y n α) Ω) :
    MemWkp K p (fun x => A 0 (fun i => Fin.elim0 i) x *
      Y 0 (fun i => Fin.elim0 i) x) Ω := by
  have hnode : ∀ k n m α β, n + k ≤ K → m + k ≤ K →
      MemWkp k p (fun x => A n α x * Y m β x) Ω := by
    intro k
    induction k with
    | zero =>
        intro n m α β hn hm
        exact (hY m (by omega) β).mul (hA n (by omega) α)
    | succ k ih =>
        intro n m α β hn hm
        have hnK : n < K := by omega
        have hmK : m < K := by omega
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ
          ((hY m (by omega) β).mul (hA n (by omega) α))
          (g := fun i x => A n α x * Y (m + 1) (Fin.cons i β) x +
            A (n + 1) (Fin.cons i α) x * Y m β x)
        · intro i
          exact MemWkp.add hp hΩ
            (ih n (m + 1) α (Fin.cons i β) (by omega) (by omega))
            (ih (n + 1) m (Fin.cons i α) β (by omega) (by omega))
        · intro i
          have hw := (hYweak m hmK β i).mul_contDiffOn hΩ (hAsmooth n hnK α)
            ((hY m (by omega) β).locallyIntegrable hp)
            ((hY (m + 1) (by omega) (Fin.cons i β)).locallyIntegrable hp)
          intro φ hφ hφc hφs
          refine (hw φ hφ hφc hφs).trans ?_
          congr 1
          apply integral_congr_ae
          filter_upwards [hDA n hnK α i] with x hx
          rw [hx]
  exact hnode K 0 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (by omega) (by omega)

theorem ae_memWkp_of_finite_sum_weak_partial_trees
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (f : Z × E → ℝ)
    (A Y : ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hA : ∀ j n, n ≤ K → ∀ α, MemLp (A j n α) ∞ (μ.prod (volume.restrict Ω)))
    (hY : ∀ j n, n ≤ K → ∀ α, MemLp (Y j n α) p (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ j n, n < K → ∀ α, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A j n α (t, x)) Ω)
    (hDA : ∀ j n, n < K → ∀ α i,
      A j (n + 1) (Fin.cons i α) =ᵐ[μ.prod (volume.restrict Ω)]
        fun q => fderiv ℝ (fun x => A j n α (q.1, x)) q.2 (EuclideanSpace.single i 1))
    (hYweak : ∀ j n, n < K → ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y j n α (t, x)) Ω)
    (hf : f =ᵐ[μ.prod (volume.restrict Ω)] fun q => ∑ j,
      A j 0 (fun i => Fin.elim0 i) q * Y j 0 (fun i => Fin.elim0 i) q) :
    ∀ᵐ t ∂μ, MemWkp K p (fun x => f (t, x)) Ω := by
  classical
  have hAslice : ∀ j n (hn : n ≤ K) α, ∀ᵐ t ∂μ,
      MemLp (fun x => A j n α (t, x)) ∞ (volume.restrict Ω) :=
    fun j n hn α => (hA j n hn α).prodMk_left_top
  have hYslice : ∀ j n (hn : n ≤ K) α, ∀ᵐ t ∂μ,
      MemLp (fun x => Y j n α (t, x)) p (volume.restrict Ω) := by
    intro j n hn α
    by_cases hptop : p = ⊤
    · subst p
      exact (hY j n hn α).prodMk_left_top
    · exact (hY j n hn α).prodMk_left hptop
  have hDAslice : ∀ j n (hn : n < K) α i, ∀ᵐ t ∂μ,
      (fun x => A j (n + 1) (Fin.cons i α) (t, x)) =ᵐ[volume.restrict Ω]
        fun x => fderiv ℝ (fun y => A j n α (t, y)) x (EuclideanSpace.single i 1) :=
    fun j n hn α i => Measure.ae_ae_of_ae_prod (hDA j n hn α i)
  have hAp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr (hAslice j n hn)
  have hYp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr (hYslice j n hn)
  have hAsp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr (hAsmooth j n hn)
  have hDAp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr fun α => ae_all_iff.mpr (hDAslice j n hn α)
  have hYwp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr fun α => ae_all_iff.mpr (hYweak j n hn α)
  filter_upwards [hAp, hYp, hAsp, hDAp, hYwp, Measure.ae_ae_of_ae_prod hf]
    with t hAt hYt hAst hDAt hYwt hft
  apply (MemWkp_congr_ae hp hΩ hft).mpr
  have hterm (j : ι) : MemWkp K p (fun x =>
      A j 0 (fun i => Fin.elim0 i) (t, x) * Y j 0 (fun i => Fin.elim0 i) (t, x)) Ω :=
    memWkp_mul_of_finite_weak_partial_trees hp hΩ K
      (fun n α x => A j n α (t, x)) (fun n α x => Y j n α (t, x))
      (hAt j) (hYt j) (hAst j) (hDAt j) (hYwt j)
  have hsum (s : Finset ι) : MemWkp K p (fun x => ∑ j ∈ s,
      A j 0 (fun i => Fin.elim0 i) (t, x) * Y j 0 (fun i => Fin.elim0 i) (t, x)) Ω := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (MemWkp_zero_fun (k := K) hp hΩ)
    | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using MemWkp.add hp hΩ (hterm j) ih
  exact hsum Finset.univ

private theorem hasWeakPartialDeriv_sum
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    {V W : ι → E → ℝ} {i : Fin d}
    (hV : ∀ j, MemLp (V j) p (volume.restrict Ω))
    (hW : ∀ j, MemLp (W j) p (volume.restrict Ω))
    (hweak : ∀ j, DeGiorgi.HasWeakPartialDeriv i (W j) (V j) Ω) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => ∑ j, W j x) (fun x => ∑ j, V j x) Ω := by
  intro φ hφ hφc hφs
  have hI j : Integrable (fun x => V j x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) (volume.restrict Ω) :=
    (hV j).locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hJ j : Integrable (fun x => W j x * φ x) (volume.restrict Ω) :=
    (hW j).locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => hI j, integral_finsetSum _ fun j _ => hJ j,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hweak j φ hφ hφc hφs

theorem exists_lp_weak_partial_tree_of_finite_sum
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (f : Lp ℝ p (μ.prod (volume.restrict Ω)))
    (A Y : ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hA : ∀ j n, n ≤ K → ∀ α, MemLp (A j n α) ∞ (μ.prod (volume.restrict Ω)))
    (hY : ∀ j n, n ≤ K → ∀ α, MemLp (Y j n α) p (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ j n, n < K → ∀ α, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A j n α (t, x)) Ω)
    (hDA : ∀ j n, n < K → ∀ α i,
      A j (n + 1) (Fin.cons i α) =ᵐ[μ.prod (volume.restrict Ω)]
        fun q => fderiv ℝ (fun x => A j n α (q.1, x)) q.2 (EuclideanSpace.single i 1))
    (hYweak : ∀ j n, n < K → ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y j n α (t, x)) Ω)
    (hf : f =ᵐ[μ.prod (volume.restrict Ω)] fun q => ∑ j,
      A j 0 (fun i => Fin.elim0 i) q * Y j 0 (fun i => Fin.elim0 i) q) :
    ∃ F : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)),
      F 0 (fun i => Fin.elim0 i) = f ∧
        ∀ n < K, ∀ α i, ∀ᵐ t ∂μ,
          DeGiorgi.HasWeakPartialDeriv i
            (fun x => F (n + 1) (Fin.cons i α) (t, x))
            (fun x => F n α (t, x)) Ω := by
  classical
  have hslices {g : Z × E → ℝ} (hg : MemLp g p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun x => g (t, x)) p (volume.restrict Ω) := by
    by_cases hpt : p = ⊤
    · subst p
      exact hg.prodMk_left_top
    · exact hg.prodMk_left hpt
  induction K generalizing ι f with
  | zero =>
      exact ⟨fun _ _ => f, rfl, fun n hn => by omega⟩
  | succ K ih =>
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      let V := fun j q => A j 0 e q * Y j 0 e q
      let D := fun i j q => A j 0 e q * Y j 1 (Fin.cons i e) q +
        A j 1 (Fin.cons i e) q * Y j 0 e q
      let W := fun i q => ∑ j, D i j q
      have hV j : MemLp (V j) p (μ.prod (volume.restrict Ω)) :=
        (hY j 0 (by omega) e).mul (hA j 0 (by omega) e)
      have hD i j : MemLp (D i j) p (μ.prod (volume.restrict Ω)) :=
        ((hY j 1 (by omega) (Fin.cons i e)).mul (hA j 0 (by omega) e)).add
          ((hY j 0 (by omega) e).mul (hA j 1 (by omega) (Fin.cons i e)))
      have hW i : MemLp (W i) p (μ.prod (volume.restrict Ω)) :=
        memLp_finsetSum Finset.univ fun j _ => hD i j
      let w := fun i => (hW i).toLp (W i)
      have hweak i : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
          (fun x => w i (t, x)) (fun x => f (t, x)) Ω := by
        have hterm j : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
            (fun x => D i j (t, x)) (fun x => V j (t, x)) Ω := by
          filter_upwards [hAsmooth j 0 (by omega) e, hYweak j 0 (by omega) e i,
            hslices (hY j 0 (by omega) e),
            hslices (hY j 1 (by omega) (Fin.cons i e)),
            Measure.ae_ae_of_ae_prod (hDA j 0 (by omega) e i)]
            with t hAt hwt hYt hDYt hDAt
          have hw := hwt.mul_contDiffOn hΩ hAt
            (hYt.locallyIntegrable hp) (hDYt.locallyIntegrable hp)
          intro φ hφ hφc hφs
          refine (hw φ hφ hφc hφs).trans ?_
          congr 1
          apply integral_congr_ae
          filter_upwards [hDAt] with x hx
          dsimp [D]
          rw [hx]
        filter_upwards [ae_all_iff.mpr hterm,
          ae_all_iff.mpr (fun j => hslices (hV j)),
          ae_all_iff.mpr (fun j => hslices (hD i j)),
          Measure.ae_ae_of_ae_prod hf,
          Measure.ae_ae_of_ae_prod (hW i).coeFn_toLp] with t hwt hVt hDt hft hWt
        have hw := hasWeakPartialDeriv_sum hp hVt hDt hwt
        intro φ hφ hφc hφs
        calc
          (∫ x in Ω, f (t, x) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
              ∫ x in Ω, (∑ j, V j (t, x)) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
            apply integral_congr_ae
            filter_upwards [hft] with x hx
            rw [hx]
          _ = -∫ x in Ω, (∑ j, D i j (t, x)) * φ x := hw φ hφ hφc hφs
          _ = -∫ x in Ω, w i (t, x) * φ x := by
            congr 1
            apply integral_congr_ae
            filter_upwards [hWt] with x hx
            rw [hx]
      have hchild i :
          ∃ F : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)),
            F 0 e = w i ∧ ∀ n < K, ∀ α r, ∀ᵐ t ∂μ,
              DeGiorgi.HasWeakPartialDeriv r
                (fun x => F (n + 1) (Fin.cons r α) (t, x))
                (fun x => F n α (t, x)) Ω := by
        let B : ι ⊕ ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ :=
          Sum.elim (fun j n α => A j n α) (fun j n α => A j (n + 1) (Fin.snoc α i))
        let U : ι ⊕ ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ :=
          Sum.elim (fun j n α => Y j (n + 1) (Fin.snoc α i)) (fun j n α => Y j n α)
        apply ih (w i) B U
        · intro j n hn α
          cases j with
          | inl j => exact hA j n (by omega) α
          | inr j => exact hA j (n + 1) (by omega) (Fin.snoc α i)
        · intro j n hn α
          cases j with
          | inl j => exact hY j (n + 1) (by omega) (Fin.snoc α i)
          | inr j => exact hY j n (by omega) α
        · intro j n hn α
          cases j with
          | inl j => exact hAsmooth j n (by omega) α
          | inr j => exact hAsmooth j (n + 1) (by omega) (Fin.snoc α i)
        · intro j n hn α r
          cases j with
          | inl j => exact hDA j n (by omega) α r
          | inr j =>
              simpa only [B, Sum.elim_inr, Fin.cons_snoc_eq_snoc_cons] using
                hDA j (n + 1) (by omega) (Fin.snoc α i) r
        · intro j n hn α r
          cases j with
          | inl j =>
              simpa only [U, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
                hYweak j (n + 1) (by omega) (Fin.snoc α i) r
          | inr j => exact hYweak j n (by omega) α r
        · refine ((hW i).coeFn_toLp).trans ?_
          apply Filter.Eventually.of_forall
          intro q
          simp only [W, D, B, U, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
            Finset.sum_add_distrib]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> congr 2 <;>
            funext r <;> fin_cases r <;> rfl
      choose C hC hCW using hchild
      let F : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)) :=
        fun n => match n with
        | 0 => fun _ => f
        | n + 1 => fun α => C (α (Fin.last n)) n (Fin.init α)
      refine ⟨F, rfl, ?_⟩
      intro n hn α i
      cases n with
      | zero =>
          have hα : α = e := Subsingleton.elim _ _
          subst α
          have he : Fin.init (Fin.cons i e : Fin 1 → Fin d) = e :=
            Subsingleton.elim _ _
          simpa only [F, Fin.cons_zero, Fin.last_zero, hC,
            he] using hweak i
      | succ n =>
          obtain ⟨β, j, rfl⟩ : ∃ (β : Fin n → Fin d) (j : Fin d), α = Fin.snoc β j :=
            ⟨Fin.init α, α (Fin.last n), (Fin.snoc_init_self α).symm⟩
          simpa only [F, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_last, Fin.init_snoc] using
            hCW j n (by omega) β i

theorem ae_memWkp_and_memLp_wkpNorm_of_finite_sum_weak_partial_trees
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (f : Z × E → ℝ)
    (A Y : ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hA : ∀ j n, n ≤ K → ∀ α, MemLp (A j n α) ∞ (μ.prod (volume.restrict Ω)))
    (hY : ∀ j n, n ≤ K → ∀ α, MemLp (Y j n α) p (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ j n, n < K → ∀ α, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A j n α (t, x)) Ω)
    (hDA : ∀ j n, n < K → ∀ α i,
      A j (n + 1) (Fin.cons i α) =ᵐ[μ.prod (volume.restrict Ω)]
        fun q => fderiv ℝ (fun x => A j n α (q.1, x)) q.2 (EuclideanSpace.single i 1))
    (hYweak : ∀ j n, n < K → ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y j n α (t, x)) Ω)
    (hf : f =ᵐ[μ.prod (volume.restrict Ω)] fun q => ∑ j,
      A j 0 (fun i => Fin.elim0 i) q * Y j 0 (fun i => Fin.elim0 i) q) :
    (∀ᵐ t ∂μ, MemWkp K p (fun x => f (t, x)) Ω) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm K p (fun x => f (t, x)) Ω).toReal) p μ := by
  have hfLp : MemLp f p (μ.prod (volume.restrict Ω)) :=
    (memLp_finsetSum Finset.univ fun j _ =>
      (hY j 0 (by omega) (fun i => Fin.elim0 i)).mul
        (hA j 0 (by omega) (fun i => Fin.elim0 i))).ae_eq hf.symm
  obtain ⟨F, hF, hFW⟩ := exists_lp_weak_partial_tree_of_finite_sum hp hΩ K
    (hfLp.toLp f) A Y hA hY hAsmooth hDA hYweak (hfLp.coeFn_toLp.trans hf)
  have heq : ∀ᵐ t ∂μ, (fun x => F 0 (fun i => Fin.elim0 i) (t, x)) =ᵐ[volume.restrict Ω]
      fun x => f (t, x) := by
    rw [hF]
    exact Measure.ae_ae_of_ae_prod hfLp.coeFn_toLp
  obtain ⟨hmem, hnorm⟩ := ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree hp hpt hΩ K
    (fun n α q => F n α q) (fun n _ α => Lp.memLp (F n α)) hFW
  constructor
  · filter_upwards [hmem, heq] with t ht he
    exact (MemWkp_congr_ae hp hΩ he).mp ht
  · apply hnorm.ae_eq
    filter_upwards [heq] with t ht
    exact congrArg ENNReal.toReal (wkpNorm_congr_ae hp hΩ ht)

theorem ae_memWkp_mul_and_memLp_wkpNorm_of_finite_weak_partial_trees
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (A Y : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hA : ∀ n, n ≤ K → ∀ α, MemLp (A n α) ∞ (μ.prod (volume.restrict Ω)))
    (hY : ∀ n, n ≤ K → ∀ α, MemLp (Y n α) p (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ n, n < K → ∀ α, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A n α (t, x)) Ω)
    (hDA : ∀ n, n < K → ∀ α i,
      A (n + 1) (Fin.cons i α) =ᵐ[μ.prod (volume.restrict Ω)]
        fun q => fderiv ℝ (fun x => A n α (q.1, x)) q.2 (EuclideanSpace.single i 1))
    (hYweak : ∀ n, n < K → ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y n α (t, x)) Ω) :
    (∀ᵐ t ∂μ, MemWkp K p (fun x => A 0 (fun i => Fin.elim0 i) (t, x) *
      Y 0 (fun i => Fin.elim0 i) (t, x)) Ω) ∧
      MemLp (fun t => (iteratedWeakSobolevNorm K p
        (fun x => A 0 (fun i => Fin.elim0 i) (t, x) *
          Y 0 (fun i => Fin.elim0 i) (t, x)) Ω).toReal) p μ := by
  simpa only [Fintype.sum_unique] using
    ae_memWkp_and_memLp_wkpNorm_of_finite_sum_weak_partial_trees hp hpt hΩ K
      (fun q => A 0 (fun i => Fin.elim0 i) q * Y 0 (fun i => Fin.elim0 i) q)
      (fun _ : Unit => A) (fun _ : Unit => Y)
      (fun _ => hA) (fun _ => hY) (fun _ => hAsmooth) (fun _ => hDA) (fun _ => hYweak)
      (Filter.Eventually.of_forall fun _ => by simp only [Fintype.sum_unique])

theorem exists_lp_weak_partial_tree_of_finite_sum_of_contDiffOn
    {Z ι : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] [Fintype ι]
    {μ : Measure Z} {J : Set Z} (hJ : IsCompact J)
    {W Ω : Set E} (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩW : closure Ω ⊆ W)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : ℕ)
    (f : Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)))
    (A : ι → Z × E → ℝ)
    (hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (A j) (J ×ˢ W))
    (Y : ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hY : ∀ j n, n ≤ K → ∀ α, MemLp (Y j n α) p ((μ.restrict J).prod (volume.restrict Ω)))
    (hYweak : ∀ j n, n < K → ∀ α i, ∀ᵐ t ∂μ.restrict J,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y j n α (t, x)) Ω)
    (hf : f =ᵐ[(μ.restrict J).prod (volume.restrict Ω)] fun q => ∑ j,
      A j q * Y j 0 (fun i => Fin.elim0 i) q) :
    ∃ F : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)),
      F 0 (fun i => Fin.elim0 i) = f ∧
        ∀ n < K, ∀ α i, ∀ᵐ t ∂μ.restrict J,
          DeGiorgi.HasWeakPartialDeriv i
            (fun x => F (n + 1) (Fin.cons i α) (t, x))
            (fun x => F n α (t, x)) Ω := by
  let B := fun j n (α : Fin n → Fin d) (q : Z × E) =>
    iteratedFDeriv ℝ n (fun x => A j (q.1, x)) q.2 (fun i => EuclideanSpace.single (α i) 1)
  have hjet (j n) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : Z × E => iteratedFDeriv ℝ n (fun x => A j (q.1, x)) q.2) (J ×ˢ W) :=
    spatial_iteratedFDeriv_contDiffOn (𝕜 := ℝ) (G := fun t x => A j (t, x)) hW (hA j) n
  have hB (j n α) : ContDiffOn ℝ (⊤ : ℕ∞) (B j n α) (J ×ˢ W) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ
      (fun i => EuclideanSpace.single (α i) 1)).contDiff.comp_contDiffOn (hjet j n)
  have hmem : ∀ᵐ q ∂(μ.restrict J).prod (volume.restrict Ω), q ∈ J ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (hJ.measurableSet.prod hΩ.measurableSet)).mpr
    filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    exact (ae_restrict_mem hΩ.measurableSet).mono fun x hx => ⟨ht, hx⟩
  have hBmem (j n α) : MemLp (B j n α) ∞ ((μ.restrict J).prod (volume.restrict Ω)) := by
    have hb := ((hB j n α).continuousOn.mono (prod_mono Subset.rfl hΩW)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (μ.restrict J).prod (volume.restrict Ω))
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at hb
  have hBs (j n α) : ∀ᵐ t ∂μ.restrict J,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => B j n α (t, x)) Ω := by
    filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    exact (hB j n α).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun x hx => ⟨ht, hΩW (subset_closure hx)⟩)
  have hDB (j n α k) :
      B j (n + 1) (Fin.cons k α) =ᵐ[(μ.restrict J).prod (volume.restrict Ω)]
        fun q => fderiv ℝ (fun x => B j n α (q.1, x)) q.2 (EuclideanSpace.single k 1) := by
    filter_upwards [hmem] with q hq
    have hc : ContDiffOn ℝ (⊤ : ℕ∞)
        (iteratedFDeriv ℝ n (fun x => A j (q.1, x))) W :=
      (hjet j n).comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => ⟨hq.1, hx⟩)
    have hd := (hc.differentiableOn (by simp) q.2 (hΩW (subset_closure hq.2))).differentiableAt
      (hW.mem_nhds (hΩW (subset_closure hq.2)))
    simpa only [B, Fin.tail_def, Fin.cons_succ, Fin.cons_zero] using
      (hd.iteratedFDeriv_succ_apply_left'
        (m := fun i => EuclideanSpace.single (Fin.cons k α i) 1))
  apply exists_lp_weak_partial_tree_of_finite_sum hp hΩ K f B Y
    (fun j n _ α => hBmem j n α) hY (fun j n _ α => hBs j n α)
    (fun j n _ α k => hDB j n α k) hYweak
  simpa only [B, iteratedFDeriv_zero_apply] using hf

end DifferentialGeometry.Analysis.Sobolev.Euclidean
