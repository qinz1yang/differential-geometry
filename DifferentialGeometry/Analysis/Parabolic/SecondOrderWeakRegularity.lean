import DifferentialGeometry.Analysis.Sobolev.Euclidean.FiniteWeakPartialSource
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeightedDivergence

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_mixed_weak_partial_trees_of_second_order_evolution
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    {μ : Measure Z} [IsLocallyFiniteMeasure μ]
    {J V : Set Z} (hJ : IsCompact J) (hV : IsOpen V) (hJV : J ⊆ V)
    {W Ω : Set E} (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩW : closure Ω ⊆ W)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (v : Z)
    (U : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)))
    (F : ℕ → ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)))
    (hU : ∀ m β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => U (m + 1) (Fin.cons i β) (t, z)) (fun z => U m β (t, z)) Ω)
    (hF : ∀ k m β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => F k (m + 1) (Fin.cons i β) (t, z)) (fun z => F k m β (t, z)) Ω)
    (hFt : ∀ k (φ : Z × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ interior J ×ˢ Ω →
      (∫ q, F k 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (v, 0)
        ∂(μ.restrict J).prod (volume.restrict Ω)) =
        -∫ q, F (k + 1) 0 (fun i => Fin.elim0 i) q * φ q ∂(μ.restrict J).prod (volume.restrict Ω))
    (B : Fin d → Fin d → Z × E → ℝ) (C : Fin d → Z × E → ℝ) (s q : Z × E → ℝ)
    (hB : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (B i j) (V ×ˢ W))
    (hC : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C i) (V ×ˢ W))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) s (V ×ˢ W))
    (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (V ×ˢ W))
    (hweak : ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ interior J ×ˢ Ω →
      (∫ x, U 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (v, 0)
        ∂(μ.restrict J).prod (volume.restrict Ω)) =
        -∫ x, ((∑ i, ∑ j, B i j x * U 2 (Fin.cons j (Fin.cons i (fun l => Fin.elim0 l))) x) +
          (∑ i, C i x * U 1 (Fin.cons i (fun l => Fin.elim0 l)) x) +
          q x * U 0 (fun i => Fin.elim0 i) x + s x * F 0 0 (fun i => Fin.elim0 i) x) * φ x
          ∂(μ.restrict J).prod (volume.restrict Ω)) :
    ∀ K N : ℕ, ∃ P : ℕ → ∀ m : ℕ, (Fin m → Fin d) →
        Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)),
      P 0 0 (fun i => Fin.elim0 i) = U 0 (fun i => Fin.elim0 i) ∧
      (∀ k ≤ K, ∀ m < N, ∀ β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω) ∧
      ∀ k < K, ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ interior J ×ˢ Ω →
        (∫ x, P k 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (v, 0)
          ∂(μ.restrict J).prod (volume.restrict Ω)) =
          -∫ x, P (k + 1) 0 (fun i => Fin.elim0 i) x * φ x
            ∂(μ.restrict J).prod (volume.restrict Ω) := by
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  have hmem : ∀ᵐ x ∂(μ.restrict J).prod (volume.restrict Ω), x ∈ J ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (hJ.measurableSet.prod hΩ.measurableSet)).mpr
    filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    exact (ae_restrict_mem hΩ.measurableSet).mono fun z hz => ⟨ht, hz⟩
  have hbounded {A : Z × E → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A (V ×ˢ W)) :
      MemLp A ∞ ((μ.restrict J).prod (volume.restrict Ω)) := by
    have h := (hA.continuousOn.mono (prod_mono hJV hΩW)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (μ.restrict J).prod (volume.restrict Ω))
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h
  let r := fun x => (∑ i, ∑ j, B i j x * U 2 (Fin.cons j (Fin.cons i e)) x) +
    (∑ i, C i x * U 1 (Fin.cons i e) x) + q x * U 0 e x + s x * F 0 0 e x
  have hr : MemLp r p ((μ.restrict J).prod (volume.restrict Ω)) :=
    ((memLp_finsetSum Finset.univ fun i _ => memLp_finsetSum Finset.univ fun j _ =>
      (Lp.memLp (U 2 (Fin.cons j (Fin.cons i e)))).mul (hbounded (hB i j))).add
      (memLp_finsetSum Finset.univ fun i _ =>
        (Lp.memLp (U 1 (Fin.cons i e))).mul (hbounded (hC i)))).add
          ((Lp.memLp (U 0 e)).mul (hbounded hq)) |>.add
            ((Lp.memLp (F 0 0 e)).mul (hbounded hs))
  let R := hr.toLp r
  have hR : R =ᵐ[(μ.restrict J).prod (volume.restrict Ω)] r := hr.coeFn_toLp
  have hRtime (φ : Z × E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ interior J ×ˢ Ω) :
      (∫ x, U 0 e x * fderiv ℝ φ x (v, 0) ∂(μ.restrict J).prod (volume.restrict Ω)) =
        -∫ x, R x * φ x ∂(μ.restrict J).prod (volume.restrict Ω) := by
    refine (hweak φ hφ hφc hφs).trans ?_
    congr 1
    apply integral_congr_ae
    filter_upwards [hR] with x hx
    rw [hx]
  intro K
  induction K with
  | zero =>
    intro N
    exact ⟨fun _ => U, rfl, fun _ _ m _ β i => hU m β i, fun k hk => by omega⟩
  | succ K ih =>
    intro N
    obtain ⟨P, hP, hPw, hPt⟩ := ih (N + 2)
    have hPalign := eq_of_finite_weak_partial_trees hp hΩ (N + 2) (P 0) U
      (hPw 0 (by omega)) (fun m _ β i => hU m β i) hP
    have hPtime (k) (hk : k < K) := integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
      (N + 2) v (fun m β x => P k m β x) (fun m β x => P (k + 1) m β x)
      (fun m _ β => (Lp.memLp (P k m β)).locallyIntegrable hp)
      (fun m _ β => (Lp.memLp (P (k + 1) m β)).locallyIntegrable hp)
      (hPw k (by omega)) (hPw (k + 1) (by omega)) (hPt k hk)
    let Idx := (Fin d × Fin d) ⊕ (Fin d ⊕ Bool)
    let A : Idx → Z × E → ℝ :=
      Sum.elim (fun ij => B ij.1 ij.2) (Sum.elim C (fun b => if b then s else q))
    let Y : Idx → ℕ → ∀ m : ℕ, (Fin m → Fin d) →
        Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)) :=
      Sum.elim (fun ij k m β => P k (m + 2) (Fin.snoc (Fin.snoc β ij.2) ij.1))
        (Sum.elim (fun i k m β => P k (m + 1) (Fin.snoc β i))
          (fun b k m β => if b then F k m β else P k m β))
    have hA (i) : ContDiffOn ℝ (⊤ : ℕ∞) (A i) (V ×ˢ W) := by
      rcases i with ij | (i | b)
      · exact hB ij.1 ij.2
      · exact hC i
      · cases b
        · exact hq
        · exact hs
    have hY (j : Idx) (k) (hk : k ≤ K) (m) (hm : m < N) (β i) : ∀ᵐ t ∂μ.restrict J,
        DeGiorgi.HasWeakPartialDeriv i
          (fun z => Y j k (m + 1) (Fin.cons i β) (t, z)) (fun z => Y j k m β (t, z)) Ω := by
      rcases j with ij | (j | b)
      · simpa only [Y, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
          hPw k hk (m + 2) (by omega) (Fin.snoc (Fin.snoc β ij.2) ij.1) i
      · simpa only [Y, Sum.elim_inr, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
          hPw k hk (m + 1) (by omega) (Fin.snoc β j) i
      · cases b
        · exact hPw k hk m (by omega) β i
        · exact hF k m β i
    have hsnoc (i : Fin d) : (Fin.snoc e i : Fin 1 → Fin d) = Fin.cons i e := by
      ext j; fin_cases j; rfl
    have hsnoc₂ (i j : Fin d) : (Fin.snoc (Fin.cons j e) i : Fin 2 → Fin d) =
        Fin.cons j (Fin.cons i e) := by ext l; fin_cases l <;> rfl
    have hYt (j : Idx) (k) (hk : k < K) (φ : Z × E → ℝ)
        (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
        (hφs : tsupport φ ⊆ interior J ×ˢ Ω) :
        (∫ x, Y j k 0 e x * fderiv ℝ φ x (v, 0) ∂(μ.restrict J).prod (volume.restrict Ω)) =
          -∫ x, Y j (k + 1) 0 e x * φ x ∂(μ.restrict J).prod (volume.restrict Ω) := by
      rcases j with ij | (j | b)
      · simpa only [Y, Sum.elim_inl, hsnoc, hsnoc₂] using
          hPtime k hk 2 (by omega) (Fin.cons ij.2 (Fin.cons ij.1 e)) φ hφ hφc hφs
      · simpa only [Y, Sum.elim_inr, Sum.elim_inl, hsnoc] using
          hPtime k hk 1 (by omega) (Fin.cons j e) φ hφ hφc hφs
      · cases b
        · exact hPt k hk φ hφ hφc hφs
        · exact hFt k φ hφ hφc hφs
    have hsum : R =ᵐ[(μ.restrict J).prod (volume.restrict Ω)] fun x =>
        ∑ j : Idx, A j x * Y j 0 0 e x := by
      filter_upwards [hR] with x hx
      rw [hx]
      simp only [Idx, A, Y, Fintype.sum_sum_type, Fintype.sum_bool, Bool.false_eq_true,
        ↓reduceIte, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, hsnoc, hsnoc₂,
        hPalign 2 (by omega), hPalign 1 (by omega), hPalign 0 (by omega)]
      dsimp only [r]
      ring
    obtain ⟨T, hT, hTw, hTt⟩ := exists_lp_mixed_weak_partial_trees_of_finite_sum
      hJ hV hJV hW hΩ hΩc hΩW hp K N v R A hA Y hY hYt hsum
    let Q : ℕ → ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω))
      | 0 => P 0
      | k + 1 => T k
    refine ⟨Q, hP, ?_, ?_⟩
    · intro k hk m hm β i
      cases k with
      | zero => exact hPw 0 (by omega) m (by omega) β i
      | succ k => exact hTw k (by omega) m hm β i
    · intro k hk φ hφ hφc hφs
      cases k with
      | zero =>
        change (∫ x, P 0 0 e x * fderiv ℝ φ x (v, 0) ∂(μ.restrict J).prod (volume.restrict Ω)) =
          -∫ x, T 0 0 e x * φ x ∂(μ.restrict J).prod (volume.restrict Ω)
        rw [hP, hT]
        exact hRtime φ hφ hφc hφs
      | succ k => exact hTt k (by omega) φ hφ hφc hφs

theorem exists_lp_mixed_weak_partial_trees_of_weighted_divergence
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    {μ : Measure Z} [IsLocallyFiniteMeasure μ]
    {J V : Set Z} (hJ : IsCompact J) (hV : IsOpen V) (hJV : J ⊆ V)
    {W Ω : Set E} (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩW : closure Ω ⊆ W)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (v : Z)
    (U : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)))
    (F : ℕ → ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)))
    (hU : ∀ m β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => U (m + 1) (Fin.cons i β) (t, z)) (fun z => U m β (t, z)) Ω)
    (hF : ∀ k m β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => F k (m + 1) (Fin.cons i β) (t, z)) (fun z => F k m β (t, z)) Ω)
    (hFt : ∀ k (φ : Z × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ interior J ×ˢ Ω →
      (∫ q, F k 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (v, 0)
        ∂(μ.restrict J).prod (volume.restrict Ω)) =
        -∫ q, F (k + 1) 0 (fun i => Fin.elim0 i) q * φ q ∂(μ.restrict J).prod (volume.restrict Ω))
    (ρ : Z × E → ℝ) (A : Fin d → Fin d → Z × E → ℝ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (V ×ˢ W)) (hρne : ∀ x ∈ V ×ˢ W, ρ x ≠ 0)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (V ×ˢ W))
    (hweak : ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ interior J ×ˢ Ω →
      (∫ x, ρ x * U 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (v, 0)
        ∂(μ.restrict J).prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ x, A i j x * U 1 (Fin.cons i (fun l => Fin.elim0 l)) x *
          fderiv ℝ φ x (0, EuclideanSpace.single j 1) ∂(μ.restrict J).prod (volume.restrict Ω)) -
            ∫ x, F 0 0 (fun i => Fin.elim0 i) x * φ x ∂(μ.restrict J).prod (volume.restrict Ω)) :
    ∀ K N : ℕ, ∃ P : ℕ → ∀ m : ℕ, (Fin m → Fin d) →
        Lp ℝ p ((μ.restrict J).prod (volume.restrict Ω)),
      P 0 0 (fun i => Fin.elim0 i) = U 0 (fun i => Fin.elim0 i) ∧
      (∀ k ≤ K, ∀ m < N, ∀ β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω) ∧
      ∀ k < K, ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ interior J ×ˢ Ω →
        (∫ x, P k 0 (fun i => Fin.elim0 i) x * fderiv ℝ φ x (v, 0)
          ∂(μ.restrict J).prod (volume.restrict Ω)) =
          -∫ x, P (k + 1) 0 (fun i => Fin.elim0 i) x * φ x
            ∂(μ.restrict J).prod (volume.restrict Ω) := by
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  have hmem : ∀ᵐ x ∂(μ.restrict J).prod (volume.restrict Ω), x ∈ J ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (hJ.measurableSet.prod hΩ.measurableSet)).mpr
    filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    exact (ae_restrict_mem hΩ.measurableSet).mono fun z hz => ⟨ht, hz⟩
  have hbounded {B : Z × E → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (V ×ˢ W)) :
      MemLp B ∞ ((μ.restrict J).prod (volume.restrict Ω)) := by
    have h := (hB.continuousOn.mono (prod_mono hJV hΩW)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (μ.restrict J).prod (volume.restrict Ω))
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h
  have hDA (i j) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun z => A i j (x.1, z)) x.2 (EuclideanSpace.single j 1)) (V ×ˢ W) :=
    ((hA i j).fderiv_snd (G := fun t z => A i j (t, z)) hW (by simp)).clm_apply contDiffOn_const
  have hinv := hρ.inv hρne
  have hlog := hinv.mul ((hρ.fderiv_of_isOpen (hV.prod hW) (by simp)).clm_apply
    (contDiffOn_const (c := (v, (0 : E)))))
  have hAs (i j) : ∀ᵐ t ∂μ.restrict J, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A i j (t, z)) Ω := by
    filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    exact (hA i j).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hJV ht, hΩW (subset_closure hz)⟩)
  have hregion : interior J ×ˢ Ω ⊆ V ×ˢ W :=
    prod_mono (interior_subset.trans hJV) (subset_closure.trans hΩW)
  obtain ⟨R, hR, hRt⟩ := exists_lp_weak_deriv_of_weighted_divergence hp isOpen_interior hΩ v
    (Lp.memLp (U 0 e)) (Lp.memLp (F 0 0 e))
    (fun i => U 1 (Fin.cons i e)) (fun i j => U 2 (Fin.cons j (Fin.cons i e)))
    (fun i j => hbounded (hA i j)) (fun i j => hbounded (hDA i j)) hAs
    (fun i j => hU 1 (Fin.cons i e) j) (hρ.mono hregion)
    (fun x hx => hρne x (hregion hx)) (hbounded hinv) (hbounded hlog) hweak
  apply exists_lp_mixed_weak_partial_trees_of_second_order_evolution hJ hV hJV hW hΩ hΩc hΩW hp v
    U F hU hF hFt
    (fun i j x => (ρ x)⁻¹ * A i j x)
    (fun i x => ∑ j, (ρ x)⁻¹ * fderiv ℝ (fun z => A i j (x.1, z)) x.2 (EuclideanSpace.single j 1))
    (fun x => (ρ x)⁻¹) (fun x => -((ρ x)⁻¹ * fderiv ℝ ρ x (v, 0)))
    (fun i j => hinv.mul (hA i j))
    (fun i => ContDiffOn.sum fun j _ => hinv.mul (hDA i j)) hinv hlog.neg
  intro φ hφ hφc hφs
  refine (hRt φ hφ hφc hφs).trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [hR] with x hx
  rw [hx]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add, mul_assoc]
  ring

end DifferentialGeometry.Analysis.Parabolic
