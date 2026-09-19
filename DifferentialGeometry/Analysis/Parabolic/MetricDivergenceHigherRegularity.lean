import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceGradient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.FiniteWeakPartialSource

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private theorem exists_lp_weak_partial_tree_of_second_order_sum
    {d : ℕ} {μ : Measure ℝ} {J : Set ℝ} (hJ : IsCompact J)
    {W Ω : Set (EuclideanSpace ℝ (Fin d))} (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩW : closure Ω ⊆ W) (N : ℕ)
    (F P Q : ∀ m : ℕ, (Fin m → Fin d) → ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ m ≤ N, ∀ β, MemLp (F m β) 2 ((μ.restrict J).prod (volume.restrict Ω)))
    (hP : ∀ m ≤ N + 2, ∀ β, MemLp (P m β) 2 ((μ.restrict J).prod (volume.restrict Ω)))
    (hQ : ∀ m ≤ N, ∀ β, MemLp (Q m β) 2 ((μ.restrict J).prod (volume.restrict Ω)))
    (hFw : ∀ m < N, ∀ β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω)
    (hPw : ∀ m < N + 2, ∀ β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω)
    (hQw : ∀ m < N, ∀ β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => Q (m + 1) (Fin.cons i β) (t, z)) (fun z => Q m β (t, z)) Ω)
    (B D : Fin d → Fin d → ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (s r q : ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (hB : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (B i j) (J ×ˢ W))
    (hD : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (D i j) (J ×ˢ W))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) s (J ×ˢ W))
    (hr : ContDiffOn ℝ (⊤ : ℕ∞) r (J ×ˢ W))
    (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (J ×ˢ W))
    (C : Lp ℝ 2 ((μ.restrict J).prod (volume.restrict Ω)))
    (hC : C =ᵐ[(μ.restrict J).prod (volume.restrict Ω)] fun p =>
      s p * F 0 (fun i => Fin.elim0 i) p +
        (∑ i, ∑ j, (B i j p * P 2 (Fin.cons j (Fin.cons i (fun l => Fin.elim0 l))) p +
          D i j p * P 1 (Fin.cons i (fun l => Fin.elim0 l)) p)) -
        (r p * Q 0 (fun i => Fin.elim0 i) p + q p * P 0 (fun i => Fin.elim0 i) p)) :
    ∃ CF : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ 2 ((μ.restrict J).prod (volume.restrict Ω)),
      CF 0 (fun i => Fin.elim0 i) = C ∧
      ∀ m < N, ∀ β i, ∀ᵐ t ∂μ.restrict J, DeGiorgi.HasWeakPartialDeriv i
        (fun z => CF (m + 1) (Fin.cons i β) (t, z)) (fun z => CF m β (t, z)) Ω := by
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  let Idx := Unit ⊕ (Bool ⊕ ((Fin d × Fin d) ⊕ (Fin d × Fin d)))
  let A : Idx → ℝ × EuclideanSpace ℝ (Fin d) → ℝ :=
    Sum.elim (fun _ => s)
      (Sum.elim (fun b p => if b then -r p else -q p)
        (Sum.elim (fun ij => B ij.1 ij.2) (fun ij => D ij.1 ij.2)))
  let Y := fun (j : Idx) m (β : Fin m → Fin d) p =>
    Sum.elim (fun _ => F m β p)
      (Sum.elim (fun b => if b then Q m β p else P m β p)
        (Sum.elim (fun ij => P (m + 2) (Fin.snoc (Fin.snoc β ij.2) ij.1) p)
          (fun ij => P (m + 1) (Fin.snoc β ij.1) p))) j
  have hA (j : Idx) : ContDiffOn ℝ (⊤ : ℕ∞) (A j) (J ×ˢ W) := by
    rcases j with u | (b | (ij | ij))
    · exact hs
    · cases b
      · exact hq.neg
      · exact hr.neg
    · exact hB ij.1 ij.2
    · exact hD ij.1 ij.2
  have hY (j : Idx) (m) (hm : m ≤ N) (β) :
      MemLp (Y j m β) 2 ((μ.restrict J).prod (volume.restrict Ω)) := by
    rcases j with u | (b | (ij | ij))
    · exact hF m hm β
    · cases b
      · exact hP m (by omega) β
      · exact hQ m hm β
    · exact hP (m + 2) (by omega) (Fin.snoc (Fin.snoc β ij.2) ij.1)
    · exact hP (m + 1) (by omega) (Fin.snoc β ij.1)
  have hYw (j : Idx) (m) (hm : m < N) (β) (i) : ∀ᵐ t ∂μ.restrict J,
      DeGiorgi.HasWeakPartialDeriv i
        (fun z => Y j (m + 1) (Fin.cons i β) (t, z)) (fun z => Y j m β (t, z)) Ω := by
    rcases j with u | (b | (ij | ij))
    · exact hFw m hm β i
    · cases b
      · exact hPw m (by omega) β i
      · exact hQw m hm β i
    · simpa only [Y, Sum.elim_inr, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hPw (m + 2) (by omega) (Fin.snoc (Fin.snoc β ij.2) ij.1) i
    · simpa only [Y, Sum.elim_inr, Fin.cons_snoc_eq_snoc_cons] using
        hPw (m + 1) (by omega) (Fin.snoc β ij.1) i
  have hsum : C =ᵐ[(μ.restrict J).prod (volume.restrict Ω)] fun p => ∑ j : Idx, A j p * Y j 0 e p := by
    filter_upwards [hC] with p hp
    have hsnoc (i : Fin d) : (Fin.snoc e i : Fin 1 → Fin d) = (Fin.cons i e : Fin 1 → Fin d) := by
      ext j; fin_cases j; rfl
    have hsnoc₂ (i j : Fin d) : (Fin.snoc (Fin.cons j e) i : Fin 2 → Fin d) =
        (Fin.cons j (Fin.cons i e) : Fin 2 → Fin d) := by ext l; fin_cases l <;> rfl
    rw [hp]
    simp only [Idx, A, Y, Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl,
      Sum.elim_inr, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, Fintype.sum_prod_type,
      hsnoc, hsnoc₂]
    simp_rw [Finset.sum_add_distrib]
    ring
  exact exists_lp_weak_partial_tree_of_finite_sum_of_contDiffOn hJ hW hΩ hΩc hΩW
    (by norm_num) N C A hA Y hY hYw hsum

omit [T2Space M] [CompactSpace M] in
private theorem exists_weak_time_partial_tree_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (N : ℕ) :
    let μ := volume.restrict (Icc a b)
    let μ₀ := μ.restrict (Icc c d)
    let ν₀ := μ₀.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : ℝ × EuStd → ℝ,
      ∀ F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → ℝ × EuStd → ℝ,
      ∀ P : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
      (P 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] U) →
      (∀ m ≤ N, ∀ β, MemLp (F m β) 2 ν₀) →
      (∀ m < N, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω₀) →
      (∀ m < N + 2, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω₀) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
          (∑ i, ∑ j, ∫ p, A i j p * P 1 (Fin.cons i (fun l => Fin.elim0 l)) p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) -
              ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀) →
      ∃ Q : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
        (∀ m < N, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => Q (m + 1) (Fin.cons i β) (t, z)) (fun z => Q m β (t, z)) Ω₀) ∧
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, Q 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀ := by
  intro μ μ₀ ν₀ ρ A U F P hU₀ hFm hF hPweak hweak₀
  let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ μ.prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hU₀m : MemLp U 2 ν₀ := (Lp.memLp (P 0 e)).ae_eq hU₀
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  let O := D.regular ×ˢ W
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hO : IsOpen O := D.regular_isOpen.prod hW
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ O :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) O :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hdiff {B : ℝ × EuStd → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B O) (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ B p v) O :=
    (hB.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  let V₀ := fun i => P 1 (Fin.cons i e)
  let H₀ := fun i j => P 2 (Fin.cons j (Fin.cons i e))
  have hH₀ (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H₀ i j (t, z)) (fun z => V₀ i (t, z)) Ω₀ :=
    hPweak 1 (by omega) (Fin.cons i e) j
  have hbounded {B : ℝ × EuStd → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B O) :
      MemLp B ∞ ν₀ := by
    have hm := (hB.continuousOn.mono (prod_mono hreg hΩs)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm.mono_measure hmeasure
  have hρne (p : ℝ × EuStd) (hp : p ∈ O) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp.2))
  have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => (ρ p)⁻¹) O := hρ.inv hρne
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => (ρ p)⁻¹ * fderiv ℝ ρ p (1, 0)) O :=
    hinv.mul (hdiff hρ (1, 0))
  have hDA (i j) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)) O :=
    (weightedInvGramOnEuclid_family_fderiv_contDiffOn
      (G := G) hG Subset.rfl α hW Subset.rfl i j).clm_apply contDiffOn_const
  have hAs (i j) : ∀ᵐ t ∂μ₀, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A i j (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d)
      (ae_restrict_mem (μ := volume) measurableSet_Icc)] with t ht
    exact (hA i j).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hreg ht, hΩs (subset_closure (hsub hz))⟩)
  have hregion : Ioo c d ×ˢ Ω₀ ⊆ O :=
    prod_mono (fun t ht => hreg ⟨(hac.trans ht.1).le, (ht.2.trans hdb).le⟩)
      (hsub.trans (subset_closure.trans hΩs))
  obtain ⟨R₀, hR₀, hR₀weak⟩ := exists_lp_weak_deriv_of_weighted_divergence
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_Ioo hΩ₀ (1 : ℝ) hU₀m
    (hFm 0 (Nat.zero_le N) e) V₀ H₀
    (fun i j => hbounded (hA i j)) (fun i j => hbounded (hDA i j)) hAs hH₀
    (hρ.mono hregion) (fun p hp => hρne p (hregion hp)) (hbounded hinv) (hbounded hlog) hweak₀
  have hIc : Icc c d ⊆ D.regular := (Icc_subset_Icc hac.le hdb.le).trans hreg
  obtain ⟨Q, hQ, hQweak⟩ := exists_lp_weak_partial_tree_of_second_order_sum
    (μ := μ) isCompact_Icc hW hΩ₀ hΩ₀c (hΩ₀Ω.trans (subset_closure.trans hΩs)) N
    (fun m β p => F m β p) (fun m β p => P m β p) (fun m β p => P m β p)
    hFm
    (fun m _ β => Lp.memLp (P m β)) (fun m _ β => Lp.memLp (P m β))
    hF hPweak (fun m hm β i => hPweak m (by omega) β i)
    (fun i j p => (ρ p)⁻¹ * A i j p)
    (fun i j p => (ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1, z)) p.2
      (EuclideanSpace.single j 1))
    (fun p => (ρ p)⁻¹) (fun _ => 0) (fun p => (ρ p)⁻¹ * fderiv ℝ ρ p (1, 0))
    (fun i j => (hinv.mul (hA i j)).mono (prod_mono hIc Subset.rfl))
    (fun i j => (hinv.mul (hDA i j)).mono (prod_mono hIc Subset.rfl))
    (hinv.mono (prod_mono hIc Subset.rfl)) contDiffOn_const
    (hlog.mono (prod_mono hIc Subset.rfl)) R₀ (by
      filter_upwards [hR₀, hU₀] with p hp hu
      change P 0 e p = U p at hu
      rw [hp, hu]
      dsimp only [V₀, H₀, e]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, zero_mul, zero_add]
      ring)
  refine ⟨Q, hQweak, ?_⟩
  intro φ hφ hφc hφs
  rw [hQ]
  exact hR₀weak φ hφ hφc hφs
theorem exists_local_weak_partial_trees_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) (N : ℕ) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∀ F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ m < N, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∃ P Q : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
        (P 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] U) ∧
        (∀ m < N + 2, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω₀) ∧
        (∀ m < N, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => Q (m + 1) (Fin.cons i β) (t, z)) (fun z => Q m β (t, z)) Ω₀) ∧
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, Q 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀ := by
  induction N generalizing a b Ω Ω₀ c d with
  | zero =>
    intro μ ν ρ A U K F hK hF hweak μ₀ ν₀
    obtain ⟨H, hH, _, _⟩ := exists_local_second_weak_derivative_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb U (F 0 (fun i => Fin.elim0 i)) K hK hweak
    obtain ⟨R, hR⟩ := exists_local_weak_time_deriv_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb U (F 0 (fun i => Fin.elim0 i)) K hK hweak
    have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
    have hmeasure : ν₀ ≤ ν :=
      Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
    have hUm := (Lp.memLp U).mono_measure hmeasure
    have hKm (i) := (Lp.memLp (K i)).mono_measure hmeasure
    let U₀ := hUm.toLp U
    let K₀ := fun i => (hKm i).toLp (K i)
    have hU₀ : U₀ =ᵐ[ν₀] U := hUm.coeFn_toLp
    have hK₀ (i) : K₀ i =ᵐ[ν₀] K i := (hKm i).coeFn_toLp
    have hfirst (i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K₀ i (t, z)) (fun z => U₀ (t, z)) Ω₀ := by
      filter_upwards [ae_restrict_of_ae (s := Icc c d) (hK i),
        Measure.ae_ae_of_ae_prod hU₀, Measure.ae_ae_of_ae_prod (hK₀ i)] with t ht hu hk
      exact (ht.restrict hΩ₀ hsub).congr_ae (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hk)
    have hsecond (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H i j (t, z)) (fun z => K₀ i (t, z)) Ω₀ := by
      filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hK₀ i)] with t ht hk
      exact hasWeakPartialDeriv_congr_ae hΩ₀ j (Filter.EventuallyEq.symm hk) ht
    let P : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀
      | 0, _ => U₀
      | 1, β => K₀ (β 0)
      | 2, β => H (β 1) (β 0)
      | _ + 3, _ => 0
    refine ⟨P, fun _ _ => R, hU₀, ?_, ?_, hR⟩
    · intro m hm β i
      interval_cases m
      · simpa only [P, Fin.cons_zero] using hfirst i
      · simpa only [P, Fin.cons_zero, Fin.cons_one] using hsecond (β 0) i
    · intro m hm
      omega
  | succ N ih =>
    intro μ ν ρ A U K F hK hF hweak μ₀ ν₀
    have hΩ₀c : IsCompact (closure Ω₀) :=
      hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
    obtain ⟨Ω₁, hΩ₁, hΩ₀₁, hΩ₁Ω, hΩ₁c⟩ :=
      exists_open_between_and_isCompact_closure hΩ₀c hΩ hΩ₀Ω
    have hΩ₁s := hΩ₁Ω.trans (subset_closure.trans hΩs)
    let c₁ := (a + c) / 2
    let d₁ := (d + b) / 2
    have hac₁ : a < c₁ := by dsimp [c₁]; linarith
    have hc₁c : c₁ < c := by dsimp [c₁]; linarith
    have hdd₁ : d < d₁ := by dsimp [d₁]; linarith
    have hd₁b : d₁ < b := by dsimp [d₁]; linarith
    have hc₁d₁ : c₁ < d₁ := hc₁c.trans (hcd.trans hdd₁)
    have hI₁ : Icc c₁ d₁ ⊆ Icc a b := Icc_subset_Icc hac₁.le hd₁b.le
    let μ₁ := volume.restrict (Icc c₁ d₁)
    let ν₁ := μ₁.prod (volume.restrict Ω₁)
    have hμ₁ : μ.restrict (Icc c₁ d₁) = μ₁ := by
      change (volume.restrict (Icc a b)).restrict (Icc c₁ d₁) = volume.restrict (Icc c₁ d₁)
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hI₁]
    have hih := ih hab hreg hΩ hΩc hΩs hΩ₁ hΩ₁Ω hac₁ hd₁b hc₁d₁ U K F hK
      (fun m hm β i => hF m (by omega) β i) hweak
    dsimp only at hih
    rw [hμ₁] at hih
    obtain ⟨P₁, Q₁, hP₁, hP₁weak, hQ₁weak, hQ₁time⟩ := hih
    let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
    let DS := fun i => F 1 (Fin.cons i e)
    have hDS (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => DS i (t, z)) (fun z => F 0 e (t, z)) Ω := hF 0 (by omega) e i
    have hgrad := exists_local_weak_gradient_equation_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₁ hΩ₁Ω hac₁ hd₁b U (F 0 e) K hK hweak DS hDS
    dsimp only at hgrad
    rw [hμ₁] at hgrad
    obtain ⟨R, H, C, hR, hH, hHsym, hC, hCweak⟩ := hgrad
    have hμ₁le : μ₁ ≤ μ := by rw [← hμ₁]; exact Measure.restrict_le_self
    have hsub₁ : Ω₁ ⊆ Ω := subset_closure.trans hΩ₁Ω
    have hν₁le : ν₁ ≤ ν := Measure.prod_mono hμ₁le (Measure.restrict_mono hsub₁ le_rfl)
    have hKalign (i) : P₁ 1 (Fin.cons i e) =ᵐ[ν₁] K i := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_eq_fun (Lp.stronglyMeasurable (P₁ 1 (Fin.cons i e))).measurable
          (Lp.stronglyMeasurable (K i)).measurable)).mpr
      filter_upwards [hP₁weak 0 (by omega) e i, Measure.ae_ae_of_ae_prod hP₁,
        (hK i).filter_mono (ae_mono hμ₁le),
        (Lp.memLp (P₁ 1 (Fin.cons i e))).prodMk_left (by norm_num),
        ((Lp.memLp (K i)).mono_measure hν₁le).prodMk_left (by norm_num)] with t ht hu hk hm hkLp
      exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₁
        (hasWeakPartialDeriv_congr_ae hΩ₁ i hu ht) (hk.restrict hΩ₁ hsub₁)
        (hm.locallyIntegrable (by norm_num)) (hkLp.locallyIntegrable (by norm_num))
    have hHalign (i j) : P₁ 2 (Fin.cons j (Fin.cons i e)) = H i j := by
      apply Lp.ext_curry
      filter_upwards [hP₁weak 1 (by omega) (Fin.cons i e) j,
        Measure.ae_ae_of_ae_prod (hKalign i), hH i j,
        (Lp.memLp (P₁ 2 (Fin.cons j (Fin.cons i e)))).prodMk_left (by norm_num),
        (Lp.memLp (H i j)).prodMk_left (by norm_num)] with t ht hk hh hm hhm
      exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₁
        (hasWeakPartialDeriv_congr_ae hΩ₁ j hk ht) hh
        (hm.locallyIntegrable (by norm_num)) (hhm.locallyIntegrable (by norm_num))
    have hmem : ∀ᵐ p ∂ν₁, p ∈ Ioo c₁ d₁ ×ˢ Ω₁ := by
      have htime : μ₁ = volume.restrict (Ioo c₁ d₁) :=
        Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
      change ∀ᵐ p ∂μ₁.prod (volume.restrict Ω₁), p ∈ Ioo c₁ d₁ ×ˢ Ω₁
      rw [htime]
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod hΩ₁.measurableSet)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (ae_restrict_mem hΩ₁.measurableSet).mono fun z hz => ⟨ht, hz⟩
    have hQalign : Q₁ 0 e = R := Sobolev.lp_eq_of_weak_deriv_integral
      (isOpen_Ioo.prod hΩ₁) hmem (by norm_num) (1, 0) hQ₁time hR
    let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
    let O := D.regular ×ˢ W
    have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
    have hO : IsOpen O := D.regular_isOpen.prod hW
    let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
      { metric := g
        connection := fun t => leviCivitaConnectionOfMetric (g t)
        metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
    have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ O :=
      (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
        (prod_mono Subset.rfl (image_mono interior_subset))
    have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) O :=
      weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
    have hdiff {B : ℝ × EuStd → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B O) (v : ℝ × EuStd) :
        ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ B p v) O :=
      (hB.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have hFinner (m) (hm : m < N + 1) (β i) : ∀ᵐ t ∂μ₁, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω₁ := by
      filter_upwards [(hF m hm β i).filter_mono (ae_mono hμ₁le)] with t ht
      exact ht.restrict hΩ₁ hsub₁
    have hCf (k) : C k =ᵐ[ν₁] fun p => F 1 (Fin.cons k e) p +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) *
          P₁ 2 (Fin.cons j (Fin.cons i e)) p +
          fderiv ℝ (fun y => fderiv ℝ (A i j) y (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * P₁ 1 (Fin.cons i e) p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * Q₁ 0 e p +
          fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0) * P₁ 0 e p) := by
      filter_upwards [hC k, hP₁, ae_all_iff.mpr hKalign] with p hc hu hk
      change P₁ 0 e p = U p at hu
      rw [hc]
      simp only [← hHalign, ← hQalign, ← hk, ← hu]
      rfl
    have hCtree (k) := exists_lp_weak_partial_tree_of_second_order_sum
      (μ := volume) isCompact_Icc hW hΩ₁ hΩ₁c hΩ₁s N
      (fun m β p => F (m + 1) (Fin.snoc β k) p) (fun m β p => P₁ m β p) (fun m β p => Q₁ m β p)
      (fun m _ β => (Lp.memLp (F (m + 1) (Fin.snoc β k))).mono_measure hν₁le)
      (fun m _ β => Lp.memLp (P₁ m β)) (fun m _ β => Lp.memLp (Q₁ m β))
      (fun m hm β i => by
        simpa only [Fin.cons_snoc_eq_snoc_cons] using
          hFinner (m + 1) (by omega) (Fin.snoc β k) i) hP₁weak hQ₁weak
      (fun i j p => fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1))
      (fun i j p => fderiv ℝ (fun y => fderiv ℝ (A i j) y (0, EuclideanSpace.single k 1))
        p (0, EuclideanSpace.single j 1))
      (fun _ => 1) (fun p => fderiv ℝ ρ p (0, EuclideanSpace.single k 1))
      (fun p => fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0))
      (fun i j => (hdiff (hA i j) _).mono (prod_mono (hI₁.trans hreg) Subset.rfl))
      (fun i j => (hdiff (hdiff (hA i j) _) _).mono (prod_mono (hI₁.trans hreg) Subset.rfl))
      contDiffOn_const ((hdiff hρ _).mono (prod_mono (hI₁.trans hreg) Subset.rfl))
      ((hdiff (hdiff hρ _) _).mono (prod_mono (hI₁.trans hreg) Subset.rfl)) (C k) (by
        have he : (Fin.snoc e k : Fin 1 → Fin (Module.finrank ℝ EuN)) =
            (Fin.cons k e : Fin 1 → Fin (Module.finrank ℝ EuN)) := by
          ext j; fin_cases j; rfl
        simp only [e] at he
        simpa only [one_mul, he] using hCf k)
    choose CF hCF hCFweak using hCtree
    have hHK (k i) : ∀ᵐ t ∂μ₁, DeGiorgi.HasWeakPartialDeriv i
        (fun z => H k i (t, z)) (fun z => P₁ 1 (Fin.cons k e) (t, z)) Ω₁ := by
      filter_upwards [hH k i, Measure.ae_ae_of_ae_prod (hKalign k)] with t ht hk
      exact hasWeakPartialDeriv_congr_ae hΩ₁ i (Filter.EventuallyEq.symm hk) ht
    have hbaseP (k) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
        (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c₁ d₁ ×ˢ Ω₁) :
        (∫ p, ρ p * P₁ 1 (Fin.cons k e) p * fderiv ℝ φ p (1, 0) ∂ν₁) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₁) -
            ∫ p, CF k 0 e p * φ p ∂ν₁ := by
      rw [hCF k]
      refine (integral_congr_ae ?_).trans (hCweak k φ hφ hφc hφs)
      filter_upwards [hKalign k] with p hp
      rw [hp]
    have hμ₀ : μ₀ = volume.restrict (Icc c d) := by
      change (volume.restrict (Icc a b)).restrict (Icc c d) = volume.restrict (Icc c d)
      rw [Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (Icc_subset_Icc hac.le hdb.le)]
    have hμ₁₀ : μ₁.restrict (Icc c d) = μ₀ := by
      rw [hμ₀]
      change (volume.restrict (Icc c₁ d₁)).restrict (Icc c d) = volume.restrict (Icc c d)
      rw [Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (Icc_subset_Icc hc₁c.le hdd₁.le)]
    have hchild (k) := ih hc₁d₁ (hI₁.trans hreg) hΩ₁ hΩ₁c hΩ₁s hΩ₀ hΩ₀₁
      hc₁c hdd₁ hcd (P₁ 1 (Fin.cons k e)) (H k) (CF k) (hHK k) (hCFweak k) (hbaseP k)
    dsimp only at hchild
    rw [hμ₁₀] at hchild
    choose PC QC hPC hPCweak hQCweak hQCtime using hchild
    have hμ₀le : μ₀ ≤ μ₁ := by rw [← hμ₁₀]; exact Measure.restrict_le_self
    have hsub₀₁ : Ω₀ ⊆ Ω₁ := subset_closure.trans hΩ₀₁
    have hν₀le : ν₀ ≤ ν₁ := Measure.prod_mono hμ₀le (Measure.restrict_mono hsub₀₁ le_rfl)
    have hU₀m := (Lp.memLp U).mono_measure (hν₀le.trans hν₁le)
    let U₀ := hU₀m.toLp U
    have hU₀ : U₀ =ᵐ[ν₀] U := hU₀m.coeFn_toLp
    have hPCfirst (i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
        (fun z => PC i 0 e (t, z)) (fun z => U₀ (t, z)) Ω₀ := by
      have hi : PC i 0 e =ᵐ[ν₀] K i :=
        (hPC i).trans ((hKalign i).filter_mono (ae_mono hν₀le))
      filter_upwards [ae_restrict_of_ae (s := Icc c d) (hK i),
        Measure.ae_ae_of_ae_prod hU₀, Measure.ae_ae_of_ae_prod hi] with t ht hu hi
      exact (ht.restrict hΩ₀ (hsub₀₁.trans hsub₁)).congr_ae
        (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hi)
    let P : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀ :=
      fun m => match m with
      | 0 => fun _ => U₀
      | m + 1 => fun β => PC (β (Fin.last m)) m (Fin.init β)
    have hPweak : ∀ m < N + 1 + 2, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω₀ := by
      intro m hm β i
      cases m with
      | zero =>
        have hβ : β = e := Subsingleton.elim _ _
        subst β
        have he : Fin.init (Fin.cons i e : Fin 1 → Fin (Module.finrank ℝ EuN)) = e :=
          Subsingleton.elim _ _
        simpa only [P, Fin.cons_zero, Fin.last_zero, he] using hPCfirst i
      | succ m =>
        obtain ⟨γ, j, rfl⟩ : ∃ (γ : Fin m → Fin (Module.finrank ℝ EuN)) (j : Fin (Module.finrank ℝ EuN)), β = Fin.snoc γ j :=
          ⟨Fin.init β, β (Fin.last m), (Fin.snoc_init_self β).symm⟩
        simpa only [P, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_last, Fin.init_snoc] using
          hPCweak j m (by omega) γ i
    let V₀ := fun i => P 1 (Fin.cons i e)
    have hV₀ (i) : V₀ i =ᵐ[ν₀] K i := by
      have he : Fin.init (Fin.cons i e : Fin 1 → Fin (Module.finrank ℝ EuN)) = e :=
        Subsingleton.elim _ _
      simpa only [V₀, P, Fin.cons_zero, Fin.last_zero, he] using
        (hPC i).trans ((hKalign i).filter_mono (ae_mono hν₀le))
    have hweak₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
        (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
          (∑ i, ∑ j, ∫ p, A i j p * V₀ i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) -
            ∫ p, F 0 e p * φ p ∂ν₀ := by
      have hw := hweak φ hφ hφc
        (hφs.trans (prod_mono (fun t ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩) (hsub₀₁.trans hsub₁)))
      have hφsupport : tsupport φ ⊆ Icc c d ×ˢ Ω₀ :=
        hφs.trans (prod_mono Ioo_subset_Icc_self Subset.rfl)
      have hres (v : ℝ × EuStd) (B : ℝ × EuStd → ℝ) :
          (∫ p, B p * fderiv ℝ φ p v ∂ν) = ∫ p, B p * fderiv ℝ φ p v ∂ν₀ := by
        apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet (hsub₀₁.trans hsub₁)
        intro p hp
        rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p v)
          (fun hs => hp (hφsupport (tsupport_fderiv_apply_subset ℝ v hs))), mul_zero]
      have hresφ : (∫ p, F 0 e p * φ p ∂ν) = ∫ p, F 0 e p * φ p ∂ν₀ := by
        apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet (hsub₀₁.trans hsub₁)
        intro p hp
        rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφsupport hs)), mul_zero]
      change (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, F 0 e p * φ p ∂ν at hw
      simp_rw [hres, hresφ] at hw
      refine hw.trans ?_
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [hV₀ i] with p hp
      rw [hp]
    have hF₀ (m) (hm : m < N + 1) (β i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω₀ := by
      filter_upwards [ae_restrict_of_ae (s := Icc c d) (hF m hm β i)] with t ht
      exact ht.restrict hΩ₀ (hsub₀₁.trans hsub₁)
    obtain ⟨Q, hQweak, hQtime⟩ := exists_weak_time_partial_tree_of_metric_divergence_equation
      hG hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb (N + 1) U (fun m β p => F m β p) P hU₀
      (fun m _ β => (Lp.memLp (F m β)).mono_measure (hν₀le.trans hν₁le)) hF₀ hPweak hweak₀
    exact ⟨P, Q, hU₀, hPweak, hQweak, hQtime⟩

theorem exists_local_weak_time_deriv_and_memWkp_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) (N : ℕ) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∀ F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ m < N, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∃ R : Lp ℝ 2 ν₀,
        (∀ᵐ t ∂μ₀, MemWkp (N + 2) 2 (fun z => U (t, z)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm (N + 2) 2
          (fun z => U (t, z)) Ω₀).toReal) 2 μ₀ ∧
        (∀ᵐ t ∂μ₀, MemWkp N 2 (fun z => R (t, z)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm N 2
          (fun z => R (t, z)) Ω₀).toReal) 2 μ₀ ∧
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, R p * φ p ∂ν₀ := by
  intro μ ν ρ A U K F hK hF hweak μ₀ ν₀
  obtain ⟨P, Q, hP, hPweak, hQweak, hQtime⟩ :=
    exists_local_weak_partial_trees_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd N U K F hK hF hweak
  obtain ⟨hmemP, hnormP⟩ := ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ₀ (N + 2)
    (fun m β p => P m β p) (fun m _ β => Lp.memLp (P m β)) hPweak
  obtain ⟨hmemQ, hnormQ⟩ := ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ₀ N
    (fun m β p => Q m β p) (fun m _ β => Lp.memLp (Q m β)) hQweak
  refine ⟨Q 0 (fun i => Fin.elim0 i), ?_, ?_, hmemQ, hnormQ, hQtime⟩
  · filter_upwards [hmemP, Measure.ae_ae_of_ae_prod hP] with t ht he
    exact (MemWkp_congr_ae (by norm_num) hΩ₀ he).mp ht
  · apply hnormP.ae_eq
    filter_upwards [Measure.ae_ae_of_ae_prod hP] with t he
    exact congrArg ENNReal.toReal (wkpNorm_congr_ae (by norm_num) hΩ₀ he)

end DifferentialGeometry.Analysis.Parabolic
