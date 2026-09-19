import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceHigherRegularity
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeFiniteSum
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

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

theorem exists_local_second_weak_time_derivative_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∀ F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ m < 2, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∀ Ft : Lp ℝ 2 ν₀,
        (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, F 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, Ft p * φ p ∂ν₀) →
        ∃ R Rt : Lp ℝ 2 ν₀,
          (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, R p * φ p ∂ν₀) ∧
          ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, R p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, Rt p * φ p ∂ν₀ := by
  intro μ ν ρ A U K F hK hF hweak μ₀ ν₀ Ft hFt
  obtain ⟨P, Q, hP, hPweak, hQweak, hQtime⟩ :=
    exists_local_weak_partial_trees_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd 2 U K F hK hF hweak
  let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
  let S := F 0 e
  let V := fun i => P 1 (Fin.cons i e)
  let H := fun i j => P 2 (Fin.cons j (Fin.cons i e))
  let R := Q 0 e
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : V i =ᵐ[ν₀] K i := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (V i)).measurable
        (Lp.stronglyMeasurable (K i)).measurable)).mpr
    filter_upwards [hPweak 0 (by omega) e i, Measure.ae_ae_of_ae_prod hP,
      ae_restrict_of_ae (s := Icc c d) (hK i),
      (Lp.memLp (V i)).prodMk_left (by norm_num),
      ((Lp.memLp (K i)).mono_measure hmeasure).prodMk_left (by norm_num)] with t ht hu hk hm hkLp
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (hasWeakPartialDeriv_congr_ae hΩ₀ i hu ht) (hk.restrict hΩ₀ hsub)
      (hm.locallyIntegrable (by norm_num)) (hkLp.locallyIntegrable (by norm_num))
  have hHV (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => V i (t, z)) Ω₀ :=
    hPweak 1 (by omega) (Fin.cons i e) j
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩW : closure Ω ⊆ W := hΩs
  have hbounded (C : ℝ × EuStd → ℝ) (hC : ContinuousOn C (D.regular ×ˢ W)) :
      MemLp C ∞ ν₀ := by
    have hm := (hC.mono (prod_mono hreg hΩW)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm.mono_measure hmeasure
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ W) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ W) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp.2))
  have hρinv := hbounded (fun p => (ρ p)⁻¹) (hρ.continuousOn.inv₀ hρne)
  have hDρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ ρ p (1, 0))
      (D.regular ×ˢ W) :=
    (hρ.fderiv_of_isOpen (D.regular_isOpen.prod hW) (by simp)).clm_apply contDiffOn_const
  have hDρ := hbounded _ hDρsmooth.continuousOn
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ W) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hAb (i j) := hbounded (A i j) (hA i j).continuousOn
  have hDAb (i j) : MemLp
      (fun p => fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)) ∞ ν₀ :=
    hbounded _ (((weightedInvGramOnEuclid_family_fderiv_contDiffOn
      (G := G) hG Subset.rfl α hW Subset.rfl i j).clm_apply contDiffOn_const).continuousOn)
  have hAs (i j) : ∀ᵐ t ∂μ₀, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A i j (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d)
      (ae_restrict_mem (μ := volume) measurableSet_Icc)] with t ht
    exact (hA i j).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hreg ht, hΩW (subset_closure (hsub hz))⟩)
  have hregion : Ioo c d ×ˢ Ω₀ ⊆ D.regular ×ˢ W :=
    prod_mono (fun t ht => hreg ⟨(hac.trans ht.1).le, (ht.2.trans hdb).le⟩)
      (hsub.trans (subset_closure.trans hΩW))
  have hweak₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        (∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) -
          ∫ p, S p * φ p ∂ν₀ := by
    have hbase := hweak φ hφ hφc
      (hφs.trans (prod_mono (fun t ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩) hsub))
    have hφsupport : tsupport φ ⊆ Icc c d ×ˢ Ω₀ :=
      hφs.trans (prod_mono Ioo_subset_Icc_self Subset.rfl)
    have hres (v : ℝ × EuStd) (C : ℝ × EuStd → ℝ) :
        (∫ p, C p * fderiv ℝ φ p v ∂ν) = ∫ p, C p * fderiv ℝ φ p v ∂ν₀ := by
      apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p v)
        (fun hs => hp (hφsupport (tsupport_fderiv_apply_subset ℝ v hs))), mul_zero]
    have hresφ : (∫ p, S p * φ p ∂ν) = ∫ p, S p * φ p ∂ν₀ := by
      apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφsupport hs)), mul_zero]
    dsimp only [S, e] at hresφ
    simp_rw [hres, hresφ] at hbase
    refine hbase.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hV i] with p hp
    rw [hp]
  obtain ⟨R₀, hR₀, hR₀weak⟩ := exists_lp_weak_deriv_of_weighted_divergence
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_Ioo hΩ₀ (1 : ℝ)
    ((Lp.memLp U).mono_measure hmeasure) ((Lp.memLp S).mono_measure hmeasure)
    V H hAb hDAb hAs hHV (hρ.mono hregion) (fun p hp => hρne p (hregion hp))
    hρinv (hDρ.mul (r := ∞) hρinv) hweak₀
  have hmem : ∀ᵐ p ∂ν₀, p ∈ Ioo c d ×ˢ Ω₀ := by
    have htime : μ₀ = volume.restrict (Ioo c d) := by
      change (volume.restrict (Icc a b)).restrict (Icc c d) = volume.restrict (Ioo c d)
      rw [Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (Icc_subset_Icc hac.le hdb.le)]
      exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    change ∀ᵐ p ∂μ₀.prod (volume.restrict Ω₀), p ∈ Ioo c d ×ˢ Ω₀
    rw [htime]
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod hΩ₀.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (ae_restrict_mem hΩ₀.measurableSet).mono fun z hz => ⟨ht, hz⟩
  have hRalign : R = R₀ := Sobolev.lp_eq_of_weak_deriv_integral
    (isOpen_Ioo.prod hΩ₀) hmem (by norm_num) (1, 0) hQtime hR₀weak
  have hroot (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, P 0 e p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, Q 0 e p * φ p ∂ν₀ := by
    refine (integral_congr_ae ?_).trans (hQtime φ hφ hφc hφs)
    filter_upwards [hP] with p hp
    rw [hp]
  have htime := integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
    2 (1 : ℝ) (fun m β p => P m β p) (fun m β p => Q m β p)
    (fun m _ β => (Lp.memLp (P m β)).locallyIntegrable (by norm_num))
    (fun m _ β => (Lp.memLp (Q m β)).locallyIntegrable (by norm_num))
    (fun m hm β i => hPweak m (by omega) β i) hQweak hroot
  have hSm := (Lp.memLp S).mono_measure hmeasure
  let S₀ := hSm.toLp S
  have hS₀ : S₀ =ᵐ[ν₀] S := hSm.coeFn_toLp
  let B := fun i j p => (ρ p)⁻¹ * A i j p
  let C := fun i (p : ℝ × EuStd) =>
    ∑ j, (ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
  let r := fun p => (ρ p)⁻¹
  let q := fun p => -((ρ p)⁻¹ * fderiv ℝ ρ p (1, 0))
  have hr : ContDiffOn ℝ (⊤ : ℕ∞) r (D.regular ×ˢ W) := hρ.inv hρne
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q (D.regular ×ˢ W) := (hr.mul hDρsmooth).neg
  have hB (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (B i j) (D.regular ×ˢ W) := hr.mul (hA i j)
  have hC (i) : ContDiffOn ℝ (⊤ : ℕ∞) (C i) (D.regular ×ˢ W) := by
    apply ContDiffOn.sum
    intro j _
    exact hr.mul ((weightedInvGramOnEuclid_family_fderiv_contDiffOn
      (G := G) hG Subset.rfl α hW Subset.rfl i j).clm_apply contDiffOn_const)
  let Idx := (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) ⊕ Bool)
  let Y : Idx → Lp ℝ 2 ν₀ :=
    Sum.elim (fun ij => H ij.1 ij.2) (Sum.elim V (fun b => if b then S₀ else P 0 e))
  let DY : Idx → Lp ℝ 2 ν₀ :=
    Sum.elim (fun ij => Q 2 (Fin.cons ij.2 (Fin.cons ij.1 e)))
      (Sum.elim (fun i => Q 1 (Fin.cons i e)) (fun b => if b then Ft else R))
  let Z : Idx → ℝ × EuStd → ℝ :=
    Sum.elim (fun ij => B ij.1 ij.2) (Sum.elim C (fun b => if b then r else q))
  have hZ (i) : ContDiffOn ℝ (⊤ : ℕ∞) (Z i) (D.regular ×ˢ W) := by
    rcases i with ⟨i, j⟩ | (i | b)
    · exact hB i j
    · exact hC i
    · cases b
      · exact hq
      · exact hr
  have hDZ (i) : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ (Z i) p (1, 0))
      (D.regular ×ˢ W) :=
    ((hZ i).fderiv_of_isOpen (D.regular_isOpen.prod hW) (by simp)).clm_apply contDiffOn_const
  have hY (i) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, Y i p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, DY i p * φ p ∂ν₀ := by
    rcases i with ⟨i, j⟩ | (i | b)
    · exact htime 2 le_rfl (Fin.cons j (Fin.cons i e)) φ hφ hφc hφs
    · exact htime 1 (by omega) (Fin.cons i e) φ hφ hφc hφs
    · cases b
      · exact hroot φ hφ hφc hφs
      · refine (integral_congr_ae ?_).trans (hFt φ hφ hφc hφs)
        filter_upwards [hS₀] with p hp
        exact congrArg (fun z => z * fderiv ℝ φ p (1, 0)) hp
  have hRsum : R =ᵐ[ν₀] fun p => ∑ i : Idx, Z i p * Y i p := by
    rw [hRalign]
    filter_upwards [hR₀, hS₀, hP] with p hp hs hu
    change S₀ p = S p at hs
    change P 0 e p = U p at hu
    rw [hp]
    simp only [Idx, Z, Y, Fintype.sum_sum_type, Fintype.sum_bool, Bool.false_eq_true,
      ↓reduceIte, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, hs, hu]
    dsimp only [B, C, r, q]
    simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add, mul_assoc]
    ring
  obtain ⟨Rt, _, hRt⟩ := Sobolev.exists_lp_weak_deriv_of_ae_eq_finite_sum
    Finset.univ (isOpen_Ioo.prod hΩ₀) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (1, 0) R Y DY Z
    (fun i _ => hbounded _ (hZ i).continuousOn)
    (fun i _ => hbounded _ (hDZ i).continuousOn)
    (fun i _ => (hZ i).mono hregion) (fun i _ => hY i) hRsum
  exact ⟨R, Rt, hQtime, hRt⟩

end DifferentialGeometry.Analysis.Parabolic
