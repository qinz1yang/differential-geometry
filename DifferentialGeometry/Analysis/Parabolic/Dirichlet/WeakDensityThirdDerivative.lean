import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityGradientEquation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_local_lp_third_weak_derivative_of_weighted_weak_equation
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (DF : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hFspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => DF k (t, x)) (fun x => F (t, x)) Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ R : Lp ℝ 2 ν,
      ∃ J : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ T : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ i j, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv j (fun x => H i j (t, x)) (fun x => K i (t, x)) Ω₀) ∧
        (∀ i j k, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv k (fun x => J i j k (t, x)) (fun x => H i j (t, x)) Ω₀) ∧
        (∀ᵐ t ∂volume.restrict (Icc c d),
          Sobolev.Euclidean.MemWkp 3 2 (fun x => U (t, x)) Ω₀) ∧
        (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
        (R =ᵐ[ν] fun p => (ρ p)⁻¹ *
          ((∑ i, ∑ j, (A i j p * H i j p +
            fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K i p)) +
              F p - fderiv ℝ ρ p (1, 0) * U p)) ∧
        ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, K k p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, T k p * φ p ∂ν := by
  intro ν ρ A
  classical
  by_cases hcd : c ≤ d
  swap
  · refine ⟨(fun _ _ => 0), 0, (fun _ _ _ => 0), (fun _ => 0), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [ν, Icc_eq_empty_of_lt (lt_of_not_ge hcd), Filter.EventuallyEq]
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨Ω₁, hΩ₁, hΩ₀₁, hΩ₁Ω⟩ :=
    hΩ₀c.exists_isOpen_closure_subset (hΩ.mem_nhdsSet.mpr hΩ₀Ω)
  have hΩ₁c : IsCompact (closure Ω₁) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₁Ω.trans subset_closure)
  have hΩ₁s := hΩ₁Ω.trans (subset_closure.trans hΩs)
  let c₁ := (a + c) / 2
  let d₁ := (d + b) / 2
  have hac₁ : a < c₁ := by dsimp [c₁]; linarith
  have hc₁c : c₁ < c := by dsimp [c₁]; linarith
  have hdd₁ : d < d₁ := by dsimp [d₁]; linarith
  have hd₁b : d₁ < b := by dsimp [d₁]; linarith
  have hc₁d₁ : c₁ < d₁ := hc₁c.trans_le (hcd.trans hdd₁.le)
  have hI₁ : Icc c₁ d₁ ⊆ Icc a b := Icc_subset_Icc hac₁.le hd₁b.le
  have hI₀ : Icc c d ⊆ Icc c₁ d₁ := Icc_subset_Icc hc₁c.le hdd₁.le
  have hIoo : Ioo c d ⊆ Ioo c₁ d₁ := fun _ ht => ⟨hc₁c.trans ht.1, ht.2.trans hdd₁⟩
  have hsub₁ : Ω₁ ⊆ Ω := subset_closure.trans hΩ₁Ω
  have hsub₀ : Ω₀ ⊆ Ω₁ := subset_closure.trans hΩ₀₁
  let μ₁ := volume.restrict (Icc c₁ d₁)
  let ν₁ := μ₁.prod (volume.restrict Ω₁)
  have hν₁ : ν₁ ≤ (volume.restrict (Icc a b)).prod (volume.restrict Ω) :=
    Measure.prod_mono (Measure.restrict_mono hI₁ le_rfl) (Measure.restrict_mono hsub₁ le_rfl)
  have hμ₀ : volume.restrict (Icc c d) ≤ μ₁ := Measure.restrict_mono hI₀ le_rfl
  have hν₀ : ν ≤ ν₁ := Measure.prod_mono hμ₀ (Measure.restrict_mono hsub₀ le_rfl)
  obtain ⟨H₁, R₁, S₁, hH₁, hHcomm, hR₁, hRformula, _, hSeq⟩ :=
    exists_local_lp_weak_gradient_equation_of_weighted_weak_equation
      hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak DF hFspatial
        hac₁ hd₁b hΩ₁ hΩ₁Ω
  have hK₁ (i) : MemLp (K i) 2 ν₁ := (Lp.memLp (K i)).mono_measure hν₁
  let V := fun i => (hK₁ i).toLp (K i)
  have hV (i) : V i =ᵐ[ν₁] K i := (hK₁ i).coeFn_toLp
  have hVweak (i k) : ∀ᵐ t ∂μ₁, DeGiorgi.HasWeakPartialDeriv i
      (fun x => H₁ i k (t, x)) (fun x => V k (t, x)) Ω₁ := by
    filter_upwards [hHcomm i k, Measure.ae_ae_of_ae_prod (hV k)] with t ht he
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₁ i
      (Filter.EventuallyEq.symm he) ht
  have hVeq (k) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c₁ d₁ ×ˢ Ω₁) :
      (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν₁) =
        (∑ j, ∫ p, (∑ i, A i j p * H₁ i k p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₁) -
          ∫ p, S₁ k p * φ p ∂ν₁ := by
    calc
      _ = ∫ p, ρ p * K k p * fderiv ℝ φ p (1, 0) ∂ν₁ := by
        apply integral_congr_ae
        filter_upwards [hV k] with p hp
        rw [hp]
      _ = _ := hSeq k φ hφ hφc hφs
  have hex (k) := exists_local_lp_time_weak_derivative_of_weighted_weak_equation
    hG hc₁d₁ (hI₁.trans hreg) α hΩ₁ hΩ₁c hΩ₁s
      (V k) (S₁ k) (fun i => H₁ i k) (fun i => hVweak i k) (hVeq k)
      hc₁c hdd₁ hΩ₀ hΩ₀₁
  choose J₁ T hJ₁ hVtwo hTformula hT using hex
  have hHmem (i j) : MemLp (H₁ i j) 2 ν := (Lp.memLp (H₁ i j)).mono_measure hν₀
  let H := fun i j => (hHmem i j).toLp (H₁ i j)
  have hHrep (i j) : H i j =ᵐ[ν] H₁ i j := (hHmem i j).coeFn_toLp
  have hRmem : MemLp R₁ 2 ν := (Lp.memLp R₁).mono_measure hν₀
  let R := hRmem.toLp R₁
  have hRrep : R =ᵐ[ν] R₁ := hRmem.coeFn_toLp
  let J := fun i j k => J₁ j i k
  have hH (i j) : ∀ᵐ t ∂volume.restrict (Icc c d), DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => K i (t, x)) Ω₀ := by
    filter_upwards [(hH₁ i j).filter_mono (ae_mono hμ₀),
      Measure.ae_ae_of_ae_prod (hHrep i j)] with t ht he
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub₀ ht).congr_ae
      Filter.EventuallyEq.rfl (Filter.EventuallyEq.symm he)
  have hJ (i j k) : ∀ᵐ t ∂volume.restrict (Icc c d), DeGiorgi.HasWeakPartialDeriv k
      (fun x => J i j k (t, x)) (fun x => H i j (t, x)) Ω₀ := by
    filter_upwards [hJ₁ j i k, Measure.ae_ae_of_ae_prod (hHrep i j)] with t ht he
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ k
      (Filter.EventuallyEq.symm he) ht
  have hV₀ (k) : V k =ᵐ[ν] K k := (hV k).filter_mono (ae_mono hν₀)
  have hKtwo (k) : ∀ᵐ t ∂volume.restrict (Icc c d),
      Sobolev.Euclidean.MemWkp 2 2 (fun x => K k (t, x)) Ω₀ := by
    filter_upwards [hVtwo k, Measure.ae_ae_of_ae_prod (hV₀ k)] with t ht he
    exact (Sobolev.Euclidean.MemWkp_congr_ae (by norm_num) hΩ₀ he).mp ht
  have hUmem : MemLp U 2 ν := (Lp.memLp U).mono_measure (hν₀.trans hν₁)
  have hfirst (i) : ∀ᵐ t ∂volume.restrict (Icc c d), DeGiorgi.HasWeakPartialDeriv i
      (fun x => K i (t, x)) (fun x => U (t, x)) Ω₀ := by
    filter_upwards [(hspatial i).filter_mono
      (ae_mono (hμ₀.trans (Measure.restrict_mono hI₁ le_rfl)))] with t ht
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ (hsub₀.trans hsub₁) ht
  have hUthree : ∀ᵐ t ∂volume.restrict (Icc c d),
      Sobolev.Euclidean.MemWkp 3 2 (fun x => U (t, x)) Ω₀ := by
    filter_upwards [hUmem.prodMk_left (by norm_num), ae_all_iff.mpr hKtwo,
      ae_all_iff.mpr hfirst] with t hut hKt hft
    exact Sobolev.Euclidean.memWkp_succ_of_hasWeakPartialDeriv (by norm_num) hΩ₀ hut hKt hft
  have hrestrict (f ψ : ℝ × EuStd → ℝ) (hs : tsupport ψ ⊆ Icc c d ×ˢ Ω₀) :
      (∫ p, f p * ψ p ∂ν₁) = ∫ p, f p * ψ p ∂ν := by
    dsimp only [ν₁, ν, μ₁]
    rw [Measure.prod_restrict, Measure.prod_restrict]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Icc.prod hΩ₁.measurableSet) (Set.prod_mono hI₀ hsub₀)
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp.2 (hs h)), mul_zero]
  refine ⟨H, R, J, T, hH, hJ, hUthree, ?_, ?_, ?_⟩
  · intro φ hφ hφc hφs
    have hs : tsupport φ ⊆ Icc c d ×ˢ Ω₀ :=
      hφs.trans (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
    have hd : tsupport (fun p => fderiv ℝ φ p (1, 0)) ⊆ Icc c d ×ˢ Ω₀ :=
      (tsupport_fderiv_apply_subset ℝ (1, 0)).trans hs
    calc
      _ = ∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₁ :=
        (hrestrict U (fun p => fderiv ℝ φ p (1, 0)) hd).symm
      _ = -∫ p, R₁ p * φ p ∂ν₁ :=
        hR₁ φ hφ hφc (hφs.trans (Set.prod_mono hIoo hsub₀))
      _ = -∫ p, R₁ p * φ p ∂ν := congrArg Neg.neg (hrestrict R₁ φ hs)
      _ = _ := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        filter_upwards [hRrep] with p hp
        rw [hp]
  · filter_upwards [hRrep, hRformula.filter_mono (ae_mono hν₀),
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hHrep i)] with p hp hformula hHp
    rw [hp]
    simpa only [hHp] using hformula
  · intro k φ hφ hφc hφs
    calc
      _ = ∫ p, V k p * fderiv ℝ φ p (1, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hV₀ k] with p hp
        rw [hp]
      _ = _ := hT k φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
