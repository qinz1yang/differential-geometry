import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceSecondTimeDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeSecondWeakDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.WeakPartialRegularity

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
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

theorem exists_local_timeH1_weak_partial_trees_of_metric_divergence_equation
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
      (∀ m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := volume.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∃ P Q : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
        (P 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] U) ∧
        (∀ m β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω₀) ∧
        (∀ m β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => Q (m + 1) (Fin.cons i β) (t, z)) (fun z => Q m β (t, z)) Ω₀) ∧
        ∀ m β, ∃ w : TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
          ∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
            ((w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => P m β (c + t, z)) ∧
            ((w.deriv t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => Q m β (c + t, z)) := by
  intro μ ν ρ A U K F hK hF hweak μ₀ ν₀
  have hμ₀ : μ.restrict (Icc c d) = μ₀ := by
    change (volume.restrict (Icc a b)).restrict (Icc c d) = volume.restrict (Icc c d)
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (Icc_subset_Icc hac.le hdb.le)]
  have horder := exists_local_weak_partial_trees_of_all_orders_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF hweak
  dsimp only at horder
  rw [hμ₀] at horder
  obtain ⟨P, Q, hP, hPweak, hQweak, hQtime⟩ := horder
  have hroot (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, P 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        -∫ p, Q 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀ := by
    refine (integral_congr_ae ?_).trans (hQtime φ hφ hφc hφs)
    filter_upwards [hP] with p hp
    rw [hp]
  refine ⟨P, Q, hP, hPweak, hQweak, ?_⟩
  intro m β
  exact TimeSobolev.exists_timeH1_of_finite_weak_partial_trees hcd hΩ₀ m P Q
    (fun k _ γ i => hPweak k γ i) (fun k _ γ i => hQweak k γ i) hroot m le_rfl β

private theorem exists_timeH1_partial_tree_of_metric_divergence_equation
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
      (∀ m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      ∃ W : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) →
          TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
        (∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
          ((W 0 (fun i => Fin.elim0 i)).toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
            fun z => U (c + t, z)) ∧
        ∀ m β i, ∀ᵐ t ∂TimeSobolev.timeMeasure (d - c), DeGiorgi.HasWeakPartialDeriv i
          ((W (m + 1) (Fin.cons i β)).toFun t) ((W m β).toFun t) Ω₀ := by
  intro μ ν ρ A U K F hK hF hweak
  obtain ⟨P, Q, hP, hPweak, hQweak, htime⟩ :=
    exists_local_timeH1_weak_partial_trees_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF hweak
  choose W hW using htime
  have hshift : MeasurePreserving (fun t : ℝ => c + t)
      (TimeSobolev.timeMeasure (d - c)) (volume.restrict (Icc c d)) := by
    have h := (measurePreserving_add_right volume c).restrict_image_emb
      (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (d - c))
    simpa only [TimeSobolev.timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm c] using h
  have hWweak (m β i) : ∀ᵐ t ∂TimeSobolev.timeMeasure (d - c), DeGiorgi.HasWeakPartialDeriv i
      ((W (m + 1) (Fin.cons i β)).toFun t) ((W m β).toFun t) Ω₀ := by
    filter_upwards [hW m β, hW (m + 1) (Fin.cons i β),
      hshift.quasiMeasurePreserving.ae (hPweak m β i)] with t ht hc hw
    exact hw.congr_ae (Filter.EventuallyEq.symm ht.1) (Filter.EventuallyEq.symm hc.1)
  refine ⟨W, ?_, hWweak⟩
  filter_upwards [hW 0 (fun i => Fin.elim0 i),
    hshift.quasiMeasurePreserving.ae (Measure.ae_ae_of_ae_prod hP)] with t ht hu
  exact ht.1.trans hu

theorem exists_local_timeH1_with_smooth_spatial_slices_of_metric_divergence_equation
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
      (∀ m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      ∃ w : TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
        (∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
          (w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => U (c + t, z)) ∧
        ∀ t ∈ Icc (0 : ℝ) (d - c), ∃ v : EuStd → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) v Ω₀ ∧
            (w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] v := by
  intro μ ν ρ A U K F hK hF hweak
  obtain ⟨W, hW, hWweak⟩ := exists_timeH1_partial_tree_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF hweak
  exact ⟨W 0 (fun i => Fin.elim0 i), hW,
    TimeSobolev.exists_contDiffOn_ae_eq_toFun_of_weak_partial_tree (sub_pos.mpr hcd) hΩ₀ W hWweak⟩

theorem exists_local_timeH1_with_sobolev_continuity_of_metric_divergence_equation
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
      (∀ m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      ∃ w : TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
        (∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
          (w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => U (c + t, z)) ∧
        ∀ N : ℕ,
          (∀ t ∈ Icc (0 : ℝ) (d - c), Sobolev.Euclidean.MemWkp N 2 (w.toFun t) Ω₀) ∧
          ∀ t₀ ∈ Icc (0 : ℝ) (d - c),
            Tendsto (fun t => (Sobolev.Euclidean.iteratedWeakSobolevNorm N 2
              (fun z => w.toFun t z - w.toFun t₀ z) Ω₀).toReal)
              (𝓝[Icc (0 : ℝ) (d - c)] t₀) (𝓝 0) := by
  intro μ ν ρ A U K F hK hF hweak
  obtain ⟨W, hW, hWweak⟩ := exists_timeH1_partial_tree_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF hweak
  refine ⟨W 0 (fun i => Fin.elim0 i), hW, fun N => ⟨?_, ?_⟩⟩
  · exact fun t ht => TimeSobolev.memWkp_toFun_of_weak_partial_tree
      (sub_pos.mpr hcd) hΩ₀ W hWweak t ht N
  · exact TimeSobolev.tendsto_wkpNorm_sub_toFun_of_weak_partial_tree
      (sub_pos.mpr hcd) hΩ₀ W hWweak N

theorem exists_local_contDiffOn_timeH1_of_metric_divergence_equation
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
        ∃ w : TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
          ContDiffOn ℝ 1 w.toFun (Icc (0 : ℝ) (d - c)) ∧
          ∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
            (w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => U (c + t, z) := by
  intro μ ν ρ A U K F hK hF hweak μ₀ ν₀ Ft hFt
  obtain ⟨R, Rt, hR, hRt⟩ := exists_local_second_weak_time_derivative_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF hweak Ft hFt
  have hμ₀ : μ₀ = volume.restrict (Icc c d) := by
    change (volume.restrict (Icc a b)).restrict (Icc c d) = volume.restrict (Icc c d)
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (Icc_subset_Icc hac.le hdb.le)]
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hUm := (Lp.memLp U).mono_measure hmeasure
  let U₀ := hUm.toLp U
  have hU₀ : U₀ =ᵐ[ν₀] U := hUm.coeFn_toLp
  have hroot (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, U₀ p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, R p * φ p ∂ν₀ := by
    refine (integral_congr_ae ?_).trans (hR φ hφ hφc hφs)
    filter_upwards [hU₀] with p hp
    rw [hp]
  have hregular : ∃ w v : TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
      (∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
        ((w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => U₀ (c + t, z)) ∧
        ((v.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => R (c + t, z)) ∧
        ((v.deriv t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => Rt (c + t, z))) ∧
      w.deriv = v.toFunL2 ∧
      ContDiffOn ℝ 1 w.toFun (Icc (0 : ℝ) (d - c)) ∧
      EqOn (derivWithin w.toFun (Icc (0 : ℝ) (d - c))) v.toFun (Icc (0 : ℝ) (d - c)) := by
    have hgeneral := TimeSobolev.exists_contDiffOn_timeH1_of_second_spacetime_weak_deriv
      (ν := volume) hcd hΩ₀
    rw [← hμ₀] at hgeneral
    exact hgeneral U₀ R Rt hroot hRt
  obtain ⟨w, v, hw, _, hc, _⟩ := hregular
  have hshift : MeasurePreserving (fun t : ℝ => c + t) (TimeSobolev.timeMeasure (d - c)) μ₀ := by
    rw [hμ₀]
    have h := (measurePreserving_add_right volume c).restrict_image_emb
      (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (d - c))
    simpa only [TimeSobolev.timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm c] using h
  refine ⟨w, hc, ?_⟩
  filter_upwards [hw, hshift.quasiMeasurePreserving.ae (Measure.ae_ae_of_ae_prod hU₀)] with t ht hu
  exact ht.1.trans hu

theorem exists_local_contDiffOn_timeH1_of_homogeneous_metric_divergence_equation
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
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν)) →
      ∃ w : TimeSobolev.timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (d - c),
        ContDiffOn ℝ 1 w.toFun (Icc (0 : ℝ) (d - c)) ∧
        ∀ᵐ t ∂TimeSobolev.timeMeasure (d - c),
          (w.toFun t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z => U (c + t, z) := by
  intro μ ν ρ A U K hK hweak
  let μ₀ := μ.restrict (Icc c d)
  let ν₀ := μ₀.prod (volume.restrict Ω₀)
  let F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν := fun _ _ => 0
  have hzero : (0 : Lp ℝ 2 ν) =ᵐ[ν] (fun _ => 0) := Lp.coeFn_zero ℝ 2 ν
  have hF (m β i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω := by
    filter_upwards [Measure.ae_ae_of_ae_prod hzero] with t ht
    have hz : DeGiorgi.HasWeakPartialDeriv i (fun _ => 0) (fun _ => 0) Ω := by
      intro φ hφ hφc hφs
      simp
    exact hz.congr_ae (Filter.EventuallyEq.symm ht) (Filter.EventuallyEq.symm ht)
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  apply exists_local_contDiffOn_timeH1_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK
    (fun m _ β i => hF m β i) ?_ (0 : Lp ℝ 2 ν₀) ?_
  · intro φ hφ hφc hφs
    have hz : (∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) = 0 := by
      trans ∫ p, (0 : ℝ) ∂ν
      · apply integral_congr_ae
        filter_upwards [hzero] with p hp
        change (0 : Lp ℝ 2 ν) p * φ p = 0
        rw [hp, zero_mul]
      · exact integral_zero _ _
    rw [hz, sub_zero]
    exact hweak φ hφ hφc hφs
  · intro φ hφ hφc hφs
    have hz : (∫ p, F 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) = 0 := by
      trans ∫ p, (0 : ℝ) ∂ν₀
      · apply integral_congr_ae
        filter_upwards [hzero.filter_mono (ae_mono hmeasure)] with p hp
        change (0 : Lp ℝ 2 ν) p * fderiv ℝ φ p (1, 0) = 0
        rw [hp, zero_mul]
      · exact integral_zero _ _
    have hzt : (∫ p, (0 : Lp ℝ 2 ν₀) p * φ p ∂ν₀) = 0 := by
      trans ∫ p, (0 : ℝ) ∂ν₀
      · apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero ℝ 2 ν₀] with p hp
        simp only [hp, Pi.zero_apply, zero_mul]
      · exact integral_zero _ _
    rw [hz, hzt, neg_zero]

end DifferentialGeometry.Analysis.Parabolic
