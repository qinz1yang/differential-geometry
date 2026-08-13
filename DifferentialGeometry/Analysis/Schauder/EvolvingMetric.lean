import DifferentialGeometry.Analysis.Schauder.CompactEllipticity
import DifferentialGeometry.Analysis.Schauder.CompactRegularity
import DifferentialGeometry.Analysis.Schauder.ParabolicChartOperator
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

noncomputable section

open Matrix Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclN (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem exists_chartInvGramOnE_parabolic_schauder_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (a b : Real) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    (i j : Fin (Module.finrank Real E))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
        ‖chartInvGramOnE (I := I) (G.metric p.time) chartCenter i j p.space‖ ≤ C₀) ∧
      HolderWith Cα alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (fun p => chartInvGramOnE (I := I)
            (G.metric p.time) chartCenter i j p.space)) := by
  let f : Real × E → Real := fun p =>
    chartInvGramOnE (I := I) (G.metric p.1) chartCenter i j p.2
  have hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K) :=
    ((chartInvGramOnE_contDiffOn (I := I) hG habreg chartCenter i j).mono
      (Set.prod_mono Subset.rfl hKchart)).of_le (by simp)
  simpa only [f, Function.comp_apply, parabolicToProduct] using
    exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hf halpha

theorem exists_chartInvGramOnE_parabolic_schauder_coefficient_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (a b : Real) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ A Ka : Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → NNReal,
      (∀ i j p, p ∈ parabolicCylinder (Set.Icc a b) K →
        ‖chartInvGramOnE (I := I) (G.metric p.time)
          chartCenter i j p.space‖ ≤ A i j) ∧
      (∀ i j, HolderWith (Ka i j) alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (fun p => chartInvGramOnE (I := I)
            (G.metric p.time) chartCenter i j p.space))) ∧
      ∀ p, p ∈ parabolicCylinder (Set.Icc a b) K →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          chartInvGramOnE (I := I) (G.metric p.time)
            chartCenter i j p.space).PosDef := by
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      ∃ C₀ Cα : NNReal,
        (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
          ‖chartInvGramOnE (I := I) (G.metric p.time)
            chartCenter i j p.space‖ ≤ C₀) ∧
        HolderWith Cα alpha
          ((parabolicCylinder (Set.Icc a b) K).restrict
            (fun p => chartInvGramOnE (I := I)
              (G.metric p.time) chartCenter i j p.space)) := by
    intro i j
    exact exists_chartInvGramOnE_parabolic_schauder_bounds
      hG a b habreg chartCenter hK hKconv hKchart i j halpha
  choose A Ka hbounds using hentry
  refine ⟨A, Ka, ?_, ?_, ?_⟩
  · intro i j p hp
    exact (hbounds i j).1 p hp
  · intro i j
    exact (hbounds i j).2
  · intro p hp
    exact chartInvGramOnE_posDef (I := I) (G.metric p.time) chartCenter
      (interior_subset (hKchart hp.2))

theorem exists_chartChristoffelOnE_parabolic_schauder_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    (i j k : Fin (Module.finrank Real E))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
        ‖chartChristoffel (I := I) (G.metric p.time)
          chartCenter i j k p.space‖ ≤ C₀) ∧
      HolderWith Cα alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (fun p => chartChristoffel (I := I) (G.metric p.time)
            chartCenter i j k p.space)) := by
  let f : Real × E → Real := fun p =>
    chartChristoffel (I := I) (G.metric p.1) chartCenter i j k p.2
  have hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K) :=
    ((chartChristoffelOnE_contDiffOn (I := I) hG habreg
      (uniqueDiffOn_Icc hab) chartCenter i j k).mono
      (Set.prod_mono Subset.rfl hKchart)).of_le (by simp)
  simpa only [f, Function.comp_apply, parabolicToProduct] using
    exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hf halpha

theorem exists_parabolicChartPrincipalCoefficient_schauder_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (a b : Real) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ A Ka : Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → NNReal,
      (∀ i j p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K) →
        ‖parabolicChartPrincipalCoefficient (I := I) G.metric
          chartCenter i j p‖ ≤ A i j) ∧
      (∀ i j, HolderWith (Ka i j) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K)).restrict
            (parabolicChartPrincipalCoefficient (I := I) G.metric
              chartCenter i j))) ∧
      ∀ p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          parabolicChartPrincipalCoefficient (I := I) G.metric
            chartCenter i j p).PosDef := by
  obtain ⟨A, Ka, hnorm, hholder, hpos⟩ :=
    exists_chartInvGramOnE_parabolic_schauder_coefficient_bounds
      hG a b habreg chartCenter hK hKconv hKchart halpha
  let L := ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
  let Ka' : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal :=
    fun i j ↦ Ka i j * (max 1 ‖L‖₊) ^ (alpha : Real)
  refine ⟨A, Ka', ?_, ?_, ?_⟩
  · intro i j p hp
    have h := hnorm i j (parabolicLinearMap L p) hp
    simpa [L, parabolicChartPrincipalCoefficient, euclideanChartPoint,
      chartInvGramOnE_def] using h
  · intro i j
    have h := parabolicHolder_linearMap L (hholder i j)
    simpa [L, Ka', parabolicChartPrincipalCoefficient, euclideanChartPoint,
      chartInvGramOnE_def, Function.comp_def] using h
  · intro p hp
    have h := hpos (parabolicLinearMap L p) hp
    simpa [L, parabolicChartPrincipalCoefficient, euclideanChartPoint,
      chartInvGramOnE_def] using h

theorem exists_parabolicChartChristoffelCoefficient_schauder_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ B KGamma : Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → NNReal,
      (∀ i j k p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K) →
        ‖parabolicChartChristoffelCoefficient (I := I) G.metric
          chartCenter i j k p‖ ≤ B i j k) ∧
      ∀ i j k, HolderWith (KGamma i j k) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K)).restrict
            (parabolicChartChristoffelCoefficient (I := I) G.metric
              chartCenter i j k)) := by
  have hentry : ∀ i j k : Fin (Module.finrank Real E),
      ∃ C₀ Cα : NNReal,
        (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
          ‖chartChristoffel (I := I) (G.metric p.time)
            chartCenter i j k p.space‖ ≤ C₀) ∧
        HolderWith Cα alpha
          ((parabolicCylinder (Set.Icc a b) K).restrict
            (fun p => chartChristoffel (I := I) (G.metric p.time)
              chartCenter i j k p.space)) := by
    intro i j k
    exact exists_chartChristoffelOnE_parabolic_schauder_bounds
      hG hab habreg chartCenter hK hKconv hKchart i j k halpha
  choose B KGamma hbounds using hentry
  let L := ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
  let KGamma' : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → NNReal :=
    fun i j k ↦ KGamma i j k * (max 1 ‖L‖₊) ^ (alpha : Real)
  refine ⟨B, KGamma', ?_, ?_⟩
  · intro i j k p hp
    have h := (hbounds i j k).1 (parabolicLinearMap L p) hp
    simpa only [L, parabolicChartChristoffelCoefficient,
      parabolicLinearMap_time, parabolicLinearMap_space] using h
  · intro i j k
    have h := parabolicHolder_linearMap L (hbounds i j k).2
    simpa only [L, KGamma', parabolicChartChristoffelCoefficient,
      Function.comp_apply, parabolicLinearMap_time,
      parabolicLinearMap_space] using h

theorem exists_parabolicChartDriftCoefficient_schauder_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      (∀ k p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K) →
        ‖parabolicChartDriftCoefficient (I := I) G.metric
          chartCenter k p‖ ≤ Bb k) ∧
      ∀ k, HolderWith (Kb k) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K)).restrict
            (parabolicChartDriftCoefficient (I := I) G.metric
              chartCenter k)) := by
  obtain ⟨A, Ka, hAnorm, ha, _hpos⟩ :=
    exists_parabolicChartPrincipalCoefficient_schauder_bounds
      hG a b habreg chartCenter hK hKconv hKchart halpha
  obtain ⟨BGamma, KGamma, hGammaNorm, hGamma⟩ :=
    exists_parabolicChartChristoffelCoefficient_schauder_bounds
      hG hab habreg chartCenter hK hKconv hKchart halpha
  let Q := parabolicLinearPreimage
    ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
    (parabolicCylinder (Set.Icc a b) K)
  let Bb : Fin (Module.finrank Real E) → NNReal := fun k ↦
    ∑ i, ∑ j, A i j * BGamma i j k
  let Kb : Fin (Module.finrank Real E) → NNReal := fun k ↦
    ∑ i, ∑ j, (A i j * KGamma i j k + BGamma i j k * Ka i j)
  refine ⟨Bb, Kb, ?_, ?_⟩
  · intro k p hp
    rw [parabolicChartDriftCoefficient_apply, norm_neg]
    calc
      ‖∑ i, ∑ j,
          parabolicChartPrincipalCoefficient (I := I) G.metric
              chartCenter i j p *
            parabolicChartChristoffelCoefficient (I := I) G.metric
              chartCenter i j k p‖ ≤
          ∑ i, ‖∑ j,
            parabolicChartPrincipalCoefficient (I := I) G.metric
                chartCenter i j p *
              parabolicChartChristoffelCoefficient (I := I) G.metric
                chartCenter i j k p‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖parabolicChartPrincipalCoefficient (I := I) G.metric
              chartCenter i j p *
            parabolicChartChristoffelCoefficient (I := I) G.metric
              chartCenter i j k p‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, (A i j : Real) * BGamma i j k := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hAnorm i j p hp) (hGammaNorm i j k p hp)
          (norm_nonneg _) (by positivity)
      _ = (Bb k : Real) := by
        simp only [Bb, NNReal.coe_sum, NNReal.coe_mul]
  · intro k
    have hproduct : ∀ i j,
        HolderWith (A i j * KGamma i j k + BGamma i j k * Ka i j) alpha
          (fun p : Q ↦
            parabolicChartPrincipalCoefficient (I := I) G.metric
                chartCenter i j p.1 *
              parabolicChartChristoffelCoefficient (I := I) G.metric
                chartCenter i j k p.1) := by
      intro i j
      have h := holderWith_smul_of_norm_le (ha i j) (hGamma i j k)
        (fun p : Q ↦ hAnorm i j p.1 p.2)
        (fun p : Q ↦ hGammaNorm i j k p.1 p.2)
      simpa only [Pi.smul_apply, smul_eq_mul, Set.restrict_apply] using h
    have hj : ∀ i, HolderWith
        (∑ j, (A i j * KGamma i j k + BGamma i j k * Ka i j)) alpha
          (fun p : Q ↦ ∑ j,
            parabolicChartPrincipalCoefficient (I := I) G.metric
                chartCenter i j p.1 *
              parabolicChartChristoffelCoefficient (I := I) G.metric
                chartCenter i j k p.1) := by
      intro i
      exact holderWith_finset_sum (Finset.univ)
        (fun j _ ↦ hproduct i j)
    have hi := holderWith_finset_sum (Finset.univ)
      (fun i _ ↦ hj i)
    have hneg : HolderWith
        (∑ i, ∑ j, (A i j * KGamma i j k + BGamma i j k * Ka i j)) alpha
          (-(fun p : Q ↦ ∑ i, ∑ j,
            parabolicChartPrincipalCoefficient (I := I) G.metric
                chartCenter i j p.1 *
              parabolicChartChristoffelCoefficient (I := I) G.metric
                chartCenter i j k p.1)) := by
      intro p q
      simpa only [Pi.neg_apply, edist_neg_neg] using hi p q
    simpa only [Q, Kb, parabolicChartDriftCoefficient,
      Set.restrict_apply, Pi.neg_apply] using hneg

theorem exists_uniform_parabolic_chart_operator_coefficient_schauder_bounds_of_finite
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    {Achart : Type*} [Finite Achart]
    (chartCenter : Achart → M) (K : Achart → Set E)
    (hK : ∀ r, IsCompact (K r))
    (hKconv : ∀ r, Convex Real (K r))
    (hKchart : ∀ r, K r ⊆ interior (extChartAt I (chartCenter r)).target)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Apr Ka : Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → NNReal,
      ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      (∀ r i j p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPrincipalCoefficient (I := I) G.metric
          (chartCenter r) i j p‖ ≤ Apr i j) ∧
      (∀ r i j, HolderWith (Ka i j) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPrincipalCoefficient (I := I) G.metric
              (chartCenter r) i j))) ∧
      (∀ r p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          parabolicChartPrincipalCoefficient (I := I) G.metric
            (chartCenter r) i j p).PosDef) ∧
      (∀ r k p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartDriftCoefficient (I := I) G.metric
          (chartCenter r) k p‖ ≤ Bb k) ∧
      ∀ r k, HolderWith (Kb k) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartDriftCoefficient (I := I) G.metric
              (chartCenter r) k)) := by
  classical
  letI := Fintype.ofFinite Achart
  have hpkg : ∀ r : Achart,
      ∃ Ar Kar : Fin (Module.finrank Real E) →
            Fin (Module.finrank Real E) → NNReal,
        ∃ Bbr Kbr : Fin (Module.finrank Real E) → NNReal,
        (∀ i j p, p ∈ parabolicLinearPreimage
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
            (parabolicCylinder (Set.Icc a b) (K r)) →
          ‖parabolicChartPrincipalCoefficient (I := I) G.metric
            (chartCenter r) i j p‖ ≤ Ar i j) ∧
        (∀ i j, HolderWith (Kar i j) alpha
          ((parabolicLinearPreimage
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
            (parabolicCylinder (Set.Icc a b) (K r))).restrict
              (parabolicChartPrincipalCoefficient (I := I) G.metric
                (chartCenter r) i j))) ∧
        (∀ p, p ∈ parabolicLinearPreimage
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
            (parabolicCylinder (Set.Icc a b) (K r)) →
          (Matrix.of fun i j : Fin (Module.finrank Real E) =>
            parabolicChartPrincipalCoefficient (I := I) G.metric
              (chartCenter r) i j p).PosDef) ∧
        (∀ k p, p ∈ parabolicLinearPreimage
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
            (parabolicCylinder (Set.Icc a b) (K r)) →
          ‖parabolicChartDriftCoefficient (I := I) G.metric
            (chartCenter r) k p‖ ≤ Bbr k) ∧
        ∀ k, HolderWith (Kbr k) alpha
          ((parabolicLinearPreimage
            ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
            (parabolicCylinder (Set.Icc a b) (K r))).restrict
              (parabolicChartDriftCoefficient (I := I) G.metric
                (chartCenter r) k)) := by
    intro r
    obtain ⟨Ar, Kar, hAnorm, ha, hpos⟩ :=
      exists_parabolicChartPrincipalCoefficient_schauder_bounds
        hG a b habreg (chartCenter r) (hK r) (hKconv r) (hKchart r) halpha
    obtain ⟨Bbr, Kbr, hbnorm, hb⟩ :=
      exists_parabolicChartDriftCoefficient_schauder_bounds
        hG hab habreg (chartCenter r) (hK r) (hKconv r) (hKchart r) halpha
    exact ⟨Ar, Kar, Bbr, Kbr, hAnorm, ha, hpos, hbnorm, hb⟩
  choose Ar Kar Bbr Kbr hpkg using hpkg
  let Apr : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal := fun i j ↦ ∑ r, Ar r i j
  let Ka : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal := fun i j ↦ ∑ r, Kar r i j
  let Bb : Fin (Module.finrank Real E) → NNReal := fun k ↦ ∑ r, Bbr r k
  let Kb : Fin (Module.finrank Real E) → NNReal := fun k ↦ ∑ r, Kbr r k
  refine ⟨Apr, Ka, Bb, Kb, ?_, ?_, ?_, ?_, ?_⟩
  · intro r i j p hp
    exact (hpkg r).1 i j p hp |>.trans
      (Finset.single_le_sum (fun s _ ↦ zero_le (Ar s i j)) (Finset.mem_univ r))
  · intro r i j
    exact (hpkg r).2.1 i j |>.mono
      (Finset.single_le_sum (fun s _ ↦ zero_le (Kar s i j)) (Finset.mem_univ r))
  · intro r p hp
    exact (hpkg r).2.2.1 p hp
  · intro r k p hp
    exact (hpkg r).2.2.2.1 k p hp |>.trans
      (Finset.single_le_sum (fun s _ ↦ zero_le (Bbr s k)) (Finset.mem_univ r))
  · intro r k
    exact (hpkg r).2.2.2.2 k |>.mono
      (Finset.single_le_sum (fun s _ ↦ zero_le (Kbr s k)) (Finset.mem_univ r))

theorem exists_uniform_parabolic_chart_principal_coefficient_quadratic_lower_bound_of_finite
    [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    {Achart : Type*} [Finite Achart]
    (chartCenter : Achart → M) (K : Achart → Set E)
    (hK : ∀ r, IsCompact (K r))
    (hKconv : ∀ r, Convex Real (K r))
    (hKchart : ∀ r, K r ⊆ interior (extChartAt I (chartCenter r)).target) :
    ∃ c : Real, 0 < c ∧ ∀ r p,
      p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ∀ v : EuclN E,
          c * ‖v‖ ^ 2 ≤ star v ⬝ᵥ
            (Matrix.of fun i j : Fin (Module.finrank Real E) =>
              parabolicChartPrincipalCoefficient (I := I) G.metric
                (chartCenter r) i j p) *ᵥ v := by
  classical
  obtain ⟨_, _, _, _, _, ha, hpos, _, _⟩ :=
    exists_uniform_parabolic_chart_operator_coefficient_schauder_bounds_of_finite
      hG hab habreg chartCenter K hK hKconv hKchart
        (alpha := (1 : NNReal)) (by norm_num)
  let e := (toEuclidean (E := E)).symm
  let Q : Achart → Set (ParabolicPoint (EuclN E)) := fun r ↦
    parabolicLinearPreimage (e : EuclN E →L[Real] E)
      (parabolicCylinder (Set.Icc a b) (K r))
  have hQeq : ∀ r,
      Q r = parabolicCylinder (Set.Icc a b) (toEuclidean '' K r) := by
    intro r
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, ⟨e p.space, hp.2, by simp [e]⟩⟩
    · intro hp
      rcases hp.2 with ⟨y, hy, hyp⟩
      have hey : e p.space = y := by
        rw [← hyp]
        simp [e]
      refine ⟨hp.1, ?_⟩
      change e p.space ∈ K r
      rw [hey]
      exact hy
  have hQcompact : ∀ r, IsCompact (Q r) := by
    intro r
    rw [hQeq r]
    exact isCompact_parabolicCylinder_Icc a b
      ((hK r).image (toEuclidean (E := E)).continuous)
  let A : Achart → ParabolicPoint (EuclN E) →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun r p ↦ Matrix.of fun i j ↦
      parabolicChartPrincipalCoefficient (I := I) G.metric (chartCenter r) i j p
  have hAcont : ∀ r i j, ContinuousOn (fun p ↦ A r p i j) (Q r) := by
    intro r i j
    exact (HolderWith.restrict_iff.mp (ha r i j)).continuousOn zero_lt_one
  have hApos : ∀ r p, p ∈ Q r → (A r p).PosDef := by
    intro r p hp
    exact hpos r p hp
  simpa only [Q, A] using
    exists_uniform_matrix_quadratic_lower_bound_of_finite Q hQcompact A hAcont hApos

theorem exists_finite_buffered_chart_cover_with_uniform_parabolic_operator_coefficient_schauder_bounds
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ s : Finset M, ∃ r R Rext : M → Real,
      (∀ x ∈ s, 0 < r x ∧ r x < R x ∧ R x < Rext x) ∧
      (∀ x ∈ s,
        (toEuclidean (E := E)).symm ''
            Metric.closedBall (toEuclidean (extChartAt I x x)) (Rext x) ⊆
          (extChartAt I x).target) ∧
      (∀ y : M, ∃ x ∈ s,
        y ∈ (extChartAt I x).source ∧
          toEuclidean (extChartAt I x y) ∈
            Metric.ball (toEuclidean (extChartAt I x x)) (r x)) ∧
      ∃ Apr Ka : Fin (Module.finrank Real E) →
            Fin (Module.finrank Real E) → NNReal,
        ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
        (∀ x : ↥s, ∀ i j p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ‖parabolicChartPrincipalCoefficient (I := I) G.metric x.1 i j p‖ ≤
              Apr i j) ∧
        (∀ x : ↥s, ∀ i j, HolderWith (Ka i j) alpha
          ((parabolicCylinder (Set.Icc a b)
            (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1))).restrict
              (parabolicChartPrincipalCoefficient (I := I) G.metric x.1 i j))) ∧
        (∀ x : ↥s, ∀ p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            (Matrix.of fun i j : Fin (Module.finrank Real E) =>
              parabolicChartPrincipalCoefficient (I := I) G.metric x.1 i j p).PosDef) ∧
        (∀ x : ↥s, ∀ k p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ‖parabolicChartDriftCoefficient (I := I) G.metric x.1 k p‖ ≤ Bb k) ∧
        ∀ x : ↥s, ∀ k, HolderWith (Kb k) alpha
          ((parabolicCylinder (Set.Icc a b)
            (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1))).restrict
              (parabolicChartDriftCoefficient (I := I) G.metric x.1 k)) := by
  classical
  obtain ⟨s, r, R, Rext, hradii, hchart, hcover⟩ :=
    exists_finite_buffered_euclidean_chart_cover (E := E) (I := I) (M := M)
  let center : ↥s → M := fun x ↦ x.1
  let K : ↥s → Set E := fun x ↦
    (toEuclidean (E := E)).symm ''
      Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)
  have hK : ∀ x : ↥s, IsCompact (K x) := by
    intro x
    exact (isCompact_closedBall _ _).image (toEuclidean (E := E)).symm.continuous
  have hKconv : ∀ x : ↥s, Convex Real (K x) := by
    intro x
    exact (convex_closedBall _ _).linear_image
      (toEuclidean (E := E)).symm.toLinearEquiv.toLinearMap
  have hKchart : ∀ x : ↥s,
      K x ⊆ interior (extChartAt I (center x)).target := by
    intro x
    rw [(isOpen_extChartAt_target x.1).interior_eq]
    exact hchart x.1 x.2
  obtain ⟨Apr, Ka, Bb, Kb, hAnorm, ha, hpos, hbnorm, hb⟩ :=
    exists_uniform_parabolic_chart_operator_coefficient_schauder_bounds_of_finite
      hG hab habreg center K hK hKconv hKchart halpha
  let e := (toEuclidean (E := E)).symm
  have hpreimage : ∀ x : ↥s,
      parabolicLinearPreimage (e : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K x)) =
        parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) := by
    intro x
    ext p
    constructor
    · intro hp
      rcases hp.2 with ⟨z, hz, hzp⟩
      have hzp' : e z = e p.space := hzp
      exact ⟨hp.1, e.injective hzp' ▸ hz⟩
    · intro hp
      exact ⟨hp.1, ⟨p.space, hp.2, rfl⟩⟩
  refine ⟨s, r, R, Rext, hradii, hchart, hcover,
    Apr, Ka, Bb, Kb, ?_, ?_, ?_, ?_, ?_⟩
  · intro x i j p hp
    exact hAnorm x i j p (by rw [hpreimage x]; exact hp)
  · intro x i j
    rw [← hpreimage x]
    exact ha x i j
  · intro x p hp
    exact hpos x p (by rw [hpreimage x]; exact hp)
  · intro x k p hp
    exact hbnorm x k p (by rw [hpreimage x]; exact hp)
  · intro x k
    rw [← hpreimage x]
    exact hb x k

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

end
