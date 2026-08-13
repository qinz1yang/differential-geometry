import DifferentialGeometry.Analysis.Schauder.EvolvingMetric
import DifferentialGeometry.Analysis.Schauder.ParabolicBallExtension

noncomputable section

open Matrix Set
open scoped ContDiff ENNReal Manifold NNReal

namespace DifferentialGeometry.Analysis.Schauder

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

omit [FiniteDimensional Real E] in
theorem contDiffOn_potential_in_extChart_of_contMDiffOn
    (V : Real → M → Real) (J : Set Real) (chartCenter : M)
    (hV : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
      (fun p : Real × M ↦ V p.1 p.2) (J ×ˢ Set.univ)) :
    ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (J ×ˢ interior (extChartAt I chartCenter).target) := by
  let Ψ : Real × E → Real × M :=
    fun p ↦ (p.1, (extChartAt I chartCenter).symm p.2)
  have hΨ : ContMDiffOn (𝓘(Real, Real).prod 𝓘(Real, E))
      (𝓘(Real, Real).prod I) 1 Ψ
      (J ×ˢ interior (extChartAt I chartCenter).target) := by
    refine ContMDiffOn.prodMk contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt_symm (I := I) (n := 1) chartCenter).comp
      contMDiffOn_snd ?_
    intro p hp
    exact Set.mem_preimage.mpr (interior_subset hp.2)
  have hmaps : Set.MapsTo Ψ
      (J ×ˢ interior (extChartAt I chartCenter).target)
      (J ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hcomp := hV.comp hΨ hmaps
  have hcomp' : ContMDiffOn (𝓘(Real, Real).prod 𝓘(Real, E))
      𝓘(Real, Real) 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (J ×ˢ interior (extChartAt I chartCenter).target) := by
    simpa only [Ψ, Function.comp_apply] using hcomp
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod]
  exact hcomp'

omit [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
theorem exists_parabolicChartPotentialCoefficient_schauder_bounds
    (V : Real → M → Real) (a b : Real) (chartCenter : M)
    {K : Set E} (hK : IsCompact K) (hKconv : Convex Real K)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ K))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Bc Kc : NNReal,
      (∀ p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K) →
        ‖parabolicChartPotentialCoefficient (I := I) V chartCenter p‖ ≤ Bc) ∧
      HolderWith Kc alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K)).restrict
            (parabolicChartPotentialCoefficient (I := I) V chartCenter)) := by
  obtain ⟨Bc, Kc, hnorm, hholder⟩ :=
    exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hV halpha
  let L := ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
  let Kc' : NNReal := Kc * (max 1 ‖L‖₊) ^ (alpha : Real)
  refine ⟨Bc, Kc', ?_, ?_⟩
  · intro p hp
    have h := hnorm (parabolicLinearMap L p) hp
    simpa only [L, parabolicChartPotentialCoefficient,
      euclideanChartPoint, Function.comp_apply, parabolicLinearMap_time,
      parabolicLinearMap_space, parabolicToProduct] using h
  · have h := parabolicHolder_linearMap L hholder
    simpa only [L, Kc', parabolicChartPotentialCoefficient,
      euclideanChartPoint, Function.comp_apply, parabolicLinearMap_time,
      parabolicLinearMap_space, parabolicToProduct] using h

end DifferentialGeometry.Analysis.Schauder

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Analysis.Schauder

universe v vE vH

variable {E : Type vE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type vH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclM (E : Type vE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem exists_uniform_parabolic_chart_nondivergence_operator_coefficient_schauder_bounds_of_finite
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    {Achart : Type*} [Finite Achart]
    (chartCenter : Achart → M) (K : Achart → Set E)
    (hK : ∀ r, IsCompact (K r))
    (hKconv : ∀ r, Convex Real (K r))
    (hKchart : ∀ r, K r ⊆ interior (extChartAt I (chartCenter r)).target)
    (V : Real → M → Real)
    (hV : ∀ r, ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I (chartCenter r)).symm p.2))
      (Set.Icc a b ×ˢ K r))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Apr Ka : Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → NNReal,
      ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      ∃ Bc Kc : NNReal,
      (∀ r i j p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPrincipalCoefficient (I := I) G.metric
          (chartCenter r) i j p‖ ≤ Apr i j) ∧
      (∀ r i j, HolderWith (Ka i j) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPrincipalCoefficient (I := I) G.metric
              (chartCenter r) i j))) ∧
      (∀ r p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          parabolicChartPrincipalCoefficient (I := I) G.metric
            (chartCenter r) i j p).PosDef) ∧
      (∀ r k p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartDriftCoefficient (I := I) G.metric
          (chartCenter r) k p‖ ≤ Bb k) ∧
      (∀ r k, HolderWith (Kb k) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartDriftCoefficient (I := I) G.metric
              (chartCenter r) k))) ∧
      (∀ r p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPotentialCoefficient (I := I) V
          (chartCenter r) p‖ ≤ Bc) ∧
      ∀ r, HolderWith Kc alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPotentialCoefficient (I := I) V
              (chartCenter r))) := by
  classical
  letI := Fintype.ofFinite Achart
  obtain ⟨Apr, Ka, Bb, Kb, hAnorm, ha, hpos, hbnorm, hb⟩ :=
    exists_uniform_parabolic_chart_operator_coefficient_schauder_bounds_of_finite
      hG hab habreg chartCenter K hK hKconv hKchart halpha
  have hpotential : ∀ r : Achart, ∃ Bcr Kcr : NNReal,
      (∀ p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPotentialCoefficient (I := I) V
          (chartCenter r) p‖ ≤ Bcr) ∧
      HolderWith Kcr alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPotentialCoefficient (I := I) V
              (chartCenter r))) := by
    intro r
    exact DifferentialGeometry.Analysis.Schauder.exists_parabolicChartPotentialCoefficient_schauder_bounds
      V a b (chartCenter r) (hK r) (hKconv r) (hV r) halpha
  choose Bcr Kcr hpotential using hpotential
  let Bc : NNReal := ∑ r, Bcr r
  let Kc : NNReal := ∑ r, Kcr r
  refine ⟨Apr, Ka, Bb, Kb, Bc, Kc, hAnorm, ha, hpos, hbnorm, hb, ?_, ?_⟩
  · intro r p hp
    exact (hpotential r).1 p hp |>.trans
      (Finset.single_le_sum (fun s _ ↦ zero_le (Bcr s)) (Finset.mem_univ r))
  · intro r
    exact (hpotential r).2.mono
      (Finset.single_le_sum (fun s _ ↦ zero_le (Kcr s)) (Finset.mem_univ r))

theorem exists_parabolic_chart_nondivergence_operator_coefficient_schauder_bounds_on_closedBall
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) (center : EuclM E) (R : Real)
    (hchart : ((toEuclidean (E := E)).symm : EuclM E → E) ''
      Metric.closedBall center R ⊆ interior (extChartAt I chartCenter).target)
    (V : Real → M → Real)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall center R)))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Apr Ka : Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → NNReal,
      ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      ∃ Bc Kc : NNReal,
      (∀ i j p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        ‖parabolicChartPrincipalCoefficient (I := I) G.metric
          chartCenter i j p‖ ≤ Apr i j) ∧
      (∀ i j, HolderWith (Ka i j) alpha
        ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R)).restrict
            (parabolicChartPrincipalCoefficient (I := I) G.metric
              chartCenter i j))) ∧
      (∀ p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          parabolicChartPrincipalCoefficient (I := I) G.metric
            chartCenter i j p).PosDef) ∧
      (∀ k p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        ‖parabolicChartDriftCoefficient (I := I) G.metric
          chartCenter k p‖ ≤ Bb k) ∧
      (∀ k, HolderWith (Kb k) alpha
        ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R)).restrict
            (parabolicChartDriftCoefficient (I := I) G.metric
              chartCenter k))) ∧
      (∀ p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        ‖parabolicChartPotentialCoefficient (I := I) V
          chartCenter p‖ ≤ Bc) ∧
      HolderWith Kc alpha
        ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R)).restrict
            (parabolicChartPotentialCoefficient (I := I) V chartCenter)) := by
  let e := (toEuclidean (E := E)).symm
  let K := e '' Metric.closedBall center R
  have hK : IsCompact K := (isCompact_closedBall center R).image e.continuous
  have hKconv : Convex Real K :=
    (convex_closedBall center R).linear_image e.toLinearEquiv.toLinearMap
  have hpreimage : parabolicLinearPreimage
      (e : EuclM E →L[Real] E)
      (parabolicCylinder (Set.Icc a b) K) =
        parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) := by
    ext p
    constructor
    · intro hp
      rcases hp.2 with ⟨x, hx, hxp⟩
      have hxp' : e x = e p.space := hxp
      exact ⟨hp.1, e.injective hxp' ▸ hx⟩
    · intro hp
      exact ⟨hp.1, ⟨p.space, hp.2, rfl⟩⟩
  obtain ⟨Apr, Ka, hAnorm, ha, hpos⟩ :=
    exists_parabolicChartPrincipalCoefficient_schauder_bounds
      hG a b habreg chartCenter hK hKconv (by simpa only [K, e] using hchart)
        halpha
  obtain ⟨Bb, Kb, hbnorm, hb⟩ :=
    exists_parabolicChartDriftCoefficient_schauder_bounds
      hG hab habreg chartCenter hK hKconv (by simpa only [K, e] using hchart)
        halpha
  obtain ⟨Bc, Kc, hcnorm, hc⟩ :=
    DifferentialGeometry.Analysis.Schauder.exists_parabolicChartPotentialCoefficient_schauder_bounds
      V a b chartCenter hK hKconv (by simpa only [K, e] using hV) halpha
  refine ⟨Apr, Ka, Bb, Kb, Bc, Kc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [e, hpreimage] using hAnorm
  · intro i j
    rw [← hpreimage]
    simpa only [e] using ha i j
  · simpa only [e, hpreimage] using hpos
  · simpa only [e, hpreimage] using hbnorm
  · intro k
    rw [← hpreimage]
    simpa only [e] using hb k
  · simpa only [e, hpreimage] using hcnorm
  · rw [← hpreimage]
    simpa only [e] using hc

theorem exists_finite_buffered_chart_cover_with_uniform_parabolic_nondivergence_operator_coefficient_schauder_bounds
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (V : Real → M → Real)
    (hV : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
      (fun p : Real × M ↦ V p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
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
        ∃ Bc Kc : NNReal,
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
            (Matrix.of fun i j : Fin (Module.finrank Real E) ↦
              parabolicChartPrincipalCoefficient (I := I) G.metric x.1 i j p).PosDef) ∧
        (∀ x : ↥s, ∀ k p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ‖parabolicChartDriftCoefficient (I := I) G.metric x.1 k p‖ ≤ Bb k) ∧
        (∀ x : ↥s, ∀ k, HolderWith (Kb k) alpha
          ((parabolicCylinder (Set.Icc a b)
            (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1))).restrict
              (parabolicChartDriftCoefficient (I := I) G.metric x.1 k))) ∧
        (∀ x : ↥s, ∀ p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ‖parabolicChartPotentialCoefficient (I := I) V x.1 p‖ ≤ Bc) ∧
        ∀ x : ↥s, HolderWith Kc alpha
          ((parabolicCylinder (Set.Icc a b)
            (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1))).restrict
              (parabolicChartPotentialCoefficient (I := I) V x.1)) := by
  classical
  obtain ⟨s, r, R, Rext, hradii, hchart, hcover,
      Apr, Ka, Bb, Kb, hAnorm, ha, hpos, hbnorm, hb⟩ :=
    exists_finite_buffered_chart_cover_with_uniform_parabolic_operator_coefficient_schauder_bounds
      hG hab habreg halpha
  let e := (toEuclidean (E := E)).symm
  let K : ↥s → Set E := fun x ↦ e ''
    Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)
  have hK : ∀ x : ↥s, IsCompact (K x) := by
    intro x
    exact (isCompact_closedBall _ _).image e.continuous
  have hKconv : ∀ x : ↥s, Convex Real (K x) := by
    intro x
    exact (convex_closedBall _ _).linear_image e.toLinearEquiv.toLinearMap
  have hKinterior : ∀ x : ↥s,
      K x ⊆ interior (extChartAt I x.1).target := by
    intro x
    rw [(isOpen_extChartAt_target x.1).interior_eq]
    exact hchart x.1 x.2
  have hpotential : ∀ x : ↥s, ∃ Bcx Kcx : NNReal,
      (∀ p, p ∈ parabolicLinearPreimage
          (e : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K x)) →
        ‖parabolicChartPotentialCoefficient (I := I) V x.1 p‖ ≤ Bcx) ∧
      HolderWith Kcx alpha
        ((parabolicLinearPreimage (e : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K x))).restrict
            (parabolicChartPotentialCoefficient (I := I) V x.1)) := by
    intro x
    have hVchart :=
      DifferentialGeometry.Analysis.Schauder.contDiffOn_potential_in_extChart_of_contMDiffOn
        V (Set.Icc a b) x.1 hV
    exact
      DifferentialGeometry.Analysis.Schauder.exists_parabolicChartPotentialCoefficient_schauder_bounds
        V a b x.1 (hK x) (hKconv x)
          (hVchart.mono (Set.prod_mono Set.Subset.rfl (hKinterior x))) halpha
  choose Bcx Kcx hpotential using hpotential
  let Bc : NNReal := ∑ x, Bcx x
  let Kc : NNReal := ∑ x, Kcx x
  have hpreimage : ∀ x : ↥s,
      parabolicLinearPreimage (e : EuclM E →L[Real] E)
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
    Apr, Ka, Bb, Kb, Bc, Kc, hAnorm, ha, hpos, hbnorm, hb, ?_, ?_⟩
  · intro x p hp
    exact (hpotential x).1 p (by rw [hpreimage x]; exact hp) |>.trans
      (Finset.single_le_sum (fun y _ ↦ zero_le (Bcx y)) (Finset.mem_univ x))
  · intro x
    rw [← hpreimage x]
    exact (hpotential x).2.mono
      (Finset.single_le_sum (fun y _ ↦ zero_le (Kcx y)) (Finset.mem_univ x))

theorem exists_finite_buffered_chart_cover_with_uniform_parabolic_nondivergence_operator_schauder_and_ellipticity_bounds
    [I.Boundaryless] [CompactSpace M] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (V : Real → M → Real)
    (hV : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
      (fun p : Real × M ↦ V p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
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
        ∃ Bc Kc : NNReal, ∃ c : Real, 0 < c ∧
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
            (Matrix.of fun i j : Fin (Module.finrank Real E) ↦
              parabolicChartPrincipalCoefficient (I := I) G.metric x.1 i j p).PosDef) ∧
        (∀ x : ↥s, ∀ p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ∀ v : EuclM E,
              c * ‖v‖ ^ 2 ≤ star v ⬝ᵥ
                ((Matrix.of fun i j : Fin (Module.finrank Real E) ↦
                  parabolicChartPrincipalCoefficient (I := I)
                    G.metric x.1 i j p) *ᵥ v)) ∧
        (∀ x : ↥s, ∀ k p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ‖parabolicChartDriftCoefficient (I := I) G.metric x.1 k p‖ ≤ Bb k) ∧
        (∀ x : ↥s, ∀ k, HolderWith (Kb k) alpha
          ((parabolicCylinder (Set.Icc a b)
            (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1))).restrict
              (parabolicChartDriftCoefficient (I := I) G.metric x.1 k))) ∧
        (∀ x : ↥s, ∀ p,
          p ∈ parabolicCylinder (Set.Icc a b)
              (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)) →
            ‖parabolicChartPotentialCoefficient (I := I) V x.1 p‖ ≤ Bc) ∧
        ∀ x : ↥s, HolderWith Kc alpha
          ((parabolicCylinder (Set.Icc a b)
            (Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1))).restrict
              (parabolicChartPotentialCoefficient (I := I) V x.1)) := by
  classical
  obtain ⟨s, r, R, Rext, hradii, hchart, hcover,
      Apr, Ka, Bb, Kb, Bc, Kc, hAnorm, ha, hpos, hbnorm, hb, hcnorm, hc⟩ :=
    exists_finite_buffered_chart_cover_with_uniform_parabolic_nondivergence_operator_coefficient_schauder_bounds
      hG hab habreg V hV halpha
  let e := (toEuclidean (E := E)).symm
  let center : ↥s → M := fun x ↦ x.1
  let K : ↥s → Set E := fun x ↦ e ''
    Metric.closedBall (toEuclidean (extChartAt I x.1 x.1)) (Rext x.1)
  have hK : ∀ x : ↥s, IsCompact (K x) := by
    intro x
    exact (isCompact_closedBall _ _).image e.continuous
  have hKconv : ∀ x : ↥s, Convex Real (K x) := by
    intro x
    exact (convex_closedBall _ _).linear_image e.toLinearEquiv.toLinearMap
  have hKchart : ∀ x : ↥s,
      K x ⊆ interior (extChartAt I (center x)).target := by
    intro x
    rw [(isOpen_extChartAt_target x.1).interior_eq]
    exact hchart x.1 x.2
  obtain ⟨c, hcpos, hlower⟩ :=
    exists_uniform_parabolic_chart_principal_coefficient_quadratic_lower_bound_of_finite
      hG hab habreg center K hK hKconv hKchart
  have hpreimage : ∀ x : ↥s,
      parabolicLinearPreimage (e : EuclM E →L[Real] E)
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
    Apr, Ka, Bb, Kb, Bc, Kc, c, hcpos, hAnorm, ha, hpos, ?_,
      hbnorm, hb, hcnorm, hc⟩
  intro x p hp v
  exact hlower x p (by rw [hpreimage x]; exact hp) v

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

end
