import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderPointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteReferenceLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section

open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
private local instance : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
private local instance : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
private local instance : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
private local instance : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact
private abbrev Q := cylinderReferenceCopy.Q
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem interior_solution_of_closed_gram
    (τ : ℝ) (g : ℝ → SmoothRiemannianMetric (𝓡 3) Q)
    (hgram : ∀ (q : Q) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × Q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) q p.2 i j)
        (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet))
    (hpde : ∀ t ∈ Ioo 0 τ, ∀ (q : Q) (v w : TangentSpace (𝓡 3) q),
      HasDerivAt (fun s => (g s).inner q v w)
        (-2 * ricciTensor (g t) q v w) t)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ τ) :
    IsSolutionOn
      ({ base := { metric := g } } :
        SolutionOn (I := 𝓡 3) (M := Q) (RealTimeInterval.closedOpen a b hab)) := by
  apply solutionOn_of_joint hab g
  · intro q i j
    exact (hgram q i j).mono (Set.prod_mono_left (by
      intro t ht
      exact ⟨ha.le.trans ht.1, ht.2.le.trans hb⟩))
  · intro t ht q v w
    exact (hpde t ⟨ha.trans_le ht.1, ht.2.trans_le hb⟩ q v w).hasDerivWithinAt

theorem exists_standard_cylinder_closed_limit (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∀ (S : ℕ → StandardSolution) (x : ℕ → E3),
      Tendsto (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal)
        atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x)
            cylinderPointedReference φ,
          (∀ j : ℕ, ∃ hfit : transitionEnd + ((j : ℝ) + 1) ≤ ‖x (φ j)‖,
            Φ.partialDiffeomorph j = cylinderReferenceInitialMap
              (pointedInitialRotation (x (φ j))) ‖x (φ j)‖ ((j : ℝ) + 1) hfit) ∧
          let hsrc := standardClosedPointedMaps_sourceSigma Φ
          let htgt := standardClosedPointedMaps_targetSigma Φ
          ∃ bf : BumpFamily Φ,
          ∃ co : FlowMetricConvergenceData Φ cylinderReferenceMetric bf hsrc htgt 0 τ,
            (∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ cylinderReferenceMetric j) ∧
            StrictMono (φ ∘ co.φ) ∧
            (∀ k : ℕ,
              ∃ hfit : transitionEnd + ((co.φ k : ℝ) + 1) ≤ ‖x ((φ ∘ co.φ) k)‖,
                (Φ.compSubseq co.φ co.strictMono).partialDiffeomorph k =
                  cylinderReferenceInitialMap
                    (pointedInitialRotation (x ((φ ∘ co.φ) k)))
                    ‖x ((φ ∘ co.φ) k)‖ ((co.φ k : ℝ) + 1) hfit) ∧
            co.gInf 0 = cylinderReferenceMetric ∧
            Diffeomorph.pullbackMetricCross (co.gInf 0) cylinderReferenceCopy.equiv =
              roundCylinderMetric (E := E3) (n := 2) ∧
            (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
            (∀ (r : ℕ) (q : Q) (i j : Fin (Module.finrank ℝ E3)),
              ContinuousOn
                (fun p : ℝ × E3 => iteratedFDeriv ℝ r
                  (chartGramOnE (co.gInf p.1) q i j) p.2)
                (Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) q).target)) ∧
            (∀ (q : Q) (i j : Fin (Module.finrank ℝ E3)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                (fun p : ℝ × Q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) q p.2 i j)
                (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet)) ∧
            (∀ t ∈ Ioo 0 τ, ∀ (q : Q) (v w : TangentSpace (𝓡 3) q),
              HasDerivAt (fun s => (co.gInf s).inner q v w)
                (-2 * ricciTensor (co.gInf t) q v w) t) ∧
            (∀ (a b : ℝ) (_ha : 0 < a) (hab : a < b), b ≤ τ →
              IsSolutionOn
                ({ base := { metric := co.gInf } } :
                  SolutionOn (I := 𝓡 3) (M := Q) (RealTimeInterval.closedOpen a b hab))) ∧
            (∀ K : Set Q, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
              ∃ k₀ : ℕ, ∀ k ≥ k₀,
                K ⊆ Φ.source (co.φ k) ∧
                ∀ t ∈ Icc 0 τ,
                  (SourceDomainMetricData.ofRestrictPullback
                    (Φ := Φ) (k := co.φ k) (hsrc (co.φ k))
                    (fun _ => sourceMetricRestriction Φ cylinderReferenceMetric (co.φ k)) co.gInf).derivNormSupOn (I := 𝓡 3) K p t < ε) ∧
            (∀ K : Set Q, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
              ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ q ∈ K,
                metricDerivNorm a (co.gInf s) (co.gInf t) cylinderReferenceMetric q ≤
                  Lp * |s - t|) := by
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  intro S x hescape
  obtain ⟨φ, hφ, Φ, hcharts, hinit⟩ := exists_standard_cylinder_pointed_maps τ hτ hlt S x hescape
  let hsrc := standardClosedPointedMaps_sourceSigma Φ
  let htgt := standardClosedPointedMaps_targetSigma Φ
  have hbounds := hb S x cylinderPointedReference φ Φ hsrc htgt hinit
  have hequiv :
      ∀ j,
        letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
        letI : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
        letI : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
        letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
        letI : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
        ∀ t ∈ Icc 0 τ,
          MetricUniformEquivalentOn univ (sourceMetricRestriction Φ cylinderReferenceMetric j)
            (sourceMetric Φ hsrc htgt j t) Λ := by
    intro j
    exact (hbounds.1 j).1
  obtain ⟨bf, co, _hlower, _hcov, hzero, hcomplete, hjets, hgram, hpde, hlip⟩ :=
    exists_complete_closed_reference_limit Φ τ hτ (fun _ ht => ht) (fun _ ht => ht)
      cylinderPointedReference_complete hsrc htgt Λ hΛ hinit hequiv hbounds.2
  refine ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hφ.comp co.strictMono, ?_, hzero, ?_,
    hcomplete, hjets, hgram, hpde, ?_, ?_, hlip⟩
  · intro k
    obtain ⟨hfit, hchart⟩ := hcharts (co.φ k)
    exact ⟨hfit, hchart⟩
  · rw [hzero]
    exact pullback_cylinderReferenceMetric
  · intro a b ha hab hbτ
    exact interior_solution_of_closed_gram τ co.gInf hgram hpde a b ha hab hbτ
  · intro K hK p ε hε
    obtain ⟨kc, hkc⟩ := ofRP_supOn_convergence Φ cylinderReferenceMetric bf hsrc htgt
      0 τ co co.gInf (fun _ _ => rfl) K hK p ε hε
    obtain ⟨kg, hkg⟩ := bf.grow_cover K hK
    refine ⟨max kc kg, ?_⟩
    intro k hk
    have hkg' : K ⊆ bf.grow (co.φ k) :=
      hkg (co.φ k) (((le_max_right kc kg).trans hk).trans (co.strictMono.id_le k))
    exact ⟨hkg'.trans (bf.grow_subset (co.φ k)),
      fun t ht => hkc k ((le_max_left kc kg).trans hk) t ht⟩

end DifferentialGeometry.PDE.RicciFlow
