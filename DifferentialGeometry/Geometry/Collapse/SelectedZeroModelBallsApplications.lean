import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelBalls
import DifferentialGeometry.Geometry.Collapse.SelectedZeroPacketsOriginalBuffer

/-!
# LC80 items 1–4 at ONE selection: LCP04 with the LC58 model balls (consumer)

Master207A, LC80 (A:24719) and LCP04 (A:30123). For a sequence of closed connected Riemannian
three-manifolds `(M^α, g^α)` with a continuous positive scale `ρ_α` satisfying LC58's sequential
hypothesis (models complete, connected, `sec ≥ 0`, with proper LC21 cones), the fixed-index data
of `exists_uniform_scale_zero_model_data` are chosen pointwise (`r p = s p ρ_α(p)`, model `b p`,
the LC67 radial function `η p`) BEFORE the selection, and LCP04
(`exists_selected_zero_packets_of_original_buffer`) is applied to exactly these families. One finite
selection `J` then carries, with the SAME radius, model, cone and radial function at each index:
LC80 item 1 (disjoint balls meeting the zero stratum, tenth-radius cover), item 3 (shell splitting,
original radial coordinate, adapted coordinate from `η i`), item 4 (one end of `N_{b i}`), and
item 2: a Kleiner–Lott map at `r i` to `C_{b i}`, the radial function `η i` with all LC30 clauses,
the buffered window and LC31's cutoff, and the core/interior identification
`B(i, ρ' r i) ≃ N_{b i}` for every `ρ' ∈ [1/5, 2]`.
LCP04's constants `ε, δ', Λ'` are fixed first; then the cone error `δ < δ'`, the lower ratio
`T = 20 Λ'`, the upper ratio `V` and `α₀` (LC80's parameter order).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter Metric
open scoped Topology ContDiff Manifold NNReal ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC80 items 1–4 at one selection (LCP04 with the LC58 model balls).** Under LC58's
sequential hypothesis for closed connected Riemannian three-manifolds `(M^α, g^α)`: LCP04's
constants `ε, Λ'`, a cone error `δ`, ratios `20 Λ' = T ≤ V` and `α₀` such that for `α > α₀` there
are radii `r ∈ [T ρ_α, V ρ_α]`, models `b`, radial functions `η` (all fixed before the selection)
and ONE finite selection `J` with LCP04's conclusions (LC80 items 1, 3, 4) and, at every `i ∈ J`,
LC80 item 2: a Kleiner–Lott `δ`-map of `(M, r_i⁻¹ d, i)` to `(C_{b i}, o_{b i})`, `η i` with all
LC30 clauses, smooth near `{3/40 ≤ r_i⁻¹ d ≤ 11}`, LC31's cutoff, and `B(i, ρ' r_i) ≃ N_{b i}` for
every `ρ' ∈ [1/5, 2]`. -/
theorem exists_selected_zero_packets_with_model_balls (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1)
    {M : ℕ → Type} [∀ α, TopologicalSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [∀ α, T3Space (M α)] [∀ α, SigmaCompactSpace (M α)]
    [∀ α, ConnectedSpace (M α)] [∀ α, CompactSpace (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (ρ : ∀ α, M α → ℝ) (hρc : ∀ α, Continuous (ρ α)) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type} {N C : ι → Type} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)]
    [∀ b, IsManifold I ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, ConnectedSpace (N b)]
    [∀ b, RiemannianBundle (fun x : N b => TangentSpace I x)] [∀ b, IsRiemannianManifold I (N b)]
    [∀ b, CompleteSpace (N b)]
    [∀ b, IsContinuousRiemannianBundle E (fun x : N b => TangentSpace I x)]
    [∀ b, T2Space (TangentBundle I (N b))] [mC : ∀ b, MetricSpace (C b)]
    [∀ b, ProperSpace (C b)]
    (gN : ∀ b, SmoothRiemannianMetric I (N b)) (hgN : ∀ b, IsMetricNorm (I := I) (gN b))
    (hsecN : ∀ b x, SectionalBoundedBelowAt (gN b) x 0)
    (n : ∀ b, N b) (o : ∀ b, C b) (Hc : ∀ b, RadialConeData (o b))
    (hcone : ∀ b : ι, ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b)
        (n b) (o b) τ))
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (inducedMetricSpace (g (a (k j)))).rescale (ρ (a (k j)) (z (k j)))⁻¹
            (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        (∃ jm : ∀ j, PartialDiffeomorph I I (N b) (M (a (k j))) ∞, (∀ j, jm j (n b) = z (k j)) ∧
          ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ l,
            ((⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)) :
              Set (N b)) ⊆ (jm (l + i₀)).source,
            ∀ K : Set (⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)),
              IsCompact K → MetricCPConvergenceOn K 1
                (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i₀)) _ (hsub l)
                  (scaleMetric ((ρ (a (k (l + i₀))) (z (k (l + i₀))))⁻¹ ^ 2)
                    (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k (l + i₀))))))
                ((gN b).restrictOpen _) ((gN b).restrictOpen _)) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((inducedMetricSpace (g (a (k j)))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {e : ℝ} (he : 0 < e) (he1 : e < 1 / 40) :
    ∃ ε δ Λ' T V : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ ∧ 0 < Λ' ∧ 0 < T ∧ 20 * Λ' ≤ T ∧ T ≤ V ∧
      ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α →
      letI m := inducedMetricSpace (g α)
      ∃ (r : M α → ℝ) (hr : ∀ p, 0 < r p) (b : M α → ι) (η : M α → M α → ℝ),
        (∀ p, T * ρ α p ≤ r p ∧ r p ≤ V * ρ α p) ∧
        ∃ J : Set (M α), J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ i ∈ J, (ball i (r i) ∩
            {q | @splittingRank.{0, 0} (M α) (m.rescale (ρ α q)⁻¹ (inv_pos.mpr (hρ α q))) q β 3 = 0}
            ).Nonempty) ∧
          (∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ α q) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{0, 0} (M α) (m.rescale (ρ α q)⁻¹ (inv_pos.mpr (hρ α q))) q 1
              (β 1) ∧
            @splittingRank.{0, 0} (M α) (m.rescale (ρ α q)⁻¹ (inv_pos.mpr (hρ α q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{0, 0} (M α) (m.rescale (ρ α q)⁻¹ (inv_pos.mpr (hρ α q))) q β 3 = 0} ⊆
            ⋃ i ∈ J, ball i (r i / 10) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
              ∃ (z : Z) (F : @KleinerLottApprox (M α)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                (m.rescale (ρ α q)⁻¹ (inv_pos.mpr (hρ α q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : M α, (@KleinerLottApprox.toFun (M α)
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                  (m.rescale (ρ α q)⁻¹ (inv_pos.mpr (hρ α q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ α q)⁻¹ * (dist i x - dist i q)))) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
            let hri := hr i
            let mr := m.rescale (r i)⁻¹ (inv_pos.mpr hri)
            let gr := scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) (g α)
            let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) (g α)
              (inducedMetricSpace_hmetric (g α)) hri
            let := mr.rescale lam hlam
            letI := (mr.rescale_completeSpace_iff lam hlam).mpr
              ((m.rescale_completeSpace_iff (r i)⁻¹ (inv_pos.mpr hri)).mpr
                (inducedMetricSpace_completeSpace (g α)))
            letI := radialScaledBundle gr lam hlam
            letI := radialScaledContinuous gr lam hlam
            letI := radialScaledManifold (m := mr) gr hmr lam hlam
            let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
            let ψ := fun x => lam * (η i x - η i q)
            ∃ hEnorm : IsMetricNorm h,
              ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
                ∃ (z : Z) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                (∀ x, (κ.toFun x).fst = lam *
                  (@dist (M α) mr.toDist i x - @dist (M α) mr.toDist i q)) ∧
                ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                  ∀ w : TangentSpace I x, h.inner x w w = 1 →
                  intrinsicGeodesic h hEnorm x w (dist x y) = y →
                  |mvfderiv (I := I) ψ x w -
                    ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ) ∧
          (∀ i ∈ J, ∀ K : Set (N (b i)), IsCompact K → ∀ a₁ a₂ : N (b i),
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a₁) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a₂) →
            connectedComponentIn Kᶜ a₁ = connectedComponentIn Kᶜ a₂) ∧
          ∀ i ∈ J,
            Nonempty (@KleinerLottApprox (M α) (C (b i))
              (m.rescale (r i)⁻¹ (inv_pos.mpr (hr i))) (mC (b i)) i (o (b i)) δ) ∧
            (letI := m.rescale (r i)⁻¹ (inv_pos.mpr (hr i))
            let gR := scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) (g α)
            LipschitzWith (Real.toNNReal (1 + ε)) (η i) ∧
              (∃ O : Set (M α), IsOpen O ∧ {x : M α | 3 / 40 ≤ dist x i ∧ dist x i ≤ 11} ⊆ O ∧
                ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) O) ∧
              (∀ x, |η i x - Metric.infDist x {i}| < e) ∧
              (∀ x, x ∉ {x : M α | 1 / 20 < dist x i ∧ dist x i < 20} →
                η i x = Metric.infDist x {i}) ∧
              (∀ x y, |(η i x - Metric.infDist x {i}) - (η i y - Metric.infDist y {i})| ≤
                ε * dist x y) ∧
              (∀ x, 0 ≤ η i x) ∧ η i i = 0 ∧
              (∀ q ∈ {x : M α | 1 / 10 ≤ dist x i ∧ dist x i ≤ 10},
                1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR (η i) q) (gradFun gR (η i) q)) ∧
                  Real.sqrt (gR.inner q (gradFun gR (η i) q) (gradFun gR (η i) q)) ≤ 1 + ε) ∧
              (∀ x, η i x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x i ∧ dist x i < 2 + e) ∧
              η i ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M α | 1 / 10 ≤ dist x i ∧ dist x i ≤ 10} ∧
              (∃ O' : Set (M α), IsOpen O' ∧ η i ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
                ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) O' ∧ ∀ q ∈ O', gradFun gR (η i) q ≠ 0) ∧
              ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
                ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (η i x)) ∧
                (∀ x, annularCutoff cutoffProfile (η i x) ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, η i x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (η i x) = 1) ∧
                tsupport (fun x => annularCutoff cutoffProfile (η i x)) ⊆
                  {x : M α | 1 / 5 - e < dist x i ∧ dist x i < 9 / 10 + e} ∧
                ∀ q, Real.sqrt (gR.inner q
                  (gradFun gR (fun x => annularCutoff cutoffProfile (η i x)) q)
                  (gradFun gR (fun x => annularCutoff cutoffProfile (η i x)) q)) ≤ L * (1 + ε)) ∧
            ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I I (M α) (N (b i)) ∞,
              Ψ.source = Metric.ball i (ρ' * r i) ∧ Ψ.target = univ := by
  obtain ⟨ε, δ', Λ', hε, hεq, hδ', hΛ', hLCP⟩ :=
    exists_selected_zero_packets_of_original_buffer (E := E) (H := H) (I := I) hE hβ hβone hβζ
      hζone
  have hmdim : Module.finrank ℝ E = 2 + 1 := by rw [hE]
  obtain ⟨V, hTV, δ, hδ0, hδδ', α₀, hdata⟩ := exists_uniform_scale_zero_model_data hmdim
    (M := M) (mM := fun α => inducedMetricSpace (g α))
    (hMc := fun α => inducedMetricSpace_completeSpace (g α)) g
    (fun α => inducedMetricSpace_hmetric (g α)) ρ hρ gN hgN hsecN n o Hc hcone hmodel
    (T := 20 * Λ') hε (by linarith) hδ' he he1
  have hmodelN := fun b => model_lcp04_clauses_of_sectional_nonneg (gN b) (hgN b) (hsecN b)
  have : ∀ b, ProperSpace (N b) := fun b => (hmodelN b).1
  have hT : (0 : ℝ) < 20 * Λ' := by positivity
  refine ⟨ε, δ, Λ', 20 * Λ', V, hε, hεq, hδ0, hΛ', hT, le_rfl, hTV, α₀, fun α hα => ?_⟩
  choose s hsI hs b hbuf hKL hη h3 using hdata α hα
  let η : M α → M α → ℝ := fun p => (hη p).choose
  have hηs : ∀ p, _ := fun p => (hη p).choose_spec
  have hr : ∀ p, 0 < s p * ρ α p := fun p => mul_pos (hs p) (hρ α p)
  have hlower : ∀ p, 20 * Λ' * ρ α p ≤ s p * ρ α p :=
    fun p => mul_le_mul_of_nonneg_right (hsI p).1 (hρ α p).le
  have hupper : ∀ p, s p * ρ α p ≤ V * ρ α p :=
    fun p => mul_le_mul_of_nonneg_right (hsI p).2 (hρ α p).le
  obtain ⟨J, hfin, hdisj, hmeet, hloc, hcond⟩ := hLCP (M α) (g α) (fun i => N (b i))
    (fun i => C (b i)) (fun i => n (b i)) (fun i => o (b i)) (fun i => Hc (b i)) (fun _ => δ) η
    (fun p => s p * ρ α p) (ρ α) (hρc α) (hρ α) hT le_rfl hTV hlower hupper
  obtain ⟨hshell, hcover, hcoord, hadapt, hend⟩ := hcond fun i _ => by
    obtain ⟨-, hFO, -, -, hdiff, -⟩ := hηs i
    obtain ⟨hsmooth, hlip⟩ := radial_original_clauses_of_rescaled (I := I)
      (m := inducedMetricSpace (g α)) (hr i) hFO hdiff
    refine ⟨fun y hy => hbuf i y ?_, (hmodelN (b i)).2.1, (hmodelN (b i)).2.2,
      fun δ₁ hδ₁ hδ₁1 => ?_, hδδ', hKL i, hsmooth, hlip⟩
    · rw [inducedMetricSpace_ball]
      exact hy
    · obtain ⟨R₀, hR₀⟩ := hcone (b i) δ₁ hδ₁ hδ₁1
      exact ⟨R₀, fun R hR hRpos => hR₀ R hRpos hR⟩
  exact ⟨fun p => s p * ρ α p, hr, b, η, fun p => ⟨hlower p, hupper p⟩, J, hfin, hdisj, hmeet,
    hloc, hshell, hcover, hcoord, hadapt, hend, fun i _ => ⟨hKL i, hηs i, h3 i⟩⟩

end DifferentialGeometry.Geometry.Collapse
