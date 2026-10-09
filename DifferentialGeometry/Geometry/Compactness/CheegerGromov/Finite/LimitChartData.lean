import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.SmoothCarrier
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LimitChartGlue
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CarrierChart

/-!
# I-LIM: the finite-regularity limit chart data on the smooth carrier (LFR14 steps 1–3)

Blueprint 207A, LFR14 (Theorem 13.97, A:25869–26084), steps 1–3 together with the LFR01 carrier,
in the shape the patching kernels of step 4 consume (frozen interface I-LIM of
`build-logs/scratch/D-LFR14/Interfaces.lean`).

The proof binds the ported theorem `exists_pointed_smooth_carrier_limit_of_curvature_bounds`
(`Limit/SmoothCarrier.lean`) to the aligned block of chapter 13:
* the sources are the aligned pointed manifolds `{ M := X i, basepoint := p i, metric := g i }`
  (completeness from `metricComplete_aligned`; their Riemannian metric space is the given one,
  `riemMetricSpace_aligned_eq`);
* the limit is the smooth carrier `N := SmoothCarrier 𝒜` with the carrier metric `G'`;
* `σ a := carrierChartParam 𝒜 (ψ a) …` (order `K`, partial equivalence that of `ψ a`),
  `d a i := Φ a (τ i)`, `D a := ball 0 (a_j)`, the subsequence is `φ ∘ ν ∘ τ`;
* the pointed ball approximations are those of the theorem along `τ`, read with the given metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

/-- **I-LIM.** The limit of LFR14 steps 1–3 on its smooth carrier `N`: the countable limit chart
parametrizations `σ a` (order `K`), the actual smooth normal charts `d a i` of the sources, the
convex buffers `D a`, the `C^K` transition convergence, the `C^{K-1}` coefficient limits `b a`
(= `G` in `σ a` coordinates), and the pointed ball approximations `F i : X (φ i) → N` with the
chart capture. -/
theorem exists_finite_limit_chart_data
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (Q : ∀ i, X i → (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)))
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (σ : Option (ℕ × ℕ) → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) N K)
        (d : Option (ℕ × ℕ) → ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) (X (φ i)) ∞)
        (D : Option (ℕ × ℕ) → Set (EuclideanSpace ℝ (Fin n)))
        (b : Option (ℕ × ℕ) → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i)),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
        (∀ x : N, ∃ a, x ∈ (σ a).target) ∧
        0 ∈ (σ none).source ∧ σ none 0 = q ∧ (∀ i, d none i 0 = p (φ i)) ∧
        (∀ a, IsOpen (D a) ∧ Convex ℝ (D a) ∧ (σ a).source ⊆ D a ∧ ∀ i, D a ⊆ (d a i).source) ∧
        (∀ a c (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ ((σ a).trans (σ c).symm).source →
          MapCPConvergenceOn L K (fun i x => (d c i).symm (d a i x)) ((σ a).trans (σ c).symm) ∧
          ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d c i).symm).source) ∧
        (∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (D a) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ D a →
            MapCPConvergenceOn S (K - 1)
              (fun i => pullbackMetricCoefficients (g (φ i)) (d a i)) (b a)) ∧
        (∀ a, ∀ u ∈ (σ a).source, ∀ v w : EuclideanSpace ℝ (Fin n),
          G.inner (σ a u)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (σ a) u v)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (σ a) u w) =
          b a u v w) ∧
        (∀ a (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L → L ⊆ (σ a).source →
          (∀ᶠ i in atTop, MapsTo (d a i) L (closedBall (p (φ i)) (R i))) ∧
          TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (d a i u)) (σ a) atTop L) := by
  classical
  obtain ⟨rad, C, hrad, hC, hmain⟩ :=
    exists_pointed_smooth_carrier_limit_of_curvature_bounds.{u} n K hn hK hr hv A hA
  let P : ℕ → PointedRiemannianManifold.{u} 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) := fun i =>
    { M := X i, basepoint := p i, metric := g i }
  have hcomplete : ∀ i, MetricComplete (P i) := fun i =>
    metricComplete_aligned (g i) (hmetric i) (p i)
  have hconn : ∀ i, letI : TopologicalSpace (P i).M := (P i).topology; ConnectedSpace (P i).M :=
    fun i => inferInstanceAs (ConnectedSpace (X i))
  obtain ⟨φ, Y, m, hφ, hYp, hYc, hYpc, hYconn, q, hGH, hlen, hseg, ν, R, ε, F, hν, hR, hε, qq, z,
    Φ, τ, gg, ψ, hcover, b, hq, hΦ0, hτ, hU, h5, h6, h7, h8, h9, hM, G, hGb, hRG, 𝒜, κ, hrest⟩ :=
    hmain P hcomplete hconn Q hvol hcurv
  obtain ⟨hchart, -, hreg, -, -, -, ⟨f, hf, -⟩, -, -, G', hG', hblock⟩ := hrest
  have hRiemN := hblock.2.2.2.2.2.2
  have : ProperSpace Y := hYp
  have : ConnectedSpace Y := hYconn
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  -- the per-chart clauses of the theorem
  have hψsrc : ∀ j, (ψ j).source = ball 0 (rad (j.elim 0 Prod.fst) / 16) := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h5 j
    exact h
  have hψ0 : ∀ j, ψ j 0 = qq j := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h5 j
    exact h
  have hΦsrc : ∀ j i, (Φ j i).source = ball 0 (2 * rad (j.elim 0 Prod.fst)) := fun j i =>
    ((h5 j).2.2.2.2.1 i).1
  -- the ball approximations, read with the given metric and post-composed with `ofBase`
  have hFex := fun i => exists_pointedBallApprox_of_metricSpace_eq
    (riemMetricSpace_aligned_eq (g (φ (ν (τ i)))) (hmetric (φ (ν (τ i))))) (F (τ i))
  choose F₁ hF₁ using hFex
  let σ : Option (ℕ × ℕ) → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) (SmoothCarrier 𝒜) K :=
    fun a => carrierChartParam 𝒜 (ψ a) a (κ a) (hchart a) (hreg a).1 (hreg a).2
  refine ⟨fun i => φ (ν (τ i)), hφ.comp (hν.comp hτ), SmoothCarrier 𝒜, inferInstance,
    inferInstance, inferInstance, G', SmoothCarrier.ofBase 𝒜 q, σ, fun a i => Φ a (τ i),
    fun a => ball 0 (rad (a.elim 0 Prod.fst)), b, fun i => R (τ i), fun i => ε (τ i),
    fun i => (F₁ i).mapTargetIsometry (smoothCarrierOfBaseIsometryEquiv 𝒜),
    inferInstance, inferInstanceAs (ConnectedSpace Y), hRiemN, ?_,
    hR.comp hτ.tendsto_atTop, hε.comp hτ.tendsto_atTop, fun x => hcover x, ?_, ?_,
    fun i => hΦ0 (τ i), ?_, ?_, ?_, ?_, ?_⟩
  · -- pointed Gromov–Hausdorff convergence along `ν ∘ τ`, read with the given metrics
    exact pointedGHConverges_comp_of_metricSpace_eq
      (fun i => riemMetricSpace_aligned_eq (g (φ i)) (hmetric (φ i))) (hν.comp hτ) hGH
  · change (0 : EuclideanSpace ℝ (Fin n)) ∈ (ψ none).source
    rw [hψsrc none]
    exact mem_ball_self (div_pos (hrad _) (by norm_num))
  · change SmoothCarrier.ofBase 𝒜 (ψ none 0) = SmoothCarrier.ofBase 𝒜 q
    rw [hψ0 none, hq]
  · intro a
    refine ⟨isOpen_ball, convex_ball _ _, ?_, fun i => ?_⟩
    · change (ψ a).source ⊆ _
      rw [hψsrc a]
      exact ball_subset_ball (by linarith [hrad (a.elim 0 Prod.fst)])
    · change _ ⊆ (Φ a (τ i)).source
      rw [hΦsrc a (τ i)]
      exact ball_subset_ball (by linarith [hrad (a.elim 0 Prod.fst)])
  · intro a c L hL hLsub
    have hLsub' : L ⊆ ((ψ a).trans (ψ c).symm).source := by
      rw [← (carrierChartParam_trans_symm 𝒜 (ψ a) (ψ c) a c (κ a) (κ c) (hchart a) (hchart c)
        (hreg a).1 (hreg a).2 (hreg c).1 (hreg c).2).1]
      exact hLsub
    obtain ⟨hconv, s, hs0, hs1, hev⟩ := (h7 a c).2 L hL hLsub'
    exact ⟨hconv, hev.mono fun i hi => hi.1⟩
  · intro a
    exact ⟨(h6 a).1, fun S hS hSD => (h6 a).2.2.2 S hS hSD⟩
  · intro a u hu v w
    let _ := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
    let _ := hM
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 Y :=
      IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
    have hT : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (SmoothCarrier.toBase 𝒜) := by
      rw [← hf]
      exact f.mdifferentiable hK0
    exact carrierChartParam_inner 𝒜 hK (ψ a) a (κ a) (hchart a) (hreg a).1 (hreg a).2
      (by exact ⟨a, rfl⟩) hT G.inner G'.inner (b a) (fun x hx v w => hGb a x hx v w) hG' hu v w
  · intro a L hL hLsrc
    obtain ⟨-, -, -, -, -, -, -, -, -, hcap, hunif, -, hsrc, -, -, -, -, hψg⟩ := h5 a
    have hLball : ∀ u ∈ L,
        u ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (rad (a.elim 0 Prod.fst) / 16) := by
      intro u hu
      rw [← hsrc]
      exact hLsrc hu
    have hLcb : ∀ u ∈ L,
        u ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (rad (a.elim 0 Prod.fst) / 8) :=
      fun u hu => closedBall_subset_closedBall (by linarith [hrad (a.elim 0 Prod.fst)])
        (ball_subset_closedBall (hLball u hu))
    refine ⟨?_, ?_⟩
    · filter_upwards [hcap] with i hi
      intro u hu
      exact (closedBall_eq_of_metricSpace_eq
        (riemMetricSpace_aligned_eq (g (φ (ν (τ i)))) (hmetric (φ (ν (τ i))))) _ _).subset
          (hi ⟨u, hLcb u hu⟩)
    · have key := hunif.comp (fun u : L => (⟨u, hLcb u u.2⟩ :
          closedBall (0 : EuclideanSpace ℝ (Fin n)) (rad (a.elim 0 Prod.fst) / 8)))
      have e2 : ((σ a) ∘ Subtype.val : L → SmoothCarrier 𝒜) =
          fun u : L => smoothCarrierOfBaseIsometryEquiv 𝒜 (gg a ⟨u, hLcb u u.2⟩) :=
        funext fun u => congrArg (smoothCarrierOfBaseIsometryEquiv 𝒜) (hψg ⟨u, hLball u u.2⟩)
      have key₁ : TendstoUniformly
          (fun i (x : L) => (F₁ i).extendToWholeSpace (Φ a (τ i) (x : EuclideanSpace ℝ (Fin n))))
          (fun x : L => gg a ⟨x, hLcb x x.2⟩) atTop :=
        tendstoUniformly_comp_congr _ (fun i => (F₁ i).extendToWholeSpace)
          (fun i => (hF₁ i).symm) (fun i (x : L) => Φ a (τ i) (x : EuclideanSpace ℝ (Fin n))) key
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, e2]
      exact tendstoUniformly_comp_congr
        (fun i y => smoothCarrierOfBaseIsometryEquiv 𝒜 ((F₁ i).extendToWholeSpace y))
        (fun i => ((F₁ i).mapTargetIsometry (smoothCarrierOfBaseIsometryEquiv 𝒜)).extendToWholeSpace)
        (fun i => funext fun y => (extendToWholeSpace_mapTargetIsometry _ _ y).symm)
        (fun i (x : L) => Φ a (τ i) (x : EuclideanSpace ℝ (Fin n)))
        ((smoothCarrierOfBaseIsometryEquiv 𝒜).isometry.uniformContinuous.comp_tendstoUniformly
          key₁)

end DifferentialGeometry.CheegerGromovCompactness
