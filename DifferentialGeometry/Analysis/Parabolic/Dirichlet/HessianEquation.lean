import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientSourceRegularity

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

section

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_lp_differentiated_forcing
    {ν : Measure (ℝ × E)} [IsFiniteMeasure ν]
    {O P : Set (ℝ × E)} (hO : IsOpen O) (hP : IsOpen P) (hPO : P ⊆ O)
    {ρ : ℝ × E → ℝ} {A : Fin d → Fin d → ℝ × E → ℝ}
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ O)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) O)
    (hbound : ∀ f : ℝ × E → ℝ, ContinuousOn f O → MemLp f ∞ ν)
    {V : ℝ × E → ℝ} (hV : MemLp V 2 ν)
    (H : Fin d → Lp ℝ 2 ν) (K : Fin d → Fin d → Lp ℝ 2 ν)
    (R F : Lp ℝ 2 ν) (DF : Fin d → Lp ℝ 2 ν)
    (hH : ∀ i, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → (∫ p, V p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, H i p * φ p ∂ν)
    (hK : ∀ i j, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → (∫ p, H i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
        -∫ p, K i j p * φ p ∂ν)
    (hR : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → (∫ p, V p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν)
    (hDF : ∀ l, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → (∫ p, F p * fderiv ℝ φ p (0, EuclideanSpace.single l 1) ∂ν) =
        -∫ p, DF l p * φ p ∂ν)
    (hbase : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → (∫ p, ρ p * V p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ i, ∑ j, ∫ p, A i j p * H i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F p * φ p ∂ν)
    (l : Fin d) :
    ∃ S : Lp ℝ 2 ν,
      (S =ᵐ[ν] fun p => DF l p +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single l 1) * K i j p +
          fderiv ℝ (fun y => fderiv ℝ (A i j) y (0, EuclideanSpace.single l 1)) p
            (0, EuclideanSpace.single j 1) * H i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single l 1) * R p +
          fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single l 1)) p (1, 0) * V p)) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ P →
        (∫ p, ρ p * H l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i l p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S p * φ p ∂ν := by
  classical
  let DA := fun i j p => fderiv ℝ (A i j) p (0, EuclideanSpace.single l 1)
  let DDA := fun i j p => fderiv ℝ (DA i j) p (0, EuclideanSpace.single j 1)
  let Dρ := fun p => fderiv ℝ ρ p (0, EuclideanSpace.single l 1)
  let TDρ := fun p => fderiv ℝ Dρ p (1, 0)
  have hDA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (DA i j) O :=
    ((hA i j).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hDDA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (DDA i j) O :=
    ((hDA i j).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hDρ : ContDiffOn ℝ (⊤ : ℕ∞) Dρ O :=
    (hρ.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hTDρ : ContDiffOn ℝ (⊤ : ℕ∞) TDρ O :=
    (hDρ.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  let B := fun i j p => DA i j p * K i j p + DDA i j p * H i p
  let C := fun p => Dρ p * R p + TDρ p * V p
  have hB (i j) : MemLp (B i j) 2 ν :=
    ((Lp.memLp (K i j)).mul (hbound _ (hDA i j).continuousOn)).add
      ((Lp.memLp (H i)).mul (hbound _ (hDDA i j).continuousOn))
  have hC : MemLp C 2 ν := ((Lp.memLp R).mul (hbound _ hDρ.continuousOn)).add
    (hV.mul (hbound _ hTDρ.continuousOn))
  let s := fun p => DF l p + (∑ i, ∑ j, B i j p) - C p
  have hsum : MemLp (fun p => ∑ i, ∑ j, B i j p) 2 ν :=
    by
    exact memLp_finsetSum Finset.univ (fun i _ => memLp_finsetSum Finset.univ (fun j _ => hB i j))
  have hs : MemLp s 2 ν := ((Lp.memLp (DF l)).add hsum).sub hC
  refine ⟨hs.toLp s, hs.coeFn_toLp, ?_⟩
  intro φ hφ hφc hφs
  have hbase' : ∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ P → (∫ p, ρ p * V p * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ ij : Fin d × Fin d, ∫ p, A ij.1 ij.2 p * H ij.1 p *
          fderiv ℝ ψ p (0, EuclideanSpace.single ij.2 1) ∂ν) - ∫ p, F p * ψ p ∂ν := by
    simpa only [Fintype.sum_prod_type] using hbase
  have hcomm := Sobolev.integral_weak_deriv_weighted_divergence Finset.univ hP
    (0, EuclideanSpace.single l 1) (1, 0)
    (fun ij : Fin d × Fin d => (0, EuclideanSpace.single ij.2 1))
    (hV.locallyIntegrable (by norm_num)) ((Lp.memLp (H l)).locallyIntegrable (by norm_num))
    ((Lp.memLp R).locallyIntegrable (by norm_num))
    (fun ij _ => (Lp.memLp (H ij.1)).locallyIntegrable (by norm_num))
    (fun ij _ => (Lp.memLp (K ij.1 l)).locallyIntegrable (by norm_num))
    (hρ.mono hPO) (fun ij _ => (hA ij.1 ij.2).mono hPO) (hH l) hR
    (fun ij _ => hK ij.1 l) hbase' hφ hφc hφs
  simp only [Fintype.sum_prod_type] at hcomm
  have hφLp : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hφc ν
  have hint (f : ℝ × E → ℝ) (hf : MemLp f 2 ν) : Integrable (fun p => f p * φ p) ν :=
    (hφLp.mul (r := 2) hf).integrable (by norm_num)
  have hdmem (j) : MemLp (fun p => fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∞ ν :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
  have hmainI (i j) : Integrable (fun p => A i j p * K i l p *
      fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
    ((hdmem j).mul (r := 2) ((Lp.memLp (K i l)).mul (r := 2)
      (hbound _ (hA i j).continuousOn))).integrable (by norm_num)
  have herrI (i j) : Integrable (fun p => DA i j p * H i p *
      fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
    ((hdmem j).mul (r := 2) ((Lp.memLp (H i)).mul (r := 2)
      (hbound _ (hDA i j).continuousOn))).integrable (by norm_num)
  have hsplit (i j) : (∫ p, (A i j p * K i l p + DA i j p * H i p) *
      fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
      (∫ p, A i j p * K i l p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
        ∫ p, B i j p * φ p ∂ν := by
    have hp := Sobolev.integral_weak_product_deriv hP (0, EuclideanSpace.single j 1)
      ((Lp.memLp (H i)).locallyIntegrable (by norm_num))
      ((Lp.memLp (K i j)).locallyIntegrable (by norm_num)) ((hDA i j).mono hPO)
      (hK i j) hφ hφc hφs
    simp_rw [add_mul]
    rw [integral_add (hmainI i j) (herrI i j), hp]
    rfl
  have hsumB : (∫ p, (∑ i, ∑ j, B i j p) * φ p ∂ν) =
      ∑ i, ∑ j, ∫ p, B i j p * φ p ∂ν := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint _ (hB i j)))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hint _ (hB i j))
  have hseq : (∫ p, hs.toLp s p * φ p ∂ν) =
      (∫ p, DF l p * φ p ∂ν) + (∑ i, ∑ j, ∫ p, B i j p * φ p ∂ν) - ∫ p, C p * φ p ∂ν := by
    have heq : (∫ p, hs.toLp s p * φ p ∂ν) = ∫ p, s p * φ p ∂ν := by
      apply integral_congr_ae
      filter_upwards [hs.coeFn_toLp] with p hp
      rw [hp]
    rw [heq]
    simp only [s, sub_mul, add_mul]
    have hsumI : Integrable (fun p => DF l p * φ p + (∑ i, ∑ j, B i j p) * φ p) ν :=
      (hint _ (Lp.memLp (DF l))).add (hint _ hsum)
    rw [integral_sub hsumI (hint _ hC),
      integral_add (hint _ (Lp.memLp (DF l))) (hint _ hsum), hsumB]
  change (∫ p, ρ p * H l p * fderiv ℝ φ p (1, 0) ∂ν) = _
  change _ = (∑ i, ∑ j, ∫ p, (A i j p * K i l p + DA i j p * H i p) *
    fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) + _ + ∫ p, C p * φ p ∂ν at hcomm
  simp_rw [hsplit, Finset.sum_sub_distrib] at hcomm
  rw [hDF l φ hφ hφc hφs] at hcomm
  linarith

end

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem IsWeakEvolutionSolution.exists_lp_weak_hessian_equation
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ ≤ t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i j, H i j = H j i) ∧
      (∀ k, F k =ᵐ[ν] fun p => ∑ s,
        gradientSourceCoefficient ρ A C C₀ k s p *
          gradientSourceField (fun p => U p) (fun i p => V i p)
            (fun i j p => H i j p) (fun p => R p) k s p) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν) ∧
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ DF : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
          (fun z => K i j l (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
        (∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DR j (t, z)) (fun z => R (t, z)) Ω₀) ∧
        (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DF k j (t, z)) (fun z => F k (t, z)) Ω₀) ∧
        (∀ k j, DF k j =ᵐ[ν] fun p => ∑ s,
          (gradientSourceCoefficient ρ A C C₀ k s p *
            gradientSourceField (fun p => V j p) (fun i p => H i j p)
              (fun i l p => K i l j p) (fun p => DR j p) k s p +
            fderiv ℝ (fun x => gradientSourceCoefficient ρ A C C₀ k s (p.1, x)) p.2
              (EuclideanSpace.single j 1) *
              gradientSourceField (fun p => U p) (fun i p => V i p)
                (fun i l p => H i l p) (fun p => R p) k s p)) ∧
        (∀ k, ∀ᵐ t ∂μ, MemWkp 1 2 (fun x => F k (t, x)) Ω₀) ∧
        (∀ k, MemLp (fun t => (iteratedWeakSobolevNorm 1 2
          (fun x => F k (t, x)) Ω₀).toReal) 2 μ) ∧
        (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
          (∫ p, V k p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DR k p * φ p ∂ν) ∧
        (∀ k i l, K k i l = K k l i) ∧
        ∃ S : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
          (∀ k l, S k l =ᵐ[ν] fun p => DF k l p +
            (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single l 1) * K k i j p +
              fderiv ℝ (fun y => fderiv ℝ (A i j) y (0, EuclideanSpace.single l 1)) p
                (0, EuclideanSpace.single j 1) * H k i p)) -
            (fderiv ℝ ρ p (0, EuclideanSpace.single l 1) * DR k p +
              fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single l 1)) p (1, 0) * V k p)) ∧
          ∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
            (∫ p, ρ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
              (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
                fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k l p * φ p ∂ν := by
  intro μ ν ρ A U V B τ C C₀
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hFormula, hF, K, DR, DF,
    hK, hDR, hDF, hDFformula, hFW, hFLp⟩ :=
    hu.exists_lp_weak_gradient_equation_with_source_spatial_derivative hXcont hacont
      α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => V i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hsecond (k i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => H k i (t, z)) (fun z => V k (t, z)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [hH k i, hc] with t ht hct
    exact hasWeakPartialDeriv_congr_ae hΩ₀ i
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub hct)) ht
  have hspace (i) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, V i p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hU.locallyIntegrable (by norm_num)) ((hV i).locallyIntegrable (by norm_num)) i
      (hfirst i) φ hφ hφc (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have htime (k) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, V k p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DR k p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have hc := Sobolev.integral_weak_deriv_fderiv_comm
      (0, EuclideanSpace.single k 1) (1, 0) (hspace k) hR hφ hφc hφs
    exact hc.trans (integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp R).locallyIntegrable (by norm_num))
      ((Lp.memLp (DR k)).locallyIntegrable (by norm_num)) k (hDR k) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl)))
  have hKsym (k i l) : K k i l = K k l i := by
    apply Lp.ext
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (K k i l)).measurable
        (Lp.stronglyMeasurable (K k l i)).measurable)).mpr
    filter_upwards [hH k i, hH k l, hK k i l, hK k l i,
      (Lp.memLp (K k i l)).prodMk_left (by norm_num),
      (Lp.memLp (K k l i)).prodMk_left (by norm_num)] with t hi hl hil hli hilLp hliLp
    exact Sobolev.ae_eq_of_weak_second_deriv_comm hΩ₀ (ae_restrict_mem hΩ₀.measurableSet)
      (EuclideanSpace.single i 1) (EuclideanSpace.single l 1) hi hl hil hli
      (hilLp.locallyIntegrable (by norm_num)) (hliLp.locallyIntegrable (by norm_num))
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hAall (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ Ω) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α
      (subset_closure.trans hΩs) i j
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : MemLp f ∞ ν := by
    have hb := (hc.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hPO : Ioo t₀ t₁ ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω :=
    prod_mono (fun t ht => hreg ⟨ht₀.le.trans ht.1.le, ht.2.le.trans ht₁.le⟩) hsub
  have hHint (k i) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, V k p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, H k i p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((hV k).locallyIntegrable (by norm_num))
      ((Lp.memLp (H k i)).locallyIntegrable (by norm_num)) i (hsecond k i) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hKint (k i j) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, H k i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
        -∫ p, K k i j p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp (H k i)).locallyIntegrable (by norm_num))
      ((Lp.memLp (K k i j)).locallyIntegrable (by norm_num)) j (hK k i j) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hDFint (k l) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, F k p * fderiv ℝ φ p (0, EuclideanSpace.single l 1) ∂ν) =
        -∫ p, DF k l p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp (F k)).locallyIntegrable (by norm_num))
      ((Lp.memLp (DF k l)).locallyIntegrable (by norm_num)) l (hDF k l) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  choose S hSformula hS using fun k l => exists_lp_differentiated_forcing
    (D.regular_isOpen.prod hΩ) (isOpen_Ioo.prod hΩ₀) hPO hρall hAall hlift
    (hV k) (H k) (K k) (DR k) (F k) (DF k) (hHint k) (hKint k) (htime k)
    (hDFint k) (hF k) l
  refine ⟨R, H, F, hR, hH, hHsym, hFormula, hF, K, DR, DF, hK, hDR, hDF,
    hDFformula, hFW, hFLp, htime, hKsym, S, hSformula, ?_⟩
  intro k l φ hφ hφc hφs
  simpa only [hKsym k _ l] using hS k l φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
