import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakGradientSource

noncomputable section

open Filter MeasureTheory
open scoped BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

section

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def gradientSourceCoefficient (ρ : ℝ × E → ℝ)
    (A : Fin d → Fin d → ℝ × E → ℝ) (C : Fin d → ℝ × E → ℝ)
    (C₀ : ℝ × E → ℝ) (k : Fin d) :
    ((Fin d × Fin d) × Bool) ⊕ (Fin d × Bool) ⊕ (Bool × Bool) → ℝ × E → ℝ :=
  Sum.elim
    (fun s p => if s.2 then
      fderiv ℝ (fun z => fderiv ℝ (fun y => A s.1.1 s.1.2 (p.1, y)) z
        (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single s.1.2 1)
      else fderiv ℝ (fun z => A s.1.1 s.1.2 (p.1, z)) p.2
        (EuclideanSpace.single k 1))
    (Sum.elim
      (fun s p => if s.2 then C s.1 p
        else fderiv ℝ (fun z => C s.1 (p.1, z)) p.2 (EuclideanSpace.single k 1))
      (fun s p => if s.1 then
        if s.2 then -fderiv ℝ ρ p (0, EuclideanSpace.single k 1) else C₀ p
        else if s.2 then
          -fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)
        else fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1)))

def gradientSourceField {Q : Type*} (U : Q) (V : Fin d → Q)
    (H : Fin d → Fin d → Q) (R : Q) (k : Fin d) :
    ((Fin d × Fin d) × Bool) ⊕ (Fin d × Bool) ⊕ (Bool × Bool) → Q :=
  Sum.elim
    (fun s => if s.2 then V s.1.1 else H s.1.1 s.1.2)
    (Sum.elim (fun s => if s.2 then H s.1 k else V s.1)
      (fun s => if s.1 then if s.2 then R else V k else U))

theorem gradientSourceField_map {Q Q' : Type*} (f : Q → Q')
    (U : Q) (V : Fin d → Q) (H : Fin d → Fin d → Q) (R : Q) (k : Fin d)
    (s : ((Fin d × Fin d) × Bool) ⊕ (Fin d × Bool) ⊕ (Bool × Bool)) :
    f (gradientSourceField U V H R k s) =
      gradientSourceField (f U) (fun i => f (V i)) (fun i j => f (H i j)) (f R) k s := by
  rcases s with ⟨ij, b⟩ | (⟨i, b⟩ | ⟨a, b⟩)
  · cases b <;> rfl
  · cases b <;> rfl
  · cases a <;> cases b <;> rfl

theorem sum_gradientSourceCoefficient_mul_field
    (ρ : ℝ × E → ℝ) (A : Fin d → Fin d → ℝ × E → ℝ)
    (C : Fin d → ℝ × E → ℝ) (C₀ U R : ℝ × E → ℝ)
    (V : Fin d → ℝ × E → ℝ) (H : Fin d → Fin d → ℝ × E → ℝ)
    (k : Fin d) (p : ℝ × E) :
    (∑ s, gradientSourceCoefficient ρ A C C₀ k s p *
      gradientSourceField U V H R k s p) =
      (∑ i, ∑ j,
        (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
            (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
        (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
          C i p * H i k p)) +
        (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
          fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
        C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
    gradientSourceCoefficient, gradientSourceField, Sum.elim_inl, Sum.elim_inr,
    Bool.false_eq_true, ↓reduceIte]
  have hm : (∑ i, ∑ j,
      (fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
          (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p +
        fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p)) =
      ∑ i, ∑ j,
        (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
            (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p) := by
    simp only [add_comm]
  rw [hm]
  simp only [add_comm (C _ _ * H _ _ _)]
  ring


end

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.weak_gradient_source_eq_finite_sum
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
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
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
    ∀ (R : Lp ℝ 2 ν)
      (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν)
      (k : Fin (Module.finrank ℝ EuN)) (F : Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F p * φ p ∂ν) →
      F =ᵐ[ν] fun p => ∑ s,
        gradientSourceCoefficient ρ A C C₀ k s p *
          gradientSourceField (fun p => U p) (fun i p => V i p)
            (fun i j p => H i j p) (fun p => R p) k s p := by
  intro μ ν ρ A U V B τ C C₀ R H k F hR hH hF
  have hf := hu.weak_gradient_source_eq hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω R H k F hR hH hF
  simpa only [sum_gradientSourceCoefficient_mul_field] using hf

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
