import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IntegralBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap


def arcLength (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (p q t : ℝ) : ℝ :=
  ∫ x in p..q, c.speed g x t

def arcTotalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (p q t : ℝ) : ℝ :=
  ∫ x in p..q, c.curvature g x t * c.speed g x t

def arcEnergy (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (p q t : ℝ) : ℝ :=
  ∫ x in p..q, c.curvatureSq g x t * c.speed g x t

end CurveMap

variable [SigmaCompactSpace M] [t2M : T2Space M]


theorem arc_totalCurvature_le_sqrt (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (p q t : ℝ) (hpq : p ≤ q) (hqp : q ≤ p + 1)
    (ht : t ∈ J) :
    c.arcTotalCurvature g p q t ≤ Real.sqrt (c.arcLength g p q t * c.arcEnergy g p q t) ∧
    c.arcEnergy g p q t ≤ c.energy g t := by
  sorry

variable [compactM : CompactSpace M] [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

theorem rfs_csf_local_regularity (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      (∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
        (J = Ico a T ∨ J = Icc a T) →
        ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
          c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
            r ≤ c.length B.family.metric tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric p q tstar = r →
              c.arcTotalCurvature B.family.metric p q tstar ≤ δ) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
              c.normSq B.family.metric
                (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
                  A m * (t - tstar) ^ (-((m : ℤ) + 1))) ∧
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
        (J = Ico a T ∨ J = Icc a T) →
        ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
          c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
            r ≤ c.length B.family.metric lambda tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric lambda p q tstar = r →
              c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
              c.normSq B.family.metric lambda
                (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x t ≤
                  A m * (t - tstar) ^ (-((m : ℤ) + 1))) := by
  sorry


theorem local_regularity_base (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      ∀ (T : ℝ) (_hT : a < T) (_hTb : T ≤ b) (J : Set ℝ),
        (J = Ico a T ∨ J = Icc a T) →
        ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
          c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
            r ≤ c.length B.family.metric tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric p q tstar = r →
              c.arcTotalCurvature B.family.metric p q tstar ≤ δ) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
              c.normSq B.family.metric
                (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
                  A m * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  obtain ⟨δ, r₀, A, hδ, hδ1, hr₀, hr₀1, hA, hbase, hproduct⟩ :=
    rfs_csf_local_regularity B L₀ Θ₀ hL₀ hΘ₀
  exact ⟨δ, r₀, A, hδ, hδ1, hr₀, hr₀1, hA, hbase⟩

omit compactM nonemptyM hBoundary in
theorem good_time_arc_bound (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) {δ r B : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hB : 0 < B) (hrB : r ≤ δ ^ 2 / B)
    (t : ℝ) (ht : t ∈ J) (hE : c.energy g t ≤ B) :
    ∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength g p q t = r →
      c.arcTotalCurvature g p q t ≤ δ := by
  intro p q hpq hqp hlen
  obtain ⟨hcs, he⟩ := arc_totalCurvature_le_sqrt g c hc hi p q t hpq hqp ht
  have hprod : c.arcLength g p q t * c.arcEnergy g p q t ≤ δ ^ 2 := by
    rw [hlen]
    exact (mul_le_mul_of_nonneg_left (he.trans hE) hr.le).trans
      ((le_div_iff₀ hB).mp hrB)
  exact hcs.trans ((Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq hδ.le))

theorem bad_energy_times_measure (B : RicciBackground (I := I) (M := M) D a b)
    {u : ℝ} (hau : a < u) (hub : u ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a u))
    {L₀ threshold : ℝ} (hL₀ : c.length B.family.metric a ≤ L₀) (hB : 0 < threshold)
    (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htu : t ≤ u) :
    volume {v : ℝ | v ∈ Icc s t ∧ threshold < c.energy B.family.metric v} ≤
      ENNReal.ofReal (Real.exp (B.B₀ * (b - a)) * L₀ / threshold) := by
  sorry

theorem rfs_csf_good_times (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      ∀ threshold : ℝ, 0 < threshold →
        let r := min r₀ (δ ^ 2 / threshold)
        let d := δ * r ^ 2
        let C_E := Real.exp (B.B₀ * (b - a)) * L₀
        (∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
          (J = Ico a T ∨ J = Icc a T) →
          ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
            c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
            (∀ s u : ℝ, a ≤ s → s ≤ u → u ∈ J →
              volume {v : ℝ | v ∈ Icc s u ∧ threshold < c.energy B.family.metric v} ≤
                ENNReal.ofReal (C_E / threshold)) ∧
            (∀ tstar ∈ Ico a T, c.energy B.family.metric tstar ≤ threshold →
              r ≤ c.length B.family.metric tstar →
              (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
                c.arcLength B.family.metric p q tstar = r →
                c.arcTotalCurvature B.family.metric p q tstar ≤ δ) ∧
              ∀ m x t, t ∈ J → t ∈ Icc (tstar + d / 2) (tstar + d) →
                c.normSq B.family.metric
                  (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
                    A m * (d / 2) ^ (-((m : ℤ) + 1)))) ∧
        (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
          ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ,
          (J = Ico a T ∨ J = Icc a T) →
          ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
            c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
            (∀ s u : ℝ, a ≤ s → s ≤ u → u ∈ J →
              volume {v : ℝ | v ∈ Icc s u ∧ threshold < c.energy B.family.metric lambda v} ≤
                ENNReal.ofReal (C_E / threshold)) ∧
            (∀ tstar ∈ Ico a T, c.energy B.family.metric lambda tstar ≤ threshold →
              r ≤ c.length B.family.metric lambda tstar →
              (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
                c.arcLength B.family.metric lambda p q tstar = r →
                c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ) ∧
              ∀ m x t, t ∈ J → t ∈ Icc (tstar + d / 2) (tstar + d) →
                c.normSq B.family.metric lambda
                  (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x t ≤
                    A m * (d / 2) ^ (-((m : ℤ) + 1)))) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
