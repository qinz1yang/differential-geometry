import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

def isExteriorSpanningDisk (W : Set M) (γ : freeLoop M) (u : C(closedDisk, M)) : Prop :=
  diskTrace u = γ ∧ Set.range γ ⊆ frontier W ∧ Topology.IsEmbedding u ∧ Set.range u ⊆ W ∧
    (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → u z ∈ interior W) ∧
    ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)

def leastExteriorDiskArea (g : SmoothRiemannianMetric (𝓡 3) M)
    (W : Set M) (γ : freeLoop M) : ℝ :=
  sInf ((fun u : C(closedDisk, M) => riemannianDiskArea g u) ''
    {u | isExteriorSpanningDisk W γ u})

theorem leastExteriorDiskArea_nonneg (g : SmoothRiemannianMetric (𝓡 3) M)
    (W : Set M) (γ : freeLoop M) : 0 ≤ leastExteriorDiskArea g W γ := by
  apply Real.sInf_nonneg
  rintro _ ⟨u, _, rfl⟩
  exact riemannianDiskArea_nonneg g u

theorem leastExteriorDiskArea_le (g : SmoothRiemannianMetric (𝓡 3) M)
    (W : Set M) (γ : freeLoop M) (u : C(closedDisk, M))
    (hu : isExteriorSpanningDisk W γ u) :
    leastExteriorDiskArea g W γ ≤ riemannianDiskArea g u := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact riemannianDiskArea_nonneg g v
  · exact ⟨u, hu, rfl⟩

def exteriorDiskAreaOn
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t : ℝ) : ℝ :=
  if ht : T ≤ t then leastExteriorDiskArea (g t) (W t) (γ t ht) else 0

theorem exteriorDiskAreaOn_nonneg
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t : ℝ) :
    0 ≤ exteriorDiskAreaOn M g W T γ t := by
  unfold exteriorDiskAreaOn
  split
  · exact leastExteriorDiskArea_nonneg _ _ _
  · exact le_rfl

theorem continuousOn_leastExteriorDiskArea_of_local_disk_comparisons
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t))
    (hmin : ∀ (t : ℝ) (ht : T ≤ t), ∃ u : C(closedDisk, M t),
      isExteriorSpanningDisk (W t) (γ t ht) u ∧
      riemannianDiskArea (g t) u = leastExteriorDiskArea (g t) (W t) (γ t ht))
    (hcomparison : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ →
        (∀ u : C(closedDisk, M t₀), isExteriorSpanningDisk (W t₀) (γ t₀ ht₀) u →
          riemannianDiskArea (g t₀) u = leastExteriorDiskArea (g t₀) (W t₀) (γ t₀ ht₀) →
          ∃ v : C(closedDisk, M t), isExteriorSpanningDisk (W t) (γ t ht) v ∧
            riemannianDiskArea (g t) v ≤ Real.exp ε * riemannianDiskArea (g t₀) u) ∧
        (∀ v : C(closedDisk, M t), isExteriorSpanningDisk (W t) (γ t ht) v →
          riemannianDiskArea (g t) v = leastExteriorDiskArea (g t) (W t) (γ t ht) →
          ∃ u : C(closedDisk, M t₀), isExteriorSpanningDisk (W t₀) (γ t₀ ht₀) u ∧
            riemannianDiskArea (g t₀) u ≤ Real.exp ε * riemannianDiskArea (g t) v)) :
    ContinuousOn (exteriorDiskAreaOn M g W T γ) (Ici T) := by
  have hfeq : ∀ t (ht : T ≤ t),
      exteriorDiskAreaOn M g W T γ t = leastExteriorDiskArea (g t) (W t) (γ t ht) := by
    intro t ht
    simp only [exteriorDiskAreaOn, dif_pos ht]
  have key : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀) (ε : ℝ), 0 < ε →
      ∀ᶠ t in 𝓝[Ici T] t₀,
        exteriorDiskAreaOn M g W T γ t ≤ Real.exp ε * exteriorDiskAreaOn M g W T γ t₀ ∧
        exteriorDiskAreaOn M g W T γ t₀ ≤ Real.exp ε * exteriorDiskAreaOn M g W T γ t := by
    intro t₀ ht₀ ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hcomparison t₀ ht₀ ε hε
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun t hdist ht => ?_⟩
    have ht' : T ≤ t := ht
    rw [Real.dist_eq] at hdist
    obtain ⟨h1, h2⟩ := hδ' t ht' hdist
    obtain ⟨u, hu, hu'⟩ := hmin t₀ ht₀
    obtain ⟨v, hv, hv'⟩ := hmin t ht'
    obtain ⟨v', hv'1, hv'2⟩ := h1 u hu hu'
    obtain ⟨u', hu'1, hu'2⟩ := h2 v hv hv'
    rw [hfeq t ht', hfeq t₀ ht₀]
    constructor
    · calc leastExteriorDiskArea (g t) (W t) (γ t ht') ≤ riemannianDiskArea (g t) v' :=
            leastExteriorDiskArea_le _ _ _ v' hv'1
        _ ≤ Real.exp ε * riemannianDiskArea (g t₀) u := hv'2
        _ = Real.exp ε * leastExteriorDiskArea (g t₀) (W t₀) (γ t₀ ht₀) := by rw [hu']
    · calc leastExteriorDiskArea (g t₀) (W t₀) (γ t₀ ht₀) ≤ riemannianDiskArea (g t₀) u' :=
            leastExteriorDiskArea_le _ _ _ u' hu'1
        _ ≤ Real.exp ε * riemannianDiskArea (g t) v := hu'2
        _ = Real.exp ε * leastExteriorDiskArea (g t) (W t) (γ t ht') := by rw [hv']
  intro t₀ ht₀
  have ht₀' : T ≤ t₀ := ht₀
  set f := exteriorDiskAreaOn M g W T γ with hf
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro a ha
    have hlim : Tendsto (fun ε : ℝ => Real.exp (-ε) * f t₀) (𝓝 0) (𝓝 (f t₀)) := by
      have h1 : Tendsto (fun ε : ℝ => Real.exp (-ε)) (𝓝 0) (𝓝 1) := by
        have := (Real.continuous_exp.comp continuous_neg).tendsto 0
        simpa [Function.comp_def] using this
      simpa using h1.mul_const (f t₀)
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), a < Real.exp (-ε) * f t₀ :=
      hlim.eventually (lt_mem_nhds ha)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    have hε : 0 < δ / 2 := by positivity
    have hεa : a < Real.exp (-(δ / 2)) * f t₀ := by
      apply hδ'
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      linarith
    filter_upwards [key t₀ ht₀' (δ / 2) hε] with t ht
    have h2 : Real.exp (-(δ / 2)) * f t₀ ≤ f t := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact ht.2
    exact lt_of_lt_of_le hεa h2
  · intro b hb
    have hlim : Tendsto (fun ε : ℝ => Real.exp ε * f t₀) (𝓝 0) (𝓝 (f t₀)) := by
      have h1 : Tendsto (fun ε : ℝ => Real.exp ε) (𝓝 0) (𝓝 1) := by
        have := Real.continuous_exp.tendsto 0
        simpa using this
      simpa using h1.mul_const (f t₀)
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), Real.exp ε * f t₀ < b :=
      hlim.eventually (gt_mem_nhds hb)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    have hε : 0 < δ / 2 := by positivity
    have hεb : Real.exp (δ / 2) * f t₀ < b := by
      apply hδ'
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      linarith
    filter_upwards [key t₀ ht₀' (δ / 2) hε] with t ht
    exact lt_of_le_of_lt ht.1 hεb

theorem leastExteriorDiskArea_eq_zero_of_empty {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M) (W : Set M) (γ : freeLoop M)
    (h : {u | isExteriorSpanningDisk W γ u} = ∅) : leastExteriorDiskArea g W γ = 0 := by
  simp [leastExteriorDiskArea, h]

end DifferentialGeometry.Geometry.MinimalSurface
