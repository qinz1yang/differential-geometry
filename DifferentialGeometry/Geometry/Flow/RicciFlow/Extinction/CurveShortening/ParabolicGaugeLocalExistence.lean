import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SmoothSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.GaugeNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem contDiffOn_deriv_fst {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × ℝ → G} {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ J)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv (fun y => F (y, p.2)) p.1) (univ ×ˢ J) := by
  have hd := (hF.fderivWithin (uniqueDiffOn_univ.prod hJ) (by simp)).clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) (univ ×ˢ J))
  refine hd.congr ?_
  intro p hp
  have h := derivWithin_slice_eq_fderivWithin_apply hp.2
    ((hF.differentiableOn (by simp) p hp).hasFDerivWithinAt)
  simpa only [derivWithin_univ] using h

namespace CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isGeometricSolutionOn_of_parabolicGauge [I.Boundaryless]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hJD : J ⊆ D.regular)
    {c : CurveMap M} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (heq : ∀ x t, t ∈ J → c.velocity (I := I) J x t =
      (c.speed g x t) ^ (-2 : ℤ) • c.Dx g c.X x t) :
    c.IsGeometricSolutionOn g J
      (fun x t => deriv (fun y => c.speed g y t) x / c.speed g x t ^ 2) := by
  have hs := Field.smoothOn_speed g hG hJD c hc hi
  refine ⟨hc, hi, ?_, ?_⟩
  · exact (contDiffOn_deriv_fst hJ hs).div (hs.pow 2)
      (fun p hp => pow_ne_zero 2 (c.speed_pos g hi p.1 p.2 hp.2).ne')
  · intro x t ht
    rw [heq x t ht, (parabolic_gauge_velocity (I := I) g c hc hi x t ht).2]
    simp only [CurveMap.unitTangent, smul_smul]
    congr 1
    field_simp

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval} {a b : ℝ}

theorem curveShorteningParabolicGaugeLocalExistence_of_parabolic_equation
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (h : ∀ t₀ ∈ Ico a b, ∀ c₀ : SmoothImmersion (I := I) (M := M),
      ∃ τ : ℝ, 0 < τ ∧ t₀ + τ ≤ b ∧ ∃ c : CurveMap M,
        c.SmoothOn (I := I) (Icc t₀ (t₀ + τ)) ∧
        (∀ z, c z t₀ = c₀.map z) ∧
        (∀ x t, t ∈ Icc t₀ (t₀ + τ) →
          c.velocity (I := I) (Icc t₀ (t₀ + τ)) x t =
            c.speed B.family.metric x t ^ (-2 : ℤ) • c.Dx B.family.metric c.X x t)) :
    curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hτb, c, hcT, hinit, heq⟩ := h t₀ ht₀ c₀
  have hX₀ : ∀ x, c.X (I := I) x t₀ ≠ 0 := by
    intro x
    have hpoint : c.X (I := I) x t₀ =
        mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ))) x (1 : ℝ) := by
      have hfun : (fun y : ℝ => c.lift y t₀) =
          fun y : ℝ => c₀.map (y : AddCircle (1 : ℝ)) := by
        funext y
        rw [CurveMap.lift, hinit]
      simp only [CurveMap.X]
      exact congrArg (fun f : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I f x) (1 : ℝ)) hfun
    rw [hpoint]
    exact c₀.immersed x
  obtain ⟨τ', hτ'pos, hτ'le, himm'⟩ :=
    curveShorteningImmersedPersistence (I := I) (M := M)
      (by linarith : t₀ < t₀ + τ) c hcT hX₀
  let τ'' : ℝ := τ' / 2
  have hτ''pos : 0 < τ'' := by dsimp [τ'']; linarith
  have hτ''τ' : τ'' < τ' := by dsimp [τ'']; linarith
  have hτ'τ : τ' ≤ τ := by linarith
  have hτ''τ : τ'' < τ := lt_of_lt_of_le hτ''τ' hτ'τ
  have hτ''b : t₀ + τ'' ≤ b := by linarith
  have hc'' : c.SmoothOn (I := I) (Icc t₀ (t₀ + τ'')) :=
    hcT.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by linarith)))
  have hsub : Icc t₀ (t₀ + τ'') ⊆ Icc t₀ (t₀ + τ) :=
    Icc_subset_Icc le_rfl (by linarith)
  have himm'' : c.ImmersedOn (I := I) (Icc t₀ (t₀ + τ'')) :=
    fun x t ht => himm' x t ⟨ht.1, le_trans ht.2 (by linarith)⟩
  have heq'' : ∀ x t, t ∈ Icc t₀ (t₀ + τ'') →
      c.velocity (I := I) (Icc t₀ (t₀ + τ'')) x t =
        c.speed B.family.metric x t ^ (-2 : ℤ) • c.Dx B.family.metric c.X x t := by
    intro x t ht
    rw [CurveMap.velocity_Icc_of_lt (t₀ := t₀) (σ := τ'') (τ := τ)
      hτ''pos hτ''τ hcT ht]
    exact heq x t (hsub ht)
  have hJD : Icc t₀ (t₀ + τ'') ⊆ D.regular := by
    intro t ht
    exact B.regular ⟨le_trans ht₀.1 ht.1, le_trans ht.2 hτ''b⟩
  have hgeo := c.isGeometricSolutionOn_of_parabolicGauge B.smooth
    (uniqueDiffOn_Icc (by linarith : t₀ < t₀ + τ'')) hJD hc'' himm'' heq''
  obtain ⟨φ, hφ, hsol⟩ := hgeo.exists_reparametrization_isSolutionOn B.smooth
    (by linarith : t₀ < t₀ + τ'') hJD
  let d : CurveMap M := fun z t => c (φ.map t z) t
  refine ⟨τ'', hτ''pos, hτ''b, d, hsol.smooth, ?_, ?_⟩
  · intro z
    change c (φ.map t₀ z) t₀ = c₀.map z
    rw [hφ, hinit]
  · intro x t ht
    have hpar := parabolic_gauge_velocity (I := I) B.family.metric d
      hsol.smooth hsol.immersed x t ht
    rw [hsol.equation x t ht, hpar.2, add_sub_cancel_right]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
