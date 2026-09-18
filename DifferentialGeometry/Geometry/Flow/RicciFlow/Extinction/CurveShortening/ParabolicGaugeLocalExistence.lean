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

noncomputable section

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_diffeomorph_flow_lift_iteratedFDeriv_tendstoUniformlyOn_of_parabolic_equation
    {ι : Type*} {l : Filter ι}
    {D : ι → RealTimeInterval} {DInf : RealTimeInterval}
    {g : ι → ℝ → SmoothRiemannianMetric I M} {gInf : ℝ → SmoothRiemannianMetric I M}
    (hG : ∀ i, MetricFamilySmoothOn (I := I) (M := M) (D i) (g i))
    (hGInf : MetricFamilySmoothOn (I := I) (M := M) DInf gInf)
    {a b : ℝ} (hab : a < b)
    (hJ : ∀ i, Icc a b ⊆ (D i).regular) (hJInf : Icc a b ⊆ DInf.regular)
    {c : ι → CurveMap M} {cInf : CurveMap M}
    (hc : ∀ i, (c i).SmoothOn (I := I) (Icc a b))
    (hi : ∀ i, (c i).ImmersedOn (I := I) (Icc a b))
    (hcInf : cInf.SmoothOn (I := I) (Icc a b))
    (hiInf : cInf.ImmersedOn (I := I) (Icc a b))
    (heq : ∀ i x t, t ∈ Icc a b → (c i).velocity (I := I) (Icc a b) x t =
      (c i).speed (g i) x t ^ (-2 : ℤ) • (c i).Dx (g i) (c i).X x t)
    (heqInf : ∀ x t, t ∈ Icc a b → cInf.velocity (I := I) (Icc a b) x t =
      cInf.speed gInf x t ^ (-2 : ℤ) • cInf.Dx gInf cInf.X x t)
    (hconv : ∀ k : ℕ, TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedDeriv (k + 1)
        (fun x => (c i).speed (g i) x q.2 ^ (-2 : ℤ)) q.1)
      (fun q : ℝ × ℝ => iteratedDeriv (k + 1)
        (fun x => cInf.speed gInf x q.2 ^ (-2 : ℤ)) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ∃ (F : ι → ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (FInf : ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (γ : ι → ℝ → ℝ → ℝ) (γInf : ℝ → ℝ → ℝ),
      (∀ i, CurveMap.IsSolutionOn (I := I) (fun z t => c i (F i t z) t) (g i) (Icc a b)) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => cInf (FInf t z) t) gInf (Icc a b) ∧
      (∀ i z, F i a z = z) ∧ (∀ z, FInf a z = z) ∧
      (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b) ∧
      (∀ i x t, t ∈ Icc a b →
        (γ i x t : AddCircle (1 : ℝ)) = F i t (x : AddCircle (1 : ℝ))) ∧
      (∀ x t, t ∈ Icc a b →
        (γInf x t : AddCircle (1 : ℝ)) = FInf t (x : AddCircle (1 : ℝ))) ∧
      (∀ i x t, t ∈ Icc a b → γ i (x + 1) t = γ i x t + 1) ∧
      (∀ x t, t ∈ Icc a b → γInf (x + 1) t = γInf x t + 1) ∧
      (∀ i x, γ i x a = x) ∧ (∀ x, γInf x a = x) ∧
      (∀ i x, IsIntegralCurveOn (γ i x)
        (fun t y => -(deriv (fun z => (c i).speed (g i) z t) y / (c i).speed (g i) y t ^ 2) /
          (c i).speed (g i) y t) (Icc a b)) ∧
      (∀ x, IsIntegralCurveOn (γInf x)
        (fun t y => -(deriv (fun z => cInf.speed gInf z t) y / cInf.speed gInf y t ^ 2) /
        cInf.speed gInf y t) (Icc a b)) ∧
      ∀ K : Set ℝ, IsCompact K → ∀ k : ℕ, TendstoUniformlyOn
        (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k (fun x => γ i x q.2) q.1)
        (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (fun x => γInf x q.2) q.1)
        l (K ×ˢ Icc a b) := by
  have hgeo (i : ι) := CurveMap.isGeometricSolutionOn_of_parabolicGauge
    (hG i) (uniqueDiffOn_Icc hab) (hJ i) (hc i) (hi i) (heq i)
  have hgeoInf := CurveMap.isGeometricSolutionOn_of_parabolicGauge
    hGInf (uniqueDiffOn_Icc hab) hJInf hcInf hiInf heqInf
  exact exists_diffeomorph_flow_lift_iteratedFDeriv_tendstoUniformlyOn hG hGInf hab hJ hJInf
    hgeo hgeoInf (fun k => CurveMap.tendstoUniformlyOn_iteratedFDeriv_gaugeCoefficient_of_diffusion
      hc hi hcInf hiInf k (hconv k))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
