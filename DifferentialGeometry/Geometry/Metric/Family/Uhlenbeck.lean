import DifferentialGeometry.Analysis.ODE.Flow.BundleLinearODE
import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Operator.Gradient

noncomputable section

namespace DifferentialGeometry

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem contDiffAt_fixed_space
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {f : ℝ → ∀ x, V x} {t : ℝ} {x : M} {n : WithTop ℕ∞}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : TotalSpace F V)) (t, x)) :
    ContDiffAt ℝ n (fun s => f s x) t := by
  rw [← contDiffWithinAt_univ]
  apply ContMDiffWithinAt.fiberwise_time_contDiffWithinAt (I := I) (F := F) (V := V)
    (u := univ) ?_ (mem_univ x)
  simpa only [univ_prod_univ] using hf.contMDiffWithinAt (s := univ)


section ODE

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

private theorem exists_linear_ode_inverse
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (A : ℝ → ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ioo a b ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, V x →L[ℝ] V x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (V x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
        (Ioo a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, (Φ p.1 p.2).inverse⟩ : TotalSpace (F →L[ℝ] F)
            (fun x => V x →L[ℝ] V x))) (Ioo a b ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : V x, ∀ t ∈ Ioo a b,
        HasDerivAt (fun s : ℝ => Φ s x v) (A t x (Φ t x v)) t) ∧
      ∀ t ∈ Ioo a b, ∀ x : M, ∀ v : V x,
        (Φ t x).inverse (Φ t x v) = v ∧ Φ t x ((Φ t x).inverse v) = v := by
  obtain ⟨Φ, hΦ₀, hΦsmooth, hΦderiv, _, hΦbij⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_fiberwise_linear_ode_solution ht₀ A hA
  have hΦinv : ∀ t ∈ Ioo a b, ∀ x, (Φ t x).IsInvertible := by
    intro t ht x
    let e := VectorBundle.continuousLinearEquivAt ℝ F V x
    let L : F →L[ℝ] F := e.toContinuousLinearMap.comp
      ((Φ t x).comp e.symm.toContinuousLinearMap)
    have hbij : Function.Bijective L := e.bijective.comp ((hΦbij t ht x).comp e.symm.bijective)
    have hinv : L.IsInvertible :=
      ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, by ext; rfl⟩
    simpa only [L, ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv] using hinv
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine ⟨Φ, hΦ₀, hΦsmooth, hΦsmooth.clm_bundle_inverse
    (fun p hp => hΦinv p.1 hp.1 p.2), hΦderiv, ?_⟩
  intro t ht x v
  obtain ⟨e, he⟩ := hΦinv t ht x
  rw [← he]
  simp

end ODE

section Metric

open Geometry.Operator

variable [FiniteDimensional ℝ E]

private theorem inner_isInvertible (g : SmoothRiemannianMetric I M) (x : M) :
    (g.inner x).IsInvertible := by
  let e :=
    ((metricFlatMap (I := I) g x).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  exact ⟨e, by ext v w; rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem metric_time_deriv_contMDiffAt
    {g : ℝ → SmoothRiemannianMetric I M} {p₀ : ℝ × M}
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) p₀) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, deriv (fun t => (g t).inner p.2) p.1⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) p₀ := by
  let : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  exact hg.fiberwise_time_deriv (by simp)

def metricGaugeVelocity (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (- (1 / 2 : ℝ)) • ((g t).inner x).inverse.comp (deriv (fun s => (g s).inner x) t)

def metricGaugeVelocityWithin (g : ℝ → SmoothRiemannianMetric I M) (s : Set ℝ) (t : ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (- (1 / 2 : ℝ)) •
    ((g t).inner x).inverse.comp (derivWithin (fun r => (g r).inner x) s t)

omit [FiniteDimensional ℝ E] in
theorem metricGaugeVelocityWithin_eq_metricGaugeVelocity
    (g : ℝ → SmoothRiemannianMetric I M) {s : Set ℝ} {t : ℝ}
    (hs : s ∈ nhds t) (x : M) :
    metricGaugeVelocityWithin g s t x = metricGaugeVelocity g t x := by
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  simp only [metricGaugeVelocityWithin, metricGaugeVelocity, derivWithin_of_mem_nhds hs]

private theorem metricGaugeVelocity_contMDiffAt
    {g : ℝ → SmoothRiemannianMetric I M} {p₀ : ℝ × M}
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) p₀) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, metricGaugeVelocity g p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x))) p₀ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hginv := ContMDiffAt.clm_bundle_inverse (𝕜 := ℝ) (I := I)
    (J := 𝓘(ℝ, ℝ).prod I) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (V₁ := TangentSpace I) (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := Prod.snd) (φ := fun p : ℝ × M => (g p.1).inner p.2) (p₀ := p₀) hg
    (inner_isInvertible (g p₀.1) p₀.2)
  have hgd := metric_time_deriv_contMDiffAt hg
  rw [contMDiffAt_hom_bundle] at hginv hgd ⊢
  refine ⟨contMDiffAt_snd, ?_⟩
  have h := (contMDiffAt_const (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ))
    (c := - (1 / 2 : ℝ))).smul (hginv.2.clm_comp hgd.2)
  apply h.congr_of_eventuallyEq
  let e := trivializationAt (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) p₀.2
  have hbase : ∀ᶠ p : ℝ × M in 𝓝 p₀, p.2 ∈ e.baseSet :=
    continuous_snd.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] ℝ) p₀.2))
  filter_upwards [hbase] with p hp
  ext v
  simp only [metricGaugeVelocity, ContinuousLinearMap.inCoordinates,
    Pi.smul_apply', ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  rw [Trivialization.symmL_continuousLinearMapAt _ hp]

theorem inner_metricGaugeVelocity (g : ℝ → SmoothRiemannianMetric I M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    (g t).inner x (metricGaugeVelocity g t x v) w =
      - (1 / 2 : ℝ) * deriv (fun s => (g s).inner x) t v w := by
  have hinv (α : TangentSpace I x →L[ℝ] ℝ) :
      (g t).inner x (((g t).inner x).inverse α) = α := by
    obtain ⟨e, he⟩ := inner_isInvertible (g t) x
    rw [← he]
    simp
  simp only [metricGaugeVelocity, smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, hinv, smul_eq_mul]

theorem inner_metricGaugeVelocityWithin (g : ℝ → SmoothRiemannianMetric I M)
    (s : Set ℝ) (t : ℝ) (x : M) (v w : TangentSpace I x) :
    (g t).inner x (metricGaugeVelocityWithin g s t x v) w =
      - (1 / 2 : ℝ) * derivWithin (fun r => (g r).inner x) s t v w := by
  have hinv (α : TangentSpace I x →L[ℝ] ℝ) :
      (g t).inner x (((g t).inner x).inverse α) = α := by
    obtain ⟨e, he⟩ := inner_isInvertible (g t) x
    rw [← he]
    simp
  simp only [metricGaugeVelocityWithin, smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, hinv, smul_eq_mul]

private theorem metricGaugeVelocityWithin_contMDiffOn
    {g : ℝ → SmoothRiemannianMetric I M} {s : Set ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (s ×ˢ (univ : Set M))) (hs : UniqueDiffOn ℝ s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, metricGaugeVelocityWithin g s p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x))) (s ×ˢ (univ : Set M)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hginv := ContMDiffOn.clm_bundle_inverse (𝕜 := ℝ) (I := I)
    (J := 𝓘(ℝ, ℝ).prod I) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (V₁ := TangentSpace I) (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := Prod.snd) (φ := fun p : ℝ × M => (g p.1).inner p.2) hg
    (fun p _ => inner_isInvertible (g p.1) p.2)
  have hgd := ContMDiffOn.fiberwise_time_derivWithin (I := I)
    (F := E →L[ℝ] E →L[ℝ] ℝ)
    (V := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (f := fun t x => (g t).inner x) hg hs (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  have hcomp := ContMDiffOn.clm_bundle_comp (𝕜 := ℝ) (I := I)
    (J := 𝓘(ℝ, ℝ).prod I) (F₁ := E) (F₂ := E →L[ℝ] ℝ) (F₃ := E)
    (V₁ := TangentSpace I) (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (V₃ := TangentSpace I) (b := Prod.snd)
    (φ := fun p : ℝ × M => derivWithin (fun t => (g t).inner p.2) s p.1)
    (ψ := fun p : ℝ × M => ((g p.1).inner p.2).inverse) hginv hgd
  intro p hp
  have hc := hcomp p hp
  rw [contMDiffWithinAt_hom_bundle] at hc ⊢
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  have h := (contMDiffWithinAt_const (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ))
    (c := - (1 / 2 : ℝ))).smul hc.2
  apply h.congr
  · intro q hq
    ext v
    simp only [metricGaugeVelocityWithin, ContinuousLinearMap.inCoordinates,
      Pi.smul_apply', ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  · ext v
    simp only [metricGaugeVelocityWithin, ContinuousLinearMap.inCoordinates,
      Pi.smul_apply', ContinuousLinearMap.comp_apply, smul_apply, map_smul]

theorem exists_metric_freezing_automorphism [I.Boundaryless]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioo a b ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (Ioo a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, (Φ p.1 p.2).inverse⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (Ioo a b ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : TangentSpace I x, ∀ t ∈ Ioo a b,
        HasDerivAt (fun s : ℝ => Φ s x v)
          (metricGaugeVelocity g t x (Φ t x v)) t) ∧
      (∀ t ∈ Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
        (Φ t x).inverse (Φ t x v) = v ∧ Φ t x ((Φ t x).inverse v) = v) ∧
      ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
        (g t).inner x (Φ t x v) (Φ t x w) = (g t₀).inner x v w := by
  have hopen : IsOpen (Ioo a b ×ˢ (univ : Set M)) := isOpen_Ioo.prod isOpen_univ
  have hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, metricGaugeVelocity g p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
      (Ioo a b ×ˢ (univ : Set M)) := fun p hp =>
    (metricGaugeVelocity_contMDiffAt (hg.contMDiffAt (hopen.mem_nhds hp))).contMDiffWithinAt
  obtain ⟨Φ, hΦ₀, hΦsmooth, hΦinvSmooth, hΦderiv, hΦinv⟩ :=
    exists_linear_ode_inverse (I := I) (F := E) (V := TangentSpace I) ht₀
      (metricGaugeVelocity g) hA
  refine ⟨Φ, hΦ₀, hΦsmooth, hΦinvSmooth, hΦderiv, hΦinv, ?_⟩
  intro t ht x v w
  let : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hzero : ∀ r ∈ Ioo a b,
      HasDerivAt (fun s => (g s).inner x (Φ s x v) (Φ s x w)) 0 r := by
    intro r hr
    have hgtime : DifferentiableAt ℝ (fun s => (g s).inner x) r := by
      have hgsmooth := contDiffAt_fixed_space (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (f := fun s x => (g s).inner x) (t := r) (x := x)
        (hg.contMDiffAt (x := (r, x)) (hopen.mem_nhds ⟨hr, mem_univ x⟩))
      exact hgsmooth.differentiableAt (by simp)
    have hgderiv := hgtime.hasDerivAt
    have hsymm : ∀ u z : TangentSpace I x,
        deriv (fun s => (g s).inner x) r u z = deriv (fun s => (g s).inner x) r z u := by
      intro u z
      have hleft := (hgderiv.clm_apply (hasDerivAt_const r u)).clm_apply (hasDerivAt_const r z)
      have hright := (hgderiv.clm_apply (hasDerivAt_const r z)).clm_apply (hasDerivAt_const r u)
      simp only [map_zero, add_zero] at hleft hright
      have heq : (fun s => (g s).inner x u z) = (fun s => (g s).inner x z u) :=
        funext fun s => (g s).symm x u z
      rw [heq] at hleft
      exact hleft.unique hright
    have h := (hgderiv.clm_apply (hΦderiv x v r hr)).clm_apply (hΦderiv x w r hr)
    apply h.congr_deriv
    simp only [add_apply]
    rw [inner_metricGaugeVelocity,
      (g r).symm x (Φ r x v) (metricGaugeVelocity g r x (Φ r x w)),
      inner_metricGaugeVelocity, hsymm (Φ r x w) (Φ r x v)]
    ring
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hzero r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hzero r hr).deriv) ht ht₀
  simpa only [hΦ₀, ContinuousLinearMap.id_apply] using heq

theorem exists_metric_freezing_isometry [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioo a b ×ˢ (univ : Set M)))
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (Ioo a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (Ioo a b ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ Ioo a b, HasDerivAt (fun s => ι s x v)
        (metricGaugeVelocity g t x (ι t x v)) t) ∧
      ∀ t ∈ Ioo a b, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w := by
  classical
  obtain ⟨Φ, hΦ₀, hΦsmooth, _, hΦderiv, hΦinv, hΦmetric⟩ :=
    exists_metric_freezing_automorphism ht₀ g hg
  let Ψ : ℝ → ∀ x, TangentSpace I x ≃L[ℝ] TangentSpace I x := fun t x =>
    if ht : t ∈ Ioo a b then
      ContinuousLinearEquiv.equivOfInverse (Φ t x) (Φ t x).inverse
        (fun v => (hΦinv t ht x v).1) (fun v => (hΦinv t ht x v).2)
    else ContinuousLinearEquiv.refl ℝ (TangentSpace I x)
  let ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x := fun t x => (ι₀ x).trans (Ψ t x)
  have hι : ∀ t ∈ Ioo a b, ∀ x v, ι t x v = Φ t x (ι₀ x v) := by
    intro t ht x v
    change Ψ t x (ι₀ x v) = _
    dsimp only [Ψ]
    rw [dif_pos ht]
    rfl
  have hιinit : ∀ x, ι t₀ x = ι₀ x := by
    intro x
    ext v
    rw [hι t₀ ht₀, hΦ₀]
    rfl
  have hopen : IsOpen (Ioo a b ×ˢ (univ : Set M)) := isOpen_Ioo.prod isOpen_univ
  have hιsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
        TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
      (Ioo a b ×ˢ (univ : Set M)) := by
    intro p hp
    have hcomp := ContMDiffWithinAt.clm_bundle_comp
      (hΦsmooth.contMDiffAt (hopen.mem_nhds hp))
      ((hι₀.comp contMDiff_snd).contMDiffAt (x := p))
    apply (hcomp.contMDiffAt Filter.univ_mem).contMDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with q hq
      congr 1
      ext v
      exact hι q.1 hq.1 q.2 v
    · congr 1
      ext v
      exact hι p.1 hp.1 p.2 v
  refine ⟨ι, hιinit, hιsmooth, ?_, ?_, ?_⟩
  · intro p hp
    let e : E ≃L[ℝ] F := (ι₀ p.2).symm.trans (VectorBundle.continuousLinearEquivAt ℝ F V p.2)
    let : FiniteDimensional ℝ F := e.toLinearEquiv.finiteDimensional
    let : CompleteSpace F := FiniteDimensional.complete ℝ F
    have hinv := (hιsmooth p hp).clm_bundle_inverse
      (show ((ι p.1 p.2).toContinuousLinearMap).IsInvertible from ⟨ι p.1 p.2, rfl⟩)
    simpa only [ContinuousLinearMap.inverse_equiv] using hinv
  · intro x v t ht
    rw [hι t ht]
    apply (hΦderiv x (ι₀ x v) t ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hι s hs x v
  · intro t ht x v w
    rw [hι t ht, hι t ht, hΦmetric t ht]
    exact h₀ x v w

theorem exists_metric_freezing_automorphism_on_interval [I.Boundaryless]
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, (Φ p.1 p.2).inverse⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : TangentSpace I x, ∀ t ∈ J,
        HasDerivWithinAt (fun s : ℝ => Φ s x v)
          (metricGaugeVelocityWithin g J t x (Φ t x v)) J t) ∧
      (∀ t ∈ J, ∀ x : M, ∀ v : TangentSpace I x,
        (Φ t x).inverse (Φ t x v) = v ∧ Φ t x ((Φ t x).inverse v) = v) ∧
      ∀ t ∈ J, ∀ x : M, ∀ v w : TangentSpace I x,
        (g t).inner x (Φ t x v) (Φ t x w) = (g t₀).inner x v w := by
  have hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, metricGaugeVelocityWithin g J p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
      (J ×ˢ (univ : Set M)) := by
    rcases J.subsingleton_or_nontrivial with hs | hn
    · have hJ_eq := hs.eq_singleton_of_mem ht₀
      subst J
      have hzero : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
          (fun p : ℝ × M => (⟨p.2, 0⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x))) :=
        (contMDiff_zeroSection ℝ
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          (IB := I) (F := E →L[ℝ] E) (n := ∞)).comp contMDiff_snd
      apply hzero.contMDiffOn.congr
      rintro ⟨t, x⟩ ⟨ht, _⟩
      have ht_eq : t = t₀ := ht
      subst t
      congr 1
      let : NormedAddCommGroup
          (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
        inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
      let : NormedSpace ℝ
          (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
        inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
      simp only [metricGaugeVelocityWithin]
      rw [derivWithin_zero_of_not_accPt (by
        rw [accPt_principal_iff_nhdsWithin]
        simp)]
      simp
    · exact metricGaugeVelocityWithin_contMDiffOn hg
        (uniqueDiffOn_convex hJ.convex (hJ.convex.nontrivial_iff_nonempty_interior.mp hn))
  obtain ⟨Φ, hΦ₀, hΦsmooth, hΦinvSmooth, hΦderiv, _, hΦinv, _⟩ :=
    Analysis.ODE.Flow.exists_fiberwise_linear_ode_solution_on_interval
      (I := I) (F := E) (V := TangentSpace I) hJ ht₀
      (metricGaugeVelocityWithin g J) hA
  refine ⟨Φ, hΦ₀, hΦsmooth, hΦinvSmooth, hΦderiv, hΦinv, ?_⟩
  intro t ht x v w
  rcases J.subsingleton_or_nontrivial with hs | hn
  · have ht_eq : t = t₀ := hs ht ht₀
    subst t
    simp only [hΦ₀, ContinuousLinearMap.id_apply]
  have hdiff := uniqueDiffOn_convex hJ.convex
    (hJ.convex.nontrivial_iff_nonempty_interior.mp hn)
  let : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hzero : ∀ r ∈ J,
      HasDerivWithinAt (fun s => (g s).inner x (Φ s x v) (Φ s x w)) 0 J r := by
    intro r hr
    have hgtime : DifferentiableWithinAt ℝ (fun s => (g s).inner x) J r := by
      have hgsmooth := ContMDiffWithinAt.fiberwise_time_contDiffWithinAt
        (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (f := fun s x => (g s).inner x) (t := r) (x := x)
        (hg (r, x) ⟨hr, mem_univ x⟩) (mem_univ x)
      exact hgsmooth.differentiableWithinAt (by simp)
    have hgderiv := hgtime.hasDerivWithinAt
    have hsymm : ∀ u z : TangentSpace I x,
        derivWithin (fun s => (g s).inner x) J r u z =
          derivWithin (fun s => (g s).inner x) J r z u := by
      intro u z
      have hleft := (hgderiv.clm_apply (hasDerivWithinAt_const r J u)).clm_apply
        (hasDerivWithinAt_const r J z)
      have hright := (hgderiv.clm_apply (hasDerivWithinAt_const r J z)).clm_apply
        (hasDerivWithinAt_const r J u)
      simp only [map_zero, add_zero] at hleft hright
      have heq : (fun s => (g s).inner x u z) = (fun s => (g s).inner x z u) :=
        funext fun s => (g s).symm x u z
      rw [heq] at hleft
      exact (hleft.derivWithin (hdiff r hr)).symm.trans
        (hright.derivWithin (hdiff r hr))
    have h := (hgderiv.clm_apply (hΦderiv x v r hr)).clm_apply (hΦderiv x w r hr)
    apply h.congr_deriv
    simp only [add_apply]
    rw [inner_metricGaugeVelocityWithin,
      (g r).symm x (Φ r x v) (metricGaugeVelocityWithin g J r x (Φ r x w)),
      inner_metricGaugeVelocityWithin, hsymm (Φ r x w) (Φ r x v)]
    ring
  have hbound := hJ.convex.norm_image_sub_le_of_norm_hasDerivWithin_le hzero
    (fun r hr => by simp : ∀ r ∈ J, ‖(0 : ℝ)‖ ≤ (0 : ℝ)) ht₀ ht
  have heq := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hbound))
  simpa only [hΦ₀, ContinuousLinearMap.id_apply] using heq

theorem exists_metric_freezing_isometry_on_interval [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)))
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (J ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
        (metricGaugeVelocityWithin g J t x (ι t x v)) J t) ∧
      ∀ t ∈ J, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w := by
  classical
  obtain ⟨Φ, hΦ₀, hΦsmooth, _, hΦderiv, hΦinv, hΦmetric⟩ :=
    exists_metric_freezing_automorphism_on_interval hJ ht₀ g hg
  let Ψ : ℝ → ∀ x, TangentSpace I x ≃L[ℝ] TangentSpace I x := fun t x =>
    if ht : t ∈ J then
      ContinuousLinearEquiv.equivOfInverse (Φ t x) (Φ t x).inverse
        (fun v => (hΦinv t ht x v).1) (fun v => (hΦinv t ht x v).2)
    else ContinuousLinearEquiv.refl ℝ (TangentSpace I x)
  let ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x := fun t x => (ι₀ x).trans (Ψ t x)
  have hι : ∀ t ∈ J, ∀ x v, ι t x v = Φ t x (ι₀ x v) := by
    intro t ht x v
    change Ψ t x (ι₀ x v) = _
    dsimp only [Ψ]
    rw [dif_pos ht]
    rfl
  have hιinit : ∀ x, ι t₀ x = ι₀ x := by
    intro x
    ext v
    rw [hι t₀ ht₀, hΦ₀]
    rfl
  have hιsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
        TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
      (J ×ˢ (univ : Set M)) := by
    intro p hp
    have hcomp := ContMDiffWithinAt.clm_bundle_comp
      (hΦsmooth p hp)
      ((hι₀.comp contMDiff_snd).contMDiffAt (x := p)).contMDiffWithinAt
    apply hcomp.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with q hq
      congr 1
      ext v
      exact hι q.1 hq.1 q.2 v
    · congr 1
      ext v
      exact hι p.1 hp.1 p.2 v
  refine ⟨ι, hιinit, hιsmooth, ?_, ?_, ?_⟩
  · intro p hp
    let e : E ≃L[ℝ] F := (ι₀ p.2).symm.trans (VectorBundle.continuousLinearEquivAt ℝ F V p.2)
    let : FiniteDimensional ℝ F := e.toLinearEquiv.finiteDimensional
    let : CompleteSpace F := FiniteDimensional.complete ℝ F
    have hinv := (hιsmooth p hp).clm_bundle_inverse
      (show ((ι p.1 p.2).toContinuousLinearMap).IsInvertible from ⟨ι p.1 p.2, rfl⟩)
    simpa only [ContinuousLinearMap.inverse_equiv] using hinv
  · intro x v t ht
    rw [hι t ht]
    exact (hΦderiv x (ι₀ x v) t ht).congr
      (fun s hs => hι s hs x v) (hι t ht x v)
  · intro t ht x v w
    rw [hι t ht, hι t ht, hΦmetric t ht]
    exact h₀ x v w

theorem exists_metric_freezing_automorphism_on_Icc [I.Boundaryless]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M))) :
    ∃ Φ : ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x,
      (∀ x, Φ t₀ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, Φ p.1 p.2⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (Icc a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M =>
          (⟨p.2, (Φ p.1 p.2).inverse⟩ : TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (Icc a b ×ˢ (univ : Set M)) ∧
      (∀ x : M, ∀ v : TangentSpace I x, ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s : ℝ => Φ s x v)
          (metricGaugeVelocityWithin g (Icc a b) t x (Φ t x v)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
        (Φ t x).inverse (Φ t x v) = v ∧ Φ t x ((Φ t x).inverse v) = v) ∧
      ∀ t ∈ Icc a b, ∀ x : M, ∀ v w : TangentSpace I x,
        (g t).inner x (Φ t x v) (Φ t x w) = (g t₀).inner x v w :=
  exists_metric_freezing_automorphism_on_interval ordConnected_Icc ht₀ g hg

theorem exists_metric_freezing_isometry_on_Icc [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M)))
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (Icc a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (Icc a b ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => ι s x v)
        (metricGaugeVelocityWithin g (Icc a b) t x (ι t x v)) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w :=
  exists_metric_freezing_isometry_on_interval ordConnected_Icc ht₀ g hg h ι₀ hι₀ h₀

theorem exists_metric_freezing_isometry_on_Ico [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ico a b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (univ : Set M)))
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (Ico a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (Ico a b ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => ι s x v)
        (metricGaugeVelocityWithin g (Ico a b) t x (ι t x v)) (Ico a b) t) ∧
      ∀ t ∈ Ico a b, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w :=
  exists_metric_freezing_isometry_on_interval ordConnected_Ico ht₀ g hg h ι₀ hι₀ h₀

theorem exists_metric_freezing_isometry_on_Ici [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {a t₀ : ℝ} (ht₀ : t₀ ∈ Ici a)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ici a ×ˢ (univ : Set M)))
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (Ici a ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (Ici a ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ Ici a, HasDerivWithinAt (fun s => ι s x v)
        (metricGaugeVelocityWithin g (Ici a) t x (ι t x v)) (Ici a) t) ∧
      ∀ t ∈ Ici a, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w :=
  exists_metric_freezing_isometry_on_interval ordConnected_Ici ht₀ g hg h ι₀ hι₀ h₀

end Metric

end DifferentialGeometry
