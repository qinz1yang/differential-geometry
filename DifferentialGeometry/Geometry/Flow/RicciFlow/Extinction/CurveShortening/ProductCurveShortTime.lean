import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionCorrespondence

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {D : RealTimeInterval} {a b : ℝ}

namespace ProductCurve

def LocalExistence (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ t₀ ∈ Ico a b, ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {t₀} →
    c₀.ImmersedOn (I := I) {t₀} →
    ∃ τ > 0, t₀ + τ ≤ b ∧ ∃ c : ProductCurve M,
      c.IsSolutionOn (I := I) B.family.metric lambda (Icc t₀ (t₀ + τ)) ∧
      ∀ z, c.map z t₀ = c₀.map z t₀

def TerminalClosure [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : ProductCurve M) (K : ℝ), 0 ≤ K →
    c.IsSolutionOn (I := I) B.family.metric lambda (Ico a T) →
    (∀ x t, t ∈ Ico a T → c.curvature (I := I) B.family.metric lambda x t ≤ K) →
    ∃ closed : ProductCurve M,
      closed.IsSolutionOn (I := I) B.family.metric lambda (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed.map z t = c.map z t

def Extension [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T < b → ∀ (c : ProductCurve M) (K : ℝ), 0 ≤ K →
    c.IsSolutionOn (I := I) B.family.metric lambda (Ico a T) →
    (∀ x t, t ∈ Ico a T → c.curvature (I := I) B.family.metric lambda x t ≤ K) →
    ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : ProductCurve M,
      extended.IsSolutionOn (I := I) B.family.metric lambda (Icc a (T + τ)) ∧
      ∀ z t, t ∈ Ico a T → extended.map z t = c.map z t

def Continuation [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : ProductCurve M) (K : ℝ), 0 ≤ K →
    c.IsSolutionOn (I := I) B.family.metric lambda (Ico a T) →
    (∀ x t, t ∈ Ico a T → c.curvature (I := I) B.family.metric lambda x t ≤ K) →
    (∃ closed : ProductCurve M,
        closed.IsSolutionOn (I := I) B.family.metric lambda (Icc a T) ∧
        ∀ z t, t ∈ Ico a T → closed.map z t = c.map z t) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : ProductCurve M,
        extended.IsSolutionOn (I := I) B.family.metric lambda (Icc a (T + τ)) ∧
        ∀ z t, t ∈ Ico a T → extended.map z t = c.map z t)

theorem continuation_iff_terminalClosure_and_extension [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    Continuation B lambda ↔ TerminalClosure B lambda ∧ Extension B lambda := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro T haT hTb c K hK hc hcurv
      exact (h T haT hTb c K hK hc hcurv).1
    · intro T haT hTb c K hK hc hcurv
      exact (h T haT hTb.le c K hK hc hcurv).2 hTb
  · rintro ⟨hclose, hext⟩ T haT hTb c K hK hc hcurv
    exact ⟨hclose T haT hTb c K hK hc hcurv,
      fun hlt => hext T haT hlt c K hK hc hcurv⟩

omit [CompleteSpace E] in
theorem map_curvature_eq (c : ProductCurve M) (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.curvature (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      c.curvature (I := I) g lambda x t := by
  let := A.charts
  let := A.smoothManifold
  have hvec := c.map_curvatureVector_eq (I := I) A g lambda hlambda hc hU x t ht
  have hprod : (quotientProductMetric A (g t) lambda hlambda).inner
        (productCoverProjection (M := M) (c.coverLift x t))
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t) (c.curvatureVector g lambda x t))
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t) (c.curvatureVector g lambda x t)) =
      c.inner g lambda x t (c.curvatureVector g lambda x t)
        (c.curvatureVector g lambda x t) := by
    refine (localPullMetric_inner (quotientProductMetric A (g t) lambda hlambda)
      (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
      (c.coverLift x t) (c.curvatureVector g lambda x t)
      (c.curvatureVector g lambda x t)).symm.trans ?_
    rw [quotientProductMetric_localPull A (g t) lambda hlambda,
      coverProductMetric_inner (g t) lambda hlambda (c.coverLift x t)
        (c.curvatureVector g lambda x t) (c.curvatureVector g lambda x t)]
    simp only [ProductCurve.inner]
    rfl
  have hstep := (c.coverProjection_lift x t) ▸ hvec ▸ hprod
  have hsq : c.map.curvatureSq (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      c.curvatureSq (I := I) g lambda x t := by
    simp only [ProductCurve.curvatureSq, ProductCurve.normSq, CurveMap.curvatureSq,
      CurveMap.normSq]
    exact hstep
  rw [CurveMap.curvature, ProductCurve.curvature, hsq]

omit [CompleteSpace E] in
theorem localExistence_of_quotientCurveLocalExistence (A : QuotientProductAtlas I M)
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : SmoothMetricWindow (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningLocalExistence (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      LocalExistence B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H t₀ ht₀ c₀ hsm₀ himm₀
  have hmap : c₀.map.SmoothOn (I := I.prod 𝓘(ℝ, ℝ)) {t₀} :=
    c₀.smoothOn_map (I := I) A hsm₀
  have himmMap : c₀.map.ImmersedOn (I := I.prod 𝓘(ℝ, ℝ)) {t₀} :=
    (c₀.map_immersedOn_iff (I := I) A hsm₀).mpr himm₀
  let d₀ : SmoothImmersion (I := I.prod 𝓘(ℝ, ℝ))
      (M := M × Surgery.Topology.Circle) :=
    SmoothImmersion.slice (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
      c₀.map hmap himmMap t₀ (by simp)
  obtain ⟨τ, hτ, hτb, c, hc, hinit⟩ := H t₀ ht₀ d₀
  have hc' : c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda)
      (Icc t₀ (t₀ + τ)) := by
    rw [← hBhat]
    exact hc
  have hsu : t₀ < t₀ + τ := by linarith
  obtain ⟨ĉ, hĉsol, hĉmap⟩ := product_solution_lift (I := I) (M := M) A
    (fun t => B.family.metric t) lambda hlambda c hsu (Icc t₀ (t₀ + τ)) (Or.inr rfl) hc'
  exact ⟨τ, hτ, hτb, ĉ, hĉsol,
    fun z => (hĉmap z t₀ ⟨le_rfl, by linarith⟩).trans (hinit z)⟩

theorem terminalClosure_of_quotient (A : QuotientProductAtlas I M)
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningTerminalClosure (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      TerminalClosure B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H T haT hTb c K hK hc hcurv
  have hU : (c.unitTangent B.family.metric lambda).SmoothOn (I := I) (Ico a T) :=
    c.field_smoothOn_unitTangent (I := I) B.family.metric lambda hlambda hc.smooth hc.immersed
  have hmap : c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) (Ico a T) :=
    c.map_isSolutionOn_of_interval_of_isSolutionOn (I := I) A B.family.metric lambda hlambda
      haT (Or.inl rfl) hc
  have hcurvMap : ∀ x t, t ∈ Ico a T →
      c.map.curvature (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (B.family.metric s) lambda hlambda) x t ≤ K :=
    fun x t ht => by
      rw [c.map_curvature_eq (I := I) A B.family.metric lambda hlambda hc.smooth hU x t ht]
      exact hcurv x t ht
  obtain ⟨closed, hsol, hagr⟩ := H T haT hTb c.map K hK (by rw [hBhat]; exact hmap)
    (fun x t ht => by rw [hBhat]; exact hcurvMap x t ht)
  obtain ⟨ĉ, hĉsol, hĉmap⟩ := product_solution_lift (I := I) (M := M) A
    (fun t => B.family.metric t) lambda hlambda closed haT (Icc a T) (Or.inr rfl)
    (by rw [← hBhat]; exact hsol)
  exact ⟨ĉ, hĉsol, fun z t ht =>
    (hĉmap z t ⟨ht.1, ht.2.le⟩).trans (hagr z t ht)⟩

theorem extension_of_quotient (A : QuotientProductAtlas I M)
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningExtension (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      Extension B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H T haT hTb c K hK hc hcurv
  have hU : (c.unitTangent B.family.metric lambda).SmoothOn (I := I) (Ico a T) :=
    c.field_smoothOn_unitTangent (I := I) B.family.metric lambda hlambda hc.smooth hc.immersed
  have hmap : c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) (Ico a T) :=
    c.map_isSolutionOn_of_interval_of_isSolutionOn (I := I) A B.family.metric lambda hlambda
      haT (Or.inl rfl) hc
  have hcurvMap : ∀ x t, t ∈ Ico a T →
      c.map.curvature (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (B.family.metric s) lambda hlambda) x t ≤ K :=
    fun x t ht => by
      rw [c.map_curvature_eq (I := I) A B.family.metric lambda hlambda hc.smooth hU x t ht]
      exact hcurv x t ht
  obtain ⟨τ, hτ, hτb, extended, hsol, hagr⟩ := H T haT hTb c.map K hK
    (by rw [hBhat]; exact hmap) (fun x t ht => by rw [hBhat]; exact hcurvMap x t ht)
  have hsu : a < T + τ := by linarith
  obtain ⟨ê, hêsol, hêmap⟩ := product_solution_lift (I := I) (M := M) A
    (fun t => B.family.metric t) lambda hlambda extended hsu (Icc a (T + τ)) (Or.inr rfl)
    (by rw [← hBhat]; exact hsol)
  exact ⟨τ, hτ, hτb, ê, hêsol, fun z t ht =>
    (hêmap z t ⟨ht.1, by linarith [ht.2, hτ]⟩).trans (hagr z t ht)⟩

theorem continuation_of_quotient (A : QuotientProductAtlas I M)
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b),
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) →
      curveShorteningContinuation (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) Bhat →
      Continuation B lambda := by
  let := A.charts
  let := A.smoothManifold
  intro Bhat hBhat H
  have hsplit := (curveShorteningContinuation_iff_terminalClosure_and_extension
    (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) Bhat).mp H
  exact (continuation_iff_terminalClosure_and_extension
      (I := I) (M := M) B lambda).mpr
    ⟨terminalClosure_of_quotient (I := I) (M := M) A B lambda hlambda Bhat hBhat hsplit.1,
      extension_of_quotient (I := I) (M := M) A B lambda hlambda Bhat hBhat hsplit.2⟩

end ProductCurve

namespace ProductCurve

variable [IsEmpty M]

omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
theorem isEmpty_of_isEmpty : IsEmpty (ProductCurve M) :=
  ⟨fun c => (inferInstance : IsEmpty M).elim (c.map 0 0).1⟩

omit [CompleteSpace E] in
theorem localExistence_of_isEmpty
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) :
    LocalExistence B lambda := by
  intro t₀ ht₀ c₀
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c₀).elim

theorem terminalClosure_of_isEmpty [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    TerminalClosure B lambda := by
  intro T haT hTb c
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c).elim

theorem extension_of_isEmpty [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    Extension B lambda := by
  intro T haT hTb c
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c).elim

theorem continuation_of_isEmpty [T2Space M]
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) :
    Continuation B lambda := by
  intro T haT hTb c
  exact ((isEmpty_of_isEmpty : IsEmpty (ProductCurve M)).false c).elim

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
