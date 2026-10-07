import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_S15
import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

/-! # CH12-S99: CX3 at `⟨H.metric⟩` with explicit instances (O35 erratum)

In Ch12 contexts `IsRiemannianManifold (𝓡 3) H.Carrier` cannot be synthesized (the global
`Tensor0SBundle` model norm on `TangentSpace` wins), so the CX3 / S15 transfer-isotopy theorems
cannot be instantiated at `⟨H.metric⟩`.  Fix: erase those two instances (as CX3 does) and fix every
instance binder of CX3 by an explicit `letI` built from `H` (`withS99%`); the `edist` clause is
`riemannianEDistOf H.metric`, bridged by `riemannianEDistOf_eq_riemannianEDist`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential Bundle Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

section S99
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- `withS99% Hm as hE, b`: all CX3 instance binders at `⟨Hm.metric⟩` (`letI`, inlined into `b`),
and `hE : IsMetricNorm Hm.metric` (same recipe as `exists_complete_unit_geodesic_S92`).  Reusable by
downstream files (global macro; the use site needs its own `attribute [-instance]` as above and
`open Bundle`, otherwise `RiemannianBundle` instance search fails). -/
macro "withS99% " Hm:ident " as " hE:ident ", " b:term : term =>
  `(letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
    letI : IsManifold (𝓡 3) 1 ($Hm).Carrier :=
      IsManifold.of_le (I := 𝓡 3) (n := (∞ : ℕ∞ω)) (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
    letI : TopologicalSpace.MetrizableSpace ($Hm).Carrier := Manifold.metrizableSpace (𝓡 3) ($Hm).Carrier
    letI : T3Space ($Hm).Carrier := inferInstance
    letI : RiemannianBundle (fun x : ($Hm).Carrier ↦ TangentSpace (𝓡 3) x) :=
      ⟨($Hm).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (fun x : ($Hm).Carrier ↦ TangentSpace (𝓡 3) x) :=
      ⟨⟨($Hm).metric.inner, ($Hm).metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : PseudoEMetricSpace ($Hm).Carrier :=
      (EMetricSpace.ofRiemannianMetric (𝓡 3) ($Hm).Carrier).toPseudoEMetricSpace
    letI : CompleteSpace ($Hm).Carrier := ($Hm).complete.complete
    letI : LocallyCompactSpace ($Hm).Carrier :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) ($Hm).Carrier
    letI $hE : IsMetricNorm (I := 𝓡 3) (M := ($Hm).Carrier) ($Hm).metric :=
      fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) ($Hm).metric x v
    $b)

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

/-- Generic CX3 with the edist clause `riemannianEDistOf g` (split from the Ch12 wrapper to keep
each declaration under the heartbeat budget). -/
theorem transfer_isotopy_of_Ck_close_edistOf_S99 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (A : CkAtlas_S15 I M)
    {D D1 D2 : Set M} (hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (k : ℕ) (hk : 1 ≤ k) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : M, TangentSpace I p) (Ψ : ℝ → ℝ → M → M) (C : Set M),
            ContMDiff I I.tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 g A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
              (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            (∀ t : ℝ, |t| ≤ 2 → ∀ i : Fin A.n,
              ∀ x ∈ Metric.closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i), ∀ j ≤ k,
                ‖iteratedFDeriv ℝ j (chartDisplacement_CX3 (I := I) (A.ctr i)
                  (scaledExp_S15 g hEnorm X t)) x‖ < ε) := by
  obtain ⟨O, hO, hD2O, ρ, hρ, hmain⟩ :=
    transfer_isotopy_of_Ck_close_CX3 g hEnorm A hD hD1 hD2 hDD1 hD12 hD2A k hk
  refine ⟨O, hO, hD2O, ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨ε', hε', h⟩ := hmain ε hε
  refine ⟨ε', hε', fun Φ hΦ hdist hclose => h Φ hΦ (fun p hp => ?_) hclose⟩
  exact lt_of_eq_of_lt (riemannianEDistOf_eq_riemannianEDist g hEnorm p (Φ p)).symm (hdist p hp)

/-- Generic `transfer_isotopy_of_field_S15` with `riemannianEDistOf g` edist clauses. -/
theorem transfer_isotopy_of_field_edistOf_S99 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (A : CkAtlas_S15 I M) {D : Set M} (hD : IsCompact D)
    (hDA : D ⊆ A.cover) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : (∀ y : M, TangentSpace I y),
      ContMDiff I I.tangent ∞ (secBundle_S15 X) → CkSmall_S15 g A X 1 ε →
      ∃ (Ψ : ℝ → ℝ → M → M) (C : Set M), IsCompact C ∧
        ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
          (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
        (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
        (∀ s t y, y ∉ C → Ψ s t y = y) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = expMapIntrinsic g hEnorm x (t • X x)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, riemannianEDistOf g x (Ψ 0 t x) ≤
          ENNReal.ofReal (tanLen_S15 g (secBundle_S15 X x))) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → ∀ x ∈ D,
          riemannianEDistOf g (Ψ 0 s x) (Ψ 0 t x) ≤
            ENNReal.ofReal (tanLen_S15 g (secBundle_S15 X x) * (t - s))) := by
  obtain ⟨ε, hε, h⟩ := transfer_isotopy_of_field_S15 g hEnorm A hD hDA
  refine ⟨ε, hε, fun X hX hs => ?_⟩
  obtain ⟨Ψ, C, hC, h1, h2, h3, h4, h5, h6, h7⟩ := h X hX hs
  exact ⟨Ψ, C, hC, h1, h2, h3, h4, h5,
    fun t ht x hx => (riemannianEDistOf_eq_riemannianEDist g hEnorm _ _).trans_le (h6 t ht x hx),
    fun s t hs hst ht x hx =>
      (riemannianEDistOf_eq_riemannianEDist g hEnorm _ _).trans_le (h7 s t hs hst ht x hx)⟩

/-- Generic `exists_CkSmall_transfer_field_CX3` with `riemannianEDistOf g` edist clauses. -/
theorem exists_CkSmall_transfer_field_edistOf_S99 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (A : CkAtlas_S15 I M) {D1 D2 : Set M} (hD1 : IsCompact D1)
    (hD2 : IsCompact D2) (hD12 : D1 ⊆ interior D2) (k : ℕ) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p ∈ D1, χ p = 1) ∧
      (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ interior D2 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ v : M → TangentBundle I M, ContMDiffOn I I.tangent ∞ v O ∧
            (∀ p ∈ O, (v p).proj = p ∧ expMapIntrinsic g hEnorm p (v p).snd = Φ p ∧
              tanLen_S15 g (v p) = (riemannianEDistOf g p (Φ p)).toReal) ∧
            ContMDiff I I.tangent ∞ (secBundle_S15 (fun p => χ p • secOf_S15 v p)) ∧
            (∀ p ∈ D1, expMapIntrinsic g hEnorm p (χ p • secOf_S15 v p) = Φ p) ∧
            (∀ p, p ∉ D2 → χ p • secOf_S15 v p = 0) ∧
            CkSmall_S15 g A (fun p => χ p • secOf_S15 v p) k ε := by
  obtain ⟨O, hO, hD2O, ρ, hρ, χ, h1, h2, h3, h4, h⟩ :=
    exists_CkSmall_transfer_field_CX3 g hEnorm A hD1 hD2 hD12 k
  refine ⟨O, hO, hD2O, ρ, hρ, χ, h1, h2, h3, h4, fun ε hε => ?_⟩
  obtain ⟨ε', hε', hh⟩ := h ε hε
  refine ⟨ε', hε', fun Φ hΦ hv hc => ?_⟩
  obtain ⟨v, hv1, hv2, rest⟩ := hh Φ hΦ (fun p hp =>
    lt_of_eq_of_lt (riemannianEDistOf_eq_riemannianEDist g hEnorm p (Φ p)).symm (hv p hp)) hc
  refine ⟨v, hv1, fun p hp => ?_, rest⟩
  obtain ⟨a, b, c⟩ := hv2 p hp
  exact ⟨a, b, c.trans (congrArg ENNReal.toReal (riemannianEDistOf_eq_riemannianEDist g hEnorm p (Φ p)).symm)⟩

end Generic

/-- **CX3 at `⟨H.metric⟩`** (`transfer_isotopy_of_Ck_close_CX3` with explicit instances; the
`edist` clause is `riemannianEDistOf H.metric`, not a restated `Manifold.riemannianEDist`). -/
theorem transfer_isotopy_of_Ck_close_S99 (Hm : FiniteVolumeHyperbolicModel.{u})
    (A : CkAtlas_S15 (𝓡 3) Hm.Carrier) {D D1 D2 : Set Hm.Carrier}
    (hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (k : ℕ) (hk : 1 ≤ k) :
    withS99% Hm as hE,
    ∃ O : Set Hm.Carrier, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : Hm.Carrier → Hm.Carrier, ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf Hm.metric p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : Hm.Carrier, TangentSpace (𝓡 3) p) (Ψ : ℝ → ℝ → Hm.Carrier → Hm.Carrier)
            (C : Set Hm.Carrier),
            ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 Hm.metric A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic Hm.metric hE p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
              (fun q : (ℝ × ℝ) × Hm.Carrier => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 Hm.metric hE X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            (∀ t : ℝ, |t| ≤ 2 → ∀ i : Fin A.n,
              ∀ x ∈ Metric.closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i), ∀ j ≤ k,
                ‖iteratedFDeriv ℝ j (chartDisplacement_CX3 (I := 𝓡 3) (A.ctr i)
                  (scaledExp_S15 Hm.metric hE X t)) x‖ < ε) :=
  withS99% Hm as hE,
    transfer_isotopy_of_Ck_close_edistOf_S99 Hm.metric hE A hD hD1 hD2 hDD1 hD12 hD2A k hk

/-- `transfer_isotopy_of_field_S15` at `⟨H.metric⟩` (edist clauses `riemannianEDistOf H.metric`). -/
theorem transfer_isotopy_of_field_S99 (Hm : FiniteVolumeHyperbolicModel.{u})
    (A : CkAtlas_S15 (𝓡 3) Hm.Carrier) {D : Set Hm.Carrier} (hD : IsCompact D)
    (hDA : D ⊆ A.cover) :
    withS99% Hm as hE,
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : (∀ y : Hm.Carrier, TangentSpace (𝓡 3) y),
      ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (secBundle_S15 X) → CkSmall_S15 Hm.metric A X 1 ε →
      ∃ (Ψ : ℝ → ℝ → Hm.Carrier → Hm.Carrier) (C : Set Hm.Carrier), IsCompact C ∧
        ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : (ℝ × ℝ) × Hm.Carrier => Ψ q.1.1 q.1.2 q.2) ∧
        (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
        (∀ s t y, y ∉ C → Ψ s t y = y) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = expMapIntrinsic Hm.metric hE x (t • X x)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, riemannianEDistOf Hm.metric x (Ψ 0 t x) ≤
          ENNReal.ofReal (tanLen_S15 Hm.metric (secBundle_S15 X x))) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → ∀ x ∈ D,
          riemannianEDistOf Hm.metric (Ψ 0 s x) (Ψ 0 t x) ≤
            ENNReal.ofReal (tanLen_S15 Hm.metric (secBundle_S15 X x) * (t - s)))  :=
  withS99% Hm as hE, transfer_isotopy_of_field_edistOf_S99 Hm.metric hE A hD hDA

/-- `transfer_isotopy_Ck_bound_CX3` at `⟨H.metric⟩` (no edist clause; instances only). -/
theorem transfer_isotopy_Ck_bound_S99 (Hm : FiniteVolumeHyperbolicModel.{u})
    (A : CkAtlas_S15 (𝓡 3) Hm.Carrier) (k : ℕ) :
    withS99% Hm as hE,
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ X : (∀ p : Hm.Carrier, TangentSpace (𝓡 3) p),
        ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (secBundle_S15 X) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ → CkSmall_S15 Hm.metric A X k ε →
          ∀ t : ℝ, |t| ≤ 2 → ∀ i : Fin A.n,
            ∀ x ∈ Metric.closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i),
              scaledExp_S15 Hm.metric hE X t ((extChartAt (𝓡 3) (A.ctr i)).symm x) ∈
                (extChartAt (𝓡 3) (A.ctr i)).source ∧
              ∀ j ≤ k, ‖iteratedFDeriv ℝ j
                (chartDisplacement_CX3 (I := 𝓡 3) (A.ctr i) (scaledExp_S15 Hm.metric hE X t)) x‖ ≤
                  C * ε :=
  withS99% Hm as hE, transfer_isotopy_Ck_bound_CX3 Hm.metric hE A k

/-- `exists_CkSmall_transfer_field_CX3` at `⟨H.metric⟩` (edist clauses `riemannianEDistOf H.metric`). -/
theorem exists_CkSmall_transfer_field_S99 (Hm : FiniteVolumeHyperbolicModel.{u})
    (A : CkAtlas_S15 (𝓡 3) Hm.Carrier) {D1 D2 : Set Hm.Carrier} (hD1 : IsCompact D1)
    (hD2 : IsCompact D2) (hD12 : D1 ⊆ interior D2) (k : ℕ) :
    withS99% Hm as hE,
    ∃ O : Set Hm.Carrier, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ χ : Hm.Carrier → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p ∈ D1, χ p = 1) ∧
      (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ interior D2 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : Hm.Carrier → Hm.Carrier, ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf Hm.metric p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ v : Hm.Carrier → TangentBundle (𝓡 3) Hm.Carrier, ContMDiffOn (𝓡 3) (𝓡 3).tangent ∞ v O ∧
            (∀ p ∈ O, (v p).proj = p ∧ expMapIntrinsic Hm.metric hE p (v p).snd = Φ p ∧
              tanLen_S15 Hm.metric (v p) = (riemannianEDistOf Hm.metric p (Φ p)).toReal) ∧
            ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (secBundle_S15 (fun p => χ p • secOf_S15 v p)) ∧
            (∀ p ∈ D1, expMapIntrinsic Hm.metric hE p (χ p • secOf_S15 v p) = Φ p) ∧
            (∀ p, p ∉ D2 → χ p • secOf_S15 v p = 0) ∧
            CkSmall_S15 Hm.metric A (fun p => χ p • secOf_S15 v p) k ε  :=
  withS99% Hm as hE, exists_CkSmall_transfer_field_edistOf_S99 Hm.metric hE A hD1 hD2 hD12 k

end S99
end GC.LongTime.Ch12
