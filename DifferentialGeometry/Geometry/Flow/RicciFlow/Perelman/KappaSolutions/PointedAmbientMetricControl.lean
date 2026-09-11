import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedMetricControl

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance fullAmbientControlTopology : TopologicalSpace L.M := L.topology
local instance fullAmbientControlCharted : ChartedSpace H L.M := L.charted
local instance fullAmbientControlSmooth : IsManifold I ∞ L.M := L.smooth
local instance fullAmbientControlT2 : T2Space L.M := L.t2
local instance fullAmbientControlSigmaCompact : SigmaCompactSpace L.M := L.sigmaCompact

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [I.Boundaryless] in
theorem metricSource_inclusion_mfderiv_injective
    (k : ℕ) (D : MetricSourceData (I := I) Φ k) :
    let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    ∀ x : MetricSourceDomain (I := I) Φ k,
      Function.Injective
        (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) := by
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let _ : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  dsimp only
  intro x
  let A := mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x
  have hzero (v : TangentSpace I x) (hv : A v = 0) : v = 0 := by
    by_contra hne
    have hpos := D.limitMetric.pos x v hne
    have hinner := D.limit_inner x v v
    change D.limitMetric.inner x v v = L.metric.inner (x : L.M) (A v) (A v) at hinner
    rw [hv] at hinner
    have hvanish : D.limitMetric.inner x v v = 0 := by simpa using hinner
    linarith
  intro v w hvw
  apply sub_eq_zero.mp
  apply hzero (v - w)
  rw [map_sub, hvw, sub_self]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metricSource_inclusion_mfderiv_surjective
    (k : ℕ) (D : MetricSourceData (I := I) Φ k) :
    let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    ∀ x : MetricSourceDomain (I := I) Φ k,
      Function.Surjective
        (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) := by
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  dsimp only
  intro x
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let _ : FiniteDimensional ℝ (TangentSpace I (x : L.M)) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rfl : Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I (x : L.M)))
    (f := (mfderiv I I
      (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x).toLinearMap)).1
    (metricSource_inclusion_mfderiv_injective k D x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
theorem metricSource_inclusion_mdifferentiableAt
    (k : ℕ) (D : MetricSourceData (I := I) Φ k) :
    let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    ∀ x : MetricSourceDomain (I := I) Φ k,
      MDifferentiableAt I I
        (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x := by
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  dsimp only
  intro x
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ)
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let _ : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  by_contra hnot
  have hzero := mfderiv_zero_of_not_mdifferentiableAt hnot
  apply hv
  apply metricSource_inclusion_mfderiv_injective k D x
  simp only [hzero, zero_apply]

omit [I.Boundaryless] in
theorem exists_pointed_full_ambient_quadratic_control
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (K : Set L.M) (hK : IsCompact K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → K ⊆ Φ.source k ∧
      (let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
       let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
       ∀ x : L.M, x ∈ K → ∀ v : TangentSpace I x,
         |(X.obj (subseq k)).metric.inner (Φ.map k x)
             (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x v) -
           L.metric.inner x v v| ≤ epsilon * L.metric.inner x v v) := by
  obtain ⟨k0, hk0⟩ := exists_pointed_ambient_quadratic_control
    C hreference K hK epsilon hepsilon
  refine ⟨k0, fun k hk => ⟨(hk0 k hk).1, ?_⟩⟩
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := (C.domain k).topology
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := (C.domain k).charted
  let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  dsimp only
  intro x hx v
  let z : MetricSourceDomain (I := I) Φ k := ⟨x, (hk0 k hk).1 hx⟩
  obtain ⟨w, hw⟩ := metricSource_inclusion_mfderiv_surjective k (C.domain k) z v
  have hIncl := metricSource_inclusion_mdifferentiableAt k (C.domain k) z
  have hMap : MDifferentiableAt I I (Φ.map k) x :=
    (Φ.partialDiffeomorph k).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) ((hk0 k hk).1 hx)
  have hchain : mfderiv I I
      (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) z w =
      mfderiv I I (Φ.map k) x v := by
    calc
      _ = mfderiv I I (Φ.map k) x
          (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) z w) :=
        mfderiv_comp_apply z hMap hIncl w
      _ = _ := by rw [hw]
  have h := (hk0 k hk).2 z hx w
  rw [hchain, hw] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
