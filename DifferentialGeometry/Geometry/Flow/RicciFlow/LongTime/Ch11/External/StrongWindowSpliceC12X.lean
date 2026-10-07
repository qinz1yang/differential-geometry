import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialClosenessTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence

/-!
# Splice core (C12X, S16 `hwin` far branch; O-C12X-S16H G4b)

The far-early branch of `hwin` reduces every input (deep backward neck before the surgery,
standard-solution far region after it) to *spatial* `C^p` closeness, at each normalized time
`s ∈ [-1, 0]`, of a normalized flow on the fixed neck buffer to the scalar-one shrinking
cylinder.  This file turns such closeness into the time-jet tower of a strong neck, uniformly:

* `isSolutionOn_strongNeckBackground_C12X`: the scalar-one shrinking cylinder on the neck buffer
  is a Ricci flow on `[a, 0]`.
* `exists_strongNeckJets_of_uniform_close_C12X`: for `ε ∈ (0, 1)` and a depth buffer `μ > 0`
  there are `δ > 0`, `p` such that every Ricci flow on the neck buffer over `[-(1 + μ), 0]`
  which is `δ`-close in `C^p` to the cylinder at every `s ∈ [-1, 0]` carries a jet tower with
  `StrongNeckJetControl ε` (compactness: `exists_ordinary_metric_time_jets_on_closed_interval`,
  `metric_time_jet_errors_uniform_on_compacts_of_closed_interval`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance s16h_sphereDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance s16h_cylFinrank :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Fin 2) × ℝ))⟩

private local instance s16h_bufferSigma (ε : ℝ) : SigmaCompactSpace (spatialNeckBuffer ε) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel
      (spatialNeckBuffer ε).isOpen)

/-- The closed core of the neck buffer is compact. -/
theorem isCompact_spatialNeckClosedCore_C12X (ε : ℝ) :
    IsCompact (spatialNeckClosedCore ε) := by
  rw [Subtype.isCompact_iff]
  have himg : ((↑) : spatialNeckBuffer ε → SpatialNeckCylinder) '' spatialNeckClosedCore ε =
      (univ : Set SpatialNeckSphere) ×ˢ Icc (-ε⁻¹) ε⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, hx.1, hx.2⟩
    · rintro ⟨-, h1, h2⟩
      refine ⟨⟨y, ?_⟩, ⟨h1, h2⟩, rfl⟩
      change -ε⁻¹ - 1 < y.2 ∧ y.2 < ε⁻¹ + 1
      constructor <;> linarith
  rw [himg]
  exact isCompact_univ.prod isCompact_Icc

/-- The scalar-one shrinking cylinder on the neck buffer is a Ricci flow on `[a, 0]`. -/
theorem isSolutionOn_strongNeckBackground_C12X (ε a : ℝ) (ha : a ≤ 0) :
    IsSolutionOn ({ base.metric := strongNeckBackgroundMetric ε } :
      SolutionOn (I := SpatialNeckCylinderModel) (M := spatialNeckBuffer ε)
        (RealTimeInterval.closed a 0 ha)) := by
  have h1 := _root_.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval
    (E := EuclideanSpace ℝ (Fin 3)) (show a < 1 by linarith) le_rfl
  have h2 := isSolutionOn_timeRestrict h1 (D' := RealTimeInterval.closed a 0 ha)
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)
  have h3 := h2.localPullback (Subtype.val : spatialNeckBuffer ε → SpatialNeckCylinder)
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val _)
  refine IsSolutionOn.congr_metric h3 ?_
  intro t ht
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hs : t ≤ 0 := ht.2
  have hs1 : t < 1 := by linarith
  rw [strongNeckBackgroundMetric_of_nonpos ε t hs, SmoothRiemannianMetric.restrictOpen_inner]
  change (localPullMetric (_root_.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric
      (E := EuclideanSpace ℝ (Fin 3)) t) Subtype.val _).inner x v w = _
  rw [localPullMetric_inner, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  exact (_root_.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner hs1 x.val v
    w).trans (scalarOneShrinkingCylinderMetric_inner t hs1 x.val.1 x.val.2 v.1 w.1 v.2 w.2).symm

/-- **Uniform conversion.**  Spatial `C^p` closeness at every `s ∈ [-1, 0]` of a Ricci flow on
the neck buffer over `[-(1 + μ), 0]` to the scalar-one shrinking cylinder gives a time-jet tower
with `StrongNeckJetControl ε`. -/
theorem exists_strongNeckJets_of_uniform_close_C12X {ε μ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : 0 < μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : ℕ, ∀ S : SolutionOn (I := SpatialNeckCylinderModel)
        (M := spatialNeckBuffer ε) (RealTimeInterval.closed (-(1 + μ)) 0 (by linarith)),
      IsSolutionOn S →
      (∀ s ∈ Icc (-1 : ℝ) 0, ∀ q ≤ p, ∀ x : spatialNeckBuffer ε,
        metricDerivNorm q (S.base.metric s) (strongNeckBackgroundMetric ε s)
          (strongNeckBackgroundMetric ε 0) x < δ) →
      ∃ jet : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
          (M := spatialNeckBuffer ε) (n := ∞) 2,
        (∀ s x (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x), jet 0 s x v =
          (S.base.metric s).inner x (v 0) (v 1) -
            (strongNeckBackgroundMetric ε s).inner x (v 0) (v 1)) ∧
        (∀ b s, s ∈ Icc (-1 : ℝ) 0 → ∀ x (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
          HasDerivWithinAt (fun r => jet b r x v) (jet (b + 1) s x v) (Icc (-1 : ℝ) 0) s) ∧
        StrongNeckJetControl ε jet := by
  classical
  have hle : -(1 + μ) ≤ (0 : ℝ) := by linarith
  let D := RealTimeInterval.closed (-(1 + μ)) 0 hle
  let U := spatialNeckBuffer ε
  let S₀ : SolutionOn (I := SpatialNeckCylinderModel) (M := U) D :=
    { base.metric := strongNeckBackgroundMetric ε }
  have hS₀ : IsSolutionOn S₀ := isSolutionOn_strongNeckBackground_C12X ε (-(1 + μ)) hle
  have hac : -(1 + μ) < (-1 : ℝ) := by linarith
  have hcb : (-1 : ℝ) < 0 := by norm_num
  have hcarrier : D.carrier = Icc (-(1 + μ)) 0 := rfl
  have hregular : Ioo (-(1 + μ)) 0 ⊆ D.regular := Subset.rfl
  obtain ⟨C, hCzero, hC⟩ :=
    exists_ordinary_metric_time_jets_on_closed_interval S₀ hS₀ hac hcb hcarrier hregular
  let K := spatialNeckClosedCore ε
  have hK : IsCompact K := isCompact_spatialNeckClosedCore_C12X ε
  let R := strongNeckBackgroundMetric ε 0
  let order := ⌈ε⁻¹⌉₊
  by_contra hcon
  have key : ∀ n : ℕ, ∃ S : SolutionOn (I := SpatialNeckCylinderModel) (M := U) D,
      IsSolutionOn S ∧
      (∀ s ∈ Icc (-1 : ℝ) 0, ∀ q ≤ n, ∀ x : U,
        metricDerivNorm q (S.base.metric s) (strongNeckBackgroundMetric ε s) R x <
          1 / ((n : ℝ) + 1)) ∧
      ¬ ∃ jet : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel) (M := U) (n := ∞) 2,
        (∀ s x (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x), jet 0 s x v =
          (S.base.metric s).inner x (v 0) (v 1) -
            (strongNeckBackgroundMetric ε s).inner x (v 0) (v 1)) ∧
        (∀ b s, s ∈ Icc (-1 : ℝ) 0 → ∀ x (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
          HasDerivWithinAt (fun r => jet b r x v) (jet (b + 1) s x v) (Icc (-1 : ℝ) 0) s) ∧
        StrongNeckJetControl ε jet := by
    intro n
    by_contra hn
    exact hcon ⟨1 / ((n : ℝ) + 1), by positivity, n, fun S hS hclose => by
      by_contra hS'
      exact hn ⟨S, hS, hclose, hS'⟩⟩
  choose S hS hclose hfail using key
  choose B hBzero hB using fun n =>
    exists_ordinary_metric_time_jets_on_closed_interval (S n) (hS n) hac hcb hcarrier hregular
  have hconv : ∀ L : Set U, IsCompact L → ∀ r : ℕ, ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (-1 : ℝ) 0,
        metricDerivNormSupOn L r ((S n).base.metric t) (S₀.base.metric t) R < η := by
    intro L _ r η hη
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hη
    refine ⟨max r N₀, fun n hn t ht => ?_⟩
    have hle' : metricDerivNormSupOn L r ((S n).base.metric t) (S₀.base.metric t) R ≤
        1 / ((n : ℝ) + 1) :=
      metricDerivNormSupOn_le_of_forall L r _ _ R _ (by positivity) fun q hq x _ =>
        (hclose n t ht q (hq.trans ((le_max_left r N₀).trans hn)) x).le
    have hn₀ : (N₀ : ℝ) ≤ n := by exact_mod_cast (le_max_right r N₀).trans hn
    have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
      gcongr
    linarith
  have hbound (i j : ℕ) : ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (-1 : ℝ) 0, ∀ x ∈ K,
      tensor02CovDerivNormWith i (B n j t - C j t) (S₀.base.metric t) (S₀.base.metric t) x ≤
        ε / 2 :=
    metric_time_jet_errors_uniform_on_compacts_of_closed_interval
      S hS S₀ hS₀ hac hcb hcarrier hregular R hconv B C hBzero hCzero
      (fun n q t ht x => (hB n q t ht x).2) (fun q t ht x => (hC q t ht x).2) hK i j (ε / 2)
      (by positivity)
  choose N hN using hbound
  let n := (Finset.range (order + 1)).sup fun i => (Finset.range (order + 1)).sup (N i)
  refine hfail n ⟨fun b s => B n b s - C b s, ?_, ?_, ?_⟩
  · intro s x v
    change B n 0 s x v - C 0 s x v = _
    rw [hBzero n s, hCzero s, metricTensorField_apply, metricTensorField_apply]
  · intro b s hs x v
    let ev := tensor0SEvalCLM (I := SpatialNeckCylinderModel) (M := U) (x := x) v
    exact (ev.hasFDerivAt.comp_hasDerivWithinAt s (hB n b s hs x).2).sub
      (ev.hasFDerivAt.comp_hasDerivWithinAt s (hC b s hs x).2)
  · refine ⟨ε / 2, by positivity, by linarith, ?_⟩
    intro a b hab s hs x hx
    apply hN a b n ?_ s hs x hx
    exact le_trans
      (Finset.le_sup (f := N a) (Finset.mem_range.mpr (by omega)))
      (Finset.le_sup (f := fun i => (Finset.range (order + 1)).sup (N i))
        (Finset.mem_range.mpr (by omega)))

universe u

/-- **Strong neck from uniform spatial closeness.**  For `ε ∈ (0, 1/11)` and a depth buffer
`μ > 0` there are `δ > 0`, `p` such that: if a Ricci flow `S` lives on the window
`[t - (1 + μ) R⁻¹, t]` (`R` = scalar curvature at the marked point `x₀`) and its normalized
pullback by a neck embedding of the buffer is `δ`-close in `C^p` to the scalar-one cylinder at
every `s ∈ [-1, 0]`, then `x₀` is the center of a strong `ε`-neck at time `t`. -/
theorem exists_strongNeck_of_uniform_close_C12X {ε μ : ℝ} (hε : 0 < ε) (hε11 : ε < 1 / 11)
    (hμ : 0 < μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : ℕ, ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
      (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
      ∀ (t : ℝ) (yStar : SpatialNeckSphere) (f : C(spatialNeckBuffer ε, M))
        (hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f) (x₀ : M),
        f (spatialNeckCentralPoint ε hε yStar) = x₀ → ∀ hQ : 0 < S.scalar t x₀,
      Icc (t - (1 + μ) * (S.scalar t x₀)⁻¹) t ⊆ D.carrier →
      Ioo (t - (1 + μ) * (S.scalar t x₀)⁻¹) t ⊆ D.regular →
      (∀ s ∈ Icc (-1 : ℝ) 0, ∀ q ≤ p, ∀ x : spatialNeckBuffer ε,
        metricDerivNorm q (strongNeckNormalizedMetric S x₀ t hQ hf s)
          (strongNeckBackgroundMetric ε s) (strongNeckBackgroundMetric ε 0) x < δ) →
      Nonempty (StrongNeck S ε x₀ t) := by
  obtain ⟨δ, hδ, p, hcore⟩ := exists_strongNeckJets_of_uniform_close_C12X hε (by linarith) hμ
  refine ⟨δ, hδ, p, ?_⟩
  intro M _ _ _ _ _ D S hS t yStar f hf x₀ hx₀ hQ hwin hreg hclose
  have : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hle : -(1 + μ) ≤ (0 : ℝ) := by linarith
  have hRinv : 0 < (S.scalar t x₀)⁻¹ := inv_pos.mpr hQ
  have hpt (s : ℝ) :
      parabolicTime t (S.scalar t x₀) s = t + s * (S.scalar t x₀)⁻¹ := by
    simp only [parabolicTime, div_eq_mul_inv]
  have htD : t ∈ D.carrier := hwin ⟨by nlinarith, le_rfl⟩
  let D₀ := RealTimeInterval.closed (-(1 + μ)) 0 hle
  have hP := isSolutionOn_timeRestrict
    (parabolicSolution_isSolutionOn S hS t (S.scalar t x₀) hQ htD) (D' := D₀)
    (fun s hs => by
      change parabolicTime t (S.scalar t x₀) s ∈ D.carrier
      rw [hpt]
      exact hwin ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩)
    (fun s hs => by
      change parabolicTime t (S.scalar t x₀) s ∈ D.regular
      rw [hpt]
      exact hreg ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩)
  have hloc : IsLocalDiffeomorph SpatialNeckCylinderModel I3 ∞ f :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv f
      hf.contMDiff (fun x => immersionAt_mfderiv_injective (hf.isImmersion.isImmersionAt x))
      (by simp [Module.finrank_prod])
  have hP2 := hP.localPullback f hloc
  let S' : SolutionOn (I := SpatialNeckCylinderModel) (M := spatialNeckBuffer ε) D₀ :=
    { base.metric := fun s => strongNeckNormalizedMetric S x₀ t hQ hf s }
  have hS' : IsSolutionOn S' := by
    refine IsSolutionOn.congr_metric hP2 ?_
    intro s _
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [strongNeckNormalizedMetric_inner]
    change (localPullMetric (scaleMetric (S.scalar t x₀) hQ
      (S.base.metric (parabolicTime t (S.scalar t x₀) s))) f hloc).inner x v w = _
    rw [localPullMetric_inner, scaleMetric_inner]
    rfl
  obtain ⟨jet, hjet0, hjet1, hctrl⟩ := hcore S' hS' hclose
  let W : StrongNeckWitness S yStar x₀ t ε :=
    { dimension_three := by simp
      isSolution := hS
      epsilon_pos := hε
      epsilon_lt_one := by linarith
      scalar_pos := hQ
      time_window := fun r hr => hwin ⟨le_trans (by nlinarith) hr.1, hr.2⟩
      embedding := f
      smooth_embedding := hf
      marked := hx₀
      jet := jet
      jet_zero := fun s _ x v => hjet0 s x v
      jet_succ := fun b s hs x v => hjet1 b s hs x v
      closeness := hctrl }
  obtain ⟨N, -⟩ := W.exists_strongNeck hε11
  exact ⟨N⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
