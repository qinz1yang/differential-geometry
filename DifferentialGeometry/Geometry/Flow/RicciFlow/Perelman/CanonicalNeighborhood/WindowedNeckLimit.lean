import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckLimitTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckParabolicTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem StrongNeck.eventually_transport_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha : ℝ} {p : L.M} (nk : StrongNeck L.S eps p 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha) :
    ∀ᶠ i in atTop, ∃ nk' : StrongNeck (S (phi i)) (2 * alpha)
        ((W (phi i)).embedding (F.map i p)) (t (phi i)),
      nk'.map = partialDiffeomorphTransMixed nk.map
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) := by
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let T := fun i => parabolicSolution (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos (W (phi i)).time_mem
  have hT (i : ℕ) : IsSolutionOn (T i) :=
    parabolicSolution_isSolutionOn (S (phi i)) (hS (phi i)) _ _ _ _
  let B : Set Cylinder := univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹
  have hB : IsCompact B := isCompact_univ.prod isCompact_Icc
  have hrad : alpha⁻¹ < eps⁻¹ :=
    inv_strictAnti₀ nk.eps_pos (heps.trans_le (neckModelTolerance_le alpha))
  have hBsource : B ⊆ nk.map.source := by
    intro y hy
    exact nk.domain ⟨hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  let K := nk.map '' B
  have hK : IsCompact K := hB.image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hBsource)
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  let _ : RegularSpace L.M := inferInstance
  obtain ⟨U, hUopen, hKU, _hUuniv, hUcompact⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  let U' : TopologicalSpace.Opens L.M := ⟨U, hUopen⟩
  let nk0 := nk.mono heps.le
    ((neckModelTolerance_le alpha).trans_lt (by linarith : alpha < 1 / 11))
  have houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk0.map y ∈ K := by
    intro y hy
    exact ⟨y, ⟨hy.1, hy.2.1.le, hy.2.2.le⟩, rfl⟩
  have hcomp (A : ℝ) (hA : 0 < A) (order : ℕ) (eta : ℝ) (heta : 0 < eta) :
      ∀ᶠ i in atTop, closure U ⊆ (Psi i).source ∧
        Nonempty (MetricComparisonOn L.S.base.metric (T i).base.metric
          (Psi i) (closure U) (Icc (-A) 0) order eta) :=
    WindowedModelWitness.eventually_composed_comparison hS W hdelta
      (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
      hUcompact hA order heta
  have hsource : ∀ᶠ i in atTop, (U' : Set L.M) ⊆ (Psi i).source :=
    (hcomp 1 zero_lt_one 0 1 zero_lt_one).mono fun _ hi => subset_closure.trans hi.1
  have hdinv : Tendsto (fun i => (delta (phi i))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hdelta.comp hphi, .of_forall fun i => (W (phi i)).eps_pos⟩)
  have htimes : ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (parabolicInterval (D (phi i)) (t (phi i))
        ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).time_mem).carrier ∧
      Ioo (-A) 0 ⊆ (parabolicInterval (D (phi i)) (t (phi i))
        ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).time_mem).regular := by
    intro A _hA
    filter_upwards [hdinv.eventually_ge_atTop A] with i hi
    obtain ⟨hcarrier, hregular⟩ := (W (phi i)).normalized_window (hreg (phi i))
    exact ⟨(Icc_subset_Icc (neg_le_neg hi) le_rfl).trans hcarrier,
      (Ioo_subset_Ioo (neg_le_neg hi) le_rfl).trans hregular⟩
  have hcompare : ∀ A : ℝ, 0 < A → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn L.S.base.metric (T i).base.metric
        (Psi i) U' (Icc (-A) 0) order eta) := by
    intro A hA order eta heta
    filter_upwards [hcomp A hA order eta heta] with i hi
    obtain ⟨C⟩ := hi.2
    exact ⟨C.mono subset_closure le_rfl le_rfl⟩
  have hnecks := nk0.eventually_transport_of_comparisons L.isSolution ha hsmall U' hUcompact
    hK hKU houter T hT Psi hsource htimes hcompare
  filter_upwards [hnecks] with i hi
  obtain ⟨nk', hmap⟩ := hi
  have hh : ∃ out : StrongNeck (S (phi i)) (2 * alpha) (Psi i p)
      (parabolicTime (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i))) 0),
      out.map = partialDiffeomorphTransMixed nk.map (Psi i) := by
    refine ⟨nk'.ofParabolic (t (phi i)) ((S (phi i)).scalar (t (phi i)) (x (phi i)))
      (W (phi i)).scalar_pos (W (phi i)).time_mem 0, ?_⟩
    exact hmap
  rw [parabolicTime_zero] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
