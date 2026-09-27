import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowShiftConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace ThreeModel)

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

theorem metricScalarAt_basepoint_eq_of_local_flow_limit_on_window
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    {f : ℕ → ℕ} (hf : StrictMono f) (F : PointedRiemannianConvergenceMaps X P f)
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)}
    {V : ℕ → Opens P.M} {N : ℕ → ℕ}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {c : ℕ → ℝ} (hc0 : 0 ≤ c 0) {G : ℝ → SmoothRiemannianMetric ThreeModel P.M}
    (hG0 : G 0 = P.metric) {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hW0 : ∀ᶠ n in atTop, ∀ z : W 0 n,
      metricScalarAt (h 0 n 0) z = metricScalarAt (X.obj n).metric z)
    {a : ℝ} (hbase : ∀ n, metricScalarAt (X.obj n).metric (X.obj n).basepoint = a) :
    metricScalarAt P.metric P.basepoint = a := by
  have hmem : P.basepoint ∈ (V 0 : Set P.M) := by
    rw [hV 0]
    change riemannianEDistOf P.metric P.basepoint P.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  let x₀ : V 0 := ⟨P.basepoint, hmem⟩
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp
    (hψ.tendsto_atTop.eventually (eventually_ge_atTop (N 0)))
  have hN0 : ∀ i, N 0 ≤ ψ (i + i0) := fun i => hi0 (i + i0) (Nat.le_add_left _ _)
  let g : ℕ → SmoothRiemannianMetric ThreeModel (V 0) := fun i =>
    localPullMetric (h 0 (f (ψ (i + i0))) 0) (φ 0 (ψ (i + i0)) (hN0 i))
      (hφ 0 (ψ (i + i0)) (hN0 i))
  have hconv' : ∀ K : Set (V 0), IsCompact K → ∀ e : ℝ, 0 < e → ∀ᶠ i in atTop,
      metricDerivNormSupOn K 2 (g i) ((G 0).restrictOpen (V 0))
        (P.metric.restrictOpen (V 0)) < e := by
    intro K hK e he
    obtain ⟨j₀, hj₀⟩ := hconv 0 K hK 2 e he
    filter_upwards [eventually_ge_atTop j₀] with i hi
    obtain ⟨hi', hbound⟩ := hj₀ (i + i0) (by omega)
    exact hbound 0 ⟨neg_nonpos.mpr hc0, le_rfl⟩
  have hlim := tendsto_metricScalarAt_of_metricDerivNormSupOn hconv'
    (tendsto_const_nhds (x := x₀))
  have hG0' : metricScalarAt ((G 0).restrictOpen (V 0)) x₀ =
      metricScalarAt P.metric P.basepoint := by
    rw [metricScalarAt_restrictOpen, hG0]
  rw [hG0'] at hlim
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  have hev : ∀ᶠ i in atTop, metricScalarAt (g i) x₀ = a := by
    filter_upwards [(hfψ.comp (tendsto_add_atTop_nat i0)).eventually hW0] with i hW
    have hW' : ∀ z : W 0 (f (ψ (i + i0))), metricScalarAt (h 0 (f (ψ (i + i0))) 0) z =
        metricScalarAt (X.obj (f (ψ (i + i0)))).metric z := hW
    have hb : F.map (ψ (i + i0)) (x₀ : P.M) = (X.obj (f (ψ (i + i0)))).basepoint :=
      F.basepoint_map (ψ (i + i0))
    change metricScalarAt (localPullMetric (h 0 (f (ψ (i + i0))) 0) (φ 0 (ψ (i + i0)) (hN0 i))
      (hφ 0 (ψ (i + i0)) (hN0 i))) x₀ = a
    rw [metricScalarAt_localPull, hW', hφF, hb]
    exact hbase _
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
