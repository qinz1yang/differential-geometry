import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Equation

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

theorem slabComparison_metric_hasDerivAt
    (L : StaticTerminalLimit X depthBound) {delta : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g)
    {t : ℝ} (ht : t ∈ Set.Ioo (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    HasDerivAt (fun s => (g s).inner x v w)
      (-2 * ricciTensor (I := I3) (g t) x v w) t := by
  let a : ℝ := (-delta + t) / 2
  let b : ℝ := t / 2
  have hat : a < t := by dsimp only [a]; linarith [ht.1]
  have htb : t < b := by dsimp only [b]; linarith [ht.2]
  have hleft : -delta < a := by dsimp only [a]; linarith [ht.1]
  have hright : b < 0 := by dsimp only [b]; linarith [ht.2]
  have hab : a ≤ b := (hat.trans htb).le
  have hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0 := by
    intro s hs
    exact ⟨hleft.le.trans hs.1, hs.2.trans hright.le⟩
  have hregular (i : ℕ) : Set.Icc a b ⊆ (X.interval i).regular := by
    intro s hs
    exact L.open_window_subset_regular hle i
      ⟨hleft.trans_le hs.1, hs.2.trans_lt hright⟩
  let f : ℕ → ℝ → ℝ := fun i s =>
    ((X.term (L.subseq (k i))).S.base.metric s).inner
      (L.maps.partialDiffeomorph (k i) x)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x w)
  have hderiv : ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i → ∀ s ∈ Set.Icc a b,
      HasDerivWithinAt (f i) (-2 * mappedRicciCoefficient L k x v w i s)
        (Set.Icc a b) s := by
    refine ⟨0, fun i _ s hs => ?_⟩
    have hd := metricDerivAt (I := I3)
      (X.term (L.subseq (k i))).S (X.term (L.subseq (k i))).isSolution
      ⟨s, hregular (L.subseq (k i)) hs⟩
      (L.maps.partialDiffeomorph (k i) x)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x w)
    have hr := metricRicciAt_apply_eq_ricciTensor (I := I3)
      ((X.term (L.subseq (k i))).S.base.metric s)
      (L.maps.partialDiffeomorph (k i) x)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x w)
    dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt] at hd
    erw [hr] at hd
    exact hd.hasDerivWithinAt
  have hvalue : ∀ s ∈ Set.Icc a b,
      Tendsto (fun i => f i s) atTop (𝓝 ((g s).inner x v w)) := by
    intro s hs
    exact slabComparison_metricCoeff_tendsto L hle hcomp hab hsub x v w hs
  have hric := Metric.tendstoUniformlyOn_iff.mp
    (slabComparison_ricciCoeff_tendstoUniformlyOn L hle hk hcomp hab hsub x v w)
  have hunif : ∀ eps : ℝ, 0 < eps → ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
      ∀ s ∈ Set.Icc a b,
        |-2 * mappedRicciCoefficient L k x v w i s -
          (-2 * ricciTensor (I := I3) (g s) x v w)| < eps := by
    intro eps heps
    obtain ⟨i0, hi0⟩ := Filter.eventually_atTop.mp (hric (eps / 2) (by positivity))
    refine ⟨i0, fun i hi s hs => ?_⟩
    have hbound := hi0 i hi s hs
    rw [dist_comm, Real.dist_eq] at hbound
    have hfactor : -2 * mappedRicciCoefficient L k x v w i s -
        (-2 * ricciTensor (I := I3) (g s) x v w) =
        -2 * (mappedRicciCoefficient L k x v w i s -
          ricciTensor (I := I3) (g s) x v w) := by ring
    rw [hfactor, abs_mul]
    norm_num only [abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
    linarith
  have hlimit := hasDeriv_lim_tail (convex_Icc a b) ⟨hat.le, htb.le⟩
    f (fun i s => -2 * mappedRicciCoefficient L k x v w i s)
    (fun s => (g s).inner x v w)
    (fun s => -2 * ricciTensor (I := I3) (g s) x v w) hderiv hvalue hunif
  exact hlimit.hasDerivAt (Icc_mem_nhds hat htb)

theorem IsSlabLimit.metric_hasDerivAt
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g)
    {t : ℝ} (ht : t ∈ Set.Ioo (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    HasDerivAt (fun s => (g s).inner x v w)
      (-2 * ricciTensor (I := I3) (g t) x v w) t := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_metric_hasDerivAt L hle hk hcomp ht x v w

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
