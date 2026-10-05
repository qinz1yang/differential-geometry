import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryChartLength
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Actual ambient chart distances are bounded by original intrinsic distances on a uniform
small ball, by trapping and transporting actual nearly minimizing original curves.
-/

set_option autoImplicit false

noncomputable section

open Manifold Set Bundle MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] {H : Type*}
  [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

variable [ambientFinite : FiniteDimensional ℝ E] [manifoldT2 : T2Space M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_boundaryChart_edist_le
    (g : SmoothRiemannianMetric I M) (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (p : M) (U : TopologicalSpace.Opens E) (hpU : extChartAt I p p ∈ U)
    (hmetric : ∀ y ∈ (U : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = metricFlatModelInChart g p y v w) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ riemannianClosedBallOf g p r,
      ∀ b ∈ riemannianClosedBallOf g p r,
      riemannianEDistOf G (extChartAt I p a) (extChartAt I p b) ≤
        riemannianEDistOf g a b := by
  have hnb : (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' (U : Set E) ∈ 𝓝 p :=
    Filter.inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds (U.isOpen.mem_nhds hpU))
  obtain ⟨R, hR, hball⟩ :=
    Geometry.Metric.exists_pos_riemannianClosedBallOf_subset_of_mem_nhds g p hnb
  let r : ℝ := R / 4
  have hr : 0 < r := div_pos hR (by norm_num)
  have hsum : ENNReal.ofReal r + (ENNReal.ofReal (2 * r) + ENNReal.ofReal r) =
      ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * r) hr.le,
      ← ENNReal.ofReal_add hr.le (by positivity : 0 ≤ 2 * r + r)]
    congr 1
    dsimp only [r]
    ring
  refine ⟨r, hr, ?_⟩
  intro a ha b hb
  change riemannianEDistOf g p a ≤ ENNReal.ofReal r at ha
  change riemannianEDistOf g p b ≤ ENNReal.ofReal r at hb
  have hap : riemannianEDistOf g a p ≤ ENNReal.ofReal r := by
    simpa only [riemannianEDistOf_comm g a p] using ha
  have hd : riemannianEDistOf g a b ≤ ENNReal.ofReal (2 * r) := by
    have h := (riemannianEDistOf_triangle g a p b).trans (add_le_add hap hb)
    simpa only [two_mul, ENNReal.ofReal_add hr.le hr.le] using h
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hεfin
  let η : ℝ := min (ε : ℝ) r
  have hη : 0 < η := lt_min hε hr
  have hηr : ENNReal.ofReal η ≤ ENNReal.ofReal r :=
    ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hηε : ENNReal.ofReal η ≤ ε := by
    exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq (by simp)
  have hshort : riemannianEDistOf g a b <
      riemannianEDistOf g a b + ENNReal.ofReal η :=
    ENNReal.lt_add_right hεfin.ne (ENNReal.ofReal_pos.mpr hη).ne'
  obtain ⟨γ, hstart, hend, hγ, hlength⟩ := exists_lt_of_edistOf_lt g hshort
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1,
      γ t ∈ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' (U : Set E) := by
    intro t ht
    have hprefix := edistOf_le_metricPathELength g ht.1
      (hγ.mono (Icc_subset_Icc le_rfl ht.2))
    rw [hstart] at hprefix
    have htotal := (hprefix.trans (metricPathELength_mono g γ le_rfl ht.2)).trans
      (hlength.le.trans (add_le_add le_rfl hηr))
    apply hball
    change riemannianEDistOf g p (γ t) ≤ ENNReal.ofReal R
    calc
      _ ≤ riemannianEDistOf g p a + riemannianEDistOf g a (γ t) :=
        riemannianEDistOf_triangle g p a (γ t)
      _ ≤ ENNReal.ofReal r + (riemannianEDistOf g a b + ENNReal.ofReal r) :=
        add_le_add ha htotal
      _ ≤ ENNReal.ofReal r + (ENNReal.ofReal (2 * r) + ENNReal.ofReal r) :=
        add_le_add le_rfl (add_le_add hd le_rfl)
      _ = _ := hsum
  have hmap : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 ((extChartAt I p) ∘ γ) (Icc 0 1) :=
    (contMDiffOn_extChartAt (I := I) (x := p) (n := 1)).comp hγ
      (fun t ht => by simpa only [mem_preimage, extChartAt_source] using (hstay t ht).1)
  have hdist := edistOf_le_metricPathELength G zero_le_one hmap
  simp only [Function.comp_apply, hstart, hend] at hdist
  have heq := boundaryChart_metricPathELength g G p γ 0 1 hγ
    (fun t ht => (hstay t ⟨ht.1.le, ht.2.le⟩).1) (by
      intro t ht
      ext v w
      exact hmetric _ ⟨(hstay t ⟨ht.1.le, ht.2.le⟩).2,
        extChartAt_target_subset_range p ((extChartAt I p).map_source
          (hstay t ⟨ht.1.le, ht.2.le⟩).1)⟩ v w)
  exact (hdist.trans_eq heq).trans
    (hlength.le.trans (add_le_add le_rfl hηε))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
