import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X]


def busemannApprox (c : ℝ≥0 → X) (t : ℝ≥0) (x : X) : ℝ :=
  (t : ℝ) - dist x (c t)

def busemann (c : ℝ≥0 → X) (x : X) : ℝ :=
  ⨆ t : ℝ≥0, busemannApprox c t x

private theorem ray_dist_of_le {c : ℝ≥0 → X} (hc : Isometry c)
    {s t : ℝ≥0} (hst : s ≤ t) : dist (c s) (c t) = (t : ℝ) - s := by
  rw [hc.dist_eq]
  change |(s : ℝ) - t| = (t : ℝ) - s
  change (s : ℝ) ≤ t at hst
  rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]


theorem busemannApprox_monotone {c : ℝ≥0 → X} (hc : Isometry c) (x : X) :
    Monotone (fun t => busemannApprox c t x) := by
  intro s t hst
  have h := dist_triangle x (c s) (c t)
  rw [ray_dist_of_le hc hst] at h
  dsimp only [busemannApprox]
  linarith


theorem abs_busemannApprox_le {c : ℝ≥0 → X} (hc : Isometry c) (t : ℝ≥0) (x : X) :
    |busemannApprox c t x| ≤ dist x (c 0) := by
  have hrad : dist (c 0) (c t) = (t : ℝ) := by
    simpa only [NNReal.coe_zero, sub_zero] using
      ray_dist_of_le hc (s := 0) (t := t) zero_le
  have hleft := dist_triangle x (c 0) (c t)
  have hright := dist_triangle (c 0) x (c t)
  rw [hrad] at hleft hright
  rw [dist_comm (c 0) x] at hright
  rw [abs_le]
  dsimp only [busemannApprox]
  constructor <;> linarith

private theorem busemannApprox_bddAbove {c : ℝ≥0 → X} (hc : Isometry c) (x : X) :
    BddAbove (range (fun t => busemannApprox c t x)) := by
  refine ⟨dist x (c 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (abs_le.mp (abs_busemannApprox_le hc t x)).2


theorem busemannApprox_le_busemann {c : ℝ≥0 → X} (hc : Isometry c) (t : ℝ≥0) (x : X) :
    busemannApprox c t x ≤ busemann c x :=
  le_ciSup (busemannApprox_bddAbove hc x) t


theorem tendsto_busemannApprox {c : ℝ≥0 → X} (hc : Isometry c) (x : X) :
    Tendsto (fun t => busemannApprox c t x) atTop (𝓝 (busemann c x)) :=
  tendsto_atTop_ciSup (busemannApprox_monotone hc x) (busemannApprox_bddAbove hc x)

theorem lipschitzWith_busemannApprox (c : ℝ≥0 → X) (t : ℝ≥0) :
    LipschitzWith 1 (busemannApprox c t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  have heq : busemannApprox c t x - busemannApprox c t y =
      dist y (c t) - dist x (c t) := by
    dsimp only [busemannApprox]
    ring
  rw [heq]
  exact (abs_dist_sub_le y x (c t)).trans_eq (dist_comm y x)


theorem lipschitzWith_busemann {c : ℝ≥0 → X} (hc : Isometry c) :
    LipschitzWith 1 (busemann c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((tendsto_busemannApprox hc x).dist (tendsto_busemannApprox hc y))
  exact Filter.Eventually.of_forall fun t => (lipschitzWith_busemannApprox c t).dist_le_mul x y

theorem tendsto_busemannApprox_of_tendsto {c : ℝ≥0 → X} (hc : Isometry c)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ≥0} {x : ι → X} {p : X}
    (ht : Tendsto t l atTop) (hx : Tendsto x l (𝓝 p)) :
    Tendsto (fun i => busemannApprox c (t i) (x i)) l (𝓝 (busemann c p)) := by
  apply ((tendsto_busemannApprox hc p).comp ht).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun i => by simpa only [Function.comp_def, NNReal.coe_one, one_mul] using
      (lipschitzWith_busemannApprox c (t i)).dist_le_mul p (x i))
  simpa only [dist_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ι => p) l (𝓝 p)).dist hx

theorem abs_busemann_le {c : ℝ≥0 → X} (hc : Isometry c) (x : X) :
    |busemann c x| ≤ dist x (c 0) :=
  le_of_tendsto (tendsto_busemannApprox hc x).abs
    (Filter.Eventually.of_forall fun t => abs_busemannApprox_le hc t x)


theorem busemann_ray {c : ℝ≥0 → X} (hc : Isometry c) (s : ℝ≥0) :
    busemann c (c s) = (s : ℝ) := by
  have hevent : ∀ᶠ t in atTop, busemannApprox c t (c s) = (s : ℝ) := by
    filter_upwards [eventually_ge_atTop s] with t ht
    rw [busemannApprox, ray_dist_of_le hc ht]
    ring
  exact tendsto_nhds_unique (tendsto_busemannApprox hc (c s))
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent))

theorem tendstoUniformlyOn_busemannApprox {c : ℝ≥0 → X} (hc : Isometry c)
    {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn (busemannApprox c) (busemann c) atTop K :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun t => (lipschitzWith_busemannApprox c t).continuous.continuousOn)
    (fun x _ => busemannApprox_monotone hc x)
    (lipschitzWith_busemann hc).continuous.continuousOn
    (fun x _ => tendsto_busemannApprox hc x)

end DifferentialGeometry.Geometry.Topology

end
