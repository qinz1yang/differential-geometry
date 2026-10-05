import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
Positive minimizing interior prefixes stop at the first exit or loss of minimality.
The distance and interior predicates use the original metric and manifold model.
-/

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M]

def boundaryRayDomain (g : SmoothRiemannianMetric I M) (p : M) (γ : ℝ → M) : Set ℝ :=
  {t | 0 < t ∧ ∃ T, t < T ∧ ∀ s ∈ Ioc 0 T,
    I.IsInteriorPoint (γ s) ∧ riemannianEDistOf g p (γ s) = ENNReal.ofReal s}

theorem boundaryRayDomain_down (g : SmoothRiemannianMetric I M) (p : M) (γ : ℝ → M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ∈ boundaryRayDomain g p γ) :
    a ∈ boundaryRayDomain g p γ := by
  obtain ⟨hbpos, T, hbT, hT⟩ := hb
  exact ⟨ha, T, hab.trans_lt hbT, hT⟩

theorem boundaryRayDomain_alive (g : SmoothRiemannianMetric I M) (p : M) (γ : ℝ → M)
    {t : ℝ} (ht : t ∈ boundaryRayDomain g p γ) :
    I.IsInteriorPoint (γ t) ∧ riemannianEDistOf g p (γ t) = ENNReal.ofReal t := by
  obtain ⟨htpos, T, htT, hT⟩ := ht
  exact hT t ⟨htpos, htT.le⟩

theorem boundaryRayDomain_eq_union (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) :
    boundaryRayDomain g p γ = ⋃ T ∈ {T | ∀ s ∈ Ioc 0 T,
      I.IsInteriorPoint (γ s) ∧ riemannianEDistOf g p (γ s) = ENNReal.ofReal s}, Ioo 0 T := by
  ext t
  simp only [boundaryRayDomain, mem_ofPred_eq, mem_iUnion, mem_Ioo]
  constructor
  · rintro ⟨ht, T, htT, hT⟩
    exact ⟨T, hT, ht, htT⟩
  · rintro ⟨T, hT, ht, htT⟩
    exact ⟨ht, T, htT, hT⟩

theorem boundaryRayDomain_isOpen (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) : IsOpen (boundaryRayDomain g p γ) := by
  rw [boundaryRayDomain_eq_union]
  exact isOpen_biUnion fun T hT => isOpen_Ioo

theorem boundaryRayDomain_measurableSet (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) : MeasurableSet (boundaryRayDomain g p γ) :=
  (boundaryRayDomain_isOpen g p γ).measurableSet

theorem boundaryRayDomain_no_reentry (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hfail : ¬ (I.IsInteriorPoint (γ s) ∧
      riemannianEDistOf g p (γ s) = ENNReal.ofReal s)) :
    t ∉ boundaryRayDomain g p γ := by
  intro ht
  exact hfail (boundaryRayDomain_alive g p γ (boundaryRayDomain_down g p γ hs hst ht))

theorem boundaryRayDomain_dist_lt (g : SmoothRiemannianMetric I M) (p : M)
    (γ : ℝ → M) {t L : ℝ} (ht : t ∈ boundaryRayDomain g p γ) (htL : t < L) :
    riemannianEDistOf g p (γ t) < ENNReal.ofReal L := by
  rw [(boundaryRayDomain_alive g p γ ht).2]
  exact (ENNReal.ofReal_lt_ofReal_iff (ht.1.trans htL)).2 htL

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
