import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Defs
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open VolumeComparison (radialCurve)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

theorem minimizingDomain_subset_expDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    minimizingDomain (I := I) g p ⊆ expDomain (I := I) g p := by
  intro v hv
  by_contra hdom
  have hexp : expMap (I := I) g p (show TangentSpace I p from v) = p :=
    expMap_of_not_mem_expDomain (I := I) hdom
  by_cases hv0 : v = 0
  · subst v
    exact hdom (zero_mem_expDomain (I := I) g p)
  · have hpos : 0 < Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v)) :=
      Real.sqrt_pos.mpr (g.pos p v hv0)
    change ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) at hv
    rw [hexp, riemannianEDist_self] at hv
    exact (ENNReal.ofReal_pos.mpr hpos).ne' hv

theorem sqrt_inner_self_eq_of_mem_minimizingDomain_of_expMap_eq
    (g : SmoothRiemannianMetric I M) (p : M) {v w : E}
    (hv : v ∈ minimizingDomain (I := I) g p) (hw : w ∈ minimizingDomain (I := I) g p)
    (hvw : expMap (I := I) g p (show TangentSpace I p from v) =
      expMap (I := I) g p (show TangentSpace I p from w)) :
    Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v)) =
      Real.sqrt (g.inner p (show TangentSpace I p from w)
        (show TangentSpace I p from w)) := by
  change ENNReal.ofReal (Real.sqrt
    (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))) =
    riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) at hv
  change ENNReal.ofReal (Real.sqrt
    (g.inner p (show TangentSpace I p from w)
      (show TangentSpace I p from w))) =
    riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from w)) at hw
  apply (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)).mp
  calc
    ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from v)) := hv
    _ = riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from w)) := by rw [hvw]
    _ = ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from w)
          (show TangentSpace I p from w))) := hw.symm

theorem smul_mem_extendibleMinimizingDomain_of_pos_of_le
    (g : SmoothRiemannianMetric I M) (p : M) {u : E} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hraw : b • u ∈ extendibleMinimizingDomain (I := I) g p) :
    a • u ∈ extendibleMinimizingDomain (I := I) g p := by
  have hb : 0 < b := ha.trans_le hab
  rcases hraw with ⟨c, hc, hcraw⟩
  refine ⟨c * b / a, ?_, ?_⟩
  · apply (lt_div_iff₀ ha).mpr
    have hcb : b < c * b := by
      simpa only [one_mul, mul_one, mul_comm] using
        (mul_lt_mul_of_pos_right hc hb)
    nlinarith
  · rw [smul_smul, div_mul_cancel₀ (c * b) ha.ne']
    simpa only [smul_smul] using hcraw

variable [I.Boundaryless] [T2Space (TangentBundle I M)]

theorem zero_mem_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ minimizingDomain (I := I) g p := by
  change ENNReal.ofReal (Real.sqrt
    (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p))) =
      riemannianEDist I p (expMap (I := I) g p (0 : TangentSpace I p))
  rw [expMap_zero, riemannianEDist_self]
  simp

theorem zero_mem_extendibleMinimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ extendibleMinimizingDomain (I := I) g p := by
  refine ⟨2, by norm_num, ?_⟩
  simpa only [smul_zero] using zero_mem_minimizingDomain (I := I) g p

theorem smul_mem_extendibleMinimizingDomain_of_le
    (g : SmoothRiemannianMetric I M) (p : M) {u : E} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hv : b • u ∈ extendibleMinimizingDomain (I := I) g p) :
    a • u ∈ extendibleMinimizingDomain (I := I) g p := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simpa only [zero_smul] using zero_mem_extendibleMinimizingDomain (I := I) g p
  · exact smul_mem_extendibleMinimizingDomain_of_pos_of_le (I := I) g p ha hab hv

theorem extendibleMinimizingDomain_subset_minimizingDomain
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    extendibleMinimizingDomain (I := I) g p ⊆ minimizingDomain (I := I) g p := by
  intro v hv
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨c, hc, hcraw⟩ := hv
  have hcpos : 0 < c := one_pos.trans hc
  have hcdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    minimizingDomain_subset_expDomain (I := I) g p hcraw
  have hdom : ∀ t ∈ Icc (0 : ℝ) c,
      (show TangentSpace I p from t • v) ∈ expDomain (I := I) g p := by
    intro t ht
    have ht_div : t / c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hcpos.le, (div_le_one hcpos).mpr ht.2⟩
    have hscale := Exponential.smul_mem_expDomain (I := I) (g := g) (p := p)
      (v := show TangentSpace I p from c • v) hcdom ht_div
    change (show TangentSpace I p from (t / c) • (c • v)) ∈
      expDomain (I := I) g p at hscale
    simpa only [smul_smul, div_mul_cancel₀ t hcpos.ne', one_smul] using hscale
  let γ : ℝ → M := radialCurve (I := I) g p v
  let L : ℝ := Real.sqrt (g.inner p (show TangentSpace I p from v)
    (show TangentSpace I p from v))
  have hLnn : 0 ≤ L := Real.sqrt_nonneg _
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (0 : ℝ) c) := by
    intro t ht
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => s • v) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    have hexp := contMDiffAt_expMap (I := I) g p (hdom t ht)
    have hcurve : radialCurve (I := I) g p v =
        fun s : ℝ => expMap (I := I) g p
          (show TangentSpace I p from s • v) := by
      funext s
      rfl
    dsimp only [γ]
    rw [hcurve]
    exact ((hexp.comp t hline).of_le
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffWithinAt
  have hspeed : ∀ t ∈ Icc (0 : ℝ) c,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ ≤ ENNReal.ofReal L := by
    intro t ht
    rw [hEnorm]
    change ENNReal.ofReal (Real.sqrt
      (g.inner (radialCurve (I := I) g p v t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p v) t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p v) t))) ≤
      ENNReal.ofReal L
    have hspeed : g.inner (radialCurve (I := I) g p v t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p v) t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p v) t) =
        g.inner p v v := by
      simpa only [radialCurve] using!
        inner_curveVelocity_expMap_smul (I := I) g p v (hdom t ht)
    rw [hspeed]
  have h01 := HopfRinow.curve_edist_le_speed_mul_time (I := I)
    (γ := γ) (s := (0 : ℝ)) (t := (1 : ℝ)) (c := L)
    hLnn zero_le_one
    (hγsmooth.mono (Icc_subset_Icc le_rfl hc.le))
    (fun t ht => hspeed t ⟨ht.1, ht.2.trans hc.le⟩)
  have hupper : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) ≤ ENNReal.ofReal L := by
    dsimp only [γ, radialCurve] at h01
    rw [zero_smul, one_smul] at h01
    change riemannianEDist I
      (expMap (I := I) g p (show TangentSpace I p from (0 : E)))
      (expMap (I := I) g p (show TangentSpace I p from v)) ≤
        ENNReal.ofReal (L * (1 - 0)) at h01
    rw [show expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p from
      expMap_zero (I := I) g p] at h01
    simpa only [sub_zero, mul_one] using h01
  have h1c := HopfRinow.curve_edist_le_speed_mul_time (I := I)
    (γ := γ) (s := (1 : ℝ)) (t := c) (c := L)
    hLnn hc.le
    (hγsmooth.mono (Icc_subset_Icc zero_le_one le_rfl))
    (fun t ht => hspeed t ⟨zero_le_one.trans ht.1, ht.2⟩)
  have htail : riemannianEDist I
      (expMap (I := I) g p (show TangentSpace I p from v))
      (expMap (I := I) g p (show TangentSpace I p from c • v)) ≤
      ENNReal.ofReal (L * (c - 1)) := by
    simpa only [γ, radialCurve, one_smul] using h1c
  simp only [minimizingDomain, Set.mem_ofPred_eq] at hcraw
  have hcLen : Real.sqrt
      (g.inner p (show TangentSpace I p from c • v)
        (show TangentSpace I p from c • v)) = c * L := by
    change Real.sqrt (g.inner p (show TangentSpace I p from c • v)
      (show TangentSpace I p from c • v)) = c *
        Real.sqrt (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v))
    exact sqrt_gInner_smul_self (I := I) g p hcpos.le
      (show TangentSpace I p from v)
  rw [hcLen] at hcraw
  have htailnn : 0 ≤ L * (c - 1) :=
    mul_nonneg hLnn (sub_nonneg.mpr hc.le)
  have hsplit : ENNReal.ofReal (c * L) =
      ENNReal.ofReal L + ENNReal.ofReal (L * (c - 1)) := by
    rw [← ENNReal.ofReal_add hLnn htailnn]
    congr 1
    ring
  have htri : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from c • v)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) +
      riemannianEDist I
        (expMap (I := I) g p (show TangentSpace I p from v))
        (expMap (I := I) g p (show TangentSpace I p from c • v)) :=
    riemannianEDist_triangle
  have hlow : ENNReal.ofReal L ≤ riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) := by
    have hchain : ENNReal.ofReal L + ENNReal.ofReal (L * (c - 1)) ≤
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from v)) +
        ENNReal.ofReal (L * (c - 1)) := by
      calc
        ENNReal.ofReal L + ENNReal.ofReal (L * (c - 1)) =
            ENNReal.ofReal (c * L) := hsplit.symm
        _ = riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from c • v)) := hcraw
        _ ≤ riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from v)) +
            riemannianEDist I
              (expMap (I := I) g p (show TangentSpace I p from v))
              (expMap (I := I) g p (show TangentSpace I p from c • v)) := htri
        _ ≤ riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from v)) +
            ENNReal.ofReal (L * (c - 1)) := add_le_add le_rfl htail
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  change ENNReal.ofReal L = riemannianEDist I p
    (expMap (I := I) g p (show TangentSpace I p from v))
  exact le_antisymm hlow hupper

end DifferentialGeometry.Geometry.Riemannian.Exponential
