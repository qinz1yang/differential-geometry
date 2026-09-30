import DifferentialGeometry.Tensor.RSTensor.PositiveSemidefinite
import DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import DifferentialGeometry.Tensor.Alternating.Composition
import DifferentialGeometry.Tensor.Multilinear.Composition
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

def MetricUnitTangent (g : SmoothRiemannianMetric I M) : Type _ :=
  {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1}

instance metricUnitTop (g : SmoothRiemannianMetric I M) :
    TopologicalSpace (MetricUnitTangent (I := I) (M := M) g) :=
  inferInstanceAs (TopologicalSpace
    {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1})

namespace MetricUnitTangent

def base {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) : M :=
  (p.1).proj

def vec {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) :
    TangentSpace I (base (I := I) (M := M) p) :=
  (p.1).2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem unit {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) :
    g.inner (base (I := I) (M := M) p)
      (vec (I := I) (M := M) p) (vec (I := I) (M := M) p) = 1 :=
  p.2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem base_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) g) = x :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem vec_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) g) = v :=
  rfl

end MetricUnitTangent

def MetricUnitTangentSlab
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) : Type _ :=
  Σ t : {t : Real // t ∈ Set.Icc t0 t1}, MetricUnitTangent (I := I) (M := M) (G t.1)

instance metricUnitTangentSlabTop
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) :
    TopologicalSpace (MetricUnitTangentSlab (I := I) (M := M) G t0 t1) :=
  inferInstanceAs (TopologicalSpace
    (Σ t : {t : Real // t ∈ Set.Icc t0 t1},
      MetricUnitTangent (I := I) (M := M) (G t.1)))

def MetricUnitTangentTimeSlab
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) : Type _ :=
  {q : ({t : Real // t ∈ K} × TangentBundle I M) //
    (G q.1.1).inner q.2.proj q.2.2 q.2.2 = 1}

instance metricUnitTangentTimeSlabTop
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) :
    TopologicalSpace (MetricUnitTangentTimeSlab (I := I) (M := M) G K) :=
  inferInstanceAs (TopologicalSpace
    {q : ({t : Real // t ∈ K} × TangentBundle I M) //
      (G q.1.1).inner q.2.proj q.2.2 q.2.2 = 1})

abbrev MetricUnitTangentIccSlab
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) : Type _ :=
  MetricUnitTangentTimeSlab (I := I) (M := M) G (Set.Icc t0 t1)

namespace MetricUnitTangentTimeSlab

def time {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : Real :=
  q.1.1.1

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem time_mem {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    time (I := I) (M := M) q ∈ K :=
  q.1.1.2

def bundlePoint {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    TangentBundle I M :=
  q.1.2

def base {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : M :=
  (bundlePoint (I := I) (M := M) q).proj

def vec {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    TangentSpace I (base (I := I) (M := M) q) :=
  (bundlePoint (I := I) (M := M) q).2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem unit {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    (G (time (I := I) (M := M) q)).inner
      (base (I := I) (M := M) q)
      (vec (I := I) (M := M) q) (vec (I := I) (M := M) q) = 1 :=
  q.2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem time_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    time (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = t :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem bundlePoint_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    bundlePoint (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) =
      (⟨x, v⟩ : TangentBundle I M) :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem base_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = x :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem vec_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = v :=
  rfl

end MetricUnitTangentTimeSlab

omit [FiniteDimensional ℝ E] in
theorem metricQuad_cont
    (g : SmoothRiemannianMetric I M) :
    Continuous (fun p : TangentBundle I M => g.inner p.proj p.2 p.2) := by
  have hmetric : Continuous (fun p : TangentBundle I M =>
      TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M =>
          TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
        p.proj (g.inner p.proj)) :=
    g.contMDiff.continuous.comp
      (FiberBundle.continuous_proj E (TangentSpace I))
  have hvec : Continuous (fun p : TangentBundle I M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.proj p.2) :=
    continuous_id
  have htotal := Continuous.clm_bundle_apply₂
    (𝕜 := Real) (F₁ := E) (F₂ := E) (F₃ := Real)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M Real)
    (b := fun p : TangentBundle I M => p.proj)
    hmetric hvec hvec
  have hprod :
      Continuous (fun p : TangentBundle I M =>
        (Bundle.Trivial.homeomorphProd M Real)
          (TotalSpace.mk' Real (E := Bundle.Trivial M Real)
            p.proj (g.inner p.proj p.2 p.2))) :=
    (Bundle.Trivial.homeomorphProd M Real).continuous.comp htotal
  exact (continuous_snd.comp hprod).congr fun _ => rfl

omit [FiniteDimensional ℝ E] in
theorem metricUnit_closed
    (g : SmoothRiemannianMetric I M) :
    IsClosed {p : TangentBundle I M | g.inner p.proj p.2 p.2 = 1} := by
  change IsClosed ((fun p : TangentBundle I M => g.inner p.proj p.2 p.2) ⁻¹' {1})
  exact isClosed_singleton.preimage (metricQuad_cont (I := I) (M := M) g)

private theorem coordMetric_lower
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M}
    (hK : IsCompact K)
    (hKsub : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ c : Real, 0 < c ∧
      ∀ x ∈ K, ∀ w : E, ‖w‖ = 1 →
        c ≤ g.inner x
          ((trivializationAt E (TangentSpace I) x₀).symmL Real x w)
          ((trivializationAt E (TangentSpace I) x₀).symmL Real x w) := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let S : Set (M × E) := K ×ˢ Metric.sphere (0 : E) 1
  have hScompact : IsCompact S := hK.prod (isCompact_sphere (0 : E) 1)
  have hSsub : S ⊆ e.baseSet ×ˢ (Set.univ : Set E) := by
    intro z hz
    exact ⟨hKsub hz.1, Set.mem_univ z.2⟩
  have hsymm_cont : ContinuousOn
      (fun z : M × E =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
          z.1 (e.symm z.1 z.2)) S :=
    e.continuousOn_symm.mono hSsub
  have hq_cont : ContinuousOn
      (fun z : M × E =>
        g.inner z.1 (e.symmL Real z.1 z.2) (e.symmL Real z.1 z.2)) S := by
    refine ContinuousOn.congr
      ((metricQuad_cont (I := I) (M := M) g).continuousOn.comp hsymm_cont
        (fun _ _ => Set.mem_univ _)) ?_
    intro z hz
    change g.inner z.1 (e.symmL Real z.1 z.2) (e.symmL Real z.1 z.2) =
      g.inner z.1 (e.symm z.1 z.2) (e.symm z.1 z.2)
    rw [e.symmL_apply (hKsub hz.1)]
  have hq_pos : ∀ z ∈ S,
      0 < g.inner z.1 (e.symmL Real z.1 z.2) (e.symmL Real z.1 z.2) := by
    intro z hz
    have hx : z.1 ∈ e.baseSet := hKsub hz.1
    have hnorm : ‖z.2‖ = 1 := by
      simpa [Metric.sphere, dist_eq_norm] using hz.2
    have hw_ne : z.2 ≠ 0 := by
      intro hzero
      simp [hzero] at hnorm
    have hv_ne : e.symmL Real z.1 z.2 ≠ 0 := by
      intro hv
      have hforward :
          e.continuousLinearMapAt Real z.1 (e.symmL Real z.1 z.2) = z.2 :=
        e.continuousLinearMapAt_symmL (R := Real) hx z.2
      rw [hv, map_zero] at hforward
      exact hw_ne (by simpa using hforward.symm)
    exact g.pos z.1 (e.symmL Real z.1 z.2) hv_ne
  by_cases hSne : S.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := hScompact.exists_isMinOn hSne hq_cont
    let c : Real :=
      g.inner z₀.1 (e.symmL Real z₀.1 z₀.2) (e.symmL Real z₀.1 z₀.2)
    refine ⟨c, hq_pos z₀ hz₀, ?_⟩
    intro x hxK w hw
    have hz : (x, w) ∈ S := by
      exact ⟨hxK, by simpa [Metric.sphere, dist_eq_norm] using hw⟩
    exact (isMinOn_iff.mp hmin) (x, w) hz
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hxK w hw
    exfalso
    exact hSne ⟨(x, w), ⟨hxK, by simpa [Metric.sphere, dist_eq_norm] using hw⟩⟩

private theorem coordMetric_bound
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M}
    (hK : IsCompact K)
    (hKsub : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ y ∈ K, ∀ v : TangentSpace I y,
        g.inner y v v = 1 →
          ‖(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt Real y v‖ ≤ R := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  obtain ⟨c, hcpos, hclower⟩ :=
    coordMetric_lower (I := I) (M := M) g x₀ hK hKsub
  refine ⟨c⁻¹ + 1, by positivity, ?_⟩
  intro y hyK v hunit
  have hybase : y ∈ e.baseSet := hKsub hyK
  let w : E := e.continuousLinearMapAt Real y v
  let r : Real := ‖w‖
  have hr_nonneg : 0 ≤ r := norm_nonneg w
  by_cases hw : w = 0
  · change r ≤ c⁻¹ + 1
    have hr0 : r = 0 := by simp [r, hw]
    rw [hr0]
    positivity
  have hrpos : 0 < r := by
    simpa [r] using (norm_pos_iff.mpr hw)
  let u : E := r⁻¹ • w
  have hnormu : ‖u‖ = 1 := by
    calc
      ‖u‖ = |r⁻¹| * ‖w‖ := by simp [u, norm_smul]
      _ = r⁻¹ * r := by
        rw [abs_of_pos (inv_pos.mpr hrpos)]
      _ = 1 := by
        exact inv_mul_cancel₀ (ne_of_gt hrpos)
  have hv_from_w : e.symmL Real y w = v := by
    simpa [w] using e.symmL_continuousLinearMapAt (R := Real) hybase v
  have hsymm_u : e.symmL Real y u = r⁻¹ • v := by
    change e.symmL Real y (r⁻¹ • w) = r⁻¹ • v
    rw [map_smul, hv_from_w]
  have hq_u :
      g.inner y (e.symmL Real y u) (e.symmL Real y u) = r⁻¹ * r⁻¹ := by
    calc
      g.inner y (e.symmL Real y u) (e.symmL Real y u)
          = g.inner y (r⁻¹ • v) (r⁻¹ • v) := by rw [hsymm_u]
      _ = r⁻¹ * (r⁻¹ * g.inner y v v) := by
        simp [smul_eq_mul]
      _ = r⁻¹ * r⁻¹ := by rw [hunit]; ring
  have hc_le : c ≤ r⁻¹ * r⁻¹ := by
    have hc_le' := hclower y hyK u hnormu
    rw [hq_u] at hc_le'
    exact hc_le'
  have hmul : c * (r * r) ≤ 1 := by
    have hrr_nonneg : 0 ≤ r * r := mul_nonneg hr_nonneg hr_nonneg
    have hle := mul_le_mul_of_nonneg_right hc_le hrr_nonneg
    have hright : (r⁻¹ * r⁻¹) * (r * r) = 1 := by
      field_simp [ne_of_gt hrpos]
    simpa [hright, mul_assoc, mul_comm, mul_left_comm] using hle
  have hsqr_le : r * r ≤ c⁻¹ := by
    have := (le_inv_mul_iff₀ hcpos).2 hmul
    simpa using this
  by_cases hrle : r ≤ 1
  · have hc_inv_nonneg : 0 ≤ c⁻¹ := by positivity
    linarith
  · have hone_le : 1 ≤ r := le_of_lt (lt_of_not_ge hrle)
    have hr_le_sq : r ≤ r * r := by nlinarith
    linarith

private theorem unitRest_compact
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E
        (TangentSpace I : M → Type _) → M))
    [e.IsLinear Real]
    {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.baseSet)
    {R : Real} (_hR : 0 ≤ R)
    (hbound : ∀ y ∈ K, ∀ v : TangentSpace I y,
      g.inner y v v = 1 →
        ‖e.continuousLinearMapAt Real y v‖ ≤ R) :
    IsCompact {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} := by
  classical
  let Kball : Set (K × E) :=
    {z | z.2 ∈ Metric.closedBall (0 : E) R}
  have hKball : IsCompact Kball := by
    have hKc : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let : CompactSpace K := hKc
    have hball : IsCompact (Metric.closedBall (0 : E) R) :=
      isCompact_closedBall (0 : E) R
    convert
      (isCompact_univ.prod hball :
        IsCompact ((Set.univ : Set K) ×ˢ Metric.closedBall (0 : E) R))
      using 1
    ext z
    simp [Kball]
  let toTan : K × E → TangentBundle I M :=
    fun z =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        z.1.1 (e.symmL Real z.1.1 z.2)
  have htoTan : ContinuousOn toTan Kball := by
    have hpair : Continuous (fun z : K × E => (z.1.1, z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hmaps : MapsTo (fun z : K × E => (z.1.1, z.2)) Kball
        (e.baseSet ×ˢ (Set.univ : Set E)) := by
      intro z hz
      exact ⟨hKe z.1.2, Set.mem_univ _⟩
    have hsymm := e.continuousOn_symm.comp hpair.continuousOn hmaps
    refine hsymm.congr ?_
    intro z hz
    change (TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
      z.1.1 (e.symmL Real z.1.1 z.2)) =
        TotalSpace.mk' E z.1.1 (e.symm z.1.1 z.2)
    rw [e.symmL_apply (hKe z.1.2)]
  let unitSet : Set (TangentBundle I M) :=
    {p | g.inner p.proj p.2 p.2 = 1}
  let D : Set (K × E) := Kball ∩ toTan ⁻¹' unitSet
  have hDcompact : IsCompact D := by
    have hclosed_pre : IsClosed (Kball ∩ toTan ⁻¹' unitSet) := by
      have hclosedUnit : IsClosed unitSet := by
        simpa [unitSet] using metricUnit_closed (I := I) (M := M) g
      exact htoTan.preimage_isClosed_of_isClosed hKball.isClosed hclosedUnit
    have hclosedD : IsClosed D := by
      simpa [D] using hclosed_pre
    exact hKball.of_isClosed_subset hclosedD inter_subset_left
  let mkUnit : D → MetricUnitTangent (I := I) (M := M) g :=
    fun z =>
      ⟨toTan z.1, by
        have hz : toTan z.1 ∈ unitSet := z.2.2
        simpa [unitSet] using hz⟩
  have hmkCont : Continuous mkUnit := by
    have hsub : Continuous (fun z : D => toTan z.1) := by
      rw [← continuousOn_univ]
      exact htoTan.comp continuous_subtype_val.continuousOn
        (fun z _ => z.2.1)
    exact Continuous.subtype_mk hsub (fun z => by
      have hz : toTan z.1 ∈ unitSet := z.2.2
      simpa [unitSet] using hz)
  have hlocal :
      {p : MetricUnitTangent (I := I) (M := M) g |
        MetricUnitTangent.base (I := I) (M := M) p ∈ K} =
        Set.range mkUnit := by
    ext p
    constructor
    · intro hpK
      let y : K := ⟨MetricUnitTangent.base (I := I) (M := M) p, hpK⟩
      let w : E :=
        e.continuousLinearMapAt Real y.1
          (MetricUnitTangent.vec (I := I) (M := M) p)
      have hwball : w ∈ Metric.closedBall (0 : E) R := by
        have hle := hbound y.1 y.2
          (MetricUnitTangent.vec (I := I) (M := M) p)
          (MetricUnitTangent.unit (I := I) (M := M) p)
        simpa [w, Metric.mem_closedBall, dist_eq_norm] using hle
      let z0 : K × E := (y, w)
      have hz0K : z0 ∈ Kball := by
        simpa [Kball, z0] using hwball
      have hz0unit : toTan z0 ∈ unitSet := by
        have hybase : y.1 ∈ e.baseSet := hKe y.2
        have hsymm :
            e.symmL Real y.1
              (e.continuousLinearMapAt Real y.1
                (MetricUnitTangent.vec (I := I) (M := M) p)) =
              MetricUnitTangent.vec (I := I) (M := M) p :=
          e.symmL_continuousLinearMapAt (R := Real) hybase
            (MetricUnitTangent.vec (I := I) (M := M) p)
        change
          g.inner y.1 (e.symmL Real y.1 w) (e.symmL Real y.1 w) = 1
        rw [show e.symmL Real y.1 w =
            MetricUnitTangent.vec (I := I) (M := M) p by
          simpa [w] using hsymm]
        exact MetricUnitTangent.unit (I := I) (M := M) p
      let z : D := ⟨z0, ⟨hz0K, hz0unit⟩⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change toTan z0 = p.1
      have hybase : y.1 ∈ e.baseSet := hKe y.2
      have hsymm :
          e.symmL Real y.1 w =
            MetricUnitTangent.vec (I := I) (M := M) p := by
        simpa [w] using
          e.symmL_continuousLinearMapAt (R := Real) hybase
            (MetricUnitTangent.vec (I := I) (M := M) p)
      change
        (TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
          y.1 (e.symmL Real y.1 w)) = p.1
      refine TotalSpace.ext rfl ?_
      exact heq_of_eq hsymm
    · rintro ⟨z, rfl⟩
      exact z.1.1.2
  rw [hlocal]
  have : CompactSpace D := isCompact_iff_compactSpace.mp hDcompact
  exact isCompact_range hmkCont

theorem metricUnitOn_compact
    [T2Space M]
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    IsCompact {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} := by
  classical
  let U : M → Set M := fun x => (trivializationAt E (TangentSpace I) x).baseSet
  have hUopen : ∀ x : M, IsOpen (U x) := by
    intro x
    exact (trivializationAt E (TangentSpace I) x).open_baseSet
  have hUcover : K ⊆ ⋃ x : M, U x := by
    intro y hy
    exact mem_iUnion.mpr
      ⟨y, mem_baseSet_trivializationAt E (TangentSpace I) y⟩
  obtain ⟨t, htcover⟩ :=
    hK.elim_finite_subcover U hUopen hUcover
  obtain ⟨Kloc, hKcompact, hKsub, hKeq⟩ :=
    hK.finite_compact_cover t U (fun i _ => hUopen i) htcover
  let localPiece : M → Set (MetricUnitTangent (I := I) (M := M) g) :=
    fun i => {p | MetricUnitTangent.base (I := I) (M := M) p ∈ Kloc i}
  have hlocal_compact : ∀ i ∈ t, IsCompact (localPiece i) := by
    intro i hi
    obtain ⟨R, hR, hbound⟩ :=
      coordMetric_bound (I := I) (M := M) g i
        (hKcompact i) (by simpa [U] using hKsub i)
    simpa [localPiece] using
      unitRest_compact (I := I) (M := M) g
        (trivializationAt E (TangentSpace I) i)
        (hKcompact i) (by simpa [U] using hKsub i) hR hbound
  have hunion :
      {p : MetricUnitTangent (I := I) (M := M) g |
          MetricUnitTangent.base (I := I) (M := M) p ∈ K} =
        ⋃ i ∈ t, localPiece i := by
    ext p
    constructor
    · intro hp
      have hbase : MetricUnitTangent.base (I := I) (M := M) p ∈
          K := hp
      rw [hKeq] at hbase
      simpa [localPiece] using hbase
    · intro hp
      change MetricUnitTangent.base (I := I) (M := M) p ∈ K
      rw [hKeq]
      simpa [localPiece] using hp
  rw [hunion]
  exact t.isCompact_biUnion hlocal_compact

theorem metricUnit_compact
    [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    IsCompact (Set.univ : Set (MetricUnitTangent (I := I) (M := M) g)) := by
  simpa using metricUnitOn_compact (I := I) (M := M) g isCompact_univ

theorem metricUnit_quadCont
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 2) :
    Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      quad02 (I := I) (M := M)
        (A (MetricUnitTangent.base (I := I) (M := M) p))
        (MetricUnitTangent.vec (I := I) (M := M) p)) := by
  let b : MetricUnitTangent (I := I) (M := M) g → M :=
    fun p => MetricUnitTangent.base (I := I) (M := M) p
  let v : Fin 2 →
      (p : MetricUnitTangent (I := I) (M := M) g) → TangentSpace I (b p) :=
    fun _ p => MetricUnitTangent.vec (I := I) (M := M) p
  have hb : Continuous b := by
    dsimp [b, MetricUnitTangent.base]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : ∀ i : Fin 2, Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p)) := by
    intro i
    exact (continuous_subtype_val :
      Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
        (p.1 : TangentBundle I M))).congr fun _ => rfl
  have hAsec : Continuous (fun x : M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun y : M => Tensor0SSpace 2 I y) x (A x)) :=
    A.contMDiff.continuous
  have hA : Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun y : M => Tensor0SSpace 2 I y) (b p) (A (b p))) :=
    hAsec.comp hb
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := MetricUnitTangent (I := I) (M := M) g)
    (n := 2) b hb (fun p => A (b p)) hA v hv
  exact hEval.congr fun _ => rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metric_smul2
    (g : SmoothRiemannianMetric I M) {x : M}
    (a : Real) (v : TangentSpace I x) :
    g.inner x (a • v) (a • v) = a * a * g.inner x v v := by
  calc
    g.inner x (a • v) (a • v) = a * g.inner x v (a • v) := by
      simp [smul_eq_mul]
    _ = a * (a * g.inner x v v) := by
      congr 1
      simp [smul_eq_mul]
    _ = a * a * g.inner x v v := by ring

end DifferentialGeometry
