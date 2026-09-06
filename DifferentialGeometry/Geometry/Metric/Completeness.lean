import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Metric.DistanceScaling
import DifferentialGeometry.Geometry.Metric.OpenSubtype
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace DifferentialGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure RiemannianMetricComplete
    (g : SmoothRiemannianMetric I M) : Prop where
  complete :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (x y : U) :
    riemannianEDistOf (I := I) g (x : M) (y : M) ≤
      riemannianEDistOf (I := I) (g.restrictOpen (I := I) U) x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun gamma => ?_
  refine le_iInf fun hgamma => ?_
  let gammaM : Path (x : M) (y : M) := gamma.map continuous_subtype_val
  have hgammaM : CMDiff 1 gammaM :=
    (contMDiff_subtype_val (I := I) (U := U)).comp hgamma
  refine iInf_le_of_le gammaM (iInf_le_of_le hgammaM ?_)
  refine MeasureTheory.lintegral_mono fun t => ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  have hval : MDifferentiableAt I I (Subtype.val : U → M) (gamma t) :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hgammaDiff : MDifferentiableAt (𝓡∂ 1) I gamma t :=
    hgamma.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hcomp :=
    mfderiv_comp_apply t hval hgammaDiff (1 : TangentSpace (𝓡∂ 1) t)
  rw [mfderiv_subtype_val_apply (I := I) U (gamma t)] at hcomp
  change g.inner (gamma t : M)
      (mfderiv (𝓡∂ 1) I (Subtype.val ∘ gamma) t
        (1 : TangentSpace (𝓡∂ 1) t))
      (mfderiv (𝓡∂ 1) I (Subtype.val ∘ gamma) t
        (1 : TangentSpace (𝓡∂ 1) t)) ≤
    g.inner (gamma t : M)
      (mfderiv (𝓡∂ 1) I gamma t (1 : TangentSpace (𝓡∂ 1) t))
      (mfderiv (𝓡∂ 1) I gamma t (1 : TangentSpace (𝓡∂ 1) t))
  rw [hcomp]

namespace RiemannianMetricComplete

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem of_compact [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    RiemannianMetricComplete (I := I) g := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  infer_instance

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (hU : IsClosed (U : Set M)) :
    RiemannianMetricComplete (I := I) (g.restrictOpen (I := I) U) := by
  let : IsManifold I 1 U :=
    IsManifold.of_le (I := I) (M := U) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace U := Manifold.metrizableSpace I U
  let : T3Space U := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : U => TangentSpace I x) :=
    ⟨(g.restrictOpen (I := I) U).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x) :=
    ⟨⟨(g.restrictOpen (I := I) U).inner,
      (g.restrictOpen (I := I) U).contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric I U
  refine EMetric.complete_of_cauchySeq_tendsto (α := U) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf (I := I) (g.restrictOpen (I := I) U)
          (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change edist (s m) (s n) < ε
    exact hN m hm n hn
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hsSource : CauchySeq (fun n => (s n : M)) :=
    EMetric.cauchySeq_iff.mpr (by
      intro ε hε
      obtain ⟨N, hN⟩ := hsTarget ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      change riemannianEDistOf (I := I) g (s m : M) (s n : M) < ε
      exact (riemannianEDistOf_le_restrictOpen (I := I) g U (s m) (s n)).trans_lt
        (hN m hm n hn))
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsSource
  have hxU : x ∈ U :=
    hU.mem_of_tendsto hx (Filter.Eventually.of_forall fun n => (s n).2)
  exact ⟨⟨x, hxU⟩, tendsto_subtype_rng.mpr hx⟩

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem of_lower
    {g h : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {c : Real} (hc : 0 < c)
    (hlower : ∀ x : M, ∀ v : TangentSpace I x,
      c * g.inner x v v ≤ h.inner x v v) :
    RiemannianMetricComplete (I := I) h := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let a : ENNReal := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hdist : ∀ x y : M,
      a * riemannianEDistOf (I := I) g x y ≤
        riemannianEDistOf (I := I) h x y := by
    intro x y
    rw [← edistOf_scale (I := I) c hc g x y]
    exact edistOf_mono (I := I) _ _ (by
      intro z v
      simpa only [scaleMetric_inner] using hlower z v) x y
  refine EMetric.complete_of_cauchySeq_tendsto (α := M) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf (I := I) h (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change edist (s m) (s n) < ε
    exact hN m hm n hn
  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hsSource : CauchySeq s := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    have haε : 0 < a * ε := ENNReal.mul_pos ha0 (ne_of_gt hε)
    obtain ⟨N, hN⟩ := hsTarget (a * ε) haε
    refine ⟨N, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I) g (s m) (s n) < ε
    apply (ENNReal.mul_lt_mul_iff_right ha0 hatop).mp
    exact lt_of_le_of_lt (hdist (s m) (s n)) (hN m hm n hn))
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsSource
  exact ⟨x, hx⟩

omit [CompleteSpace E] in
theorem scaleMetric
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    (c : Real) (hc : 0 < c) :
    RiemannianMetricComplete (I := I) (scaleMetric (I := I) c hc g) := by
  exact of_lower hg hc (fun x v => by rw [scaleMetric_inner])

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem of_uniformEquiv
    {g h : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Real} (hC : 1 ≤ C)
    (hcomp : ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ C * g.inner x v v) :
    RiemannianMetricComplete (I := I) h := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hCpos
  let a : ENNReal := ENNReal.ofReal (Real.sqrt C⁻¹)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hCinv))
  have hatop : a ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hdist : ∀ x y : M,
      a * riemannianEDistOf (I := I) g x y ≤
        riemannianEDistOf (I := I) h x y := by
    intro x y
    rw [← edistOf_scale (I := I) C⁻¹ hCinv g x y]
    exact edistOf_mono (I := I) _ _ (by
      intro z v
      simpa only [scaleMetric_inner] using (hcomp z v).1) x y
  refine EMetric.complete_of_cauchySeq_tendsto (α := M) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf (I := I) h (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change edist (s m) (s n) < ε
    exact hN m hm n hn
  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hsSource : CauchySeq s := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    have haε : 0 < a * ε := ENNReal.mul_pos ha0 (ne_of_gt hε)
    obtain ⟨N, hN⟩ := hsTarget (a * ε) haε
    refine ⟨N, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I) g (s m) (s n) < ε
    apply (ENNReal.mul_lt_mul_iff_right ha0 hatop).mp
    exact lt_of_le_of_lt (hdist (s m) (s n)) (hN m hm n hn))
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsSource
  exact ⟨x, hx⟩

end RiemannianMetricComplete
end DifferentialGeometry

end
