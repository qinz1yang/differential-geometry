import DifferentialGeometry.Geometry.Metric.Construction.OpenExtension
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Metric.Construction.Existence
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [CompleteSpace E] in
theorem exists_smooth_riemannian_metric_eq_pullback_on_compact
    [IsManifold I 1 M]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source)
    (h : SmoothRiemannianMetric I N) (gM : SmoothRiemannianMetric I M) :
    ∃ G : SmoothRiemannianMetric I M,
      ∀ x ∈ K, ∀ v w : TangentSpace I x,
        G.inner x v w = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) := by
  classical
  obtain ⟨χ, P₀, hP₀smooth, hχ, hχK, hχsupport, hχ01, hP₀def⟩ :=
    DifferentialGeometry.PartialDiffeomorph.exists_cutoff_pullback_inner Φ hK hKs h
  set G : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    P₀ x + (1 - χ x) • gM.inner x with hG
  have hGapply : ∀ (x : M) (v w : TangentSpace I x),
      G x v w = χ x * (h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w))
        + (1 - χ x) * gM.inner x v w := by
    intro x v w
    simp only [hG, hP₀def x, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply, smul_eq_mul]
  have hGpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < G x v v := by
    intro x v hv
    rw [hGapply]
    have ha : 0 ≤ χ x := (hχ01 x).1
    have hb : 0 ≤ 1 - χ x := by linarith [(hχ01 x).2]
    have hgM := gM.pos x v hv
    rcases lt_or_eq_of_le ha with ha' | ha'
    · have hxs : x ∈ Φ.source :=
        hχsupport (subset_tsupport χ (Function.mem_support.mpr (ne_of_gt ha')))
      have hpull := DifferentialGeometry.PartialDiffeomorph.pullback_inner_pos Φ hxs h v hv
      nlinarith
    · rw [← ha']
      simpa using hgM
  set Gmetric : SmoothRiemannianMetric I M :=
    { inner := G
      symm := by
        intro x v w
        rw [hGapply, hGapply, gM.symm x v w, h.symm]
      pos := hGpos
      isVonNBounded := fun x =>
        DifferentialGeometry.Geometry.posDef_isVonNBounded (E := E)
          ((G x : E →L[ℝ] E →L[ℝ] ℝ)) (fun v hv => hGpos x v hv)
      contMDiff := by
        have hgM' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
              x ((1 - χ x) • gM.inner x)) := by
          have hcoef : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) (fun x : M => 1 - χ x) :=
            contMDiff_const.sub hχ
          exact fun x₀ => (hcoef.contMDiffAt).smul_section (gM.contMDiff x₀)
        exact fun x₀ => (hP₀smooth x₀).add_section (hgM' x₀) }
    with hGmetric
  have hGinner : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      Gmetric.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) := by
    intro x hx v w
    change G x v w = _
    rw [hGapply, hχK hx]
    simp
  exact ⟨Gmetric, hGinner⟩

omit [CompleteSpace E] in
theorem exists_metric_tensor_field_eq_pullback_on_compact
    [IsManifold I 1 M]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source)
    (h : SmoothRiemannianMetric I N) (gM : SmoothRiemannianMetric I M) :
    ∃ (P : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2) (G : SmoothRiemannianMetric I M),
      P = Tensor0SBundle.metricTensorField (I := I) G ∧
      (∀ x ∈ K, ∀ v w : TangentSpace I x,
        G.inner x v w = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w)) ∧
      ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
        P x v = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x (v 0)) (mfderiv I I (Φ : M → N) x (v 1)) := by
  obtain ⟨G, hG⟩ :=
    exists_smooth_riemannian_metric_eq_pullback_on_compact
      (I := I) Φ hK hKs h gM
  refine ⟨Tensor0SBundle.metricTensorField (I := I) G, G, rfl, hG, ?_⟩
  intro x hx v
  rw [Tensor0SBundle.metricTensorField_apply]
  exact hG x hx (v 0) (v 1)

end CheegerGromovCompactness
end DifferentialGeometry

end

noncomputable section

namespace DifferentialGeometry

open Filter Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N]

theorem PartialDiffeomorph.exists_metric_preserving_on_neighborhood_of_is_compact
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric J N)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ Φ.source) :
    ∃ (h : SmoothRiemannianMetric J N) (U : Opens M),
      K ⊆ (U : Set M) ∧ (U : Set M) ⊆ Φ.source ∧
      (∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
        g.inner x v w = h.inner (Φ x)
          (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x w)) ∧
      (∀ (y : N), y ∉ Φ.target → ∀ v w : TangentSpace J y,
        h.inner y v w = R.inner y v w) := by
  let V : Opens N := ⟨Φ.target, Φ.open_target⟩
  let A : Opens M := ⟨(Φ.symm : N → M) '' (V : Set N),
    image_opens_isOpen Φ.symm (fun _ hy ↦ hy)⟩
  let Ψ : Diffeomorph J I V A ∞ :=
    PartialDiffeomorph.toOpensDiffeo Φ.symm (fun _ hy ↦ hy)
  let gV := Diffeomorph.pullbackMetricCross (g.restrictOpen A) Ψ
  have hpush (y : V) (v w : TangentSpace J y) :
      gV.inner y v w = g.inner (Φ.symm y)
        (mfderiv J I (Φ.symm : N → M) y v) (mfderiv J I (Φ.symm : N → M) y w) := by
    have hd (z : TangentSpace J y) :
        mfderiv J I Ψ y z = mfderiv J I (Φ.symm : N → M) y z :=
      PartialDiffeomorph.mfderiv_toOpensDiffeo Φ.symm (fun _ hy ↦ hy) y z
    calc
      gV.inner y v w = (g.restrictOpen A).inner (Ψ y)
          (mfderiv J I Ψ y v) (mfderiv J I Ψ y w) :=
        Diffeomorph.pullbackMetricCross_inner (g.restrictOpen A) Ψ y v w
      _ = g.inner (Φ.symm y)
          (mfderiv J I (Φ.symm : N → M) y v) (mfderiv J I (Φ.symm : N → M) y w) := by
        change g.inner (Φ.symm y) (mfderiv J I Ψ y v) (mfderiv J I Ψ y w) = _
        rw [hd v, hd w]
  have himage : IsCompact ((Φ : M → N) '' K) :=
    hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKs)
  have htarget : (Φ : M → N) '' K ⊆ (V : Set N) := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hKs hx)
  obtain ⟨h, W, hKW, hWV, hmetric, hout⟩ :=
    exists_smooth_metric_agrees_on_neighborhood_of_is_compact R V gV himage htarget
  let U : Opens M := ⟨Φ.source ∩ (Φ : M → N) ⁻¹' W,
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage W.isOpen⟩
  refine ⟨h, U, ?_, fun _ hx ↦ hx.1, ?_, hout⟩
  · intro x hx
    exact ⟨hKs hx, hKW (mem_image_of_mem Φ hx)⟩
  · intro x hx v w
    have hxsource : x ∈ Φ.source := hx.1
    have hxdiff : MDifferentiableAt I J (Φ : M → N) x :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hxsource)).mdifferentiableAt
        (by simp)
    have hydiff : MDifferentiableAt J I (Φ.symm : N → M) (Φ x) :=
      (Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.open_target.mem_nhds (Φ.map_source' hxsource))).mdifferentiableAt (by simp)
    have heq : (Φ.symm : N → M) ∘ (Φ : M → N) =ᶠ[𝓝 x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxsource] with y hy
      exact Φ.left_inv' hy
    have hinverse (z : TangentSpace I x) :
        mfderiv J I (Φ.symm : N → M) (Φ x) (mfderiv I J (Φ : M → N) x z) = z := by
      have hc := mfderiv_comp_apply x hydiff hxdiff z
      rw [heq.mfderiv_eq, mfderiv_id] at hc
      exact hc.symm
    have hp := (hmetric (Φ x) hx.2
      (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x w)).trans
        (hpush ⟨Φ x, hWV hx.2⟩
          (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x w))
    change h.inner (Φ x) (mfderiv I J (Φ : M → N) x v)
      (mfderiv I J (Φ : M → N) x w) =
      g.inner (Φ.symm (Φ x))
        (mfderiv J I (Φ.symm : N → M) (Φ x) (mfderiv I J (Φ : M → N) x v))
        (mfderiv J I (Φ.symm : N → M) (Φ x) (mfderiv I J (Φ : M → N) x w)) at hp
    rw [hinverse v, hinverse w] at hp
    exact (congrArg (fun y : M ↦ g.inner y v w) (Φ.left_inv' hxsource)).symm.trans hp.symm

end DifferentialGeometry

end
