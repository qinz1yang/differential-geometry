import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Curvature.PositiveSectional
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Mathlib.Topology.FiberBundle.Constructions

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

abbrev TangentPairBundle (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :=
  TotalSpace (E × E) ((TangentSpace I : M → Type _) ×ᵇ (TangentSpace I : M → Type _))

private def tangentPairMetricPairing
    (g : SmoothRiemannianMetric I M) (p : TangentPairBundle I M) : ℝ :=
  g.inner p.proj p.2.1 p.2.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem continuous_tangentPair_slots :
    ∀ i : Fin 2, Continuous (fun p : TangentPairBundle I M ↦
      TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) p.proj (![p.2.1, p.2.2] i)) := by
  intro i
  have hdiag : Continuous (fun p : TangentPairBundle I M ↦
      ((⟨p.1, p.2.1⟩ : TangentBundle I M), (⟨p.1, p.2.2⟩ : TangentBundle I M))) :=
    (FiberBundle.Prod.isInducing_diag E (TangentSpace I) E (TangentSpace I)).continuous
  fin_cases i
  · exact (continuous_fst.comp hdiag).congr (fun _ ↦ rfl)
  · exact (continuous_snd.comp hdiag).congr (fun _ ↦ rfl)

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
    [T2Space M] [BoundarylessManifold I M] in
private theorem continuous_tangentPairMetricPairing
    (g : SmoothRiemannianMetric I M) :
    Continuous (tangentPairMetricPairing (I := I) g) := by
  let b : TangentPairBundle I M → M := fun p ↦ p.proj
  let v : Fin 2 → (p : TangentPairBundle I M) → TangentSpace I (b p) :=
    fun i p ↦ ![p.2.1, p.2.2] i
  have hb : Continuous b := FiberBundle.continuous_proj (E × E)
    ((TangentSpace I : M → Type _) ×ᵇ (TangentSpace I : M → Type _))
  have hv : ∀ i : Fin 2, Continuous (fun p : TangentPairBundle I M ↦
      TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) (b p) (v i p)) :=
    continuous_tangentPair_slots (I := I) (M := M)
  have hmetric : Continuous (fun p : TangentPairBundle I M ↦
      TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M ↦ Tensor0SSpace 2 I x) (b p)
        (Tensor0SBundle.metricTensorField (I := I) g (b p))) :=
    (Tensor0SBundle.metricTensorField (I := I) g).contMDiff.continuous.comp hb
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := ℝ) (I := I) (M := M) (P := TangentPairBundle I M)
    (n := 2) b hb (fun p ↦ Tensor0SBundle.metricTensorField (I := I) g (b p))
    hmetric v hv
  exact hEval.congr fun p ↦ by
    change g.inner p.proj p.2.1 p.2.2 = _
    rfl

def MetricOrthonormalTwoFrameOn
    (g : SmoothRiemannianMetric I M) (K : Set M) : Type _ :=
  {p : TangentPairBundle I M //
    p.proj ∈ K ∧
      g.inner p.proj p.2.1 p.2.1 = 1 ∧
      g.inner p.proj p.2.2 p.2.2 = 1 ∧
      g.inner p.proj p.2.1 p.2.2 = 0}

instance metricOrthonormalTwoFrameOnTop
    (g : SmoothRiemannianMetric I M) (K : Set M) :
    TopologicalSpace (MetricOrthonormalTwoFrameOn (I := I) g K) :=
  inferInstanceAs (TopologicalSpace
    {p : TangentPairBundle I M //
      p.proj ∈ K ∧
        g.inner p.proj p.2.1 p.2.1 = 1 ∧
        g.inner p.proj p.2.2 p.2.2 = 1 ∧
        g.inner p.proj p.2.1 p.2.2 = 0})

namespace MetricOrthonormalTwoFrameOn

def base {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) : M := p.1.proj

def first {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) : TangentSpace I (base p) := p.1.2.1

def second {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) : TangentSpace I (base p) := p.1.2.2

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M]
    [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
@[simp] theorem base_mem {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) : base p ∈ K := p.2.1

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M]
    [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
@[simp] theorem first_unit {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) :
    g.inner (base p) (first p) (first p) = 1 := p.2.2.1

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M]
    [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
@[simp] theorem second_unit {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) :
    g.inner (base p) (second p) (second p) = 1 := p.2.2.2.1

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M]
    [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
@[simp] theorem orthogonal {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) :
    g.inner (base p) (first p) (second p) = 0 := p.2.2.2.2

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
theorem isCompact_univ
    {g : SmoothRiemannianMetric I M} {K : Set M} (hK : IsCompact K) :
    IsCompact (Set.univ : Set (MetricOrthonormalTwoFrameOn (I := I) g K)) := by
  let U : Set (MetricUnitTangent (I := I) (M := M) g) :=
    {p | MetricUnitTangent.base (I := I) (M := M) p ∈ K}
  let Uraw : Set (TangentBundle I M) :=
    (fun p : MetricUnitTangent (I := I) (M := M) g ↦ p.1) '' U
  have hU : IsCompact U := metricUnitOn_compact (I := I) (M := M) g hK
  have hUraw : IsCompact Uraw := hU.image continuous_subtype_val
  have hUraw_iff (p : TangentBundle I M) :
      p ∈ Uraw ↔ p.proj ∈ K ∧ g.inner p.proj p.2 p.2 = 1 := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq, q.2⟩
    · rintro ⟨hpK, hpunit⟩
      exact ⟨⟨p, hpunit⟩, hpK, rfl⟩
  let diag : TangentPairBundle I M → TangentBundle I M × TangentBundle I M :=
    fun p ↦ ((⟨p.1, p.2.1⟩ : TangentBundle I M),
      (⟨p.1, p.2.2⟩ : TangentBundle I M))
  have hdiag : Topology.IsInducing diag :=
    FiberBundle.Prod.isInducing_diag E (TangentSpace I) E (TangentSpace I)
  let Q : Set (TangentBundle I M × TangentBundle I M) :=
    (Uraw ×ˢ Uraw) ∩ {p | p.1.proj = p.2.proj}
  have hbase : Continuous (fun p : TangentBundle I M ↦ p.proj) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hQ : IsCompact Q :=
    (hUraw.prod hUraw).inter_right
      (isClosed_eq (hbase.comp continuous_fst) (hbase.comp continuous_snd))
  have hQrange : Q ⊆ Set.range diag := by
    rintro ⟨⟨x, v⟩, ⟨y, w⟩⟩ ⟨_hunit, hxy⟩
    change x = y at hxy
    subst y
    exact ⟨⟨x, (v, w)⟩, rfl⟩
  have hunitPairs : IsCompact (diag ⁻¹' Q) :=
    hdiag.isCompact_preimage' hQ hQrange
  have horth : IsClosed {p : TangentPairBundle I M |
      tangentPairMetricPairing (I := I) g p = 0} :=
    isClosed_eq (continuous_tangentPairMetricPairing (I := I) g) continuous_const
  have hframes : IsCompact {p : TangentPairBundle I M |
      p.proj ∈ K ∧
        g.inner p.proj p.2.1 p.2.1 = 1 ∧
        g.inner p.proj p.2.2 p.2.2 = 1 ∧
        g.inner p.proj p.2.1 p.2.2 = 0} := by
    have h := hunitPairs.inter_right horth
    convert h using 1
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    rw [show diag p ∈ Q ↔
        p.proj ∈ K ∧ g.inner p.proj p.2.1 p.2.1 = 1 ∧
          g.inner p.proj p.2.2 p.2.2 = 1 by
      simp only [Q, mem_inter_iff, mem_prod, mem_ofPred_eq]
      rw [hUraw_iff, hUraw_iff]
      simp [diag, and_assoc, and_left_comm, and_comm]]
    simp [tangentPairMetricPairing, and_assoc]
  change IsCompact (Set.univ : Set {p : TangentPairBundle I M //
    p.proj ∈ K ∧
      g.inner p.proj p.2.1 p.2.1 = 1 ∧
      g.inner p.proj p.2.2 p.2.2 = 1 ∧
      g.inner p.proj p.2.1 p.2.2 = 0})
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Set.image_univ]
  simpa only [Subtype.range_val_subtype] using hframes

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem nonempty
    {g : SmoothRiemannianMetric I M} {K : Set M}
    (hdim : 2 ≤ Module.finrank ℝ E) (hK : K.Nonempty) :
    Nonempty (MetricOrthonormalTwoFrameOn (I := I) g K) := by
  classical
  obtain ⟨x, hx⟩ := hK
  obtain ⟨basis, hbasis⟩ := exists_orthonormal_basis (I := I) (M := M) g x
  have hdim' : 2 ≤ Module.finrank ℝ (TangentSpace I x) := by
    rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]
    exact hdim
  let i0 : Fin (Module.finrank ℝ (TangentSpace I x)) :=
    ⟨0, zero_lt_two.trans_le hdim'⟩
  let i1 : Fin (Module.finrank ℝ (TangentSpace I x)) :=
    ⟨1, one_lt_two.trans_le hdim'⟩
  have hi : i0 ≠ i1 := by
    intro he
    have := congrArg Fin.val he
    simp [i0, i1] at this
  have h0 : g.inner x (basis i0) (basis i0) = 1 := by simpa using hbasis i0 i0
  have h1 : g.inner x (basis i1) (basis i1) = 1 := by simpa using hbasis i1 i1
  have h01 : g.inner x (basis i0) (basis i1) = 0 := by simpa [hi] using hbasis i0 i1
  exact ⟨⟨⟨x, (basis i0, basis i1)⟩, hx, h0, h1, h01⟩⟩

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M]
    [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
theorem linearIndependent
    {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) :
    LinearIndependent ℝ ![first p, second p] := by
  have hfirst : first p ≠ 0 := by
    intro h
    have hu := first_unit p
    rw [h] at hu
    simp at hu
  rw [LinearIndependent.pair_iff' hfirst]
  intro a ha
  have hinner := congrArg (fun v ↦ g.inner (base p) (first p) v) ha
  have hmap := (g.inner (base p) (first p)).map_smul a
  rw [hmap, first_unit p, orthogonal p] at hinner
  simp at hinner
  subst a
  have hsecond : second p = 0 := by simpa using ha.symm
  have hu := second_unit p
  rw [hsecond] at hu
  simp at hu

def curvature {g : SmoothRiemannianMetric I M} {K : Set M}
    (p : MetricOrthonormalTwoFrameOn (I := I) g K) : ℝ :=
  metricRm04StandardAt (I := I) (M := M) g (base p)
    (first p) (second p) (second p) (first p)

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem continuous_curvature {g : SmoothRiemannianMetric I M} {K : Set M} :
    Continuous (curvature (I := I) :
      MetricOrthonormalTwoFrameOn (I := I) g K → ℝ) := by
  let b : MetricOrthonormalTwoFrameOn (I := I) g K → M := base
  let v : Fin 4 → (p : MetricOrthonormalTwoFrameOn (I := I) g K) →
      TangentSpace I (b p) :=
    fun i p ↦ ![first p, second p, second p, first p] i
  have hb : Continuous b :=
    (FiberBundle.continuous_proj (E × E)
      ((TangentSpace I : M → Type _) ×ᵇ (TangentSpace I : M → Type _))).comp
        continuous_subtype_val
  have hv : ∀ i : Fin 4, Continuous (fun p : MetricOrthonormalTwoFrameOn (I := I) g K ↦
      TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) (b p) (v i p)) := by
    intro i
    fin_cases i
    · exact (continuous_tangentPair_slots (I := I) (M := M) 0).comp continuous_subtype_val
    · exact (continuous_tangentPair_slots (I := I) (M := M) 1).comp continuous_subtype_val
    · exact (continuous_tangentPair_slots (I := I) (M := M) 1).comp continuous_subtype_val
    · exact (continuous_tangentPair_slots (I := I) (M := M) 0).comp continuous_subtype_val
  have hRm : Continuous (fun p : MetricOrthonormalTwoFrameOn (I := I) g K ↦
      TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M ↦ Tensor0SSpace 4 I x) (b p)
        (metricRm04At (I := I) (M := M) g (b p))) :=
    (metricRm04 (I := I) (M := M) g).contMDiff.continuous.comp hb
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := ℝ) (I := I) (M := M) (P := MetricOrthonormalTwoFrameOn (I := I) g K)
    (n := 4) b hb (fun p ↦ metricRm04At (I := I) (M := M) g (b p)) hRm v hv
  exact hEval.congr fun p ↦ by
    change metricRm04At (I := I) (M := M) g (base p)
      (fun i ↦ ![first p, second p, second p, first p] i) = _
    congr 1
    funext i
    fin_cases i <;> rfl

end MetricOrthonormalTwoFrameOn

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem exists_positive_curvature_lowerBound_on_compact
    {g : SmoothRiemannianMetric I M}
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : Set M} (hKcompact : IsCompact K) (hKne : K.Nonempty) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : M, x ∈ K → ∀ W T : TangentSpace I x,
        g.inner x W W = 1 → g.inner x T T = 1 → g.inner x W T = 0 →
          κ ≤ metricRm04StandardAt (I := I) (M := M) g x W T T W := by
  classical
  let F := MetricOrthonormalTwoFrameOn (I := I) g K
  have hFcompact : IsCompact (Set.univ : Set F) :=
    MetricOrthonormalTwoFrameOn.isCompact_univ (I := I) hKcompact
  have hFne : (Set.univ : Set F).Nonempty := by
    obtain ⟨p⟩ := MetricOrthonormalTwoFrameOn.nonempty (I := I) (g := g) hdim hKne
    exact ⟨p, Set.mem_univ p⟩
  obtain ⟨p0, _hp0, hp0min⟩ := hFcompact.exists_isMinOn hFne
    MetricOrthonormalTwoFrameOn.continuous_curvature.continuousOn
  let κ : ℝ := MetricOrthonormalTwoFrameOn.curvature (I := I) p0
  have hκ : 0 < κ :=
    hsec (MetricOrthonormalTwoFrameOn.base p0)
      (MetricOrthonormalTwoFrameOn.first p0)
      (MetricOrthonormalTwoFrameOn.second p0)
      (MetricOrthonormalTwoFrameOn.linearIndependent p0)
  refine ⟨κ, hκ, ?_⟩
  intro x hx W T hW hT hWT
  let p : F := ⟨⟨x, (W, T)⟩, hx, hW, hT, hWT⟩
  have hmin := (isMinOn_iff.mp hp0min) p (Set.mem_univ p)
  simpa [κ, p, MetricOrthonormalTwoFrameOn.curvature,
    MetricOrthonormalTwoFrameOn.base, MetricOrthonormalTwoFrameOn.first,
    MetricOrthonormalTwoFrameOn.second] using hmin

omit [BoundarylessManifold I M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem compact_curvature_margin
    [ConnectedSpace M] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (C : Set M) (hCcompact : IsCompact C) (hCne : C.Nonempty) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    IsCompact (Metric.cthickening 1 C) ∧
      ∃ κ : ℝ, 0 < κ ∧
        ∀ x : M, x ∈ Metric.cthickening 1 C → ∀ W T : TangentSpace I x,
          g.inner x W W = 1 → g.inner x T T = 1 → g.inner x W T = 0 →
            κ ≤ metricRm04StandardAt (I := I) (M := M) g x W T T W := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hpositive : 0 < Module.finrank ℝ E :=
    lt_of_lt_of_le (by norm_num) hdim
  let : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt hpositive⟩
  let : ProperSpace M :=
    HopfRinow.properSpace_riemMetric_of_complete_metric
      (I := I) (M := M) g hcomplete
  have hKcompact : IsCompact (Metric.cthickening 1 C) := hCcompact.cthickening
  have hKne : (Metric.cthickening 1 C).Nonempty :=
    hCne.mono (Metric.self_subset_cthickening C)
  exact ⟨hKcompact,
    exists_positive_curvature_lowerBound_on_compact hsec hdim hKcompact hKne⟩

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

@[reducible] alias TangentPairBundle := DifferentialGeometry.Geometry.TangentPairBundle
@[reducible] alias MetricOrthonormalTwoFrameOn := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn
end Poincare.Geometry

namespace Poincare.Geometry.MetricOrthonormalTwoFrameOn

@[reducible] alias base := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.base
@[reducible] alias first := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.first
@[reducible] alias second := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.second
alias base_mem := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.base_mem
alias first_unit := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.first_unit
alias second_unit := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.second_unit
alias orthogonal := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.orthogonal
alias isCompact_univ := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.isCompact_univ
alias nonempty := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.nonempty
alias linearIndependent := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.linearIndependent
@[reducible] alias curvature := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.curvature
alias continuous_curvature := DifferentialGeometry.Geometry.MetricOrthonormalTwoFrameOn.continuous_curvature
end Poincare.Geometry.MetricOrthonormalTwoFrameOn

namespace Poincare.Geometry

alias exists_positive_curvature_lowerBound_on_compact := DifferentialGeometry.Geometry.exists_positive_curvature_lowerBound_on_compact
alias compact_curvature_margin := DifferentialGeometry.Geometry.compact_curvature_margin

@[reducible] alias metricOrthonormalTwoFrameOnTop := DifferentialGeometry.Geometry.metricOrthonormalTwoFrameOnTop

end Poincare.Geometry
