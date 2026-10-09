import DifferentialGeometry.Geometry.Collapse.SublevelCore.Globalization
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Topology.Manifold.RegularDomain
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# LC32: proper sublevels and a smooth enlarged band

Blueprint LC32 (master207A:21390), with the LC32 constants `a = 1/8`, `b = 3`.

Kernel (metric spaces): a function within `e` of the distance from `p` on a proper metric
space is proper (`isProperMap_of_abs_sub_dist_lt`), and its band `η⁻¹[a,b]` lies in the open
annulus `a - e < d_p < b + e` (`preimage_Icc_subset_annulus`); for `e < 1/40` the LC32 band lies
in `1/10 < d_p < 10` (`radialBand_subset_annulus`).

Binding (complete Riemannian manifold, PC setting): for the LC30 output (`η` within `e` of
`d_p`, smooth on an open `W ⊇ C = {1/10 ≤ d_p ≤ 10}`, `(1-ε)² ≤ |∇η|² ≤ (1+ε)²` on `C`),
`radialSublevel_structure` gives properness, compactness of the band, an open neighbourhood of
the band with the gradient bounds, and for every `t ∈ [1/8, 3]`: `A_t = {η ≤ t}` is compact
with interior `{η < t}` and frontier `η⁻¹(t)`, and `A_t` is the regular sublevel `{f ≤ t}` of a
globally smooth `f` agreeing with `η` near the band, carrying the smooth manifold-with-boundary
structure of `Morse.exists_isManifold_sublevel` (boundary points = level `t`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

section Kernel

variable {X : Type*} [MetricSpace X]

theorem preimage_Icc_subset_annulus {p : X} {η : X → ℝ} {e : ℝ}
    (hclose : ∀ x, |η x - dist p x| < e) (a b : ℝ) :
    η ⁻¹' Icc a b ⊆ {x | a - e < dist p x ∧ dist p x < b + e} := by
  intro x hx
  have h := abs_lt.mp (hclose x)
  exact ⟨by linarith [hx.1, h.2], by linarith [hx.2, h.1]⟩

theorem radialBand_subset_annulus {p : X} {η : X → ℝ} {e : ℝ}
    (hclose : ∀ x, |η x - dist p x| < e) (he : e < 1 / 40) :
    η ⁻¹' Icc (1 / 8) 3 ⊆ {x | 1 / 10 < dist p x ∧ dist p x < 10} := by
  intro x hx
  have h := preimage_Icc_subset_annulus hclose (1 / 8) 3 hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem isCompact_preimage_of_abs_sub_dist_lt [ProperSpace X] {p : X} {η : X → ℝ}
    (hη : Continuous η) {e : ℝ} (hclose : ∀ x, |η x - dist p x| < e) {S : Set ℝ}
    (hS : IsCompact S) : IsCompact (η ⁻¹' S) := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  apply (isCompact_closedBall p (R + e)).of_isClosed_subset (hS.isClosed.preimage hη)
  intro x hx
  have h1 := hR hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := abs_lt.mp (hclose x)
  rw [Metric.mem_closedBall, dist_comm]
  linarith [(abs_le.mp h1).2]

theorem isProperMap_of_abs_sub_dist_lt [ProperSpace X] {p : X} {η : X → ℝ}
    (hη : Continuous η) {e : ℝ} (hclose : ∀ x, |η x - dist p x| < e) : IsProperMap η :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨hη, fun _ hS => isCompact_preimage_of_abs_sub_dist_lt hη hclose hS⟩

end Kernel

section Binding

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem mfderiv_ne_zero_of_gradientFun (g : SmoothRiemannianMetric I M) {η : M → ℝ}
    {x : M} {c : ℝ} (hc : 0 < c)
    (hg : c ≤ g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x)) :
    mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0 := by
  intro h0
  have h := inner_gradientFun (I := I) g η x (gradientFun (I := I) g η x)
  have hz : mvfderiv (I := I) η x (gradientFun (I := I) g η x) = 0 := by
    change NormedSpace.fromTangentSpace (η x)
      (mfderiv I 𝓘(ℝ, ℝ) η x (gradientFun (I := I) g η x)) = 0
    rw [h0]
    rfl
  rw [hz] at h
  linarith

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC32, binding form (PC Riemannian setting; `E M : Type` because the sublevel-manifold
supplier is stated in universe zero). -/
theorem radialSublevel_structure (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} (hη : Continuous η)
    {ε e : ℝ} (hε1 : ε < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - ε) ^ 2 ≤ g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) ∧
      g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) ≤ (1 + ε) ^ 2) :
    IsProperMap η ∧ IsCompact (η ⁻¹' Icc (1 / 8) 3) ∧
    (∃ O : Set M, IsOpen O ∧ η ⁻¹' Icc (1 / 8) 3 ⊆ O ∧ O ⊆ W ∧ ∀ x ∈ O,
      (1 - ε) ^ 2 ≤ g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) ∧
      g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) ≤ (1 + ε) ^ 2) ∧
    ∀ t ∈ Icc (1 / 8 : ℝ) 3,
      IsCompact {x | η x ≤ t} ∧ interior {x | η x ≤ t} = {x | η x < t} ∧
      frontier {x | η x ≤ t} = {x | η x = t} ∧
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ {x | f x ≤ t} = {x | η x ≤ t} ∧
        (∃ O : Set M, IsOpen O ∧ {x | η x = t} ⊆ O ∧ EqOn f η O) ∧
        (∀ x, f x = t → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
        ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
          ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) (DifferentialGeometry.Topology.Morse.SublevelSpace f t),
            letI := cs
            IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
              (DifferentialGeometry.Topology.Morse.SublevelSpace f t) ∧
            ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
              (fun x : DifferentialGeometry.Topology.Morse.SublevelSpace f t => x.1) ∧
            (∀ x : DifferentialGeometry.Topology.Morse.SublevelSpace f t, Function.Bijective
              (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
                (fun y : DifferentialGeometry.Topology.Morse.SublevelSpace f t => y.1) x)) ∧
            (∀ x : DifferentialGeometry.Topology.Morse.SublevelSpace f t,
              (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔
                f x.1 = t) := by
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ)
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  set K := η ⁻¹' Icc (1 / 8 : ℝ) 3 with hKdef
  have hK : IsCompact K := isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hKann := radialBand_subset_annulus hclose he
  let O₀ : Set M := {x | 1 / 10 < dist p x ∧ dist p x < 10}
  have hO₀ : IsOpen O₀ :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const)
  have hO₀W : O₀ ⊆ W := fun x hx => hCW x hx.1.le hx.2.le
  have hKW : K ⊆ W := hKann.trans hO₀W
  have hpos : 0 < (1 - ε) ^ 2 := by
    have : 0 < 1 - ε := by linarith
    positivity
  refine ⟨isProperMap_of_abs_sub_dist_lt hη hclose, hK,
    ⟨O₀, hO₀, hKann, hO₀W, fun x hx => hgrad x hx.1.le hx.2.le⟩, ?_⟩
  intro t ht
  obtain ⟨f, hf, ⟨O, hOo, hKO, hOW, hEq⟩, hlo, hhi⟩ :=
    exists_contMDiff_eqOn_band hη hW hηW (by norm_num : (1 / 8 : ℝ) < 3) hK hKW
  have hle : ∀ x, f x ≤ t ↔ η x ≤ t := fun x => band_le_iff hEq hKO hlo hhi ht
  have hlt : ∀ x, f x < t ↔ η x < t := fun x => band_lt_iff hEq hKO hlo hhi ht
  have heq : ∀ x, f x = t ↔ η x = t := fun x => band_eq_iff hEq hKO hlo hhi ht
  have hlevelK : {x | η x = t} ⊆ K := fun x hx => by
    change η x ∈ Icc (1 / 8 : ℝ) 3
    rw [show η x = t from hx]
    exact ht
  have hreg : ∀ x, f x = t → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x hx hcrit
    have hxK : x ∈ K := hlevelK ((heq x).mp hx)
    have hxO₀ := hKann hxK
    have hfη : f =ᶠ[𝓝 x] η := Filter.eventuallyEq_of_mem (hOo.mem_nhds (hKO hxK)) hEq
    have hne := mfderiv_ne_zero_of_gradientFun g hpos (hgrad x hxO₀.1.le hxO₀.2.le).1
    apply hne
    change mfderiv I 𝓘(ℝ, ℝ) f x = 0 at hcrit
    rw [hfη.symm.mfderiv_eq, hcrit]
    exact ContinuousLinearMap.comp_zero _
  have hsetle : {x | f x ≤ t} = {x | η x ≤ t} := Set.ext hle
  have hsetlt : {x | f x < t} = {x | η x < t} := Set.ext hlt
  have hint : interior {x | η x ≤ t} = {x | η x < t} := by
    rw [← hsetle, ← hsetlt]
    exact DifferentialGeometry.Topology.Morse.interior_sublevel_eq_lt_sublevel f t hf hreg
  have hclosed : IsClosed {x | η x ≤ t} := isClosed_le hη continuous_const
  have hAt : {x | η x ≤ t} = η ⁻¹' Icc (-e) t := by
    ext x
    have h := abs_lt.mp (hclose x)
    have hd := dist_nonneg (x := p) (y := x)
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc]
    exact ⟨fun hx => ⟨by linarith, hx⟩, fun hx => hx.2⟩
  refine ⟨hAt ▸ isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc, hint, ?_, f, hf, hsetle,
    ⟨O, hOo, hlevelK.trans hKO, hEq⟩, hreg, DifferentialGeometry.Topology.Morse.exists_isManifold_sublevel f t hf hreg⟩
  rw [frontier, hclosed.closure_eq, hint]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq, not_lt]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 h2
  · intro h
    exact ⟨h.le, h.ge⟩

end Binding

end DifferentialGeometry.Geometry.Collapse
