import DifferentialGeometry.Topology.Ehresmann.SideBoundaryVectorFlow
import DifferentialGeometry.Analysis.ODE.Uniqueness
import DifferentialGeometry.Analysis.ODE.IntegralCurveNaturality

/-!
Proper side fibres over a compact closed base set have a uniform ambient rank and compactness
margin. The argument uses the actual base map in arbitrary finite dimension, together with
its joint boundary derivative, to prepare the parameterized radial transport over balls.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E G H M : Type*}
  [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [normG : NormedAddCommGroup G] [spaceG : NormedSpace ℝ G]
  [finiteG : FiniteDimensional ℝ G]
  [topH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [topM : TopologicalSpace M] [chartsM : ChartedSpace H M]
  [smoothM : IsManifold I ∞ M] [hausdorffM : T2Space M]

theorem exists_sideBoundary_compactBase_margin {P : M → G} {B : M → ℝ} {K : Set G}
    (hP : ContMDiff I 𝓘(ℝ, G) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hK : IsClosed K) (hc : IsCompact (P ⁻¹' K ∩ {x | 0 ≤ B x}))
    (hreg : ∀ x, P x ∈ K → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) P x))
    (hregb : ∀ x, P x ∈ K → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)) :
    ∃ U : Set M, IsOpen U ∧ (P ⁻¹' K ∩ {x | 0 ≤ B x}) ⊆ U ∧
      ∃ r > 0, IsCompact {x | x ∈ U ∧ P x ∈ K ∧ -r ≤ B x} ∧
        (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, G) P x)) ∧
        (∀ x ∈ U, |B x| < r →
          Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)) := by
  let compactH : LocallyCompactSpace H := I.locallyCompactSpace
  let compactM : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let R := {x | Surjective (mfderiv I 𝓘(ℝ, G) P x)}
  let S := {x | Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (P y, B y)) x)}
  have hR : IsOpen R := isOpen_setOf_surjective_mfderiv hP
  have hS : IsOpen S := isOpen_setOf_surjective_mfderiv (hP.prodMk_space hB)
  have hpos : IsOpen {x | 0 < B x} := isOpen_lt continuous_const hB.continuous
  have hinside : P ⁻¹' K ∩ {x | 0 ≤ B x} ⊆ R ∩ (S ∪ {x | 0 < B x}) := by
    intro x hx
    refine ⟨hreg x hx.1 hx.2, ?_⟩
    have hb : 0 ≤ B x := hx.2
    rcases eq_or_lt_of_le hb with he | hp
    · exact Or.inl (hregb x hx.1 he.symm)
    · exact Or.inr hp
  obtain ⟨U, ho, hcontains, hclosure, hcompact⟩ :=
    exists_open_between_and_isCompact_closure hc (hR.inter (hS.union hpos)) hinside
  obtain ⟨ε, hε, hband⟩ := exists_norm_margin_of_compact_level hcompact hB.continuous
    (0 : ℝ) hS (by
      intro x hx he
      rcases (hclosure hx).2 with hs | hp
      · exact hs
      · change 0 < B x at hp
        exact False.elim (by simp only [he, lt_self_iff_false] at hp))
  have hedge : IsCompact ((closure U \ U) ∩ P ⁻¹' K) :=
    (hcompact.diff ho).inter_right (hK.preimage hP.continuous)
  have hedgesign : ∀ x ∈ (closure U \ U) ∩ P ⁻¹' K, 0 < -B x := by
    intro x hx
    by_contra hbad
    have hb : 0 ≤ B x := by linarith [not_lt.mp hbad]
    exact hx.1.2 (hcontains ⟨hx.2, hb⟩)
  obtain ⟨m, hm, hgap⟩ := exists_pos_lowerBound_of_isCompact hedge
    hB.continuous.neg.continuousOn hedgesign
  let r := min ε m / 2
  have hr : 0 < r := half_pos (lt_min hε hm)
  have hsmall : r < m := by
    dsimp [r]
    linarith [min_le_right ε m, lt_min hε hm]
  have heq : {x | x ∈ U ∧ P x ∈ K ∧ -r ≤ B x} =
      closure U ∩ (P ⁻¹' K ∩ {x | -r ≤ B x}) := by
    ext x
    constructor
    · rintro ⟨hx, hp, hb⟩
      exact ⟨subset_closure hx, hp, hb⟩
    · rintro ⟨hx, hp, hb⟩
      refine ⟨?_, hp, hb⟩
      by_contra he
      have hbound := hgap x ⟨⟨hx, he⟩, hp⟩
      change m ≤ -B x at hbound
      change -r ≤ B x at hb
      linarith
  refine ⟨U, ho, hcontains, r, hr, ?_, ?_, ?_⟩
  · rw [heq]
    exact hcompact.inter_right ((hK.preimage hP.continuous).inter
      (isClosed_le continuous_const hB.continuous))
  · exact fun x hx => (hclosure (subset_closure hx)).1
  · intro x hx hb
    apply hband x (subset_closure hx)
    rw [sub_zero, Real.norm_eq_abs]
    have hrε : r ≤ ε := by
      dsimp [r]
      linarith [min_le_left ε m, lt_min hε hm]
    exact hb.trans_le hrε

end DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

variable {F : Type*} [normF : NormedAddCommGroup F] [spaceF : NormedSpace ℝ F]
  [finiteF : FiniteDimensional ℝ F]

theorem compactSupportFlowDiffeomorph_eq_line (V : F → F) (hV : ContDiff ℝ ∞ V)
    (hc : HasCompactSupport V) (x v : F) (t : ℝ)
    (hpath : ∀ s ∈ uIcc (0 : ℝ) t, V (x + s • v) = v) :
    compactSupportFlowDiffeomorph V (contMDiff_modelTangentSection_of_contDiff hV) hc t x =
      x + t • v := by
  let completeF : CompleteSpace F := FiniteDimensional.complete ℝ F
  let hg := exists_globalIntegralCurve_of_compactSupport V
    (contMDiff_modelTangentSection_of_contDiff hV) hc
  have hcurve := (curveAt_integralCurve V hg x).isMIntegralCurveOn (uIcc (0 : ℝ) t)
  have hordinary := isMIntegralCurveOn_iff_isIntegralCurveOn.mp hcurve
  have hline : IsIntegralCurveOn (fun s : ℝ => x + s • v) (fun s => V) (uIcc (0 : ℝ) t) := by
    intro s hs
    change HasDerivWithinAt (fun u : ℝ => x + u • v) (V (x + s • v)) (uIcc 0 t) s
    rw [hpath s hs]
    have hd := ((hasDerivAt_id s).smul_const v).const_add x
    simp only [id, one_smul] at hd
    exact hd.hasDerivWithinAt
  have he := hordinary.eqOn_of_contDiffOn hline ordConnected_uIcc
    ((hV.comp contDiff_snd).of_le (by norm_num)).contDiffOn left_mem_uIcc
    (by
      simp only [zero_smul, add_zero]
      exact curveAt_zero (I := 𝓘(ℝ, F)) V hg x)
  change curveAt V hg x t = x + t • v
  exact he right_mem_uIcc

def sideBoundaryRadialField (b : ContDiffBump (0 : F)) (y : F × F) : F × F :=
  (0, (b y.1 * b y.2) • y.1)

theorem sideBoundaryRadialField_contDiff (b : ContDiffBump (0 : F)) :
    ContDiff ℝ ∞ (sideBoundaryRadialField b) :=
  contDiff_const.prodMk (((b.contDiff.comp contDiff_fst).mul
    (b.contDiff.comp contDiff_snd)).smul contDiff_fst)

theorem sideBoundaryRadialField_support (b : ContDiffBump (0 : F)) :
    tsupport (sideBoundaryRadialField b) ⊆ tsupport b ×ˢ tsupport b := by
  apply closure_minimal
  · intro y hy
    constructor
    · apply subset_tsupport
      intro he
      apply hy
      simp only [sideBoundaryRadialField, he, zero_mul, zero_smul, Prod.zero_eq_mk]
    · apply subset_tsupport
      intro he
      apply hy
      simp only [sideBoundaryRadialField, he, mul_zero, zero_smul, Prod.zero_eq_mk]
  · exact (isClosed_tsupport b).prod (isClosed_tsupport b)

theorem sideBoundaryRadialField_compact (b : ContDiffBump (0 : F)) :
    HasCompactSupport (sideBoundaryRadialField b) :=
  (b.hasCompactSupport.isCompact.prod b.hasCompactSupport.isCompact).of_isClosed_subset
    (isClosed_tsupport (sideBoundaryRadialField b)) (sideBoundaryRadialField_support b)

theorem sideBoundaryRadialField_flow (b : ContDiffBump (0 : F)) (w p : F) (c t : ℝ)
    (hw : w ∈ Metric.closedBall 0 b.rIn) (hp : p ∈ Metric.closedBall 0 b.rIn)
    (hc : c ∈ Icc (0 : ℝ) (1 / 2)) (hpt : p + t • w ∈ Metric.closedBall 0 b.rIn) :
    compactSupportFlowDiffeomorph (sideBoundaryProfileField (sideBoundaryRadialField b))
      (contMDiff_modelTangentSection_of_contDiff
        (sideBoundaryProfileField_contDiff (sideBoundaryRadialField_contDiff b)))
      (sideBoundaryProfileField_compact (sideBoundaryRadialField_compact b)) t ((w, p), c) =
        ((w, p + t • w), c) := by
  have hconv : Convex ℝ {s : ℝ | p + s • w ∈ Metric.closedBall 0 b.rIn} :=
    ((convex_closedBall (0 : F) b.rIn).translate_preimage_right p).linear_preimage
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight w)
  have hzero : (0 : ℝ) ∈ {s : ℝ | p + s • w ∈ Metric.closedBall 0 b.rIn} := by
    change p + (0 : ℝ) • w ∈ Metric.closedBall 0 b.rIn
    simpa only [zero_smul, add_zero] using hp
  have hpath := hconv.ordConnected.uIcc_subset hzero hpt
  have he := compactSupportFlowDiffeomorph_eq_line
    (sideBoundaryProfileField (sideBoundaryRadialField b))
    (sideBoundaryProfileField_contDiff (sideBoundaryRadialField_contDiff b))
    (sideBoundaryProfileField_compact (sideBoundaryRadialField_compact b))
    ((w, p), c) (((0 : F), w), (0 : ℝ)) t (by
      intro s hs
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
      change sideBoundaryProfileField (sideBoundaryRadialField b) ((w, p + s • w), c) =
        (((0 : F), w), (0 : ℝ))
      rw [sideBoundaryProfileField, sideBoundaryRadialField,
        b.one_of_mem_closedBall hw, b.one_of_mem_closedBall (hpath hs),
        sideBoundaryProfileBump_one hc, one_mul, one_smul, one_smul])
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using he

end DifferentialGeometry.Topology.Ehresmann
