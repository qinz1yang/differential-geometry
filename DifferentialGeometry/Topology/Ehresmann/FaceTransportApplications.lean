import DifferentialGeometry.Topology.Ehresmann.FaceTransport
import DifferentialGeometry.Topology.Ehresmann.SublevelTransport

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Ehresmann

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [I.Boundaryless]

/-- Compact-carrier sublevel transport needs transversality only on the actual boundary level. -/
theorem exists_diffeomorph_sublevel_of_level_transport
    (g : M × ℝ → ℝ) (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ g) (c : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x, g (x, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ) (fun y => g (y, τ)) x)) :
    ∃ Ψ : M ≃ₘ⟮I, I⟯ M,
      Ψ '' {x | g (x, 0) ≤ c} = {x | g (x, 1) ≤ c} ∧
      Ψ '' {x | g (x, 0) = c} = {x | g (x, 1) = c} := by
  obtain ⟨ε, hε, hmargin⟩ := exists_band_margin_of_level_surjective g hg c hreg isCompact_univ
  exact exists_diffeomorph_image_sublevel_of_band_transport g hg c hε
    (fun τ hτ x hx => hmargin τ hτ x (mem_univ x) (by simpa only [Real.norm_eq_abs] using hx))

/-- A compactly supported ambient diffeomorphism moves a round disk and its boundary circle. -/
theorem exists_compactSupport_moving_roundDisk :
    ∃ Ψ : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ),
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ ∀ x ∉ K, Ψ x = x) ∧
      Ψ '' {x : ℝ × ℝ | x.1 ^ 2 + x.2 ^ 2 ≤ (1 / 16 : ℝ)} =
        {x : ℝ × ℝ | x.1 ^ 2 + (x.2 - 1) ^ 2 ≤ (1 / 16 : ℝ)} ∧
      Ψ '' {x : ℝ × ℝ | x.1 ^ 2 + x.2 ^ 2 = (1 / 16 : ℝ)} =
        {x : ℝ × ℝ | x.1 ^ 2 + (x.2 - 1) ^ 2 = (1 / 16 : ℝ)} := by
  let α : ContDiffBump (0 : ℝ) :=
    { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let Z : (x : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) x := fun x => (0, α x.1 * α x.2)
  have hZ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
      (fun x => (⟨x, Z x⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr
      (contDiff_const.prodMk ((α.contDiff.comp contDiff_fst).mul
        (α.contDiff.comp contDiff_snd)))
  let K : Set (ℝ × ℝ) := tsupport α ×ˢ tsupport α
  have hK : IsCompact K := α.hasCompactSupport.isCompact.prod α.hasCompactSupport.isCompact
  have hsupp : tsupport Z ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    have hne : α x.1 * α x.2 ≠ 0 := by
      intro hz
      apply hx
      change (0, α x.1 * α x.2) = (0 : ℝ × ℝ)
      rw [hz]
      rfl
    exact ⟨subset_tsupport α (left_ne_zero_of_mul hne),
      subset_tsupport α (right_ne_zero_of_mul hne)⟩
  have hzone (s : ℝ) (hs : |s| ≤ 1 / 4) (r : ℝ) (hr : |r| ≤ 2) :
      Z (s, r) = ((0 : ℝ), 1) := by
    change (0, α s * α r) = _
    rw [α.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hs.trans (by norm_num : (1 / 4 : ℝ) ≤ 2)),
      α.one_of_mem_closedBall (by
        simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
        exact hr), one_mul]
  let A : Bool → ∀ x : ℝ × ℝ, TangentSpace 𝓘(ℝ, ℝ × ℝ) x →L[ℝ] ℝ :=
    fun i _x => if i then ContinuousLinearMap.snd ℝ ℝ ℝ else ContinuousLinearMap.fst ℝ ℝ ℝ
  let b : Bool → (ℝ × ℝ) → ℝ := fun i _x => if i then 1 else 0
  let stratum : Bool → Set (ℝ × ℝ) :=
    fun i => if i then {x | |x.1| ≤ 1 / 4 ∧ |x.2| ≤ 2} else univ
  have hzout (x : ℝ × ℝ) (hx : x ∉ K) : Z x = 0 := by
    by_contra hz
    exact hx (hsupp (subset_tsupport Z hz))
  obtain ⟨X, hXa, hXs, hcompact⟩ := exists_smoothAffineConstraintSection_of_local A b stratum hK
    (fun _x => ⟨univ, Filter.univ_mem, Z, hZ.contMDiffOn, by
      intro x _hx i hi
      cases i with
      | false => rfl
      | true =>
        change |x.1| ≤ 1 / 4 ∧ |x.2| ≤ 2 at hi
        have heq := congrArg Prod.snd (hzone x.1 hi.1 x.2 hi.2)
        exact heq, fun x _hx hx => hzout x hx⟩)
  let D := compactSupportFlowDiffeomorph X X.contMDiff hcompact
  have hone (s : ℝ) (hs : |s| ≤ 1 / 4) (r : ℝ) (hr : r ∈ Ioo (-2 : ℝ) 2) :
      X (s, r) = ((0 : ℝ), 1) := by
    apply Prod.ext
    · exact hXa (s, r) false (mem_univ _)
    · exact hXa (s, r) true ⟨hs, abs_le.mpr ⟨hr.1.le, hr.2.le⟩⟩
  have hmove (s r t : ℝ) (hs : |s| ≤ 1 / 4)
      (hr : r ∈ Ioo (-2 : ℝ) 2) (hrt : r + t ∈ Ioo (-2 : ℝ) 2) :
      D t (s, r) = (s, r + t) :=
    flow_eq_of_bump_eq_one X X.contMDiff hcompact (hone s hs) hr hrt
  have hbounds (s r : ℝ) (h : s ^ 2 + r ^ 2 ≤ (1 / 16 : ℝ)) :
      |s| ≤ 1 / 4 ∧ |r| ≤ 1 / 4 := by
    constructor <;> apply abs_le.mpr <;> constructor <;>
      nlinarith [sq_nonneg s, sq_nonneg r]
  have hf (x : ℝ × ℝ) (hx : x.1 ^ 2 + x.2 ^ 2 ≤ (1 / 16 : ℝ)) :
      D 1 x = (x.1, x.2 + 1) := by
    obtain ⟨hs, hr⟩ := hbounds x.1 x.2 hx
    exact hmove x.1 x.2 1 hs (by constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2])
      (by constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2])
  have hb (x : ℝ × ℝ) (hx : x.1 ^ 2 + (x.2 - 1) ^ 2 ≤ (1 / 16 : ℝ)) :
      D (-1) x = (x.1, x.2 - 1) := by
    obtain ⟨hs, hr⟩ := hbounds x.1 (x.2 - 1) hx
    simpa only [sub_eq_add_neg] using hmove x.1 x.2 (-1) hs
      (by constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2])
      (by constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2])
  have hsymm : (D 1).symm = D (-1) := compactSupportFlowDiffeomorph_symm X X.contMDiff hcompact 1
  have hXout : ∀ t : ℝ, ∀ x : ℝ × ℝ, x ∉ K → X x = 0 := by
    intro _t x hx
    by_contra hne
    exact hx (hXs (subset_tsupport X hne))
  obtain ⟨Ψ, hself, _hcomp, hout, hderiv⟩ := exists_compactSupport_ambientTransport
    (fun _t x => X x) (X.contMDiff.comp contMDiff_snd) hK hXout
  have hsame : Ψ 0 1 = D 1 := by
    apply Diffeomorph.ext
    intro x
    have hnew : IsMIntegralCurve (fun t => Ψ 0 t x) X :=
      fun t => hderiv 0 t x
    have hold := curveAt_integralCurve X
      (exists_globalIntegralCurve_of_compactSupport X X.contMDiff hcompact) x
    have heq := integralCurve_eq_of_agree X (X.contMDiff.of_le (by norm_num)) hnew hold
      (t₀ := 0) (by rw [hself, curveAt_zero])
    exact congrFun heq 1
  refine ⟨Ψ 0 1, ⟨K, hK, fun x hx => hout 0 1 x hx⟩, ?_, ?_⟩
  · ext y
    rw [hsame]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hf x hx]
      simpa only [Set.mem_ofPred_eq, add_sub_cancel_right] using hx
    · intro hy
      refine ⟨D (-1) y, ?_, ?_⟩
      · rw [hb y hy]
        exact hy
      · rw [← hsymm]
        exact (D 1).apply_symm_apply y
  · ext y
    rw [hsame]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hf x hx.le]
      simpa only [Set.mem_ofPred_eq, add_sub_cancel_right] using hx
    · intro hy
      refine ⟨D (-1) y, ?_, ?_⟩
      · rw [hb y hy.le]
        exact hy
      · rw [← hsymm]
        exact (D 1).apply_symm_apply y

end DifferentialGeometry.Topology.Ehresmann
