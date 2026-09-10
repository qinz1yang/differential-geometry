import DifferentialGeometry.Topology.Manifold.Interval.Interior
import DifferentialGeometry.Topology.Manifold.Interval.StripHeight
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.Manifold.Interval

theorem mfderiv_signedStripCoordinate
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (J : ModelWithCorners ℝ E H) {ε : ℝ} [Fact ((0 : ℝ) < ε)] (a : ℝ)
    (S : Opens (B × Icc (0 : ℝ) ε)) (q : S) (v : TangentSpace (J.prod (𝓡∂ 1)) q) :
    mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ))
        (fun p : S => (p.val.1, 1 - p.val.2.val / a)) q v =
      (v.1, -(tangentCoordinateIcc q.val.2 v.2) / a) := by
  have hinc := (contMDiff_subtype_val (I := J.prod (𝓡∂ 1)) (U := S) (n := ∞)).mdifferentiableAt
    (x := q) (by simp)
  have hf := (mdifferentiableAt_fst (I := J) (I' := 𝓡∂ 1)).comp q hinc
  have hh := ((contMDiff_subtypeVal_Icc (n := ∞)).comp (contMDiff_snd.comp
    (contMDiff_subtype_val (I := J.prod (𝓡∂ 1)) (U := S)))).mdifferentiableAt (x := q) (by simp)
  have hl := ((hasDerivAt_const q.val.2.val (1 : ℝ)).sub
    ((hasDerivAt_id q.val.2.val).div_const a)).hasFDerivAt.hasMFDerivAt
  have hp := hf.hasMFDerivAt.prodMk (hl.comp q hh.hasMFDerivAt)
  have hfirst := mfderiv_comp q (mdifferentiableAt_fst (I := J) (I' := 𝓡∂ 1)) hinc
  rw [DifferentialGeometry.mfderiv_subtype_val, mfderiv_fst] at hfirst
  erw [hp.mfderiv]
  apply Prod.ext
  · exact congrArg (fun A => A v) hfirst
  · change (show ℝ from mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) (fun p : S => p.val.2.val) q v) * (0 - 1 / a) = _
    rw [mfderiv_stripHeight]
    ring

private def signedRealDiffeomorph {a : ℝ} (ha : a ≠ 0) : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := 1 - r / a
  invFun s := a * (1 - s)
  left_inv r := by field_simp; ring
  right_inv s := by field_simp; ring
  contMDiff_toFun := (show ContDiff ℝ ∞ (fun r : ℝ => 1 - r / a) by fun_prop).contMDiff
  contMDiff_invFun := (show ContDiff ℝ ∞ (fun s : ℝ => a * (1 - s)) by fun_prop).contMDiff

theorem exists_signedStrip_partialDiffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (J : ModelWithCorners ℝ E H) {ε a : ℝ} [Fact ((0 : ℝ) < ε)] (ha : a ≠ 0)
    (S : Opens (B × Icc (0 : ℝ) ε)) (q : S)
    (hq : 0 < q.val.2.val ∧ q.val.2.val < ε) :
    ∃ f : PartialDiffeomorph (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) S (B × ℝ) ∞,
      q ∈ f.source ∧ ∀ p ∈ f.source, f p = (p.val.1, 1 - p.val.2.val / a) := by
  obtain ⟨d, hd, _⟩ := exists_iccInteriorStrip_diffeomorph (B := B) J ∞ (a := (0 : ℝ)) (b := ε)
  let U : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{p | 0 < p.2.val ∧ p.2.val < ε},
      (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)⟩
  let V : Opens (B × ℝ) :=
    ⟨{p | 0 < p.2 ∧ p.2 < ε},
      (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)⟩
  let s := openSubtypePartialDiffeomorph (J.prod (𝓡∂ 1)) S ⟨q⟩
  let u := openSubtypePartialDiffeomorph (J.prod (𝓡∂ 1)) U ⟨⟨q.val, hq⟩⟩
  let v := openSubtypePartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) V ⟨d ⟨q.val, hq⟩⟩
  let A := (Diffeomorph.refl J B ∞).prodCongr (signedRealDiffeomorph ha)
  let f := (((s.trans u.symm).trans d.toPartialDiffeomorph).trans v).trans A.toPartialDiffeomorph
  have huTarget : u.target = (U : Set (B × Icc (0 : ℝ) ε)) :=
    openSubtypePartialDiffeomorph_target (J.prod (𝓡∂ 1)) U ⟨⟨q.val, hq⟩⟩
  have hsource : q ∈ f.source := by
    refine ⟨⟨⟨⟨trivial, ?_⟩, trivial⟩, trivial⟩, trivial⟩
    change q.val ∈ u.target
    rw [huTarget]
    exact hq
  refine ⟨f, hsource, ?_⟩
  intro p hp
  have hpU : p.val ∈ U := by
    have hh := hp.1.1.1.2
    change p.val ∈ u.target at hh
    rwa [huTarget] at hh
  have hu := openSubtypePartialDiffeomorph_symm_apply (J.prod (𝓡∂ 1)) U ⟨⟨q.val, hq⟩⟩ hpU
  change A ((d (u.symm p.val)).val) = _
  rw [show u.symm p.val = ⟨p.val, hpU⟩ from hu, hd]
  rfl

end Poincare.Manifold.Interval
