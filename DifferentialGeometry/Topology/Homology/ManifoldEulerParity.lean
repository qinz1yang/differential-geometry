import DifferentialGeometry.Topology.Homology.ClosedManifold
import DifferentialGeometry.Topology.Homology.ManifoldBoundary
import DifferentialGeometry.Topology.Morse.Affine

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Homology

private theorem hessian_const_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (b : ℝ) (x : E) :
    chartHessianAt (fun y => b - f y) x = -chartHessianAt f x := by
  ext v
  change (fderiv ℝ (fderiv ℝ (fun y => b - f y)) x v) v =
    -((fderiv ℝ (fderiv ℝ f) x v) v)
  rw [show fderiv ℝ (fun y => b - f y) = -fderiv ℝ f from
    funext fun y => fderiv_const_sub b, fderiv_neg]
  rfl

private theorem signature_neg_sign {E : Type} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (Q : QuadraticForm ℝ E)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    (-1 : ℤ)^sigNeg (-Q) = (-1 : ℤ)^Module.finrank ℝ E * (-1 : ℤ)^sigNeg Q := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hr : Q.radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated, LinearMap.separatingLeft_iff_ker_eq_bot.mp hQ]
  have hs := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hr, finrank_bot, add_zero] at hs
  rw [sigNeg_neg, ← hs, pow_add, mul_assoc, ← mul_pow]
  norm_num

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

include I

theorem eulerChar_eq_neg_one_pow_mul_of_compact_boundaryless_manifold
    (K : Type) [Field K] :
    eulerChar K (TopCat.of M) = (-1 : ℤ)^Module.finrank ℝ E * eulerChar K (TopCat.of M) := by
  classical
  cases subsingleton_or_nontrivial E
  · rw [Module.finrank_zero_of_subsingleton, pow_zero, one_mul]
  obtain ⟨f,hf,hnd,hinj,hfinite,hχ⟩ := DifferentialGeometry.Morse.exists_morse_eulerChar I (M := M)
  let g : M → ℝ := fun x => 0 - f x
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := contMDiff_const.sub hf
  have hc (x : M) : IsCriticalPointAt I g x ↔ IsCriticalPointAt I f x :=
    DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff (hf.mdifferentiableAt (by simp)) 0
  have hcset : {x | IsCriticalPointAt I g x} = {x | IsCriticalPointAt I f x} :=
    Set.ext hc
  have hgfinite : {x | IsCriticalPointAt I g x}.Finite := hcset.symm ▸ hfinite
  have hgnd : ∀ x, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x := by
    intro x hx
    exact (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff hf
      BoundarylessManifold.isInteriorPoint 0).mpr (hnd x ((hc x).mp hx))
  have hginj : InjOn g {x | IsCriticalPointAt I g x} := by
    intro x hx y hy he
    apply hinj ((hc x).mp hx) ((hc y).mp hy)
    change 0 - f x = 0 - f y at he
    linarith
  obtain ⟨A,hA⟩ := (isCompact_range hg.continuous).bddAbove
  have hbelow (x : M) : g x < A + 1 := lt_of_le_of_lt (hA (mem_range_self x)) (lt_add_one A)
  have htop : sublevel g (A + 1) = univ := eq_univ_of_forall fun x => (hbelow x).le
  let eTop : SublevelSpace g (A + 1) ≃ₜ M :=
    (Homeomorph.setCongr htop).trans (Homeomorph.Set.univ M)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  let e : E ≃L[ℝ] MorseModel (m + 1) :=
    ((Module.finBasis ℝ E).reindex (finCongr hm)).equivFunL
  obtain ⟨_,hgχ⟩ := DifferentialGeometry.Morse.finiteHomologyType_and_eulerChar_of_finite_morse_sublevel
    I K e hg (A + 1) (htop ▸ isCompact_univ) (fun _ _ => BoundarylessManifold.isInteriorPoint)
    hgfinite hgnd hginj (fun x _ => hbelow x)
  have hχg := (eulerChar_eq_of_homeomorph K (X := TopCat.of (SublevelSpace g (A + 1)))
    (Y := TopCat.of M) eTop).symm.trans hgχ
  have hs : hgfinite.toFinset = hfinite.toFinset := Set.Finite.toFinset_inj.mpr hcset
  rw [hs] at hχg
  conv_rhs => rw [(hχ K).2]
  calc
    eulerChar K (TopCat.of M) = ∑ p ∈ hfinite.toFinset, (-1 : ℤ)^sigNeg
        (chartHessianAt (fun y => g ((extChartAt I p).symm y)) (extChartAt I p p)) := hχg
    _ = ∑ p ∈ hfinite.toFinset, (-1 : ℤ)^Module.finrank ℝ E * (-1 : ℤ)^sigNeg
        (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      change (-1 : ℤ)^sigNeg (chartHessianAt (fun y => 0 - f ((extChartAt I p).symm y))
        (extChartAt I p p)) = _
      rw [hessian_const_sub]
      exact signature_neg_sign _ (hnd p (hfinite.mem_toFinset.mp hp)).2
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem eulerChar_eq_zero_of_odd_compact_boundaryless_manifold
    (K : Type) [Field K] (hdim : Odd (Module.finrank ℝ E)) :
    eulerChar K (TopCat.of M) = 0 := by
  have h := eulerChar_eq_neg_one_pow_mul_of_compact_boundaryless_manifold I K (M := M)
  rw [hdim.neg_one_pow, neg_one_mul] at h
  omega

end DifferentialGeometry.Homology

namespace DifferentialGeometry.Homology
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem eulerChar_intrinsicBoundary_eq_zero_of_even (K : Type) [Field K]
    (hdim : Even (Module.finrank ℝ E)) : eulerChar K (TopCat.of (I.boundary M)) = 0 := by
  let _ : CompactSpace (BoundaryManifold I M) := isCompact_iff_compactSpace.mp
    (show IsCompact (I.boundary M) from (I.isClosed_boundary (n := ∞) (by simp)).isCompact)
  have hd := hI.finrank_boundaryE_succ
  have hodd : Odd (Module.finrank ℝ hI.boundaryE) := by
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at hdim
    omega
  exact eulerChar_eq_zero_of_odd_compact_boundaryless_manifold hI.boundaryI K hodd
    (M := BoundaryManifold I M)

end DifferentialGeometry.Homology
