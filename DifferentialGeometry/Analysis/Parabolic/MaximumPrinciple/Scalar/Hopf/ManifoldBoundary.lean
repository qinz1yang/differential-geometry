import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Barrier
import DifferentialGeometry.Geometry.Boundary.Normal.InwardCurve
import DifferentialGeometry.Geometry.Boundary.Normal.Derivative

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

variable {E : Type*}
variable {H : Type*} [TopologicalSpace H]

section Barrier

variable [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

omit [FiniteDimensional Real E] [IsManifold I ∞ M] hI in
private theorem boundaryHopf_hasDerivWithinAt_comp_mfderivWithin
    (f : M → Real) (gamma : Real → M) (s : Set Real) (t : Real)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f (gamma t))
    (hgamma : MDifferentiableWithinAt
      (modelWithCornersSelf Real Real) I gamma s t) :
    HasDerivWithinAt (fun r => f (gamma r))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I (modelWithCornersSelf Real Real) f (gamma t)
          (mfderivWithin (modelWithCornersSelf Real Real) I gamma s t 1))) s t := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  have hcomp := hf.hasMFDerivAt.comp_hasMFDerivWithinAt t
    hgamma.hasMFDerivWithinAt
  have hcomp' := hcomp.hasFDerivWithinAt
  refine hcomp'.congr_fderiv ?_
  ext
  let z : Real :=
    mfderiv I (modelWithCornersSelf Real Real) f (gamma t)
      (mfderivWithin (modelWithCornersSelf Real Real) I gamma s t 1)
  change z = (ContinuousLinearMap.toSpanSingleton Real z) 1
  change z = 1 * z
  rw [one_mul]

private theorem boundaryHopf_derivWithin_nonpos_at_Icc_min_of_pos
    {phi : Real → Real} {T t : Real}
    (hmin : IsLocalMinOn phi (Set.Icc 0 T) t)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (_hphi : DifferentiableWithinAt Real phi (Set.Icc 0 T) t) :
    derivWithin phi (Set.Icc 0 T) t ≤ 0 := by
  have hdir : (0 : Real) - t ∈ posTangentConeAt (Set.Icc 0 T) t := by
    have hseg : segment Real t 0 ⊆ Set.Icc 0 T := by
      rw [segment_symm, segment_eq_Icc ht.1]
      intro y hy
      exact ⟨hy.1, hy.2.trans ht.2⟩
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg : 0 ≤
      (fderivWithin Real phi (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) :=
    hmin.fderivWithin_nonneg hdir
  have hlin :
      (fderivWithin Real phi (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) =
        (0 - t) * derivWithin phi (Set.Icc 0 T) t := by
    rw [← fderivWithin_derivWithin (f := phi) (s := Set.Icc 0 T) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc 0 T) t : Real →L[Real] Real).map_smul
        (0 - t) (1 : Real))
  rw [hlin] at hnonneg
  exact nonpos_of_mul_nonneg_right hnonneg (sub_neg.mpr htpos)

omit [TopologicalSpace M] [FiniteDimensional Real E] [IsManifold I ∞ M] hI in
private theorem boundaryHopf_derivWithin_add_eps_mul_time
    {w : Real → M → Real} {T t epsilon : Real} {x : M}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hw : DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t) :
    derivWithin (fun s => w s x + epsilon * s) (Set.Icc 0 T) t =
      derivWithin (fun s => w s x) (Set.Icc 0 T) t + epsilon := by
  have hlinear : DifferentiableWithinAt Real (fun s => epsilon * s)
      (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_fun_id (s := Set.Icc 0 T) (x := t)).const_mul epsilon
  have hderiv_linear : derivWithin (fun s => epsilon * s)
      (Set.Icc 0 T) t = epsilon := by
    rw [derivWithin_const_mul epsilon (d := fun s : Real => s)
      (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [derivWithin_id' (s := Set.Icc 0 T) (x := t) huniq]
    ring
  rw [derivWithin_fun_add hw hlinear, hderiv_linear]

omit hI in
theorem strict_barrier_on_compact_manifold_with_boundary
    [CompactSpace M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real → (x : M) → TangentSpace I x)
    (w : Real → M → Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hw0 : ∀ x : M, 0 ≤ w 0 x)
    (hw_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      0 ≤ w t (p : M))
    (hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      w t x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ w t x := by
  apply strict_barrier_on_compact_manifold_interior_region
    (I := I) G T X w (I.interior M)
    (I.isOpen_interior (M := M) (n := ∞) (by simp)) Set.Subset.rfl
    hw_cont hw0
  · intro t ht x hx
    rcases I.isInteriorPoint_or_isBoundaryPoint x with hxint | hxbdy
    · exact (hx hxint).elim
    · exact hw_boundary t ht ⟨x, hxbdy⟩
  · exact hw_time
  · exact hw_mdiff
  · exact hw_grad
  · exact hnegative

end Barrier

private theorem boundaryHopf_deriv_nonneg_at_right_endpoint
    {f : Real → Real} {a d : Real} (ha : 0 < a)
    (hmin : IsMinOn f (Set.Icc 0 a) 0)
    (hderiv : HasDerivWithinAt f d (Set.Ici 0) 0) :
    0 ≤ d := by
  have hdir : a - 0 ∈ posTangentConeAt (Set.Icc 0 a) 0 := by
    have hseg : segment Real 0 a ⊆ Set.Icc 0 a := by
      rw [segment_eq_Icc ha.le]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg : 0 ≤
      (fderivWithin Real f (Set.Icc 0 a) 0 : Real →L[Real] Real) (a - 0) :=
    hmin.isLocalMinOn.fderivWithin_nonneg hdir
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 a) 0 :=
    (uniqueDiffOn_Icc ha).uniqueDiffWithinAt (left_mem_Icc.mpr ha.le)
  have hderivWithin : derivWithin f (Set.Icc 0 a) 0 = d := by
    exact (hderiv.mono fun _ hx => hx.1).derivWithin huniq
  have hlin :
      (fderivWithin Real f (Set.Icc 0 a) 0 : Real →L[Real] Real) (a - 0) =
        (a - 0) * derivWithin f (Set.Icc 0 a) 0 := by
    rw [← fderivWithin_derivWithin (f := f) (s := Set.Icc 0 a) (x := 0)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real f (Set.Icc 0 a) 0 : Real →L[Real] Real).map_smul
        (a - 0) (1 : Real))
  rw [hlin, hderivWithin] at hnonneg
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnonneg) ha

section BoundaryPoint

variable [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem scalar_hopf_boundary_point_of_barrier_with_boundary
    [CompactSpace M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    (u v : Real → M → Real)
    (hcont : ContinuousOn (fun q : Real × M => u q.1 q.2 - v q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hinit : ∀ x : M, 0 ≤ u 0 x - v 0 x)
    (hboundary : ∀ t ∈ Set.Icc 0 T, ∀ q : BoundaryManifold I M,
      0 ≤ u t (q : M) - v t (q : M))
    (htime : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x - v s x) (Set.Icc 0 T) t)
    (hmdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (fun y => u t y - v t y) x)
    (hgrad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t)
        (fun z => u t z - v t z) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      u t x - v t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - v s y) t x)
    {p : BoundaryManifold I M}
    (heq : u T (p : M) = v T (p : M))
    (hu_mdiff : MDifferentiableAt I 𝓘(Real, Real) (u T) (p : M))
    (hv_mdiff : MDifferentiableAt I 𝓘(Real, Real) (v T) (p : M))
    (hv_inward : 0 < (G.metric T).inner (p : M)
      (gradientFun (I := I) (G.metric T) (v T) (p : M))
      (inwardCoord (M := M) p))
    (hmin : IsLocalMin
      (fun q : BoundaryManifold I M => u T (q : M)) p) :
    outwardNormalDerivative (E := E) (H := H) (I := I) (M := M)
      (G.metric T) (u T) p < 0 := by
  obtain ⟨gamma, hgamma0, hgamma_mdiff, hgamma_velocity, a, ha, _⟩ :=
    exists_inward_curve (I := I) (M := M) p
  have hu_deriv : HasDerivWithinAt (fun s => u T (gamma s))
      ((G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (u T) (p : M))
        (inwardCoord (M := M) p)) (Set.Ici 0) 0 := by
    have hcurve := boundaryHopf_hasDerivWithinAt_comp_mfderivWithin
      (I := I) (u T) gamma (Set.Ici 0) 0
      (by simpa [hgamma0] using hu_mdiff) hgamma_mdiff
    rw [hgamma0] at hcurve
    convert hcurve using 1
    change (G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (u T) (p : M))
        (inwardCoord (M := M) p) =
      mfderiv I 𝓘(Real, Real) (u T) (p : M)
        (mfderivWithin 𝓘(Real, Real) I gamma (Set.Ici 0) 0 1)
    rw [inner_gradientFun]
    exact congrArg (mfderiv I 𝓘(Real, Real) (u T) (p : M))
      hgamma_velocity.symm
  have hv_deriv : HasDerivWithinAt (fun s => v T (gamma s))
      ((G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (v T) (p : M))
        (inwardCoord (M := M) p)) (Set.Ici 0) 0 := by
    have hcurve := boundaryHopf_hasDerivWithinAt_comp_mfderivWithin
      (I := I) (v T) gamma (Set.Ici 0) 0
      (by simpa [hgamma0] using hv_mdiff) hgamma_mdiff
    rw [hgamma0] at hcurve
    convert hcurve using 1
    change (G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (v T) (p : M))
        (inwardCoord (M := M) p) =
      mfderiv I 𝓘(Real, Real) (v T) (p : M)
        (mfderivWithin 𝓘(Real, Real) I gamma (Set.Ici 0) 0 1)
    rw [inner_gradientFun]
    exact congrArg (mfderiv I 𝓘(Real, Real) (v T) (p : M))
      hgamma_velocity.symm
  let w : Real → M → Real := fun t x => u t x - v t x
  have hw_nonneg := strict_barrier_on_compact_manifold_with_boundary
    (I := I) G T X w hcont hinit hboundary htime hmdiff hgrad hoperator
  let f : Real → Real := fun s => u T (gamma s) - v T (gamma s)
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [hgamma0, heq, sub_self]
  have hf_nonneg : ∀ s ∈ Set.Icc 0 a, 0 ≤ f s := by
    intro s hs
    exact hw_nonneg T ⟨hT, le_rfl⟩ (gamma s)
  have hfmin : IsMinOn f (Set.Icc 0 a) 0 := by
    intro s hs
    rw [hf0]
    exact hf_nonneg s hs
  have hfderiv : HasDerivWithinAt f
      ((G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (u T) (p : M))
        (inwardCoord (M := M) p) -
      (G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (v T) (p : M))
        (inwardCoord (M := M) p)) (Set.Ici 0) 0 :=
    hu_deriv.sub hv_deriv
  have hdiff := boundaryHopf_deriv_nonneg_at_right_endpoint ha hfmin hfderiv
  have hinward : 0 < (G.metric T).inner (p : M)
      (gradientFun (I := I) (G.metric T) (u T) (p : M))
      (inwardCoord (M := M) p) := by
    linarith [hv_inward]
  exact
    outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min
      (E := E) (H := H) (I := I) (M := M)
      (G.metric T) hmin hu_mdiff hinward

end BoundaryPoint

end

end DifferentialGeometry.Analysis.Parabolic
