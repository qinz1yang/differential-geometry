import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Strong
import DifferentialGeometry.Geometry.Boundary.InwardCurve
import DifferentialGeometry.Geometry.Boundary.NormalDerivative

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
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
  convert hcomp' using 1
  change ContinuousLinearMap.toSpanSingleton Real
      (((mfderiv I (modelWithCornersSelf Real Real) f (gamma t)).comp
        (mfderivWithin (modelWithCornersSelf Real Real) I gamma s t)) 1) = _
  exact ContinuousLinearMap.toSpanSingleton_apply_map_one
    (R₁ := Real) (M₂ := Real) _

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
      (differentiableWithinAt_id' (s := Set.Icc 0 T) (x := t)).const_mul epsilon
  have hderiv_linear : derivWithin (fun s => epsilon * s)
      (Set.Icc 0 T) t = epsilon := by
    rw [derivWithin_const_mul epsilon (d := fun s : Real => s)
      (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [derivWithin_id' (s := Set.Icc 0 T) (x := t) huniq]
    ring
  rw [derivWithin_fun_add hw hlinear, hderiv_linear]

omit hI in
theorem strict_barrier_on_compact_manifold_with_boundary
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
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
  have hbarrier : ∀ epsilon : Real, 0 < epsilon →
      ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ w t x + epsilon * t := by
    intro epsilon hepsilon
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    let Phi : Real × M → Real := fun p => w p.1 p.2 + epsilon * p.1
    have hPhi_cont : ContinuousOn Phi (Set.Icc 0 T ×ˢ Set.univ) :=
      hw_cont.add (continuous_const.mul continuous_fst).continuousOn
    have hslab_compact : IsCompact (Set.Icc 0 T ×ˢ (Set.univ : Set M)) :=
      isCompact_Icc.prod isCompact_univ
    have hslab_nonempty : (Set.Icc 0 T ×ˢ (Set.univ : Set M)).Nonempty :=
      ⟨(tb, xb), htb, Set.mem_univ xb⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hPhi_cont
    rcases p0 with ⟨t0, x0⟩
    have ht0 : t0 ∈ Set.Icc 0 T := hp0.1
    have hPhi_bad : Phi (t0, x0) ≤ Phi (tb, xb) :=
      hp0min ⟨htb, Set.mem_univ xb⟩
    have hPhi_neg : Phi (t0, x0) < 0 := lt_of_le_of_lt hPhi_bad hbneg
    have ht0_ne : t0 ≠ 0 := by
      intro ht0zero
      have hnonneg : 0 ≤ Phi (t0, x0) := by
        simp [Phi, ht0zero, hw0 x0]
      exact not_lt_of_ge hnonneg hPhi_neg
    have ht0pos : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm ht0_ne)
    have hTpos : 0 < T := lt_of_lt_of_le ht0pos ht0.2
    have hx0int : x0 ∈ I.interior M := by
      rcases I.isInteriorPoint_or_isBoundaryPoint x0 with hx0 | hx0
      · exact hx0
      · have hw_nonneg := hw_boundary t0 ht0
          (⟨x0, hx0⟩ : BoundaryManifold I M)
        have heps_nonneg : 0 ≤ epsilon * t0 :=
          mul_nonneg hepsilon.le ht0.1
        dsimp [Phi] at hPhi_neg
        linarith
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht0
    have htime_min : IsMinOn (fun s => w s x0 + epsilon * s)
        (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min
        (show (s, x0) ∈ Set.Icc 0 T ×ˢ (Set.univ : Set M) from
          ⟨hs, Set.mem_univ x0⟩)
    have htime_diff : DifferentiableWithinAt Real
        (fun s => w s x0 + epsilon * s) (Set.Icc 0 T) t0 :=
      (hw_time t0 ht0 ht0pos x0 hx0int).add
        ((differentiableWithinAt_id' (s := Set.Icc 0 T) (x := t0)).const_mul epsilon)
    have hderiv_nonpos : derivWithin
        (fun s => w s x0 + epsilon * s) (Set.Icc 0 T) t0 ≤ 0 :=
      boundaryHopf_derivWithin_nonpos_at_Icc_min_of_pos
        htime_min.localize ht0 ht0pos htime_diff
    have hderiv_eq : derivWithin
        (fun s => w s x0 + epsilon * s) (Set.Icc 0 T) t0 =
        derivWithin (fun s => w s x0) (Set.Icc 0 T) t0 + epsilon :=
      boundaryHopf_derivWithin_add_eps_mul_time (M := M) huniq
        (hw_time t0 ht0 ht0pos x0 hx0int)
    have hw_deriv_le : derivWithin (fun s => w s x0)
        (Set.Icc 0 T) t0 ≤ -epsilon := by
      linarith
    have hwneg : w t0 x0 < 0 := by
      have heps_nonneg : 0 ≤ epsilon * t0 :=
        mul_nonneg hepsilon.le ht0.1
      dsimp [Phi] at hPhi_neg
      linarith
    have hspatial_min : IsLocalMin (w t0) x0 := by
      have hglobal : IsMinOn (w t0) Set.univ x0 := by
        intro y hy
        have hymin := hp0min
          (show (t0, y) ∈ Set.Icc 0 T ×ˢ (Set.univ : Set M) from ⟨ht0, hy⟩)
        dsimp [Phi] at hymin
        exact (add_le_add_iff_right (epsilon * t0)).mp hymin
      exact isLocalMinOn_univ_iff.mp hglobal.localize
    have hinterior_open : IsOpen (I.interior M) :=
      I.isOpen_interior (M := M) (n := ∞) (by simp)
    have hheat_nonneg : 0 ≤
        heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
        (I := I) G t0 (X t0) hspatial_min hx0int
        (hw_mdiff t0 ht0 ht0pos x0 hx0int)
        (by
          filter_upwards [hinterior_open.mem_nhds hx0int] with y hy
          exact hw_mdiff t0 ht0 ht0pos y hy)
        (hw_grad t0 ht0 ht0pos x0 hx0int)
    have hPneg : parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge
      (hnegative t0 ht0 ht0pos x0 hx0int hwneg) hPneg
  intro t ht x
  by_contra hnot
  have hwneg : w t x < 0 := lt_of_not_ge hnot
  by_cases htzero : t = 0
  · exact not_lt_of_ge (by simpa [htzero] using hw0 x) hwneg
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
    let epsilon : Real := -(w t x) / (2 * t)
    have hepsilon : 0 < epsilon :=
      div_pos (neg_pos.mpr hwneg) (mul_pos two_pos htpos)
    have hnonneg := hbarrier epsilon hepsilon t ht x
    have hepsilon_mul : epsilon * t = -(w t x) / 2 := by
      dsimp [epsilon]
      field_simp [htzero]
    rw [hepsilon_mul] at hnonneg
    linarith

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
    hmin.localize.fderivWithin_nonneg hdir
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

theorem scalar_hopf_boundary_point_of_barrier_with_boundary
    [CompleteSpace E] [CompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
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
    outwardNormalDerivative (M := M) (G.metric T) (u T) p < 0 := by
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
      (M := M) (G.metric T) hmin hu_mdiff hinward

end

end DifferentialGeometry.Analysis.Parabolic
