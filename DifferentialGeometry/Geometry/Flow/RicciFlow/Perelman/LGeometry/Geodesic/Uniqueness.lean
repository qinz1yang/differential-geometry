import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegularizedCurve_initialVector_eq_of_endpoint_eq_of_velocity_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z W : TangentSpace I x} {b : Real}
    (hZ : b ∈ lRegularizedDomain S T x Z) (hW : b ∈ lRegularizedDomain S T x W)
    (hpos : lRegularizedCurve S T x Z b = lRegularizedCurve S T x W b)
    (hvel : lVelocity (I := I) (lRegularizedCurve S T x Z) b =
      lVelocity (I := I) (lRegularizedCurve S T x W) b) :
    Z = W := by
  obtain ⟨JZ, hJZopen, hJZconn, h0JZ, hbJZ, hchosenZ⟩ :=
    lRegularizedChosen_spec S T x Z hZ
  obtain ⟨JW, hJWopen, hJWconn, h0JW, hbJW, hchosenW⟩ :=
    lRegularizedChosen_spec S T x W hW
  let alphaZ := lRegularizedChosen S T x Z hZ
  let alphaW := lRegularizedChosen S T x W hW
  have heqZ := lRegularizedCurve_eqOn S hS T hJZopen hJZconn h0JZ hchosenZ
  have heqW := lRegularizedCurve_eqOn S hS T hJWopen hJWconn h0JW hchosenW
  have hZgerm : Filter.EventuallyEq (nhds b)
      (lRegularizedCurve S T x Z) alphaZ := by
    filter_upwards [hJZopen.mem_nhds hbJZ] with s hs
    exact heqZ hs
  have hWgerm : Filter.EventuallyEq (nhds b)
      (lRegularizedCurve S T x W) alphaW := by
    filter_upwards [hJWopen.mem_nhds hbJW] with s hs
    exact heqW hs
  have hposChosen : alphaZ b = alphaW b :=
    hZgerm.eq_of_nhds.symm.trans (hpos.trans hWgerm.eq_of_nhds)
  have hvelChosen : lVelocity (I := I) alphaZ b =
      lVelocity (I := I) alphaW b := by
    unfold lVelocity
    rw [← hZgerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I),
      ← hWgerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
    exact hvel
  have hsolEq := lRegularizedSolution_eqOn S hS T hJZopen hJZconn hbJZ
    hJWopen hJWconn hbJW hchosenZ.2.2 hchosenW.2.2
    hposChosen hvelChosen
  have heq0 : Filter.EventuallyEq (nhds (0 : Real)) alphaZ alphaW := by
    filter_upwards [(hJZopen.inter hJWopen).mem_nhds ⟨h0JZ, h0JW⟩] with s hs
    exact hsolEq hs
  have hvel0 : lVelocity (I := I) alphaZ 0 =
      lVelocity (I := I) alphaW 0 := by
    unfold lVelocity
    exact congrArg (fun L ↦ L (1 : Real))
      (heq0.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I))
  have hZ2 : lVelocity (I := I) alphaZ 0 = (2 : Real) • Z :=
    hchosenZ.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 Z).symm
  have hW2 : lVelocity (I := I) alphaW 0 = (2 : Real) • W :=
    hchosenW.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 W).symm
  apply smul_right_injective (TangentSpace I x) (by norm_num : (2 : Real) ≠ 0)
  exact hZ2.symm.trans (hvel0.trans hW2)

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegularizedCurve_endpoint_velocity_ne_of_initialVector_ne_of_endpoint_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z W : TangentSpace I x} {b : Real}
    (hZ : b ∈ lRegularizedDomain S T x Z) (hW : b ∈ lRegularizedDomain S T x W)
    (hZW : Z ≠ W)
    (hpos : lRegularizedCurve S T x Z b = lRegularizedCurve S T x W b) :
    lVelocity (I := I) (lRegularizedCurve S T x Z) b ≠
      lVelocity (I := I) (lRegularizedCurve S T x W) b := by
  intro hvel
  exact hZW (lRegularizedCurve_initialVector_eq_of_endpoint_eq_of_velocity_eq
    S hS T x hZ hW hpos hvel)

end DifferentialGeometry.PDE.RicciFlow.Perelman
