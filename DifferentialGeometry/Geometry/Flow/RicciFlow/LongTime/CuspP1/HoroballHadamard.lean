import DifferentialGeometry.Geometry.Thurston.HyperbolicPrime

set_option autoImplicit false
noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Hadamard: no null-homotopic geodesic loops** (frozen CP1-F3, step 1).  On a complete connected
manifold with `⟪R(v,Y)Y,v⟫ ≤ 0`, a geodesic `c` on `(-a,a)`, continuous on `[-a,a]`, with
`c a = c (-a)` and whose reparametrised loop `P : [0,1] → M`, `P s = c(-a+2as)`, is null-homotopic
rel endpoints, is constant on `[-a,a]`. -/
theorem geodesic_loop_const_of_nullhomotopic_CPF3 [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ (x : M) (v Y : TangentSpace I x),
      g.inner x (riemannOp (LeviCivita (I := I) g) x v Y Y) v ≤ 0)
    {a : ℝ} (ha : 0 < a) {c : ℝ → M}
    (hgeo : Geodesic.IsGeodesicOn (I := I) g c (Ioo (-a) a))
    (hcont : ContinuousOn c (Icc (-a) a)) 
    (P : C(unitInterval, M)) (hP : ∀ s : unitInterval, P s = c (-a + 2 * a * s))
    (hnull : P.HomotopicRel (ContinuousMap.const unitInterval (c (-a))) {0, 1}) :
    ∀ τ ∈ Icc (-a) a, c τ = c 0 := by
  set q : M := c 0 with hq
  have h0mem : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hsub : Ioo (-a) a ⊆ Icc (-a) a := Ioo_subset_Icc_self
  let v : TangentSpace I q := mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ)
  set Γ₂ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q v with hΓ₂
  have hEq : EqOn c Γ₂ (Ioo (-a) a) := by
    apply geo_eqOn_of_initial (I := I) g isOpen_Ioo isPreconnected_Ioo h0mem hgeo
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v).isGeodesicOn _)
      (hcont.mono hsub) (intrinsicGeodesic_continuous (I := I) g hEnorm q v).continuousOn
    · simp [hq]
    · exact (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v).symm
  have hEqI : EqOn c Γ₂ (Icc (-a) a) := by
    refine hEq.of_subset_closure hcont
      (intrinsicGeodesic_continuous (I := I) g hEnorm q v).continuousOn hsub ?_
    rw [closure_Ioo (by linarith)]
  -- the straight lift
  let z : E := (normalFrame (I := I) g q).symm v
  have hcov : IsCoveringMap (framedExpMap (I := I) g q) :=
    GC.Geometry.framedExpMap_isCoveringMap_of_nonpos g hEnorm q hR
  have hlift : ∀ r : ℝ, framedExpMap (I := I) g q (r • z) = Γ₂ r := by
    intro r
    rw [framedExpMap_apply, map_smul]
    have : normalFrame (I := I) g q z = v := (normalFrame (I := I) g q).apply_symm_apply v
    rw [this, expMap_eq_expMapIntrinsic g hEnorm q]
    simp only [expMapIntrinsic]
    rw [intrinsicGeodesic_smul (I := I) g hEnorm q v r]
  let Lf : C(unitInterval, E) :=
    ⟨fun s => (-a + 2 * a * (s : ℝ)) • z, by fun_prop⟩
  have hP0 : P 0 = framedExpMap (I := I) g q ((-a) • z) := by
    rw [hP, hlift]
    simp only [Set.Icc.coe_zero, mul_zero, add_zero]
    exact hEqI ⟨le_rfl, by linarith⟩
  have hLf : Lf = hcov.liftPath P ((-a) • z) hP0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext s
      simp only [Function.comp_apply, ContinuousMap.coe_mk, Lf]
      rw [hlift, hP, hEqI ⟨by nlinarith [s.2.1, s.2.2], by nlinarith [s.2.1, s.2.2]⟩]
    · simp [Lf]
  have hP1 : (ContinuousMap.const unitInterval (c (-a))) 0 = framedExpMap (I := I) g q ((-a) • z) := by
    rw [← hP0, hP]; simp
  have hend := hcov.liftPath_apply_one_eq_of_homotopicRel hnull ((-a) • z) hP0 hP1
  rw [← hLf, hcov.liftPath_const (x := c (-a)) (by rw [← hP1]; rfl)] at hend
  have hz : z = 0 := by
    have h1 : (-a + 2 * a) • z = (-a) • z := by simpa [Lf] using hend
    have h2 : (2 * a) • z = 0 := by
      have : (-a + 2 * a) • z - (-a) • z = 0 := sub_eq_zero.mpr h1
      rwa [← sub_smul, show -a + 2 * a - -a = 2 * a by ring] at this
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by positivity)
    · exact h
  have hv : v = 0 := by
    have := congrArg (normalFrame (I := I) g q) hz
    simpa [z] using this
  intro τ hτ
  rw [hEqI hτ]
  have hconst : ∀ t, Γ₂ t = q := by
    intro t
    have h := intrinsicGeodesic_smul (I := I) g hEnorm q v t
    rw [hv, smul_zero] at h
    have h0 := intrinsicGeodesic_smul (I := I) g hEnorm q v 0
    rw [hv, smul_zero] at h0
    have : Γ₂ t = Γ₂ 0 := by
      show intrinsicGeodesic (I := I) g hEnorm q v t = intrinsicGeodesic (I := I) g hEnorm q v 0
      rw [hv, ← h, ← h0]
    rw [this]; simp [hΓ₂]
  rw [hconst]

end GC.LongTime.CuspP1
