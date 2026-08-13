import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Strong
import DifferentialGeometry.Geometry.Boundary.DefiningFunctionCurve
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem scalar_hopf_boundary_point_of_defining_function_on_compact_annulus
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * T ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (hu_zero : u T p = 0) :
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 := by
  let K : Set M := {x | r ≤ rho x ∧ rho x ≤ R}
  change IsCompact K at hK
  change p ∈ frontier K at hp
  have hpK : p ∈ K := by
    have hpcl : p ∈ closure K := frontier_subset_closure hp
    rw [hK.isClosed.closure_eq] at hpcl
    exact hpcl
  have hKne : K.Nonempty := ⟨p, hpK⟩
  have hgrad_ne : gradientFun (I := I) (G.metric T) rho p ≠ 0 := by
    intro hzero
    rw [hzero] at hgrad_boundary
    simp at hgrad_boundary
  obtain ⟨a, ha, gamma, hgamma0, hgamma, hgamma_mdiff,
      hgamma_velocity⟩ :=
    exists_levelSet_inward_curve_of_gradient_ne_zero (I := I)
      (G.metric T) rho (hrho.mdifferentiable (by simp) p)
      hrR hp_outer hgrad_ne
  exact scalar_hopf_boundary_point_of_defining_function (I := I)
    G hT X hK hKne rho hrho hr heta (by
      intro x hx
      exact hx) (frontier_levelSet_annulus_subset hrho.continuous)
      hkappa hinit halpha hdom hgrad_lower
      hheat_upper u hu_cont hu_nonneg hu_inner hu_time hu_mdiff hu_grad
      hu_super hp hp_outer hgrad_boundary gamma ha hgamma0 hgamma
      hgamma_mdiff hgamma_velocity hu_zero

theorem scalar_hopf_boundary_point_of_defining_function_on_compact_annulus_of_continuousOn
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hgrad_ne : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R},
        gradientFun (I := I) (G.metric t) rho x ≠ 0)
    (hgrad_cont : ContinuousOn (fun p : Real × M =>
      (G.metric p.1).inner p.2
        (gradientFun (I := I) (G.metric p.1) rho p.2)
        (gradientFun (I := I) (G.metric p.1) rho p.2))
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hheat_cont : ContinuousOn (fun p : Real × M =>
      heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hu_zero : u T p = 0) :
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 := by
  let K : Set M := {x | r ≤ rho x ∧ rho x ≤ R}
  let S : Set (Real × M) := Set.Icc 0 T ×ˢ K
  let q : Real × M → Real := fun z =>
    (G.metric z.1).inner z.2
      (gradientFun (I := I) (G.metric z.1) rho z.2)
      (gradientFun (I := I) (G.metric z.1) rho z.2)
  let ell : Real × M → Real := fun z =>
    |heatOperatorWithDrift (I := I) G z.1 (X z.1) rho z.2|
  have hpK : p ∈ K := by
    have hpcl : p ∈ closure K := frontier_subset_closure hp
    rw [hK.isClosed.closure_eq] at hpcl
    exact hpcl
  have hSne : S.Nonempty :=
    ⟨(0, p), ⟨⟨le_rfl, hT.le⟩, hpK⟩⟩
  have hScompact : IsCompact S := isCompact_Icc.prod hK
  have hq_cont : ContinuousOn q S := by
    simpa only [S, K, q] using hgrad_cont
  have hell_cont : ContinuousOn ell S := by
    simpa only [S, K, ell] using hheat_cont.abs
  obtain ⟨pm, hpm, hpmin⟩ := hScompact.exists_isMinOn hSne hq_cont
  obtain ⟨pB, _hpB, hpBmax⟩ := hScompact.exists_isMaxOn hSne hell_cont
  let m : Real := q pm
  let B : Real := ell pB
  have hm : 0 < m := by
    exact (G.metric pm.1).pos pm.2 _
      (hgrad_ne pm.1 hpm.1 pm.2 hpm.2)
  have hB : 0 ≤ B := by
    exact abs_nonneg _
  have hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior K,
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x) := by
    intro t ht _htpos x hx
    change q pm ≤ q (t, x)
    exact hpmin (show (t, x) ∈ S from ⟨ht, interior_subset hx⟩)
  have hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior K,
        heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B := by
    intro t ht _htpos x hx
    have habs : ell (t, x) ≤ ell pB :=
      hpBmax (show (t, x) ∈ S from ⟨ht, interior_subset hx⟩)
    change |heatOperatorWithDrift (I := I) G t (X t) rho x| ≤ B at habs
    exact (le_abs_self _).trans habs
  let kappa : Real := (R - r) / T ^ 2 + 1
  have hT_sq : 0 < T ^ 2 := sq_pos_of_pos hT
  have hgap : 0 < R - r := sub_pos.mpr hrR
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    linarith [div_pos hgap hT_sq]
  have hinit : R ≤ r + kappa * T ^ 2 := by
    have hratio : (R - r) / T ^ 2 < kappa := by
      dsimp only [kappa]
      linarith
    have hmul := (div_lt_iff₀ hT_sq).mp hratio
    linarith
  let alpha : Real := (2 * kappa * T + B) / m + 1
  have hnum : 0 ≤ 2 * kappa * T + B := by positivity
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    linarith [div_nonneg hnum hm.le]
  have hdom : 2 * kappa * T + B ≤ alpha * m := by
    apply le_of_lt ((div_lt_iff₀ hm).mp ?_)
    dsimp only [alpha]
    linarith
  have hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p) := by
    exact (G.metric T).pos p _
      (hgrad_ne T ⟨hT.le, le_rfl⟩ p hpK)
  exact scalar_hopf_boundary_point_of_defining_function_on_compact_annulus
    (I := I) G hT X rho hrho hr hrR heta hK hkappa hinit halpha hdom
      (by simpa only [K] using hgrad_lower)
      (by simpa only [K] using hheat_upper) u hu_cont hu_nonneg hu_inner
      hu_time hu_mdiff hu_grad hu_super hp hp_outer hgrad_boundary hu_zero

theorem scalar_hopf_boundary_point_of_defining_function_on_compact_annulus_of_metricFamilySmoothOn
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D (G.restrict D).metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    (hdrift : ContinuousOn (fun p : Real × M =>
      driftTerm (I := I) G p.1 (X p.1) rho p.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    {r R eta : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hgrad_ne : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R},
        gradientFun (I := I) (G.metric t) rho x ≠ 0)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hu_zero : u T p = 0) :
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 := by
  apply
    scalar_hopf_boundary_point_of_defining_function_on_compact_annulus_of_continuousOn
      (I := I) G hT X rho hrho hr hrR heta hK hgrad_ne
  · exact (G.gradient_norm_sq_continuousOn hG hslab hrho).mono
      (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
  · exact (G.heatOperatorWithDrift_continuousOn hG hslab
      (uniqueDiffOn_Icc hT) hconn X hrho hdrift).mono
      (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
  · exact hu_cont
  · exact hu_nonneg
  · exact hu_inner
  · exact hu_time
  · exact hu_mdiff
  · exact hu_grad
  · exact hu_super
  · exact hp
  · exact hp_outer
  · exact hu_zero

private theorem gradientFun_exp_mul
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) (L T : Real)
    (u : M → Real) (p : M)
    (hu : MDifferentiableAt I (modelWithCornersSelf Real Real) u p) :
    gradientFun (I := I) g (fun x => Real.exp (-L * T) * u x) p =
      Real.exp (-L * T) • gradientFun (I := I) g u p := by
  simpa only [Pi.smul_apply, smul_eq_mul] using
    gradientFun_const_smul (I := I) g (Real.exp (-L * T)) hu

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem exp_mul_mdiffAt
    [I.Boundaryless]
    (L t : Real) (u : M → Real) (x : M)
    (hu : MDifferentiableAt I (modelWithCornersSelf Real Real) u x) :
    MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y => Real.exp (-L * t) * u y) x := by
  exact (mdifferentiableAt_const (c := Real.exp (-L * t))).mul hu

private theorem exp_neg_mul_differentiableWithinAt
    (L T t : Real) :
    DifferentiableWithinAt Real (fun s => Real.exp (-L * s))
      (Set.Icc 0 T) t :=
  (((differentiableAt_const (-L)).mul differentiableAt_id).exp
    (x := t)).differentiableWithinAt

private theorem exp_neg_abs_mul_mul_le
    (L T eta t a : Real) (ht : t ∈ Set.Icc 0 T)
    (heta : 0 ≤ eta) (ha : eta ≤ a) :
    Real.exp (-|L| * T) * eta ≤ Real.exp (-L * t) * a := by
  have hLt : L * t ≤ |L| * T := by
    calc
      L * t ≤ |L| * t := mul_le_mul_of_nonneg_right (le_abs_self L) ht.1
      _ ≤ |L| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg L)
  have hscale : Real.exp (-|L| * T) ≤ Real.exp (-L * t) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-|L| * T) * eta ≤ Real.exp (-L * t) * eta :=
      mul_le_mul_of_nonneg_right hscale heta
    _ ≤ Real.exp (-L * t) * a :=
      mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le

private theorem gradientFun_exp_mul_mdiffAt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) (L t : Real)
    (u : M → Real) (x : M)
    (hu : ∀ y : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) u y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g u y) x) :
    MDiffAt (T% fun y : M => gradientFun (I := I) g
      (fun z => Real.exp (-L * t) * u z) y) x := by
  have heq :
      (T% fun y : M => gradientFun (I := I) g
        (fun z => Real.exp (-L * t) * u z) y) =
        (T% fun y : M => Real.exp (-L * t) •
          gradientFun (I := I) g u y) := by
    funext y
    apply congrArg (fun q =>
      (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
    exact gradientFun_exp_mul (I := I) g L t u y (hu y)
  rw [heq]
  exact (mdifferentiableAt_const (I := I) (c := Real.exp (-L * t))).smul_section
    hgrad

theorem scalar_hopf_boundary_point_with_potential_on_compact_annulus
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (V : Real → M → Real) (L : Real)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * T ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x - V t x * u t x)
    (hV_lower : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R}, L ≤ V t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (hu_zero : u T p = 0) :
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 := by
  let z : Real → M → Real := fun t x => Real.exp (-L * t) * u t x
  let eta' : Real := Real.exp (-|L| * T) * eta
  have heta' : 0 < eta' := mul_pos (Real.exp_pos _) heta
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}) := by
    have hscale : Continuous (fun p : Real × M => Real.exp (-L * p.1)) := by
      fun_prop
    simpa only [z] using hscale.continuousOn.mul hu_cont
  have hz_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ z t x := by
    intro t ht x hx
    exact mul_nonneg (Real.exp_pos _).le (hu_nonneg t ht x hx)
  have hz_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta' ≤ z t x := by
    intro t ht x hx hrho_x
    exact exp_neg_abs_mul_mul_le L T eta t (u t x) ht heta.le
      (hu_inner t ht x hx hrho_x)
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (exp_neg_mul_differentiableWithinAt L T t).mul
      (hu_time t ht htpos x)
  have hz_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (z t) x := by
    intro t ht htpos x
    simpa only [z] using exp_mul_mdiffAt (I := I) L t (u t) x
      (hu_mdiff t ht htpos x)
  have hz_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x
    simpa only [z] using gradientFun_exp_mul_mdiffAt (I := I) (G.metric t)
      L t (u t) x (hu_mdiff t ht htpos) (hu_grad t ht htpos x)
  have hz_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X z t x := by
    intro t ht htpos x hx
    simpa only [z] using parabolic_exp_rescale_nonneg_of_potential (I := I)
      G T hT L X V u t ht (hu_mdiff t ht htpos) x
      (hu_grad t ht htpos x) (hu_time t ht htpos x)
      (hu_nonneg t ht x (interior_subset hx)) (hV_lower t ht x hx)
      (hu_super t ht htpos x hx)
  have hz_zero : z T p = 0 := by
    simp [z, hu_zero]
  have hhopf :=
    scalar_hopf_boundary_point_of_defining_function_on_compact_annulus
      (I := I) G hT X rho hrho hr hrR heta' hK hkappa hinit halpha hdom
      hgrad_lower hheat_upper z hz_cont hz_nonneg hz_inner hz_time
      hz_mdiff hz_grad hz_super hp hp_outer hgrad_boundary hz_zero
  have hgradient :
      gradientFun (I := I) (G.metric T) (z T) p =
        Real.exp (-L * T) •
          gradientFun (I := I) (G.metric T) (u T) p := by
    simpa only [z] using gradientFun_exp_mul (I := I) (G.metric T) L T
      (u T) p (hu_mdiff T ⟨hT.le, le_rfl⟩ hT p)
  rw [hgradient, map_smul] at hhopf
  change Real.exp (-L * T) *
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 at hhopf
  rcases mul_neg_iff.mp hhopf with h | h
  · exact h.2
  · exact (not_lt_of_ge (Real.exp_pos _).le h.1).elim

theorem scalar_hopf_boundary_point_of_subsolution_on_compact_annulus
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * T ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hu_nonpos : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, u t x ≤ 0)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → u t x ≤ -eta)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_sub : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        parabolicOperatorWithDrift (I := I) G T X u t x ≤ 0)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (hu_zero : u T p = 0) :
    0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) := by
  let w : Real → M → Real := fun t x => -u t x
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}) := by
    simpa [w] using hu_cont.neg
  have hw_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ w t x := by
    intro t ht x hx
    exact neg_nonneg.mpr (hu_nonpos t ht x hx)
  have hw_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ w t x := by
    intro t ht x hx hrho_x
    dsimp [w]
    linarith [hu_inner t ht x hx hrho_x]
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    simpa [w] using (hu_time t ht htpos x).neg
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (w t) x := by
    intro t ht htpos x
    simpa [w] using (hu_mdiff t ht htpos x).neg
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M => -gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_neg (I := I) (G.metric t)
        (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_neg_section (hu_grad t ht htpos x)
  have hw_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hx
    have hneg := parabolic_neg (I := I) G T X u t x
      (hu_time t ht htpos x) (hu_mdiff t ht htpos) (hu_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hneg
    rw [hneg]
    exact neg_nonneg.mpr (hu_sub t ht htpos x hx)
  have hw_zero : w T p = 0 := by
    simp [w, hu_zero]
  have hhopf :=
    scalar_hopf_boundary_point_of_defining_function_on_compact_annulus
      (I := I) G hT X rho hrho hr hrR heta hK hkappa hinit halpha hdom
      hgrad_lower hheat_upper w hw_cont hw_nonneg hw_inner hw_time
      hw_mdiff hw_grad hw_super hp hp_outer hgrad_boundary hw_zero
  have hgradient :
      gradientFun (I := I) (G.metric T) (w T) p =
        -gradientFun (I := I) (G.metric T) (u T) p := by
    exact gradientFun_neg (I := I) (G.metric T)
      (hu_mdiff T ⟨hT.le, le_rfl⟩ hT p)
  rw [hgradient, map_neg] at hhopf
  change -((G.metric T).inner p
    (gradientFun (I := I) (G.metric T) (u T) p)
    (levelSetOutwardNormal (I := I) (G.metric T) rho p)) < 0 at hhopf
  linarith

theorem scalar_hopf_boundary_comparison_on_compact_annulus
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * T ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (u v : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (huv : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, u t x ≤ v t x)
    (huv_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → u t x + eta ≤ v t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (v t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (v t) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        parabolicOperatorWithDrift (I := I) G T X u t x ≤
          parabolicOperatorWithDrift (I := I) G T X v t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (huv_eq : u T p = v T p) :
    (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (v T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) <
      (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (u T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) := by
  let d : Real → M → Real := fun t x => u t x - v t x
  have hd_cont : ContinuousOn (fun p : Real × M => d p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}) := by
    simpa [d] using hu_cont.sub hv_cont
  have hd_nonpos : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, d t x ≤ 0 := by
    intro t ht x hx
    exact sub_nonpos.mpr (huv t ht x hx)
  have hd_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → d t x ≤ -eta := by
    intro t ht x hx hrho_x
    dsimp [d]
    linarith [huv_inner t ht x hx hrho_x]
  have hd_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => d s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    simpa [d] using (hu_time t ht htpos x).sub (hv_time t ht htpos x)
  have hd_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (d t) x := by
    intro t ht htpos x
    simpa [d] using (hu_mdiff t ht htpos x).sub (hv_mdiff t ht htpos x)
  have hd_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (d t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (d t) y) =
          (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (u t) y -
              gradientFun (I := I) (G.metric t) (v t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) (G.metric t)
        (hu_mdiff t ht htpos y) (hv_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
  have hd_sub : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        parabolicOperatorWithDrift (I := I) G T X d t x ≤ 0 := by
    intro t ht htpos x hx
    have hsub := parabolic_sub (I := I) G T X u v t x
      (hu_time t ht htpos x) (hv_time t ht htpos x)
      (hu_mdiff t ht htpos) (hv_mdiff t ht htpos)
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X d t x = _ at hsub
    rw [hsub]
    exact sub_nonpos.mpr (hoperator t ht htpos x hx)
  have hd_zero : d T p = 0 := by
    simp [d, huv_eq]
  have hhopf := scalar_hopf_boundary_point_of_subsolution_on_compact_annulus
    (I := I) G hT X rho hrho hr hrR heta hK hkappa hinit halpha hdom
    hgrad_lower hheat_upper d hd_cont hd_nonpos hd_inner hd_time hd_mdiff
    hd_grad hd_sub hp hp_outer hgrad_boundary hd_zero
  have hgradient :
      gradientFun (I := I) (G.metric T) (d T) p =
        gradientFun (I := I) (G.metric T) (u T) p -
          gradientFun (I := I) (G.metric T) (v T) p := by
    exact gradientFun_sub (I := I) (G.metric T)
      (hu_mdiff T ⟨hT.le, le_rfl⟩ hT p)
      (hv_mdiff T ⟨hT.le, le_rfl⟩ hT p)
  rw [hgradient, map_sub] at hhopf
  change 0 <
    (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (u T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) -
      (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (v T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) at hhopf
  linarith

end DifferentialGeometry.Analysis.Parabolic
