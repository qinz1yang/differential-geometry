import DifferentialGeometry.Geometry.Metric.LocalIsometryRigidity
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoOpen
import DifferentialGeometry.Geometry.Metric.Sphere.PuncturedCartan
import DifferentialGeometry.Geometry.Metric.Sphere.PuncturedOverlap
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricFiberData
import DifferentialGeometry.Geometry.Topology.CoveringSimple

set_option autoImplicit false

/-!
# Positive Killing--Hopf theorem

Two one-pole Cartan maps on the round sphere are aligned at one center,
identified on their connected overlap by local-isometry rigidity, and glued.
Compactness then upgrades the resulting local diffeomorphism to a covering;
a simply connected target makes that covering a global diffeomorphism.
-/

noncomputable section

open Bundle Filter Function Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)] [NeZero n]

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable
  [RiemannianBundle
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]
  [PseudoEMetricSpace (sphere (0 : A) 1)]
  [@CompleteSpace (sphere (0 : A) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : A) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : A) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]

variable {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
  [T2Space (TangentBundle J N)]

variable [RiemannianBundle (fun x : N => TangentSpace J x)]
  [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
  [ConnectedSpace N] [SimplyConnectedSpace N] [LocPathConnectedSpace N]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : N => TangentSpace J x)]

omit [FiniteDimensional ℝ A] [NeZero n]
  [RiemannianBundle
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]
  [PseudoEMetricSpace (sphere (0 : A) 1)]
  [@CompleteSpace (sphere (0 : A) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : A) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : A) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x)]
  [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N] [T2Space (TangentBundle J N)]
  [RiemannianBundle (fun x : N => TangentSpace J x)]
  [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
  [ConnectedSpace N] [SimplyConnectedSpace N] [LocPathConnectedSpace N]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : N => TangentSpace J x)] in
private theorem hlocAt_congr_open
    {f₁ f₂ : sphere (0 : A) 1 → N}
    {U : Set (sphere (0 : A) 1)} {x : sphere (0 : A) 1}
    (hU : IsOpen U) (hxU : x ∈ U)
    (hf : IsLocalDiffeomorphAt (𝓡 n) J ∞ f₁ x)
    (heq : Set.EqOn f₂ f₁ U) :
    IsLocalDiffeomorphAt (𝓡 n) J ∞ f₂ x := by
  obtain ⟨Φ, hxΦ, hfΦ⟩ := hf
  let e : OpenPartialHomeomorph (sphere (0 : A) 1) N :=
    Φ.toOpenPartialHomeomorph.restrOpen U hU
  let Ψ : PartialDiffeomorph (𝓡 n) J (sphere (0 : A) 1) N ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        have hsub : e.source ⊆ Φ.source := by
          intro z hz
          change z ∈ Φ.source ∩ U at hz
          exact hz.1
        simpa only [e] using Φ.contMDiffOn_toFun.mono hsub
      contMDiffOn_invFun := by
        have hsub : e.target ⊆ Φ.target := by
          intro z hz
          change z ∈ Φ.target ∩ Φ.symm ⁻¹' U at hz
          exact hz.1
        simpa only [e] using Φ.contMDiffOn_invFun.mono hsub }
  refine ⟨Ψ, ?_, ?_⟩
  · change x ∈ Φ.source ∩ U
    exact ⟨hxΦ, hxU⟩
  · intro z hz
    change z ∈ Φ.source ∩ U at hz
    change f₂ z = Φ z
    exact (heq hz.2).trans (hfΦ hz.1)

omit [SimplyConnectedSpace N] [LocPathConnectedSpace N] in
/-- Two Cartan maps whose second initial jet is taken from the first agree on
the connected overlap of their one-pole domains. -/
theorem punctCartan_match
    (hn : 1 < n)
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hR : ∀ (x : N) (X Y Z : TangentSpace J x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := J) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    (p q : sphere (0 : A) 1) (hpq : p ≠ q) (hqneg : q ≠ -p)
    (p' : N)
    (i : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (hi : ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner p' (i a) (i b) =
        (roundMetric (E := A) (n := n)).inner p a b) :
    ∃ j : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n),
      (∀ a b : EuclideanSpace ℝ (Fin n),
        g.inner (punctCartan g hEnorm p' i p q) (j a) (j b) =
          (roundMetric (E := A) (n := n)).inner q a b) ∧
      Set.EqOn
        (punctCartan g hEnorm p' i p)
        (punctCartan g hEnorm
          (punctCartan g hEnorm p' i p q) j q)
        {x | x ≠ -p ∧ x ≠ -q} := by
  classical
  let Fp : sphere (0 : A) 1 → N :=
    punctCartan g hEnorm p' i p
  have hFpP :
      IsLocalDiffeomorphOn (𝓡 n) J ∞ Fp {x | x ≠ -p} := by
    simpa only [Fp] using
      punctCartan_local hRound g hEnorm p p' i hi hR
  have hqLoc : IsLocalDiffeomorphAt (𝓡 n) J ∞ Fp q :=
    hFpP ⟨q, hqneg⟩
  let j : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    hqLoc.mfderivToContinuousLinearEquiv (by decide)
  let q' : N := Fp q
  have hj (a b : EuclideanSpace ℝ (Fin n)) :
      g.inner q' (j a) (j b) =
        (roundMetric (E := A) (n := n)).inner q a b := by
    simpa only [q', j, Fp,
      IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe] using
      punctCartan_inner hRound g hEnorm p p' i hi hR hqneg a b
  let Fq : sphere (0 : A) 1 → N :=
    punctCartan g hEnorm q' j q
  have hFqP :
      IsLocalDiffeomorphOn (𝓡 n) J ∞ Fq {x | x ≠ -q} := by
    simpa only [Fq] using
      punctCartan_local hRound g hEnorm q q' j hj hR
  let U : TopologicalSpace.Opens (sphere (0 : A) 1) :=
    ⟨{x | x ≠ -p ∧ x ≠ -q}, by
      change IsOpen
        (({-p} : Set (sphere (0 : A) 1))ᶜ ∩
          ({-q} : Set (sphere (0 : A) 1))ᶜ)
      exact isOpen_compl_singleton.inter isOpen_compl_singleton⟩
  have hUconn : IsPreconnected (U : Set (sphere (0 : A) 1)) := by
    simpa only [U] using
      punct2_preconn hn (-p) (-q) (neg_injective.ne hpq)
  letI : PreconnectedSpace U :=
    Subtype.preconnectedSpace hUconn
  letI : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen (𝓡 n) U.isOpen)
  have hFpU :
      IsLocalDiffeomorphOn (𝓡 n) J ∞ Fp U := by
    intro x
    exact hFpP ⟨x, x.property.1⟩
  have hFqU :
      IsLocalDiffeomorphOn (𝓡 n) J ∞ Fq U := by
    intro x
    exact hFqP ⟨x, x.property.2⟩
  have mfd_restrict
      (F : sphere (0 : A) 1 → N)
      (hF : IsLocalDiffeomorphOn (𝓡 n) J ∞ F U)
      (x : U) (v : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) J (fun y : U => F y) x v =
        mfderiv (𝓡 n) J F (x : sphere (0 : A) 1) v := by
    have hval :
        MDifferentiableAt (𝓡 n) (𝓡 n)
          (Subtype.val : U → sphere (0 : A) 1) x :=
      ((contMDiff_subtype_val (I := 𝓡 n) (U := U)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hFdiff :
        MDifferentiableAt (𝓡 n) J F (x : sphere (0 : A) 1) :=
      (hF x).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hc :=
      mfderiv_comp x hFdiff hval
    have hv := DFunLike.congr_fun hc v
    rw [mfderiv_subtype_val (I := 𝓡 n) U x] at hv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hv
  have hpres1 :
      ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
        ((roundMetric (E := A) (n := n)).restrictOpen
            (I := 𝓡 n) U).inner x v w =
          g.inner (Fp x)
            (mfderiv (𝓡 n) J (fun y : U => Fp y) x v)
            (mfderiv (𝓡 n) J (fun y : U => Fp y) x w) := by
    intro x v w
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      mfd_restrict Fp hFpU x v, mfd_restrict Fp hFpU x w]
    exact
      (punctCartan_inner hRound g hEnorm p p' i hi hR
        x.property.1 v w).symm
  have hpres2 :
      ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
        ((roundMetric (E := A) (n := n)).restrictOpen
            (I := 𝓡 n) U).inner x v w =
          g.inner (Fq x)
            (mfderiv (𝓡 n) J (fun y : U => Fq y) x v)
            (mfderiv (𝓡 n) J (fun y : U => Fq y) x w) := by
    intro x v w
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      mfd_restrict Fq hFqU x v, mfd_restrict Fq hFqU x w]
    exact
      (punctCartan_inner hRound g hEnorm q q' j hj hR
        x.property.2 v w).symm
  let x₀ : U :=
    ⟨q, hqneg, ne_neg_of_mem_unit_sphere ℝ q⟩
  have hxval :
      (fun x : U => Fp x) x₀ = (fun x : U => Fq x) x₀ := by
    change Fp q = Fq q
    simp only [Fq, q', punctCartan_self]
  have hxder :
      mfderiv (𝓡 n) J (fun x : U => Fp x) x₀ =
        mfderiv (𝓡 n) J (fun x : U => Fq x) x₀ := by
    ext v
    have h1 := DFunLike.congr_fun
      (hqLoc.mfderivToContinuousLinearEquiv_coe (by decide)) v
    have h2 := DFunLike.congr_fun
      (punctCartan_mfd hRound g hEnorm q' j q) v
    have h1' : mfderiv (𝓡 n) J Fp q v = j v := by
      simpa only [j] using h1.symm
    have h2' : j v = mfderiv (𝓡 n) J Fq q v := by
      simpa only [Fq] using h2.symm
    have hFpRest :
        mfderiv (𝓡 n) J (fun x : U => Fp x) x₀ v =
          mfderiv (𝓡 n) J Fp q v := by
      simpa only [x₀] using mfd_restrict Fp hFpU x₀ v
    have hFqRest :
        mfderiv (𝓡 n) J (fun x : U => Fq x) x₀ v =
          mfderiv (𝓡 n) J Fq q v := by
      simpa only [x₀] using mfd_restrict Fq hFqU x₀ v
    exact hFpRest.trans ((h1'.trans h2').trans hFqRest.symm)
  have heq :
      (fun x : U => Fp x) = (fun x : U => Fq x) :=
    Riemannian.localIso_rigid
      ((roundMetric (E := A) (n := n)).restrictOpen
        (I := 𝓡 n) U)
      g
      (hloc_restrict_open U hFpU)
      (hloc_restrict_open U hFqU)
      hpres1 hpres2 x₀ hxval hxder
  refine ⟨j, ?_, ?_⟩
  · simpa only [q', Fp] using hj
  · intro x hx
    have hx' := congrFun heq (⟨x, hx⟩ : U)
    simpa only [Fp, Fq, q'] using hx'

/-- A complete simply connected curvature-one manifold is globally isometric
to the round sphere, in a form retaining the differential isometry needed by
the later deck-action construction. -/
theorem sphere_diffeo_one
    (hn : 1 < n)
    (hRound : ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)))
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (w : TangentSpace J x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hR : ∀ (x : N) (X Y Z : TangentSpace J x),
      (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := J) g) x)
        X Y Z =
          g.inner x Y Z • X - g.inner x X Z • Y)
    (p q : sphere (0 : A) 1) (hpq : p ≠ q) (hqneg : q ≠ -p)
    (p' : N) :
    ∃ d : Diffeomorph (𝓡 n) J (sphere (0 : A) 1) N ∞,
      ∀ (x : sphere (0 : A) 1)
        (Y Z : TangentSpace (𝓡 n) x),
        g.inner (d x)
            (mfderiv (𝓡 n) J
              (d : sphere (0 : A) 1 → N) x Y)
            (mfderiv (𝓡 n) J
              (d : sphere (0 : A) 1 → N) x Z) =
          (roundMetric (E := A) (n := n)).inner x Y Z := by
  classical
  let gS : SmoothRiemannianMetric (𝓡 n) (sphere (0 : A) 1) :=
    roundMetric (E := A) (n := n)
  let DS := Tensor0SBundle.tangentMetricData (I := 𝓡 n) gS p
  let DT := Tensor0SBundle.tangentMetricData (I := J) g p'
  obtain ⟨i, hiData⟩ :=
    Tensor0SBundle.MetricFiberData.exists_metric_cle
      DS.metric DT.metric (by rfl)
  have hi (a b : EuclideanSpace ℝ (Fin n)) :
      g.inner p' (i a) (i b) =
        (roundMetric (E := A) (n := n)).inner p a b := by
    simpa only [DS, DT, gS,
      Tensor0SBundle.TangentMetricData.inner_eq] using hiData a b
  obtain ⟨j, hj, hmatch⟩ :=
    punctCartan_match hn hRound g hEnorm hR
      p q hpq hqneg p' i hi
  let Fp : sphere (0 : A) 1 → N :=
    punctCartan g hEnorm p' i p
  let q' : N := Fp q
  let Fq : sphere (0 : A) 1 → N :=
    punctCartan g hEnorm q' j q
  have hj' (a b : EuclideanSpace ℝ (Fin n)) :
      g.inner q' (j a) (j b) =
        (roundMetric (E := A) (n := n)).inner q a b := by
    simpa only [q', Fp] using hj a b
  let P : Set (sphere (0 : A) 1) := {x | x ≠ -p}
  let Q : Set (sphere (0 : A) 1) := {x | x ≠ -q}
  have hPopen : IsOpen P := by
    change IsOpen (({-p} : Set (sphere (0 : A) 1))ᶜ)
    exact isOpen_compl_singleton
  have hQopen : IsOpen Q := by
    change IsOpen (({-q} : Set (sphere (0 : A) 1))ᶜ)
    exact isOpen_compl_singleton
  have hcover : P ∪ Q = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxP : x = -p
    · right
      change x ≠ -q
      intro hxQ
      apply hpq
      exact neg_injective (hxP.symm.trans hxQ)
    · exact Or.inl hxP
  have hFpLocal :
      IsLocalDiffeomorphOn (𝓡 n) J ∞ Fp P := by
    simpa only [Fp, P] using
      punctCartan_local hRound g hEnorm p p' i hi hR
  have hFqLocal :
      IsLocalDiffeomorphOn (𝓡 n) J ∞ Fq Q := by
    simpa only [Fq, Q] using
      punctCartan_local hRound g hEnorm q q' j hj' hR
  have hmatch' : Set.EqOn Fp Fq (P ∩ Q) := by
    intro x hx
    simpa only [Fp, Fq, q', P, Q] using hmatch hx
  let F : sphere (0 : A) 1 → N :=
    P.piecewise Fp Fq
  have hFP : Set.EqOn F Fp P := by
    intro x hx
    change P.piecewise Fp Fq x = Fp x
    exact Set.piecewise_eq_of_mem P Fp Fq hx
  have hFQ : Set.EqOn F Fq Q := by
    intro x hxQ
    by_cases hxP : x ∈ P
    · have hxEq := hmatch' ⟨hxP, hxQ⟩
      change P.piecewise Fp Fq x = Fq x
      rw [Set.piecewise_eq_of_mem P Fp Fq hxP]
      exact hxEq
    · change P.piecewise Fp Fq x = Fq x
      exact Set.piecewise_eq_of_notMem P Fp Fq hxP
  have hFlocal : IsLocalDiffeomorph (𝓡 n) J ∞ F := by
    rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ, ← hcover]
    rintro ⟨x, hxP | hxQ⟩
    · exact hlocAt_congr_open hPopen hxP
        (hFpLocal ⟨x, hxP⟩) hFP
    · exact hlocAt_congr_open hQopen hxQ
        (hFqLocal ⟨x, hxQ⟩) hFQ
  have hFinner :
      ∀ (x : sphere (0 : A) 1)
        (Y Z : TangentSpace (𝓡 n) x),
        g.inner (F x)
            (mfderiv (𝓡 n) J F x Y)
            (mfderiv (𝓡 n) J F x Z) =
          (roundMetric (E := A) (n := n)).inner x Y Z := by
    intro x Y Z
    have hx : x ∈ P ∪ Q := by
      rw [hcover]
      exact Set.mem_univ x
    rcases hx with hxP | hxQ
    · have heq : F =ᶠ[𝓝 x] Fp :=
        Filter.eventuallyEq_of_mem (hPopen.mem_nhds hxP) hFP
      rw [heq.eq_of_nhds, heq.mfderiv_eq]
      simpa only [Fp] using
        punctCartan_inner hRound g hEnorm p p' i hi hR hxP Y Z
    · have heq : F =ᶠ[𝓝 x] Fq :=
        Filter.eventuallyEq_of_mem (hQopen.mem_nhds hxQ) hFQ
      rw [heq.eq_of_nhds, heq.mfderiv_eq]
      simpa only [Fq] using
        punctCartan_inner hRound g hEnorm q q' j hj' hR hxQ Y Z
  have hfr : 1 < Module.finrank ℝ A := by
    rw [show Module.finrank ℝ A = n + 1 from Fact.out]
    omega
  letI : PreconnectedSpace (sphere (0 : A) 1) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank hfr) (0 : A) 1)
  letI : Nonempty (sphere (0 : A) 1) := ⟨p⟩
  have hcov : IsCoveringMap F :=
    hFlocal.isLocalHomeomorph.covering_compact
  let d : Diffeomorph (𝓡 n) J (sphere (0 : A) 1) N ∞ :=
    hcov.diffeomorph_sc hFlocal
  refine ⟨d, ?_⟩
  intro x Y Z
  have hd : (d : sphere (0 : A) 1 → N) = F :=
    hcov.coe_diffeomorph_sc hFlocal
  rw [hd]
  exact hFinner x Y Z

end Geometry
end DifferentialGeometry
