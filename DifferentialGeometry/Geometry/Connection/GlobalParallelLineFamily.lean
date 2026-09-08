import DifferentialGeometry.Geometry.Connection.GlobalParallelLineSplitting
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Euclidean

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
variable [IsManifold J ∞ N]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

private theorem inner_product_product_formula_of_parallel_section_of_metric_dual_eq
    (g₀ g : SmoothRiemannianMetric I M)
    (h₀ : SmoothRiemannianMetric J N)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (F : N × ℝ → M) (hF : ContMDiff (J.prod 𝓘(ℝ, ℝ)) I ∞ F)
    (hflow : ∀ y t, F (y, t) =
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (F (y, 0)) t)
    (hvertical : ∀ y t r,
      mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (0, r) = r • X (F (y, t)))
    (hbase : ∀ y t (u v : TangentSpace J y) (r q : ℝ),
      g₀.inner (F (y, t))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (u, r))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (v, q)) = h₀.inner y u v + r * q)
    (hdual : ∀ x, ∀ v : TangentSpace I x,
      g.inner x (X x) v = g₀.inner x (X x) v)
    (hparallel : ∀ x, ∀ v : TangentSpace I x,
      (LeviCivita (I := I) g) X x v = 0)
    (y : N) (t : ℝ) (u v : TangentSpace J y) (r q : ℝ) :
    g.inner (F (y, t))
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (u, r))
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (v, q)) =
        g.inner (F (y, 0))
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, 0) (u, 0))
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, 0) (v, 0)) + r * q := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Phi : ℝ → M → M := fun a x =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x a
  let Ft : ℝ → N → M := fun a z => F (z, a)
  have hFt (a : ℝ) : ContMDiff J I ∞ (Ft a) :=
    hF.comp (contMDiff_id.prodMk contMDiff_const)
  have hPhi (a : ℝ) : ContMDiff I I ∞ (Phi a) :=
    (DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_complete
      X X.contMDiff hcomplete).comp (contMDiff_const.prodMk contMDiff_id)
  have hFtDerivative (a : ℝ) (w : TangentSpace J y) :
      mfderiv J I (Ft a) y w =
        mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, a) (w, 0) := by
    have hc := mfderiv_comp (I := J) (I' := J.prod 𝓘(ℝ, ℝ)) (I'' := I)
      (f := fun z : N => (z, a)) (g := F) y
      ((hF (y, a)).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    change ((mfderiv J I (F ∘ fun z : N => (z, a)) y) w) = _
    have hprod := mfderiv_prodMk (I := J) (I' := J) (I'' := 𝓘(ℝ, ℝ))
      (f := fun z : N => z) (g := fun _ : N => a) (x := y)
      mdifferentiableAt_id mdifferentiableAt_const
    have hprodApply :
        mfderiv J (J.prod 𝓘(ℝ, ℝ)) (fun z : N => (z, a)) y w =
          (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, a) from (w, 0)) := by
      rw [hprod]
      change ((mfderiv J J id y) w,
        (mfderiv J 𝓘(ℝ, ℝ) (fun _ : N => a) y) w) = (w, 0)
      rw [mfderiv_id, mfderiv_const]
      rfl
    rw [hc]
    change (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, a))
      ((mfderiv J (J.prod 𝓘(ℝ, ℝ)) (fun z : N => (z, a)) y) w) = _
    rw [hprodApply]
  have hfun : Ft t = Phi t ∘ Ft 0 := by
    funext z
    exact hflow z t
  have hhorizontal :
      g.inner (F (y, t))
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (u, 0))
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (v, 0)) =
        g.inner (F (y, 0))
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, 0) (u, 0))
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, 0) (v, 0)) := by
    rw [← hFtDerivative t u, ← hFtDerivative t v,
      ← hFtDerivative 0 u, ← hFtDerivative 0 v]
    change g.inner (Ft t y) (mfderiv J I (Ft t) y u) (mfderiv J I (Ft t) y v) = _
    rw [hfun]
    have hc := mfderiv_comp (I := J) (I' := I) (I'' := I)
      (f := Ft 0) (g := Phi t) y
      ((hPhi t (Ft 0 y)).mdifferentiableAt (by simp))
      ((hFt 0 y).mdifferentiableAt (by simp))
    rw [hc]
    exact globalIntegralCurve_inner_eq_of_parallel_section g X hcomplete hparallel
      t (Ft 0 y) (mfderiv J I (Ft 0) y u) (mfderiv J I (Ft 0) y v)
  let D : TangentSpace J y × ℝ →L[ℝ] TangentSpace I (F (y, t)) :=
    mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t)
  have hvertical' (a : ℝ) : D (0, a) = a • X (F (y, t)) := hvertical y t a
  have hbase' (w z : TangentSpace J y) (a b : ℝ) :
      g₀.inner (F (y, t)) (D (w, a)) (D (z, b)) = h₀.inner y w z + a * b :=
    hbase y t w z a b
  have horth (w : TangentSpace J y) :
      g.inner (F (y, t)) (X (F (y, t)))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (w, 0)) = 0 := by
    rw [hdual]
    have hb := hbase' 0 w 1 0
    rw [hvertical', one_smul] at hb
    change g₀.inner (F (y, t)) (X (F (y, t))) (D (w, 0)) = 0
    simpa using hb
  have horth' (w : TangentSpace J y) :
      g.inner (F (y, t))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (w, 0)) (X (F (y, t))) = 0 := by
    rw [g.symm]
    exact horth w
  have hunit : g.inner (F (y, t)) (X (F (y, t))) (X (F (y, t))) = 1 := by
    rw [hdual]
    have hb := hbase' 0 0 1 1
    rw [hvertical', one_smul] at hb
    simpa using hb
  have hsplit (w : TangentSpace J y) (a : ℝ) :
      mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (w, a) =
        mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) (w, 0) + a • X (F (y, t)) := by
    change D (w, a) = D (w, 0) + a • X (F (y, t))
    rw [show (w, a) = (w, (0 : ℝ)) + (0, a) by simp, map_add, hvertical']
  rw [hsplit u r, hsplit v q]
  simp only [map_add, add_apply, map_smul,
    smul_apply, smul_eq_mul, horth, horth', hunit, hhorizontal]
  ring

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Connection

theorem exists_global_product_metric_family_from_common_parallel_unit_section
    {m : ℕ}
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel (m + 1)) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [SimplyConnectedSpace M]
    {A : Type*} (g : A → SmoothRiemannianMetric I M) (a₀ : A)
    (hg : RiemannianMetricComplete (I := I) (g a₀))
    (X : Cₛ^∞⟮I; DifferentialGeometry.Topology.Morse.MorseModel (m + 1),
      TangentSpace I⟯)
    (hunit : ∀ x, (g a₀).inner x (X x) (X x) = 1)
    (hparallel : ∀ a x, ∀ v : TangentSpace I x,
      (LeviCivita (I := I) (g a)) X x v = 0)
    (hdual : ∀ a x, ∀ v : TangentSpace I x,
      (g a).inner x (X x) v = (g a₀).inner x (X x) v) :
    ∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel m) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : A → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m) N)
              (F : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ a, RiemannianMetricComplete (I := I) (g a) →
                RiemannianMetricComplete
                  (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) (h a)) ∧
              (∀ a, Diffeomorph.pullbackMetricCross (g a) F =
                (h a).prod (euclideanMetric (E := ℝ))) ∧
              (∀ a (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m) y),
                (h a).inner y u v = (g a).inner (F (y, 0))
                  (mfderiv
                    ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                      𝓘(ℝ, ℝ)) I F (y, 0) (u, 0))
                  (mfderiv
                    ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                      𝓘(ℝ, ℝ)) I F (y, 0) (v, 0))) ∧
              ∀ (y : N) (t r : ℝ),
                mfderiv
                  ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                    𝓘(ℝ, ℝ)) I F (y, t) (0, r) = r • X (F (y, t)) := by
  obtain ⟨f, hf, hdf, hreg, hcs, hmanifold, hσ, h₀, -, F,
      hF, hvertical, hconnected, hsimplyConnected, hbase⟩ :=
    exists_global_product_diffeomorph_with_potential_from_parallel_unit_section
      (g a₀) hg X hunit (hparallel a₀)
  let _ := hcs
  let _ := hmanifold
  let _ := hσ
  let N := DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0
  let J := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)
  let hcomplete := exists_globalIntegralCurve_of_unit_section (g a₀) hg X hunit
  have hflow (y : N) (t : ℝ) :
      F (y, t) = DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (F (y, 0)) t := by
    rw [hF y t, hF y 0, DifferentialGeometry.Analysis.ODE.curveAt_zero]
  let h : A → SmoothRiemannianMetric J N :=
    fun a => (Diffeomorph.pullbackMetricCross (g a) F).sliceFst 0
  refine ⟨N, inferInstance, hcs, hmanifold, inferInstance, hσ, h, F,
    hconnected, hsimplyConnected, ?_, ?_, ?_, hvertical⟩
  · intro a ha
    exact RiemannianMetricComplete.sliceFst
      (Diffeomorph.pullbackMetricCross (g a) F) 0
      (RiemannianMetricComplete.pullbackCross (g a) F ha)
  · intro a
    apply SmoothRiemannianMetric.ext_inner
    intro z u v
    rcases z with ⟨y, t⟩
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner,
      mfderiv_fst, mfderiv_snd]
    change (g a).inner (F (y, t))
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) u)
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, t) v) =
        (h a).inner y u.1 v.1 + inner ℝ (u.2 : ℝ) (v.2 : ℝ)
    have hs : (h a).inner y u.1 v.1 = (g a).inner (F (y, 0))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, 0) (u.1, 0))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I F (y, 0) (v.1, 0)) :=
      (SmoothRiemannianMetric.sliceFst_inner
        (Diffeomorph.pullbackMetricCross (g a) F) 0 y u.1 v.1).trans
        (Diffeomorph.pullbackMetricCross_inner (g a) F (y, 0) (u.1, 0) (v.1, 0))
    rw [hs]
    have hp := inner_product_product_formula_of_parallel_section_of_metric_dual_eq
      (g a₀) (g a) h₀ X hcomplete F F.contMDiff hflow hvertical hbase
      (hdual a) (hparallel a) y t u.1 v.1 u.2 v.2
    convert hp using 1
    · congr 2
    · simp only [RCLike.inner_apply, conj_trivial, mul_comm]
      rfl
  · intro a y u v
    exact (SmoothRiemannianMetric.sliceFst_inner
      (Diffeomorph.pullbackMetricCross (g a) F) 0 y u v).trans
      (Diffeomorph.pullbackMetricCross_inner (g a) F (y, 0) (u, 0) (v, 0))

end DifferentialGeometry.Geometry.Connection
