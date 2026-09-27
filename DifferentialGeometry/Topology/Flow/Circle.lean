import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Topology.Flow.PeriodicOrbit
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Flow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem exists_ne_of_isLocalDiffeomorph_orbit
    (φ : _root_.Flow ℝ M) (x : M)
    (hφ : IsLocalDiffeomorph 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => φ t x)) :
    ∃ t : ℝ, φ t x ≠ x := by
  by_contra h
  push Not at h
  have heq : (fun t : ℝ => φ t x) = fun _ => x := funext h
  let A : ℝ ≃L[ℝ] E := (hφ 0).mfderivToContinuousLinearEquiv (by simp)
  have hzero : (A : ℝ →L[ℝ] E) = 0 := by
    change mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => φ t x) 0 = 0
    rw [heq, mfderiv_const]
    rfl
  have h10 : A 1 = A 0 := by
    change (A : ℝ →L[ℝ] E) 1 = (A : ℝ →L[ℝ] E) 0
    rw [hzero]
    rfl
  exact one_ne_zero (A.injective h10)

theorem exists_addCircle_diffeomorph_of_isLocalDiffeomorph_orbits
    [T2Space M] [PreconnectedSpace M] [CompactSpace M]
    (φ : _root_.Flow ℝ M)
    (hφ : ∀ x, IsLocalDiffeomorph 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => φ t x)) (x : M) :
    ∃ (T : ℝ) (_ : 0 < T) (e : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), I⟯ M),
      ∀ t : ℝ, e (t : AddCircle (1 : ℝ)) = φ (T * t) x := by
  have hopen := fun y => (hφ y).isOpenMap
  obtain ⟨T, hT, hperT, hinjT, _⟩ := exists_minimal_pos_period φ
    (exists_ne_of_isLocalDiffeomorph_orbit φ x (hφ x))
    (exists_pos_period_of_isOpenMap φ hopen x)
  let D : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ T hT.ne').toContinuousLinearEquiv
  let γ : ℝ → M := fun t => φ (T * t) x
  have hγ : IsLocalDiffeomorph 𝓘(ℝ, ℝ) I ∞ γ :=
    fun t => (D.toDiffeomorph.isLocalDiffeomorph t).comp (K := I) (P := M) (hφ x (D t))
  have hper : Function.Periodic γ 1 := by
    intro t
    simpa only [γ, mul_add, mul_one] using hperT (T * t)
  have hinj : InjOn γ (Ico 0 1) := by
    intro s hs t ht he
    have hmul (r : ℝ) (hr : r ∈ Ico 0 1) : T * r ∈ Ico 0 T :=
      ⟨mul_nonneg hT.le hr.1, by nlinarith [hr.2]⟩
    exact mul_left_cancel₀ hT.ne' (hinjT (hmul s hs) (hmul t ht) he)
  have hsurj : Function.Surjective γ := by
    intro y
    have hy : y ∈ φ.orbit x := by rw [orbit_eq_univ_of_isOpenMap φ hopen x]; trivial
    obtain ⟨t, ht⟩ := φ.mem_orbit_iff.mp hy
    refine ⟨t / T, ?_⟩
    change φ (T * (t / T)) x = y
    rw [mul_div_cancel₀ t hT.ne', ht]
  let q : AddCircle (1 : ℝ) → M := hper.lift
  have hqinj : Function.Injective q := by
    intro a b hab
    apply (AddCircle.equivIco 1 0).injective
    apply Subtype.ext
    apply hinj
    · simpa using (AddCircle.equivIco 1 0 a).property
    · simpa using (AddCircle.equivIco 1 0 b).property
    · change q ((AddCircle.equivIco 1 0 a : ℝ) : AddCircle (1 : ℝ)) =
        q ((AddCircle.equivIco 1 0 b : ℝ) : AddCircle (1 : ℝ))
      simpa only [AddCircle.coe_equivIco] using hab
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨t, ht⟩ := hsurj y
    exact ⟨(t : AddCircle (1 : ℝ)), ht⟩
  let e : AddCircle (1 : ℝ) ≃ M := Equiv.ofBijective q ⟨hqinj, hqsurj⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ) I ∞ q :=
    AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
      QuotientAddGroup.mk_surjective hγ.contMDiff
  have heinv : ContMDiff I 𝓘(ℝ, ℝ) ∞ e.symm := by
    apply hγ.contMDiff_of_comp_of_surjective hsurj
    have hecomp : (e.symm ∘ γ) = fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
      funext t
      exact e.symm_apply_apply (t : AddCircle (1 : ℝ))
    rw [hecomp]
    exact AddCircle.contMDiff_coe
  exact ⟨T, hT, { toEquiv := e, contMDiff_toFun := hq, contMDiff_invFun := heinv },
    fun _ => rfl⟩

theorem exists_addCircle_diffeomorph_of_nonvanishing_vectorField
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [PreconnectedSpace M] [CompactSpace M] [Nonempty M]
    (hdim : Module.finrank ℝ E = 1)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hne : ∀ x, v x ≠ 0) :
    Nonempty (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), I⟯ M) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hc := DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
    v hv (isClosed_tsupport v).isCompact
  have hsmooth := DifferentialGeometry.Analysis.ODE.contMDiff_curveAt v hv hc
  let φ : _root_.Flow ℝ M :=
    { toFun := fun t x => DifferentialGeometry.Analysis.ODE.curveAt v hc x t
      cont' := hsmooth.continuous
      map_zero' := DifferentialGeometry.Analysis.ODE.curveAt_zero v hc
      map_add' := fun s t x => by
        simpa only [add_comm] using DifferentialGeometry.Analysis.ODE.curveAt_add
          v (hv.of_le (by norm_num)) hc x t s }
  have hφ : ∀ x, IsLocalDiffeomorph 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => φ t x) := by
    intro x
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      (fun t : ℝ => φ t x) (hsmooth.comp (contMDiff_id.prodMk contMDiff_const))
    · intro t
      change Function.Injective (mfderiv 𝓘(ℝ, ℝ) I
        (fun s => DifferentialGeometry.Analysis.ODE.curveAt v hc x s) t)
      rw [(DifferentialGeometry.Analysis.ODE.curveAt_integralCurve v hc x t).mfderiv]
      change Function.Injective (fun a : ℝ => a • v (φ t x))
      exact smul_left_injective ℝ (hne (φ t x))
    · simpa using hdim.symm
  obtain ⟨_, _, e, _⟩ := exists_addCircle_diffeomorph_of_isLocalDiffeomorph_orbits
    φ hφ (Classical.arbitrary M)
  exact ⟨e⟩

end DifferentialGeometry.Topology.Flow
