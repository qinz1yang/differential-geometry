import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue
import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs

open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

universe u v


private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_orientation_adjusting_linearEquiv (q : Orientation ℝ E3 (Fin 3)) :
    ∃ A : E3 ≃ₗ[ℝ] E3,
      Orientation.map (Fin 3) A ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) = q := by
  classical
  set b : Module.Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis with hb
  refine ⟨b.equivFun.trans ((b.adjustToOrientation q).equivFun).symm, ?_⟩
  rw [← Module.Basis.orientation_map]
  have h1 : b.map (b.equivFun.trans ((b.adjustToOrientation q).equivFun).symm) = b.adjustToOrientation q := by
    rw [show b.map (b.equivFun.trans ((b.adjustToOrientation q).equivFun).symm) =
      (b.adjustToOrientation q) from by
        ext i
        rw [Module.Basis.map_apply, LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]
        have hsingle : b.equivFun (b i) = Pi.single i 1 := by
          funext j
          rw [Module.Basis.equivFun_self]
          by_cases h : i = j <;> simp [h]
        rw [hsingle]
        simp]
  rw [h1]
  exact Module.Basis.orientation_adjustToOrientation b q

theorem mem_baseSet_chartAt {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (p y : M) (hy : y ∈ (chartAt E3 p).source) :
    y ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) p).baseSet := by
  rwa [TangentBundle.trivializationAt_baseSet]

theorem tangentChartEquiv_congr {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (p y : M)
    (h₁ h₂ : y ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) p).baseSet) :
    DifferentialGeometry.tangentChartEquiv (𝓡 3) M p y h₁
      = DifferentialGeometry.tangentChartEquiv (𝓡 3) M p y h₂ := by
  rw [Subsingleton.elim h₁ h₂]

theorem tangentChartEquiv_eq_continuousLinearMapAt {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (p y : M)
    (hy : y ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) p).baseSet) :
    ((DifferentialGeometry.tangentChartEquiv (𝓡 3) M p y hy : TangentSpace (𝓡 3) y ≃ₗ[ℝ] E3) :
        TangentSpace (𝓡 3) y →ₗ[ℝ] E3)
      = ((Bundle.Trivialization.continuousLinearMapAt ℝ
          (trivializationAt E3 (TangentSpace (𝓡 3)) p) y) : TangentSpace (𝓡 3) y →ₗ[ℝ] E3) := by
  refine LinearMap.ext fun v => ?_
  change (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E3 (TangentSpace (𝓡 3)) p) y hy) v
      = (Bundle.Trivialization.continuousLinearMapAt ℝ
          (trivializationAt E3 (TangentSpace (𝓡 3)) p) y) v
  rw [Bundle.Trivialization.linearEquivAt_apply]
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt E3 (TangentSpace (𝓡 3)) p) hy v).symm

theorem fromTangentSpace_toContinuousLinearMap (v : E3) :
    (NormedSpace.fromTangentSpace v).toContinuousLinearMap = ContinuousLinearMap.id ℝ E3 := by
  ext w
  rfl

theorem fromTangentSpace_symm_toContinuousLinearMap (v : E3) :
    (NormedSpace.fromTangentSpace v).symm.toContinuousLinearMap
      = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E3) v) := by
  ext w
  rfl

theorem isLocallyConstant_chartOrientation {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (o : DifferentialGeometry.ManifoldOrientation (𝓡 3) M 3) (p : M) :
    IsLocallyConstant fun y : ↥((chartAt E3 p).source) =>
      Orientation.map (Fin 3)
        (DifferentialGeometry.tangentChartEquiv (𝓡 3) M p y.1
          (mem_baseSet_chartAt p y.1 y.2))
        (o.orientation y.1) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  have hxbase : x.1 ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) p).baseSet :=
    mem_baseSet_chartAt p x.1 x.2
  obtain ⟨U, hUopen, hxU, hUsub, hconst⟩ := o.locally_constant p x.1 hxbase
  refine ⟨Subtype.val ⁻¹' U, hUopen.preimage continuous_subtype_val, hxU, fun y hy => ?_⟩
  have hybase : y.1 ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) p).baseSet := hUsub hy
  rw [tangentChartEquiv_congr p y.1 (mem_baseSet_chartAt p y.1 y.2) hybase,
    tangentChartEquiv_congr p x.1 hxbase (mem_baseSet_chartAt p x.1 x.2)]
  exact hconst y.1 hy

private theorem exists_oriented_ball_chart_data (M : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ (φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3) E3 M.Carrier ∞),
      Metric.closedBall (0 : E3) 2 ⊆ φ.source ∧
      (∀ x, ∀ hx : x ∈ φ.source,
        Orientation.map (Fin 3)
          ((IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
            (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ φ hx) (by simp)).toLinearEquiv)
          (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
            (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
        M.orientation.orientation (φ x)) := by
  classical
  obtain ⟨p⟩ := ConnectedSpace.toNonempty (α := M.Carrier)
  set b : Module.Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis with hb
  let o : ManifoldOrientation (𝓡 3) M.Carrier 3 := M.orientation
  let e : PartialDiffeomorph (𝓡 3) 𝓘(ℝ, E3) M.Carrier E3 ∞ :=
    DifferentialGeometry.PartialDiffeomorph.extChartAt (𝓡 3) ∞ p
  have hp : p ∈ e.source := by
    change p ∈ (extChartAt (𝓡 3) p).source
    rw [extChartAt_source]
    exact mem_chart_source E3 p
  have hp_base : p ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) p).baseSet :=
    mem_baseSet_chartAt p p (mem_chart_source E3 p)
  set c : E3 := e p with hc
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ > 0, Metric.closedBall c ρ ⊆ e.target := by
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hp))
    exact ⟨ρ / 2, by linarith, fun x hx => hρsub (Metric.closedBall_subset_ball (by linarith) hx)⟩
  set q : Orientation ℝ E3 (Fin 3) :=
    Orientation.map (Fin 3) (DifferentialGeometry.tangentChartEquiv (𝓡 3) M.Carrier p p hp_base)
      (o.orientation p) with hq
  obtain ⟨A₀, hA₀⟩ := exists_orientation_adjusting_linearEquiv q
  have hA₀b : Orientation.map (Fin 3) A₀ b.orientation = q := by simpa [hb] using hA₀
  set Acl : E3 →L[ℝ] E3 := (A₀.toContinuousLinearEquiv : E3 →L[ℝ] E3) with hAcl
  let ε : ℝ := ρ / (6 * (‖Acl‖ + 1))
  have hεpos : 0 < ε := by
    have h1 : (0:ℝ) ≤ ‖Acl‖ := norm_nonneg _
    have h2 : (0:ℝ) < 6 * (‖Acl‖ + 1) := by linarith
    exact div_pos hρpos h2
  let A : E3 ≃L[ℝ] E3 :=
    ((LinearEquiv.smulOfNeZero ℝ E3 ε (ne_of_gt hεpos)).trans A₀).toContinuousLinearEquiv
  have hA_apply : ∀ x : E3, A x = Acl (ε • x) := by
    intro x
    simp [A, Acl, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply]
  have hAl : A.toLinearEquiv = (LinearEquiv.smulOfNeZero ℝ E3 ε (ne_of_gt hεpos)).trans A₀ := by
    ext v
    simp [A]
  have hAorient : Orientation.map (Fin 3) A.toLinearEquiv b.orientation = q := by
    rw [hAl, orientation_map_trans, orientation_map_smulOfNeZero_pos ε hεpos, hA₀b]
  let τ : E3 → E3 := fun x => c + A x
  have hτ_mem : ∀ x ∈ Metric.ball (0 : E3) 3, τ x ∈ e.target := by
    intro x hx
    have hx3 : ‖x‖ < 3 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      simpa using hx
    have hstep1 : ‖τ x - c‖ = ‖A x‖ := by rw [show τ x - c = A x from by simp [τ]]
    have hstep2 : ‖A x‖ ≤ ‖Acl‖ * (ε * ‖x‖) := by
      rw [hA_apply x]
      have h : ‖Acl (ε • x)‖ ≤ ‖Acl‖ * ‖ε • x‖ := ContinuousLinearMap.le_opNorm Acl (ε • x)
      simpa [norm_smul, Real.norm_of_nonneg hεpos.le] using h
    have hstep3 : ‖Acl‖ * (ε * ‖x‖) ≤ ‖Acl‖ * (ε * 3) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg Acl)
      exact (mul_lt_mul_of_pos_left hx3 hεpos).le
    have hkey : ‖Acl‖ * (ε * 3) ≤ ρ := by
      have hN : (0:ℝ) ≤ ‖Acl‖ := norm_nonneg _
      have hD : (0:ℝ) < 6 * (‖Acl‖ + 1) := by linarith
      have hεval : ε = ρ / (6 * (‖Acl‖ + 1)) := rfl
      rw [hεval]
      rw [show ‖Acl‖ * (ρ / (6 * (‖Acl‖ + 1)) * 3) = ‖Acl‖ * ρ * 3 / (6 * (‖Acl‖ + 1)) from by ring]
      rw [div_le_iff₀ hD]
      nlinarith
    have : τ x ∈ Metric.closedBall c ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [hstep1]
      linarith
    exact hρsub this
  have hτ_smooth : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ τ := by
    have h : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun x : E3 => c + A x) :=
      (contMDiff_const (c := c)).add ((A : E3 →L[ℝ] E3).contMDiff)
    simpa [τ] using h
  have hφinv_smooth : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞
      (fun y : E3 => A.symm (y - c)) := by
    have h1 : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun y : E3 => y - c) :=
      contMDiff_iff_contDiff.mpr (contDiff_id.sub contDiff_const)
    exact ((A.symm : E3 →L[ℝ] E3).contMDiff.comp h1)
  have hτ_left : ∀ x : E3, A.symm (τ x - c) = x := by
    intro x
    have h2 : τ x - c = A x := by
      change c + A x - c = A x
      abel
    rw [h2]
    simp
  have hτ_right : ∀ y : E3, c + A (A.symm (y - c)) = y := by
    intro y
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    abel
  have hτ_open : IsOpen (τ '' Metric.ball (0 : E3) 3) := by
    have hτhomeo : E3 ≃ₜ E3 :=
      { toFun := τ
        invFun := fun y => A.symm (y - c)
        left_inv := fun x => hτ_left x
        right_inv := fun y => hτ_right y
        continuous_toFun := hτ_smooth.continuous
        continuous_invFun := hφinv_smooth.continuous }
    have h_eq : τ '' Metric.ball (0 : E3) 3
        = (fun y : E3 => A.symm (y - c)) ⁻¹' Metric.ball (0 : E3) 3 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        change A.symm (τ w - c) ∈ Metric.ball (0 : E3) 3
        rw [hτ_left w]
        exact hw
      · intro hz
        exact ⟨A.symm (z - c), hz, hτ_right z⟩
    rw [h_eq]
    exact Metric.isOpen_ball.preimage hφinv_smooth.continuous
  let φfun : E3 → M.Carrier := fun x => e.toPartialEquiv.invFun (τ x)
  let φinv : M.Carrier → E3 := fun y => A.symm (e.toPartialEquiv.toFun y - c)
  have hφinv_φfun : ∀ x ∈ Metric.ball (0 : E3) 3, φinv (φfun x) = x := by
    intro x hx
    have h1 : e.toPartialEquiv.toFun (e.toPartialEquiv.invFun (τ x)) = τ x :=
      e.toPartialEquiv.right_inv (hτ_mem x hx)
    have h2 : τ x - c = A x := by
      change c + A x - c = A x
      abel
    simp only [φinv, φfun, h1, h2]
    simp
  have hφfun_φinv : ∀ y ∈ φfun '' Metric.ball (0 : E3) 3, φfun (φinv y) = y := by
    rintro y ⟨x, hx, rfl⟩
    rw [hφinv_φfun x hx]
  have hφsub : φfun '' Metric.ball (0 : E3) 3 ⊆ e.source := by
    rintro y ⟨x, hx, rfl⟩
    exact e.toPartialEquiv.map_target (hτ_mem x hx)
  have hφ_image : φfun '' Metric.ball (0 : E3) 3
      = e.toPartialEquiv.invFun '' (τ '' Metric.ball (0 : E3) 3) := by
    rw [show φfun = e.toPartialEquiv.invFun ∘ τ from rfl, Set.image_comp]
  let φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3) E3 M.Carrier ∞ := {
    toPartialEquiv :=
      { toFun := φfun
        invFun := φinv
        source := Metric.ball (0 : E3) 3
        target := φfun '' Metric.ball (0 : E3) 3
        map_source' := fun x hx => ⟨x, hx, rfl⟩
        map_target' := fun y hy => by
          obtain ⟨x, hx, hxy⟩ := hy
          rw [← hxy, hφinv_φfun x hx]
          exact hx
        left_inv' := fun x hx => hφinv_φfun x hx
        right_inv' := fun y hy => hφfun_φinv y hy }
    open_source := Metric.isOpen_ball
    open_target := by
      have hsub : τ '' Metric.ball (0 : E3) 3 ⊆ e.toOpenPartialHomeomorph.symm.source := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact hτ_mem x hx
      have h := (e.toOpenPartialHomeomorph.symm.isOpen_image_iff_of_subset_source hsub).mpr
        hτ_open
      have himg : (↑(e.toOpenPartialHomeomorph.symm) : E3 → M.Carrier) ''
          (τ '' Metric.ball (0 : E3) 3)
          = e.toPartialEquiv.invFun '' (τ '' Metric.ball (0 : E3) 3) := rfl
      rw [himg] at h
      rwa [hφ_image]
    contMDiffOn_toFun := by
      simpa only [Function.comp_def, φfun] using
        e.contMDiffOn_invFun.comp hτ_smooth.contMDiffOn (fun x hx => hτ_mem x hx)
    contMDiffOn_invFun := by
      have h1 : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞
          (fun z : E3 => A.symm (z - c)) Set.univ := hφinv_smooth.contMDiffOn
      have h2 := h1.comp (e.contMDiffOn_toFun.mono hφsub)
        (fun y _ => Set.mem_univ (e.toPartialEquiv.toFun y))
      simpa only [Function.comp_def, φinv] using h2 }
  refine ⟨φ, ?_, ?_⟩
  · intro x hx
    exact Metric.closedBall_subset_ball (by norm_num) hx
  · intro x hx
    have hτx : τ x ∈ e.target := hτ_mem x hx
    have hmem : ∀ y : ↥(Metric.ball (0 : E3) 3), φfun y.1 ∈ (chartAt E3 p).source := fun y => by
      rw [← extChartAt_source (𝓡 3) p]
      exact e.toPartialEquiv.map_target (hτ_mem y.1 y.2)
    let H₀ : ↥((chartAt E3 p).source) → Orientation ℝ E3 (Fin 3) := fun w =>
      Orientation.map (Fin 3)
        (DifferentialGeometry.tangentChartEquiv (𝓡 3) M.Carrier p w.1
          (mem_baseSet_chartAt p w.1 w.2))
        (o.orientation w.1)
    have hH₀ : IsLocallyConstant H₀ := isLocallyConstant_chartOrientation o p
    let Φ : ↥(Metric.ball (0 : E3) 3) → ↥((chartAt E3 p).source) :=
      fun y => ⟨φfun y.1, hmem y⟩
    have hcontOn : ContinuousOn φfun (Metric.ball (0 : E3) 3) :=
      (e.contMDiffOn_invFun.comp hτ_smooth.contMDiffOn (fun z hz => hτ_mem z hz)).continuousOn
    have hΦcont : Continuous Φ := Continuous.subtype_mk hcontOn.domRestrict (fun y => hmem y)
    let H' : ↥(Metric.ball (0 : E3) 3) → Orientation ℝ E3 (Fin 3) := H₀ ∘ Φ
    have hH'LC : IsLocallyConstant H' := hH₀.comp_continuous hΦcont
    have h0mem : (0 : E3) ∈ Metric.ball (0 : E3) 3 := by
      rw [Metric.mem_ball, dist_self]
      norm_num
    have hφ0 : φfun 0 = p := by
      change e.toPartialEquiv.invFun (τ 0) = p
      have hτ0 : τ 0 = e.toPartialEquiv.toFun p := by
        change c + A 0 = c
        simp
      rw [hτ0]
      exact e.toPartialEquiv.left_inv hp
    have h0val : H' ⟨0, h0mem⟩ = q := by
      have h1 : Φ ⟨0, h0mem⟩ = (⟨p, mem_chart_source E3 p⟩ : ↥((chartAt E3 p).source)) := by
        apply Subtype.ext
        exact hφ0
      rw [show H' ⟨0, h0mem⟩ = H₀ (Φ ⟨0, h0mem⟩) from rfl, h1]
    have hpre : PreconnectedSpace ↥(Metric.ball (0 : E3) 3) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : E3) 3).isPreconnected
    have hconst : H' ⟨x, hx⟩ = H' ⟨0, h0mem⟩ :=
      @IsLocallyConstant.apply_eq_of_preconnectedSpace _ _ _ hpre H' hH'LC ⟨x, hx⟩ ⟨0, h0mem⟩
    have hclaim1 : Orientation.map (Fin 3)
        (DifferentialGeometry.tangentChartEquiv (𝓡 3) M.Carrier p (φfun x)
          (mem_baseSet_chartAt p (φfun x) (hmem ⟨x, hx⟩)))
        (o.orientation (φfun x)) = q := hconst.trans h0val
    set Bz : TangentSpace (𝓡 3) (φfun x) ≃ₗ[ℝ] E3 :=
      DifferentialGeometry.tangentChartEquiv (𝓡 3) M.Carrier p (φfun x)
        (mem_baseSet_chartAt p (φfun x) (hmem ⟨x, hx⟩)) with hBz
    have hBz_eq : Bz = DifferentialGeometry.tangentChartEquiv (𝓡 3) M.Carrier p (φfun x)
        (mem_baseSet_chartAt p (φfun x) (hmem ⟨x, hx⟩)) := hBz
    set Bclm : TangentSpace (𝓡 3) (φfun x) →L[ℝ] E3 :=
      Bundle.Trivialization.continuousLinearMapAt ℝ
        (trivializationAt E3 (TangentSpace (𝓡 3)) p) (φfun x) with hBclm
    have hBz_clm : (Bz : TangentSpace (𝓡 3) (φfun x) →ₗ[ℝ] E3) = (Bclm : _ →ₗ[ℝ] E3) := by
      rw [hBz_eq, hBclm]
      exact tangentChartEquiv_eq_continuousLinearMapAt p (φfun x)
        (mem_baseSet_chartAt p (φfun x) (hmem ⟨x, hx⟩))
    have hBz_apply : ∀ v : TangentSpace (𝓡 3) (φfun x), Bz v = Bclm v := by
      intro v
      have h := congrArg (fun (F : TangentSpace (𝓡 3) (φfun x) →ₗ[ℝ] E3) => F v) hBz_clm
      simpa using h
    have hBclm_eq : Bclm = mfderiv (𝓡 3) 𝓘(ℝ, E3) (⇑e) (φfun x) := by
      rw [hBclm]
      exact TangentBundle.continuousLinearMapAt_trivializationAt
        (mem_baseSet_chartAt p (φfun x) (hmem ⟨x, hx⟩))
    have hone : ((⇑e) ∘ (⇑e.symm)) =ᶠ[nhds (τ x)] id :=
      Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hτx)
        (fun y hy => e.toPartialEquiv.right_inv hy)
    have hcomp_inv : mfderiv (𝓡 3) 𝓘(ℝ, E3) ((⇑e) ∘ (⇑e.symm)) (τ x)
        = mfderiv (𝓡 3) 𝓘(ℝ, E3) (⇑e) (φfun x)
          ∘L mfderiv 𝓘(ℝ, E3) (𝓡 3) (⇑e.symm) (τ x) :=
      mfderiv_comp (x := τ x) (f := (⇑e.symm)) (g := (⇑e))
        (e.mdifferentiableAt (by simp) (e.toPartialEquiv.map_target hτx))
        (e.symm.mdifferentiableAt (by simp) hτx)
    have hid : mfderiv (𝓡 3) 𝓘(ℝ, E3) ((⇑e) ∘ (⇑e.symm)) (τ x)
        = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E3) (τ x)) := by
      rw [Filter.EventuallyEq.mfderiv_eq hone, mfderiv_id]
    have hBcomp : Bclm ∘L mfderiv (𝓡 3) (𝓡 3) (⇑e.symm) (τ x)
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) (τ x)) := by
      rw [hBclm_eq]
      exact hcomp_inv.symm.trans hid
    have hτ_mfderiv : mfderiv (𝓡 3) (𝓡 3) τ x = (A : E3 →L[ℝ] E3) :=
      (((A.hasFDerivAt).const_add c).hasMFDerivAt).mfderiv
    have hφmfderiv : mfderiv (𝓡 3) (𝓡 3) φfun x
        = mfderiv (𝓡 3) (𝓡 3) (⇑e.symm) (τ x)
          ∘L mfderiv (𝓡 3) (𝓡 3) τ x := by
      have hcomp := mfderiv_comp (x := x) (f := τ) (g := (⇑e.symm))
        (e.symm.mdifferentiableAt (by simp) hτx) (hτ_smooth.mdifferentiableAt (by simp))
      rw [show φfun = (⇑e.symm) ∘ τ from rfl, hcomp]
    have hBcomp_w : ∀ w : TangentSpace (𝓡 3) (τ x),
        Bclm (mfderiv (𝓡 3) (𝓡 3) (⇑e.symm) (τ x) w) = w := by
      intro w
      have h := DFunLike.congr_fun hBcomp w
      change Bclm (mfderiv (𝓡 3) (𝓡 3) (⇑e.symm) (τ x) w) = w at h
      exact h
    have hτ_w : ∀ v : TangentSpace (𝓡 3) x,
        mfderiv (𝓡 3) (𝓡 3) τ x v = (A : E3 →L[ℝ] E3) v := by
      intro v
      exact DFunLike.congr_fun hτ_mfderiv v
    set D : TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3) (φfun x) :=
      (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ φ hx) (by simp)).toLinearEquiv with hD
    have hDapply : ∀ v : TangentSpace (𝓡 3) x,
        D v = mfderiv (𝓡 3) (𝓡 3) φfun x v := by
      intro v
      have h := congrArg (fun (F : TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) (φfun x)) => F v)
        (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
          (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ φ hx) (by simp))
      simp only [hD]
      exact h
    have hsOrient : (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation)
        = Orientation.map (Fin 3) ((NormedSpace.fromTangentSpace x).symm.toLinearEquiv)
          b.orientation := by
      rw [← hb, Module.Basis.orientation_map]
    have hW : ((NormedSpace.fromTangentSpace x).symm.toLinearEquiv).trans (D.trans Bz)
        = A.toLinearEquiv := by
      refine LinearEquiv.ext fun v => ?_
      change Bz (D (((NormedSpace.fromTangentSpace x).symm.toLinearEquiv) v)) = A.toLinearEquiv v
      rw [hDapply (((NormedSpace.fromTangentSpace x).symm.toLinearEquiv) v)]
      rw [hBz_apply (mfderiv (𝓡 3) (𝓡 3) φfun x
        (((NormedSpace.fromTangentSpace x).symm.toLinearEquiv) v))]
      rw [hφmfderiv]
      change Bclm (mfderiv (𝓡 3) (𝓡 3) (⇑e.symm) (τ x)
        (mfderiv (𝓡 3) (𝓡 3) τ x
          (((NormedSpace.fromTangentSpace x).symm.toLinearEquiv) v))) = A.toLinearEquiv v
      rw [hBcomp_w (mfderiv (𝓡 3) (𝓡 3) τ x
        (((NormedSpace.fromTangentSpace x).symm.toLinearEquiv) v))]
      rw [hτ_w]
      rfl
    have key : Orientation.map (Fin 3) Bz (Orientation.map (Fin 3) D
        (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation)) = q := by
      rw [hsOrient, ← orientation_map_trans D Bz
        ((Orientation.map (Fin 3) ((NormedSpace.fromTangentSpace x).symm.toLinearEquiv)) b.orientation),
        ← orientation_map_trans ((NormedSpace.fromTangentSpace x).symm.toLinearEquiv) (D.trans Bz)
          b.orientation, hW, hAorient]
    exact (Orientation.map (Fin 3) Bz).injective (key.trans hclaim1.symm)


theorem exists_oriented_ball_chart (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (OrientedBallChart M.toClosedOrientedManifold) := by
  obtain ⟨φ, hsub, hpres⟩ := exists_oriented_ball_chart_data M
  exact ⟨{ chart := φ, closedBall_subset_source := hsub, preserves_orientation := hpres }⟩

private theorem exists_manifoldOrientation_of_ballCharts
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    ∃ O : ManifoldOrientation (𝓡 3)
        (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) 3,
      (∀ x : c.toBallChart.interior, Orientation.map (Fin 3)
        ((OrientationAssembly.interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv (M.orientation.orientation x)
        = O.orientation (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x)) ∧
      (∀ x : d.toBallChart.interior, Orientation.map (Fin 3)
        ((OrientationAssembly.interiorRight_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv (N.orientation.orientation x)
        = O.orientation (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x)) := by
  let _ := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
    (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
    (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
  exact OrientationAssembly.exists_manifoldOrientation_of_pieces (M := M.toClosedOrientedManifold)
    (N := N.toClosedOrientedManifold) c d a.1
    (fun f hf =>
      OrientationAssembly.mem_atlas_leftChart c.toBallChart d.toBallChart a.1.toHomeomorph f hf)
    (fun g hg =>
      OrientationAssembly.mem_atlas_rightChart c.toBallChart d.toBallChart a.1.toHomeomorph g hg)
    (OrientationAssembly.mem_atlas_seamChartX c.toBallChart d.toBallChart a.1.toHomeomorph) a.2

def orientedBallChart (M : ConnectedClosedOrientedManifold.{u} 3) :
    OrientedBallChart M.toClosedOrientedManifold :=
  Classical.choice (exists_oriented_ball_chart M)

def boundaryAttachment : BoundaryAttachment :=
  ⟨Topology.Manifold.sphereAntipodalDiffeomorph,
    sphereAntipodalDiffeomorph_preservesOrientation_opposite⟩

theorem boundaryAttachment_symm :
    (boundaryAttachment.1).symm = boundaryAttachment.1 :=
  Diffeomorph.ext fun _ => rfl

def smoothConnectedSum (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    SmoothConnectedSum c d a := by
  letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
    (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
    (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
  haveI : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ConnectedSumQuotient.nonempty_sphere_of_neZero
  have hO := exists_manifoldOrientation_of_ballCharts M N c d a
  exact
    { charts := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
      smooth := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
        (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
        (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
      hausdorff := inferInstance
      compact := inferInstance
      connected := inferInstance
      orientation := Classical.choose hO
      interiorLeft_localDiffeomorph :=
        OrientationAssembly.interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1
      interiorRight_localDiffeomorph :=
        OrientationAssembly.interiorRight_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1
      collar_localDiffeomorph :=
        OrientationAssembly.collarMap_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1
      interiorLeft_preserves_orientation := (Classical.choose_spec hO).1
      interiorRight_preserves_orientation := (Classical.choose_spec hO).2 }

theorem smoothConnectedSum_charts (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    (smoothConnectedSum M N c d a).charts = ConnectedSumQuotient.csChartedSpace
      c.toBallChart d.toBallChart a.1.toHomeomorph := rfl

theorem smoothConnectedSum_smooth (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    (smoothConnectedSum M N c d a).smooth = ConnectedSumQuotient.csIsManifold
      c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1) := rfl

theorem smoothConnectedSum_interiorLeft_localDiffeomorph
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    (smoothConnectedSum M N c d a).interiorLeft_localDiffeomorph =
      OrientationAssembly.interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1 := rfl

def connectedSum (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) : ConnectedClosedOrientedManifold.{max u v} 3 :=
  (smoothConnectedSum M N (orientedBallChart M) (orientedBallChart N)
    boundaryAttachment).toConnectedClosedOrientedManifold

@[simp]
theorem connectedSum_carrier (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSum M N).Carrier = ConnectedSumQuotient (orientedBallChart M).toBallChart
      (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph := rfl

@[simp]
theorem connectedSum_charts (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSum M N).charts = ConnectedSumQuotient.csChartedSpace
      (orientedBallChart M).toBallChart (orientedBallChart N).toBallChart
      boundaryAttachment.1.toHomeomorph := rfl

@[simp]
theorem connectedSum_smooth (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSum M N).smooth = ConnectedSumQuotient.csIsManifold
      (orientedBallChart M).toBallChart (orientedBallChart N).toBallChart
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1) := rfl

@[simp]
theorem connectedSum_orientation (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    (connectedSum M N).orientation = (smoothConnectedSum M N (orientedBallChart M)
      (orientedBallChart N) boundaryAttachment).orientation := rfl

theorem connectedSum_choice_independent {M : ClosedOrientedManifold.{u} 3}
    {N : ClosedOrientedManifold.{v} 3} (c c' : OrientedBallChart M)
    (d d' : OrientedBallChart N) (a a' : BoundaryAttachment)
    (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  sorry

end DifferentialGeometry.Topology
