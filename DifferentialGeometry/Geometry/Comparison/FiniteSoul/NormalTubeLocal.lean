import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeDefs
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative

/-!
# The local normal tube of a finite-order slice (lane CMS3-FLOW, S3-TUBE, G1)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §3 "S3-TUBE".

Let `S` be a `C^r` slice (`r ≥ 2`) of a complete manifold with a `C^(r+1)` metric `g`, `s₀ ∈ S`, and
`c` a slice chart at `s₀` carrying `S` onto the affine subspace `A` (direction `D`). With `P` the
orthogonal projection onto `D`, `y₀ = c s₀`, `B = (c.symm)^* g` and `N y = normalRaiseFinite (B y)`,
the vector `N y w` (`w ⊥ D`) is `B y`-orthogonal to `D`, so

  `sliceTubeParam z = ⟨c.symm (y₀ + P z), dc.symm (N (y₀ + P z) (z − P z))⟩`

parametrizes the normal vectors of `S` near `⟨s₀, 0⟩` by `z ∈ E = D ⊕ D^⊥`.

* `contMDiffAt_sliceTubeParam`: the parametrization is `C^(r−1)` into `TM`.
* `exists_local_normalTube` (**main**): there are an open `U ⊆ M`, a map `ψ₀ : M → TM` of class
  `C^(r−1)` on `U`, and `δ > 0` such that every normal vector `v` based within `δ` of `s₀` and of
  `g`-length `< δ` has `exp v ∈ U` and `ψ₀ (exp v) = v`. Route: `exp ∘ sliceTubeParam` has invertible
  differential `dc.symm ∘ (P + N y₀ (1 − P))` at `0` (`B`-orthogonality); IFT at order one, invertibility
  on an open set, IFT at order `r − 1`; `ψ₀ = sliceTubeParam ∘ (local inverse)`; every normal vector
  `v` near `⟨s₀, 0⟩` is `sliceTubeParam` of `(c v.proj − y₀) + gramOpFinite (B (c v.proj)) (dc v)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section Param

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The local normal-tube parametrization in a slice chart `c` (base point `y₀`, slice direction
`D`). -/
def sliceTubeParam {n k : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (y₀ : E) (D : Submodule ℝ E)
    [D.HasOrthogonalProjection] (z : E) : TangentBundle I M :=
  ⟨c.symm (y₀ + D.starProjection z), mfderiv 𝓘(ℝ, E) I c.symm (y₀ + D.starProjection z)
    (normalRaiseFinite (slicePullbackFinite g c (y₀ + D.starProjection z)) (z - D.starProjection z))⟩

/-- The tube parametrization is `C^m` on the preimage of the chart target (`m + 1 ≤ k`, `m ≤ n`). -/
theorem contMDiffAt_sliceTubeParam {n k m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (hmn : m ≤ n) (hmk : m + 1 ≤ k) (hk : k ≠ 0)
    (y₀ : E) (D : Submodule ℝ E) [D.HasOrthogonalProjection] {z : E}
    (hz : y₀ + D.starProjection z ∈ c.target) :
    ContMDiffAt 𝓘(ℝ, E) I.tangent m (sliceTubeParam g c y₀ D) z := by
  set P := D.starProjection with hP
  have hσd : ContDiff ℝ m (fun z : E => y₀ + P z) := contDiff_const.add P.contDiff
  have hcs : ContMDiffAt 𝓘(ℝ, E) I k c.symm (y₀ + P z) :=
    c.symm.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hz)
  have hNc := contDiffOn_normalRaiseFinite (contDiffOn_slicePullbackFinite g c hmn hmk)
    (fun y hy => isCoercive_slicePullbackFinite g hk hy)
  have hNσ : ContDiffAt ℝ m (fun z : E => normalRaiseFinite (slicePullbackFinite g c (y₀ + P z)))
      z :=
    ContDiffAt.comp (g := fun y => normalRaiseFinite (slicePullbackFinite g c y))
      (f := fun z : E => y₀ + P z) z (hNc.contDiffAt (c.open_target.mem_nhds hz)) hσd.contDiffAt
  have ha : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) m
      (fun z : E => normalRaiseFinite (slicePullbackFinite g c (y₀ + P z)) (z - P z)) z :=
    (hNσ.clm_apply (contDiff_id.sub P.contDiff).contDiffAt).contMDiffAt
  exact contMDiffAt_mk_mfderiv_apply hcs hmk hσd.contMDiff.contMDiffAt ha

end Param

section Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
theorem one_le_coe_sub_one_tube {r : ℕ∞} (hr : 2 ≤ r) :
    (1 : ℕ∞ω) ≤ ((r - 1 : ℕ∞) : ℕ∞ω) := by
  have h : (1 : ℕ∞) ≤ r - 1 := by
    induction r using ENat.recTopCoe with
    | top => simp
    | coe n =>
      have : (2 : ℕ) ≤ n := by exact_mod_cast hr
      have h3 : ((n - 1 : ℕ) : ℕ∞) = (n : ℕ∞) - 1 := by simp
      rw [← h3]
      exact_mod_cast (by omega : 1 ≤ n - 1)
  exact_mod_cast h

theorem coe_sub_one_add_one_le_tube {r : ℕ∞} (hr : 1 ≤ r) :
    ((r - 1 : ℕ∞) : ℕ∞ω) + 1 ≤ (r : ℕ∞ω) := by
  have h : (r - 1 : ℕ∞) + 1 = r := tsub_add_cancel_of_le hr
  rw [← h]
  norm_cast
  simp

theorem coe_sub_one_le_add_one_tube {r : ℕ∞} : ((r - 1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have : (r - 1 : ℕ∞) ≤ r := tsub_le_self
  exact le_trans (by exact_mod_cast this) le_self_add

/-- **The local normal tube at a point of a `C^r` slice.** -/
theorem exists_local_normalTube
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) {s₀ : M} (hs₀ : s₀ ∈ S) :
    ∃ U : Set M, IsOpen U ∧ ∃ ψ₀ : M → TangentBundle I M,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ₀ U ∧
      ∃ δ > 0, ∀ v ∈ normalSetFinite g S, dist s₀ v.proj < δ →
        g.inner v.proj v.snd v.snd < δ ^ 2 → g.expMap v ∈ U ∧ ψ₀ (g.expMap v) = v := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk0 : ((r : ℕ∞) : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr1).ne'
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hm1 : m + 1 ≤ (r : ℕ∞ω) := coe_sub_one_add_one_le_tube hr1
  have hmn : m ≤ (r : ℕ∞ω) + 1 := coe_sub_one_le_add_one_tube
  have hmr : m ≤ (r : ℕ∞ω) := (le_add_of_nonneg_right zero_le_one).trans hm1
  have hm_ge : (1 : ℕ∞ω) ≤ m := one_le_coe_sub_one_tube hr
  have hm0 : m ≠ 0 := (zero_lt_one.trans_le hm_ge).ne'
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hexpdom : g.expDomain = univ := by
    rw [Bundle.ContMDiffRiemannianMetric.expDomain, hdom, preimage_univ]
  have hexp : ContMDiff I.tangent I (r : ℕ∞ω) g.expMap := by
    have h := g.contMDiffOn_expMap hr1
    rwa [hexpdom, contMDiffOn_univ] at h
  obtain ⟨c, A, hA, hs₀c, -, himage⟩ := hS s₀ hs₀
  set y₀ : E := c s₀ with hy₀
  have hy₀A : y₀ ∈ A := (himage.apply_mem_iff hs₀c).2 hs₀
  have hy₀t : y₀ ∈ c.target := c.toPartialEquiv.map_source hs₀c
  have hcy₀ : c.symm y₀ = s₀ := c.toPartialEquiv.left_inv hs₀c
  set D : Submodule ℝ E := A.direction with hD
  set P : E →L[ℝ] E := D.starProjection with hP
  set B : E → E →L[ℝ] E →L[ℝ] ℝ := slicePullbackFinite g c with hB
  set N : E → E →L[ℝ] E := fun y => normalRaiseFinite (B y) with hN
  have hBco : ∀ y ∈ c.target, IsCoercive (B y) := fun y hy =>
    isCoercive_slicePullbackFinite g hk0 hy
  set J : E → TangentBundle I M := sliceTubeParam g c y₀ D with hJ
  set T : E → M := fun z => g.expMap (J z) with hT
  set V₀ : Set E := (fun z => y₀ + P z) ⁻¹' c.target with hV₀
  have hV₀o : IsOpen V₀ := c.open_target.preimage (continuous_const.add P.continuous)
  have h0V₀ : (0 : E) ∈ V₀ := by
    change y₀ + P 0 ∈ c.target
    rw [map_zero, add_zero]
    exact hy₀t
  have hJs : ∀ z ∈ V₀, ContMDiffAt 𝓘(ℝ, E) I.tangent m J z := fun z hz =>
    contMDiffAt_sliceTubeParam g c hmn hm1 hk0 y₀ D hz
  have hTs : ∀ z ∈ V₀, ContMDiffAt 𝓘(ℝ, E) I m T z := fun z hz =>
    (hexp.of_le hmr).contMDiffAt.comp z (hJs z hz)
  -- the differential at `0`
  set dcs : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm y₀ with hdcs
  have hTd : MDifferentiableAt 𝓘(ℝ, E) I T 0 := (hTs 0 h0V₀).mdifferentiableAt hm0
  set L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I T 0 with hL
  have hsmul : ∀ u : E, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun h : ℝ => h • u) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight u) := by
    intro u
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const u).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have hTu : ∀ u : E, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun h : ℝ => T (h • u)) 0
      (L.comp ((1 : ℝ →L[ℝ] ℝ).smulRight u)) := by
    intro u
    have hT0 : HasMFDerivAt 𝓘(ℝ, E) I T ((0 : ℝ) • u) L := by
      rw [zero_smul]
      exact hTd.hasMFDerivAt
    exact (hT0.comp (g := T) (f := fun h : ℝ => h • u) 0 (hsmul u) :)
  have hLD : ∀ u ∈ D, L u = dcs u := by
    intro u hu
    have hfun : (fun h : ℝ => T (h • u)) = fun h : ℝ => c.symm (y₀ + h • u) := by
      funext h
      have hPu : P (h • u) = h • u :=
        (Submodule.starProjection_eq_self_iff (K := D)).2 (D.smul_mem h hu)
      change g.expMap (sliceTubeParam g c y₀ D (h • u)) = c.symm (y₀ + h • u)
      simp only [sliceTubeParam]
      rw [hPu, sub_self]
      exact (congrArg g.expMap (tangentBundle_mk_eq rfl
        (by rw [map_zero]; exact map_zero _))).trans (g.expMap_zero hr1 _)
    have hcsd : MDifferentiableAt 𝓘(ℝ, E) I c.symm y₀ := c.symm.mdifferentiableAt hk0 hy₀t
    have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun h : ℝ => y₀ + h • u) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight u) := by
      have h := (((hasDerivAt_id (0 : ℝ)).smul_const u).const_add y₀).hasFDerivAt
      simp only [one_smul] at h
      exact h.hasMFDerivAt
    have hcs0 : HasMFDerivAt 𝓘(ℝ, E) I c.symm (y₀ + (0 : ℝ) • u) dcs := by
      rw [zero_smul, add_zero]
      exact hcsd.hasMFDerivAt
    have h2 := hcs0.comp 0 hlin
    have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun h : ℝ => c.symm (y₀ + h • u)) 0
        (L.comp ((1 : ℝ →L[ℝ] ℝ).smulRight u)) := by
      rw [← hfun]
      exact hTu u
    have heq := congrArg (fun F : ℝ →L[ℝ] E => F 1) (hasMFDerivAt_unique h1 h2)
    change L ((1 : ℝ →L[ℝ] ℝ) 1 • u) = dcs ((1 : ℝ →L[ℝ] ℝ) 1 • u) at heq
    simp only [one_apply_eq_self, one_smul] at heq
    exact heq
  have hLN : ∀ w ∈ Dᗮ, L w = dcs (N y₀ w) := by
    intro w hw
    set X : E := dcs (N y₀ w) with hX
    have hfun : (fun h : ℝ => T (h • w)) =
        fun h : ℝ => g.expMap (⟨s₀, h • X⟩ : TangentBundle I M) := by
      funext h
      have hPw : P (h • w) = 0 :=
        Submodule.eq_starProjection_of_mem_orthogonal (K := D) D.zero_mem
          (by rw [sub_zero]; exact Dᗮ.smul_mem h hw) |>.trans rfl
      change g.expMap (sliceTubeParam g c y₀ D (h • w)) = _
      simp only [sliceTubeParam]
      rw [hPw, add_zero, sub_zero]
      congr 1
      refine tangentBundle_mk_eq hcy₀ ?_
      change dcs (N y₀ (h • w)) = h • X
      rw [map_smul, map_smul]
    have hexp0 := g.hasMFDerivAt_expMap_zero hr1 s₀
    have hX0 : HasMFDerivAt 𝓘(ℝ, E) I (fun v : E => g.expMap (⟨s₀, v⟩ : TangentBundle I M))
        ((0 : ℝ) • X) (ContinuousLinearMap.id ℝ E) := by
      rw [zero_smul]
      exact hexp0
    have h2 := hX0.comp 0 (hsmul X)
    have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun h : ℝ => g.expMap (⟨s₀, h • X⟩ : TangentBundle I M)) 0
        (L.comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) := by
      rw [← hfun]
      exact hTu w
    have heq := congrArg (fun F : ℝ →L[ℝ] E => F 1) (hasMFDerivAt_unique h1 h2)
    change L ((1 : ℝ →L[ℝ] ℝ) 1 • w) = (ContinuousLinearMap.id ℝ E) ((1 : ℝ →L[ℝ] ℝ) 1 • X) at heq
    simp only [one_apply_eq_self, one_smul, ContinuousLinearMap.id_apply] at heq
    exact heq
  -- invertibility
  have hdcs_inj : ∀ a : E, dcs a = 0 → a = 0 := by
    intro a ha
    have h := mfderiv_apply_mfderiv_symm_tube hk0 hy₀t a
    have h' : mfderiv I 𝓘(ℝ, E) c (c.symm y₀) (dcs a) = 0 := by
      rw [ha]
      exact map_zero _
    exact h.symm.trans h'
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    set a := P z with ha
    set w := z - P z with hw
    have haD : a ∈ D := Submodule.starProjection_apply_mem D z
    have hwD : w ∈ Dᗮ := Submodule.sub_starProjection_mem_orthogonal z
    have hz' : z = a + w := by rw [ha, hw]; abel
    have hsum : dcs (a + N y₀ w) = 0 := by
      rw [map_add, ← hLD a haD, ← hLN w hwD, ← map_add, ← hz']
      exact hz
    have hab : a + N y₀ w = 0 := hdcs_inj _ hsum
    have hNw : N y₀ w = -a := eq_neg_of_add_eq_zero_right hab
    have hBNN : B y₀ (N y₀ w) (N y₀ w) = 0 := by
      rw [apply_normalRaiseFinite (hBco y₀ hy₀t), hNw, inner_neg_right,
        Submodule.inner_left_of_mem_orthogonal haD hwD, neg_zero]
    obtain ⟨κ, hκ, hcoer⟩ := hBco y₀ hy₀t
    have hb0 : N y₀ w = 0 := by
      have h := hcoer (N y₀ w)
      rw [hBNN] at h
      by_contra hne
      have hpos : 0 < ‖N y₀ w‖ := norm_pos_iff.mpr hne
      nlinarith [mul_pos (mul_pos hκ hpos) hpos]
    have hw0 : w = 0 := by
      have h := gramOpFinite_normalRaiseFinite (hBco y₀ hy₀t) w
      change gramOpFinite (B y₀) (N y₀ w) = w at h
      rw [hb0, map_zero] at h
      exact h.symm
    have ha0 : a = 0 := by
      rw [hb0, add_zero] at hab
      exact hab
    rw [hz', ha0, hw0, add_zero]
  have hLsurj : Function.Surjective (L : E →ₗ[ℝ] E) :=
    LinearMap.injective_iff_surjective.mp hLinj
  have hLinv : L.IsInvertible :=
    ⟨(LinearEquiv.ofBijective (L : E →ₗ[ℝ] E) ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  -- inverse function theorem
  have : IsManifold I (1 : ℕ∞ω) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hT1 : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1 T 0 :=
    DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤)) ((hTs 0 h0V₀).of_le hm_ge) hLinv
  obtain ⟨Φ₁, h0Φ₁, hEq₁⟩ := hT1
  set U₁ : Set E := Φ₁.source ∩ V₀ with hU₁
  have hU₁o : IsOpen U₁ := Φ₁.open_source.inter hV₀o
  have hinvU₁ : ∀ z ∈ U₁, (mfderiv 𝓘(ℝ, E) I T z).IsInvertible := fun z hz =>
    (show IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1 T z from ⟨Φ₁, hz.1, hEq₁⟩).isInvertible_mfderiv
      one_ne_zero
  have : IsManifold I m M := IsManifold.of_le (n := ∞) (by rw [hm]; exact_mod_cast le_top)
  have hTU₁ : ContMDiffOn 𝓘(ℝ, E) I m T U₁ := fun z hz => (hTs z hz.2).contMDiffWithinAt
  obtain ⟨Φ, h0Φ, hEq⟩ :=
    hTU₁.isLocalDiffeomorphOn_of_isInvertible_mfderiv hU₁o hm_ge hinvU₁ ⟨0, h0Φ₁, h0V₀⟩
  -- the local inverse
  set W : Set M := Φ.target ∩ (Φ.symm : M → E) ⁻¹' (Φ.source ∩ V₀) with hW
  have hWo : IsOpen W := Φ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_target
    (Φ.open_source.inter hV₀o)
  set ψ₀ : M → TangentBundle I M := fun x => J ((Φ.symm : M → E) x) with hψ₀
  have hψ₀s : ContMDiffOn I I.tangent m ψ₀ W := by
    intro x hx
    have hsymm : ContMDiffAt I 𝓘(ℝ, E) m (Φ.symm : M → E) x :=
      Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hx.1)
    exact ((hJs _ hx.2.2).comp x hsymm).contMDiffWithinAt
  -- the inverse parameter of a normal vector
  set prm : TangentBundle I M → E := fun v =>
    (c v.proj - y₀) + gramOpFinite (B (c v.proj)) (mfderiv I 𝓘(ℝ, E) c v.proj v.snd) with hprm
  have hprm0 : prm (⟨s₀, 0⟩ : TangentBundle I M) = 0 := by
    have h1 : mfderiv I 𝓘(ℝ, E) c s₀ (0 : TangentSpace I s₀) = 0 := map_zero _
    change (c s₀ - y₀) + gramOpFinite (B (c s₀)) (mfderiv I 𝓘(ℝ, E) c s₀ 0) = 0
    rw [h1, sub_self, zero_add]
    exact map_zero _
  have hprmc : ContinuousAt prm (⟨s₀, 0⟩ : TangentBundle I M) := by
    have hproj : ContinuousAt (fun v : TangentBundle I M => v.proj) (⟨s₀, 0⟩ : TangentBundle I M) :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt
    have hcv : ContinuousAt (fun v : TangentBundle I M => c v.proj) (⟨s₀, 0⟩ : TangentBundle I M) :=
      (c.contMDiffOn.continuousOn.continuousAt (c.open_source.mem_nhds hs₀c)).comp hproj
    have hBv : ContinuousAt (fun v : TangentBundle I M => gramOpFinite (B (c v.proj)))
        (⟨s₀, 0⟩ : TangentBundle I M) := by
      have hBc := (contDiffOn_slicePullbackFinite g c (m := 0) zero_le
        (by rw [zero_add]; exact_mod_cast hr1)).continuousOn
      have hB0 : ContinuousAt B y₀ := hBc.continuousAt (c.open_target.mem_nhds hy₀t)
      have hBv' : ContinuousAt (fun v : TangentBundle I M => B (c v.proj))
          (⟨s₀, 0⟩ : TangentBundle I M) :=
        ContinuousAt.comp (g := B) (f := fun v : TangentBundle I M => c v.proj) hB0 hcv
      exact ((gramCLMFinite (E := E)).continuous.continuousAt.comp hBv' :)
    have hcsm : ContMDiffAt I 𝓘(ℝ, E) (r : ℕ∞ω) c s₀ :=
      c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hs₀c)
    have hsec : ContMDiffAt I.tangent (I.prod 𝓘(ℝ, E)) 0
        (fun v : TangentBundle I M =>
          TotalSpace.mk' E (E := Bundle.Trivial M E) v.proj
            (mfderiv I 𝓘(ℝ, E) c v.proj v.snd)) (⟨s₀, 0⟩ : TangentBundle I M) := by
      have hhom : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
          (fun x : M => (⟨x, mfderiv I 𝓘(ℝ, E) c x⟩ :
            TotalSpace (E →L[ℝ] E) (fun x => TangentSpace I x →L[ℝ] Bundle.Trivial M E x))) s₀ := by
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        have hd := hcsm.mfderiv_const (m := 0) (by rw [zero_add]; exact_mod_cast hr1)
        apply hd.congr_of_eventuallyEq
        filter_upwards [] with x
        ext v
        simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
        rfl
      have hid : ContMDiffAt I.tangent (I.prod 𝓘(ℝ, E)) 0
          (fun v : TangentBundle I M => TotalSpace.mk' E (E := TangentSpace I) v.proj v.snd)
          (⟨s₀, 0⟩ : TangentBundle I M) := contMDiffAt_id
      exact ContMDiffAt.clm_bundle_apply (E₁ := TangentSpace I) (E₂ := Bundle.Trivial M E)
        (b := fun v : TangentBundle I M => v.proj)
        (hhom.comp (⟨s₀, 0⟩ : TangentBundle I M)
          (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt) hid
    have hdv : ContinuousAt (fun v : TangentBundle I M => mfderiv I 𝓘(ℝ, E) c v.proj v.snd)
        (⟨s₀, 0⟩ : TangentBundle I M) :=
      (contMDiffAt_totalSpace.mp hsec).2.continuousAt
    exact (hcv.sub continuousAt_const).add (hBv.clm_apply hdv)
  have hO : prm ⁻¹' (Φ.source ∩ V₀) ∩ (fun v : TangentBundle I M => v.proj) ⁻¹' c.source ∈
      𝓝 (⟨s₀, 0⟩ : TangentBundle I M) := by
    refine Filter.inter_mem (hprmc.preimage_mem_nhds ?_) ?_
    · rw [hprm0]
      exact (Φ.open_source.inter hV₀o).mem_nhds ⟨h0Φ, h0V₀⟩
    · exact (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
        (c.open_source.mem_nhds hs₀c)
  obtain ⟨δ, hδ, hδO⟩ := exists_forall_mem_of_mem_nhds_zero g s₀ hO
  refine ⟨W, hWo, ψ₀, hψ₀s, δ, hδ, fun v hv hvd hvg => ?_⟩
  obtain ⟨⟨hprmΦ, hprmV⟩, hvc⟩ := hδO v hvd hvg
  -- `v` is the parametrization of its inverse parameter
  set x : M := v.proj with hx
  have hxS : x ∈ S := hv.1
  have hxc : x ∈ c.source := hvc
  set y : E := c x with hy
  have hyA : y ∈ A := (himage.apply_mem_iff hxc).2 hxS
  have hyt : y ∈ c.target := c.toPartialEquiv.map_source hxc
  have hcyx : c.symm y = x := c.toPartialEquiv.left_inv hxc
  set u : E := y - y₀ with hu
  have huD : u ∈ D := A.vsub_mem_direction hyA hy₀A
  set a : E := mfderiv I 𝓘(ℝ, E) c x v.snd with ha
  have hdcsa : mfderiv 𝓘(ℝ, E) I c.symm y a = v.snd :=
    mfderiv_symm_apply_mfderiv_ofOrder hk0 hxc v.snd
  have hnormal : ∀ t ∈ D, B y a t = 0 := by
    intro t ht
    have hxS' : c.symm y ∈ S := by rw [hcyx]; exact hxS
    have hxc' : c.symm y ∈ c.source := c.toPartialEquiv.map_target hyt
    have htan : (mfderiv 𝓘(ℝ, E) I c.symm y t : TangentSpace I (c.symm y)) ∈
        sliceTangent I S (c.symm y) := by
      refine (mem_sliceTangent_chart_iff_ofOrder hk0 hxS' hA hxc' himage).2 ?_
      rw [mfderiv_apply_mfderiv_symm_tube hk0 hyt t]
      exact ht
    have key : ∀ x' : M, x' = x → ∀ X : E, X ∈ sliceTangent I S x' →
        g.inner x' v.snd X = 0 := by
      rintro x' rfl X hX
      exact hv.2 X hX
    rw [hB, slicePullbackFinite_apply, hdcsa]
    exact key _ hcyx _ htan
  set w' : E := gramOpFinite (B y) a with hw'
  have hw'D : w' ∈ Dᗮ := by
    rw [Submodule.mem_orthogonal]
    intro t ht
    rw [real_inner_comm, hw', inner_gramOpFinite]
    exact hnormal t ht
  have hprmv : prm v = u + w' := rfl
  have hPprm : P (prm v) = u := by
    rw [hprmv]
    exact Submodule.eq_starProjection_of_mem_orthogonal huD (by rw [add_sub_cancel_left]; exact hw'D)
  have hσ : y₀ + P (prm v) = y := by rw [hPprm, hu]; abel
  have hJv : J (prm v) = v := by
    change sliceTubeParam g c y₀ D (prm v) = v
    simp only [sliceTubeParam]
    rw [hσ]
    have hres : prm v - P (prm v) = w' := by rw [hPprm, hprmv, add_sub_cancel_left]
    rw [hres, hw', normalRaiseFinite_gramOpFinite (hBco y hyt), hdcsa]
    exact tangentBundle_mk_eq hcyx rfl
  have hTv : T (prm v) = g.expMap v := by
    change g.expMap (J (prm v)) = g.expMap v
    rw [hJv]
  have hΦv : (Φ : E → M) (prm v) = g.expMap v := by
    rw [← hEq hprmΦ, hTv]
  have hl : Φ.symm.toPartialEquiv (Φ.toPartialEquiv (prm v)) = prm v :=
    Φ.toPartialEquiv.left_inv hprmΦ
  have hexpW : g.expMap v ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [← hΦv]
      exact Φ.toPartialEquiv.map_source hprmΦ
    · rw [Set.mem_preimage, ← hΦv, hl]
      exact ⟨hprmΦ, hprmV⟩
  refine ⟨hexpW, ?_⟩
  change J ((Φ.symm : M → E) (g.expMap v)) = v
  rw [← hΦv, hl, hJv]

end Local

end DifferentialGeometry.Geometry.FiniteSoul
