import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelSolid

/-!
# The capped solid torus of one side: local diffeomorphism and collar

Lane N2f, side model, step 5 (solid torus, local part). On the level set `sgnR(t) · level = 2` of
the model the filling `G` is the shell map, so `G⁻¹ (torusPD q)` lies in the shell neighbourhood
`V` of the unit sphere (`symm_mem_V_of_level`). The fake formula `fakeMap q = Φ (2 G⁻¹ (torusPD q))`
is a local diffeomorphism wherever `‖2 G⁻¹ (torusPD q)‖ < 5/2`, and it agrees with `solMap` near
every point whose filling preimage lies in `V`. Hence `solMap` is a local diffeomorphism on the open
model solid torus (`isLocalDiffeomorphAt_solMap`). Beyond radius `5/2` the model point is real and
`solMap` reads the host collar of the port `sidePort` at depth `collarDepth ‖ζ‖`
(`solMap_collar`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b} {hlin : E.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin)}

namespace SideCap

variable {t : Bool} (S : E.SideCap h hlin K t)

theorem symm_mem_V_of_level {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * E.sideLevel h t q = 2) : S.G.symm (torusPD q) ∈ S.V := by
  have hL : E.sideLevel h t q = 2 * sgnR t := by
    have := sgnR_mul_self t
    linear_combination sgnR t * h2 - E.sideLevel h t q * this
  have hlev3 : |E.sideLevel h t q| < 3 := by
    rw [hL, mul_comm, SplitCharts.abs_sgnR_mul]
    norm_num
  have hqd : q ∈ E.liftDom h t := ⟨h3, by rw [h2]; norm_num⟩
  obtain ⟨p, hp⟩ := E.exists_tubeMap_eq_liftMap h hlin t (E.sideDom_of_mem_liftDom h hqd) hlev3
  have hpn : ‖(p : E3)‖ = 1 := norm_eq_of_mem_sphere p
  have hdir : shellDir t (p : E3) = (p, E.sideLevel h t q) := by
    refine Prod.ext ?_ ?_
    · change Manifold.sphereDirection poleS2 (p : E3) = p
      have := Manifold.sphereDirection_pos_smul poleS2 p one_pos
      rwa [one_smul] at this
    · change 2 * sgnR t * ‖(p : E3)‖ = _
      rw [hpn, hL]
      ring
  have hpV : (p : E3) ∈ S.V := S.V_sphere p.2
  have hG : S.G (p : E3) = torusPD q := by
    rw [S.G_shell _ hpV, shellMap, hdir, hp, E.liftInv_liftMap h hlin hqd]
  rw [← hG, S.G.symm_apply_apply]
  exact hpV

def fakeMap (q : ℂ × Circle) : N.Carrier := S.Φ ((2 : ℝ) • S.G.symm (torusPD q))

theorem norm_two_smul (x : E3) : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

theorem isLocalDiffeomorphAt_fakeMap {q : ℂ × Circle} (h4 : ‖q.1‖ < 4)
    (h5 : ‖(2 : ℝ) • S.G.symm (torusPD q)‖ < 5 / 2) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ S.fakeMap q := by
  let L : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) (by norm_num))).toContinuousLinearEquiv
  have a1 : IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ torusPD q :=
    isLocalDiffeomorphAt_torusPD h4
  have a2 := a1.comp _ _ (S.G.symm.isLocalDiffeomorph (torusPD q))
  have a3 := a2.comp _ _ (L.toDiffeomorph.isLocalDiffeomorph (S.G.symm (torusPD q)))
  exact a3.comp _ _ (S.loc _ h5)

theorem solMap_eq_fakeMap_of_mem {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (hV : S.G.symm (torusPD q) ∈ S.V) : S.solMap q = S.fakeMap q := by
  by_cases h2 : sgnR t * E.sideLevel h t q ≤ 2
  · exact S.solMap_of_fake h3 h2
  · rw [S.solMap_of_real (not_le.mp h2)]
    exact (S.fake_eq_real h3 hV).symm

theorem continuousOn_symm_torusPD :
    ContinuousOn (fun q : ℂ × Circle => S.G.symm (torusPD q)) {q | ‖q.1‖ < 4} :=
  S.G.symm.continuous.comp_continuousOn torusPD.toOpenPartialHomeomorph.continuousOn

theorem isLocalDiffeomorphAt_solMap {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ S.solMap q := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hO3 : IsOpen {q : ℂ × Circle | ‖q.1‖ < 3} := isOpen_lt hcn continuous_const
  by_cases hV : S.G.symm (torusPD q) ∈ S.V
  · have hU : IsOpen ({q : ℂ × Circle | ‖q.1‖ < 3} ∩
        (fun q : ℂ × Circle => S.G.symm (torusPD q)) ⁻¹' S.V) :=
      (S.continuousOn_symm_torusPD.mono fun q (hq : ‖q.1‖ < 3) =>
        show ‖q.1‖ < 4 by linarith).isOpen_inter_preimage hO3 S.V_open
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (S.isLocalDiffeomorphAt_fakeMap
      (by linarith) ?_)
    · exact eventuallyEq_of_mem (hU.mem_nhds ⟨h3, hV⟩) fun q' hq' =>
        S.solMap_eq_fakeMap_of_mem hq'.1 hq'.2
    · rw [norm_two_smul]
      linarith [(S.V_shell hV).2]
  · rcases lt_trichotomy (sgnR t * E.sideLevel h t q) 2 with hlt | heq | hgt
    · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (S.isLocalDiffeomorphAt_fakeMap
        (by linarith) ?_)
      · exact eventuallyEq_of_mem ((E.isOpen_fakeSet h t).mem_nhds ⟨h3, hlt⟩) fun q' hq' =>
          S.solMap_of_fake hq'.1 hq'.2.le
      · linarith [S.norm_two_smul_le h3 hlt.le]
    · exact absurd (S.symm_mem_V_of_level h3 heq) hV
    · have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * E.sideLevel h t q)
          {q | ‖q.1‖ < 3} :=
        (continuousOn_const.mul (E.continuousOn_sideLevel h t)).mono fun q hq =>
          show ‖q.1‖ ≤ 3 from le_of_lt hq
      have hU : IsOpen ({q : ℂ × Circle | ‖q.1‖ < 3} ∩
          (fun q : ℂ × Circle => sgnR t * E.sideLevel h t q) ⁻¹' Ioi 2) :=
        hc.isOpen_inter_preimage hO3 isOpen_Ioi
      have hqd : q ∈ E.liftDom h t := ⟨h3, by linarith⟩
      have hlev : 1 < |E.sideLevel h t q| := by
        rw [← SplitCharts.abs_sgnR_mul t]
        exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      refine IsLocalDiffeomorphAt.of_eventuallyEq ?_
        (isLocalDiffeomorphAt_coreMap_liftMap (hlin := hlin) (K := K) hqd hlev)
      exact eventuallyEq_of_mem (hU.mem_nhds ⟨h3, hgt⟩) fun q' hq' =>
        S.solMap_of_real (hq'.2 : sgnR t * E.sideLevel h t q' ∈ Ioi 2)

theorem solMap_collar {q : ℂ × Circle} (h1 : 5 / 2 ≤ ‖q.1‖) (h3 : ‖q.1‖ ≤ 3) :
    S.solMap q = coreMap K (E.hostMap h (planarCollarFormula 3 (sidePort (E.hostSide h) t)
      (((q.2⁻¹ : Circle) : ℂ), collarDepth ‖q.1‖), E.liftFib h hlin q)) := by
  have hlev := E.three_lt_sideLevel_of_ge h t h1 h3
  rw [S.solMap_of_real (by linarith), SplitCharts.liftMap_of_gt _ t (by linarith)]
  unfold SplitCharts.liftH
  rw [sideData_point_collar _ t h1 (by linarith), hostChart_hostInv]
  rfl

end SideCap

end GC.Seifert.ElementaryPresentation
