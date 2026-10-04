import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelFill

/-!
# The capped solid torus of one side

Lane N2d, side model, step 5 (solid torus, interior). For a side `t` fix the ball chart `Φ` of
`exists_sideBall` and the filling `G` of `exists_capFill` (`SideCap`). The model map `solMap` is
`Φ (2 G⁻¹ (torusPD q))` on the fake region (level `sgnR(t) · level ≤ 2`) and the lift into the core
elsewhere. Near the level `2` both formulas agree, because `G` is the shell map there and `Φ` is
untwisted on its outer shell (`fake_eq_real`). Hence `solMap` is a local diffeomorphism on the open
model solid torus (`isLocalDiffeomorphAt_solMap`), it reads the collar of the port `sidePort` near
radius `3` (`solMap_collar`), and it is injective on the closed model solid torus
(`solMap_injOn`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
  {N : ClosedOrientedManifold.{u} 3}
  (K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin))

structure SideCap (t : Bool) where
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ 1 / 2
  Φ : E3 → N.Carrier
  loc : ∀ x : E3, ‖x‖ < 5 / 2 → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ Φ x
  inj : InjOn Φ (ball 0 (5 / 2))
  cap_in : ∀ x : E3, ‖x‖ ≤ 1 → ∃ w : ClosedCell 3, Φ x = K.cap ((), t) w
  cap_surj : ∀ w : ClosedCell 3, ∃ x : E3, ‖x‖ ≤ 1 ∧ Φ x = K.cap ((), t) w
  shell : ∀ x : E3, 1 ≤ ‖x‖ → ‖x‖ < 5 / 2 →
    ∃ z : S2, Φ x = coreMap K ((E.splitCharts h hlin).tubeMap (z, sgnR t * ‖x‖))
  shell' : ∀ x : E3, 1 + r / 2 ≤ ‖x‖ → ‖x‖ < 5 / 2 →
    Φ x = coreMap K ((E.splitCharts h hlin).tubeMap
      (Manifold.sphereDirection poleS2 x, sgnR t * ‖x‖))
  G : E3 ≃ₘ[ℝ] E3
  G_ball : ∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * E.sideLevel h t q ≤ 2 →
    ‖G.symm (torusPD q)‖ ≤ 1
  G_onto : ∀ x : E3, ‖x‖ ≤ 1 → ∃ q : ℂ × Circle, ‖q.1‖ < 3 ∧
    sgnR t * E.sideLevel h t q ≤ 2 ∧ G x = torusPD q
  V : Set E3
  V_open : IsOpen V
  V_sphere : sphere (0 : E3) 1 ⊆ V
  V_shell : V ⊆ shellSet
  G_shell : ∀ x ∈ V, G x = E.shellMap h hlin t x

theorem nonempty_sideCap (t : Bool) : Nonempty (E.SideCap h hlin K t) := by
  obtain ⟨r, hr, hr2, Φ, hloc, hinj, hin, hsurj, hsh, hsh'⟩ :=
    (E.splitCharts h hlin).exists_sideBall K t
  obtain ⟨G, hG1, hG2, V, hV, hSV, hVs, hGV⟩ := E.exists_capFill h hlin t
  exact ⟨⟨r, hr, hr2, Φ, hloc, hinj, hin, hsurj, hsh, hsh', G, hG1, hG2, V, hV, hSV, hVs, hGV⟩⟩

variable {E h hlin K}

theorem liftMap_ne_tubeMap {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    {z : S2} {lv : ℝ} (hlv : |lv| < 3) (hne : E.sideLevel h t q ≠ lv) :
    (E.splitCharts h hlin).liftMap t q ≠ (E.splitCharts h hlin).tubeMap (z, lv) := by
  intro he
  obtain ⟨q', hq', -, hlev, he'⟩ := E.exists_liftMap_eq_tubeMap h hlin t z hlv
  rw [← he'] at he
  have := E.liftMap_injOn h hlin t hq hq' he
  rw [this] at hne
  exact hne hlev

theorem liftMap_mem_core {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hlev : 1 < |E.sideLevel h t q|) :
    (E.splitCharts h hlin).liftMap t q ∈ (E.splitSeamTube j b h hlin).core := by
  intro hmem
  simp only [mem_iUnion, SphericalTubeSystem.removedBand, mem_image] at hmem
  obtain ⟨a, y, hy, he⟩ := hmem
  have he' : (E.splitCharts h hlin).tubeMap (y.1, y.2.val) =
      (E.splitCharts h hlin).liftMap t q := he
  have hy1 : |y.2.val| < 1 := abs_lt.mpr ⟨hy.1, hy.2⟩
  refine liftMap_ne_tubeMap hq (by linarith) ?_ he'.symm
  intro h0
  rw [h0] at hlev
  linarith

theorem liftMap_ne_boundarySphere {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hlev : 1 < |E.sideLevel h t q|) (c : (E.splitSeamTube j b h hlin).Boundary) (z : S2) :
    (E.splitSeamTube j b h hlin).boundarySphere c z ≠ (E.splitCharts h hlin).liftMap t q := by
  rw [show (E.splitSeamTube j b h hlin).boundarySphere c z =
    (E.splitCharts h hlin).tubeMap (z, sgnR c.2) from (E.splitCharts h hlin).boundarySphere_eq c z]
  have hs : |sgnR c.2| = 1 := by rcases sgnR_eq c.2 with e | e <;> rw [e] <;> norm_num
  refine (liftMap_ne_tubeMap hq (by rw [hs]; norm_num) ?_).symm
  intro h0
  rw [h0, hs] at hlev
  exact lt_irrefl _ hlev

theorem isLocalDiffeomorphAt_coreMap_liftMap {t : Bool} {q : ℂ × Circle}
    (hq : q ∈ E.liftDom h t) (hlev : 1 < |E.sideLevel h t q|) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞
      (coreMap K ∘ (E.splitCharts h hlin).liftMap t) q := by
  have hd := E.sideDom_of_mem_liftDom h hq
  exact (E.isLocalDiffeomorphAt_liftMap_of_mem h hlin hq).comp (𝓡 3) N.Carrier
    (isLocalDiffeomorphAt_coreMap K ⟨_, liftMap_mem_core hd hlev⟩
      (isInteriorPoint_of_forall_ne K _ fun c z => liftMap_ne_boundarySphere hd hlev c z))

namespace SideCap

variable {t : Bool} (S : E.SideCap h hlin K t)

def solMap (q : ℂ × Circle) : N.Carrier :=
  if ‖q.1‖ < 3 ∧ sgnR t * E.sideLevel h t q ≤ 2 then S.Φ ((2 : ℝ) • S.G.symm (torusPD q))
  else coreMap K ((E.splitCharts h hlin).liftMap t q)

theorem solMap_of_fake {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * E.sideLevel h t q ≤ 2) :
    S.solMap q = S.Φ ((2 : ℝ) • S.G.symm (torusPD q)) :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h3, h2⟩)

theorem solMap_of_real {q : ℂ × Circle} (h2 : 2 < sgnR t * E.sideLevel h t q) :
    S.solMap q = coreMap K ((E.splitCharts h hlin).liftMap t q) :=
  ite_eq_right_of_eq_false _ _ (eq_false fun hc => absurd hc.2 (not_le.mpr h2))

theorem norm_two_smul_le {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * E.sideLevel h t q ≤ 2) :
    ‖(2 : ℝ) • S.G.symm (torusPD q)‖ ≤ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have := S.G_ball q h3 h2
  linarith

theorem fake_eq_real {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (hV : S.G.symm (torusPD q) ∈ S.V) :
    S.Φ ((2 : ℝ) • S.G.symm (torusPD q)) = coreMap K ((E.splitCharts h hlin).liftMap t q) := by
  set x := S.G.symm (torusPD q) with hx
  have hxs := S.V_shell hV
  obtain ⟨h1, h2, -⟩ := E.shellMap_spec h hlin t hxs
  have hGx : S.G x = torusPD q := S.G.apply_symm_apply _
  rw [S.G_shell x hV] at hGx
  have hq : E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (shellDir t x)) = q :=
    torusPD_injOn (show ‖_‖ < 4 by linarith [h1.1]) (show ‖q.1‖ < 4 by linarith) hGx
  rw [hq] at h2
  rw [h2]
  have hx0 : x ≠ 0 := fun h0 => by have := hxs.1; rw [h0, norm_zero] at this; linarith
  have hn : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have r2 := S.r_le
  rw [S.shell' _ (by rw [hn]; linarith [hxs.1]) (by rw [hn]; linarith [hxs.2])]
  congr 2
  refine Prod.ext ?_ ?_
  · change Manifold.sphereDirection poleS2 ((2 : ℝ) • x) = Manifold.sphereDirection poleS2 x
    conv_lhs => rw [← Manifold.norm_smul_sphereDirection poleS2 hx0, smul_smul]
    exact Manifold.sphereDirection_pos_smul poleS2 _ (by positivity)
  · change sgnR t * ‖(2 : ℝ) • x‖ = 2 * sgnR t * ‖x‖
    rw [hn]
    ring

end SideCap

end GC.Seifert.ElementaryPresentation
