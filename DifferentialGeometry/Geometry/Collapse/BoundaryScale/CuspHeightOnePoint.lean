import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CurvatureBuffers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPremises

/-!
# Curvature scale bounded by the boundary distance (statement G, BSA01.c)

Blueprint 207B, BSA01.c (`B:7615–7618`) and its proof (`B:7660–7672`): for an arbitrary point
`p`, choose (almost) closest boundary points `b = e_i(x, 0)` and the collar point `q = e_i(x, 1)`
of height `1` above `b`; then `d(p, q) ≤ d(p, ∂W) + √(1 + δ)` and a plane of sectional curvature
`≤ -1/8` at `q` forbids every permissible curvature radius `> d(p, ∂W) + 3`. An infinite
curvature scale is never used as a radius: for `d(p, ∂W) < ∞` every `D > d(p, ∂W)` gives
`R_p ≤ D + 3`, and `D ↓ d(p, ∂W)`.

* `CuspEmbedding.riemannianEDistOf_height_zero_one_le`: the vertical segment from height `0` to
  height `1` has length at most `√(1 + δ)`;
* `NearlyCuspidalBoundary.distanceToBoundary_lt_top`: on a connected carrier `d(p, ∂W) < ∞`;
* `NearlyCuspidalBoundary.exists_height_one_point`: `d(p, ∂W) < D` gives a height-one collar point
  within `D + √(1 + δ)` of `p`;
* `exists_carrier_gram_pos`: every tangent space of a carrier contains a nondegenerate
  plane (strict Cauchy–Schwarz, `metric_gram_pos_of_sub_smul_ne_zero`);
* kernel `NearlyCuspidalBoundary.curvatureRadius_le_distanceToBoundary_add_three`: if every plane at
  every height-one collar point has sectional curvature `≤ -1/8` (the upper half of BSA01.a, input
  of lane FT-C), then `R_p ≤ d(p, ∂W) + 3` at every `p`, and `R_p < ∞` on a connected carrier
  (`NearlyCuspidalBoundary.curvatureRadius_lt_top`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- Strict Cauchy–Schwarz: if `u ≠ 0` and `w` is not a multiple of `u`, the Gram determinant of
`(u, w)` is positive. -/
theorem metric_gram_pos_of_sub_smul_ne_zero {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (x : M) {u w : TangentSpace I x} (hu : u ≠ 0) (hw : ∀ t : ℝ, w - t • u ≠ 0) :
    0 < g.inner x u u * g.inner x w w - g.inner x u w ^ 2 := by
  have ha : 0 < g.inner x u u := g.pos x u hu
  set t : ℝ := g.inner x u w / g.inner x u u with ht
  have hy : 0 < g.inner x (w - t • u) (w - t • u) := g.pos x _ (hw t)
  have hsymm : g.inner x w u = g.inner x u w := g.symm x w u
  have hexp : g.inner x (w - t • u) (w - t • u) =
      g.inner x w w - 2 * t * g.inner x u w + t ^ 2 * g.inner x u u := by
    simp only [map_sub, map_smul, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hsymm]
    ring
  have hkey : g.inner x u u * g.inner x (w - t • u) (w - t • u) =
      g.inner x u u * g.inner x w w - g.inner x u w ^ 2 := by
    rw [hexp, ht]
    field_simp
    ring
  rw [← hkey]
  exact mul_pos ha hy

/-- Every tangent space of a carrier contains a nondegenerate plane. -/
theorem exists_carrier_gram_pos (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (x : W.Carrier) :
    ∃ v w : TangentSpace W.model x, 0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2 := by
  refine ⟨(EuclideanSpace.single 0 1 : TangentSpace W.model x), EuclideanSpace.single 1 1,
    metric_gram_pos_of_sub_smul_ne_zero g x ?_ fun t h => ?_⟩
  · intro h
    change (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)) = 0 at h
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) h
    simp at h0
  · change (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 3)) -
      t • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)) = 0 at h
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) h
    simp at h1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The vertical collar segment from height `0` to height `1` has `g`-length at most `√(1 + δ)`. -/
theorem CuspEmbedding.riemannianEDistOf_height_zero_one_le (e : CuspEmbedding W g K δ X)
    (x : Torus) :
    riemannianEDistOf g (e.toFun (x, halfZero)) (e.toFun (x, halfSpaceOneLift 1)) ≤
      ENNReal.ofReal (Real.sqrt (1 + δ)) := by
  let : RiemannianBundle (fun z : W.Carrier => TangentSpace W.model z) := ⟨g.toRiemannianMetric⟩
  let c : ℝ → CuspHalfSpace := fun s => (x, halfSpaceOneLift s)
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c (Icc 0 1) :=
    (contMDiffOn_const.prodMk (contMDiffOn_halfSpaceOneLift.mono Icc_subset_Ici_self)).of_le
      (by norm_cast)
  have hcd : MapsTo c (Icc 0 1) cuspDomain := by
    intro s hs
    change (halfSpaceOneLift s).val 0 < cuspDepth
    rw [halfSpaceOneLift_val_zero]
    change max s 0 < (100 : ℝ)
    exact max_lt (by linarith [hs.2]) (by norm_num)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 (e.toFun ∘ c) (Icc 0 1) :=
    (e.contMDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 K)).comp hc hcd
  have hc0 : c 0 = (x, halfZero) := by
    refine Prod.ext rfl ?_
    have h := halfSpaceOneLift_val_zero_self halfZero
    rwa [show (halfZero : EuclideanHalfSpace 1).val 0 = 0 from rfl] at h
  have hd := riemannianEDist_le_pathELength hγ (x := e.toFun (x, halfZero))
    (y := e.toFun (x, halfSpaceOneLift 1)) (by simp only [comp_apply, hc0]) rfl zero_le_one
  change Manifold.riemannianEDist W.model _ _ ≤ _
  refine hd.trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (1 + δ)) := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel c t :=
      (hc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
    have hed : MDifferentiableAt halfCollarModel W.model e.toFun (c t) :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds (hcd htI))).mdifferentiableAt
        (by simp)
    set v := mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1 with hv
    have hv1 : v.1 = 0 := by
      have hfst : mfderiv 𝓘(ℝ, ℝ) torusModel (Prod.fst ∘ c) t 1 = v.1 := by
        rw [mfderiv_comp t mdifferentiableAt_fst hdiff, mfderiv_fst]
        rfl
      rw [← hfst]
      have hconst : Prod.fst ∘ c = fun _ => x := rfl
      rw [hconst, mfderiv_const]
      rfl
    have hv2 : v.2 0 = 1 := by
      have hsnd := (hasMFDerivAt_snd (c t)).comp t hdiff.hasMFDerivAt
      have hderiv := (hasDerivAt_val_zero_of_hasMFDerivAt hsnd).deriv
      have hmax : deriv (fun s => ((Prod.snd ∘ c) s).val 0) t = 1 := by
        have heq : (fun s => ((Prod.snd ∘ c) s).val 0) =ᶠ[𝓝 t] fun s => s := by
          filter_upwards [Ioi_mem_nhds ht.1] with s hs
          change (halfSpaceOneLift s).val 0 = s
          rw [halfSpaceOneLift_val_zero, max_eq_left (le_of_lt hs)]
        rw [heq.deriv_eq, deriv_id'']
      rw [hderiv] at hmax
      exact hmax
    have hvert := e.pullback_inner_vertical_le (hcd htI) v hv1
    rw [hv2, one_pow, mul_one] at hvert
    rw [mfderiv_comp t hed hdiff, ← ofReal_norm, norm_eq_sqrt_real_inner]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hvert)
  calc ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ
      ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (1 + δ)) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal (Real.sqrt (1 + δ)) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]

/-- On a connected carrier the distance to a nearly cuspidal boundary is finite. -/
theorem NearlyCuspidalBoundary.distanceToBoundary_lt_top (B : NearlyCuspidalBoundary W g K δ)
    [ConnectedSpace W.Carrier] (p : W.Carrier) : distanceToBoundary W g p < ⊤ := by
  obtain ⟨b, hb⟩ := B.boundary_nonempty
  exact (iInf_le (fun q : W.model.boundary W.Carrier => riemannianEDistOf g p q) ⟨b, hb⟩).trans_lt
    (lt_top_iff_ne_top.mpr (riemannianEDistOf_ne_top g p b))

/-- If `d(p, ∂W) < D`, some collar point `e_i(x, 1)` of height one lies within `D + √(1 + δ)` of
`p`. -/
theorem NearlyCuspidalBoundary.exists_height_one_point (B : NearlyCuspidalBoundary W g K δ)
    {p : W.Carrier} {D : ℝ} (hD : distanceToBoundary W g p < ENNReal.ofReal D) :
    ∃ i, ∃ x : Torus, riemannianEDistOf g p ((B.collar i).toFun (x, halfSpaceOneLift 1)) ≤
      ENNReal.ofReal (D + Real.sqrt (1 + δ)) := by
  obtain ⟨⟨b, hb⟩, hpb⟩ := iInf_lt_iff.mp hD
  obtain ⟨i, x, -, rfl⟩ := B.exists_face_of_mem_boundary hb
  have hD0 : 0 ≤ D := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp h))] at hD
    exact absurd hD (not_lt.mpr zero_le)
  refine ⟨i, x, ?_⟩
  calc riemannianEDistOf g p ((B.collar i).toFun (x, halfSpaceOneLift 1))
      ≤ riemannianEDistOf g p ((B.collar i).toFun (x, halfZero)) +
          riemannianEDistOf g ((B.collar i).toFun (x, halfZero))
            ((B.collar i).toFun (x, halfSpaceOneLift 1)) := riemannianEDistOf_triangle g _ _ _
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal (Real.sqrt (1 + δ)) :=
        add_le_add hpb.le ((B.collar i).riemannianEDistOf_height_zero_one_le x)
    _ = ENNReal.ofReal (D + Real.sqrt (1 + δ)) :=
        (ENNReal.ofReal_add hD0 (Real.sqrt_nonneg _)).symm

/-- **BSA01.c (kernel).** If every plane at every height-one collar point has sectional curvature
at most `-1/8`, then `R_p ≤ d(p, ∂W) + 3` at every point (for `δ ≤ 1/100`). -/
theorem NearlyCuspidalBoundary.curvatureRadius_le_distanceToBoundary_add_three
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100)
    (hneg : ∀ (i : Fin B.count) (x : Torus)
      (u w : TangentSpace W.model ((B.collar i).toFun (x, halfSpaceOneLift 1))),
      metricRm04StandardAt g ((B.collar i).toFun (x, halfSpaceOneLift 1)) u w w u ≤
        -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    (p : W.Carrier) :
    curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3 := by
  rcases eq_top_or_lt_top (distanceToBoundary W g p) with htop | hlt
  · rw [htop, top_add]
    exact le_top
  have hs : Real.sqrt (1 + δ) ≤ 101 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set D : ℝ := (distanceToBoundary W g p).toReal + ε with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hdD : distanceToBoundary W g p < ENNReal.ofReal D := by
    rw [hDdef, ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hlt.ne, ENNReal.ofReal_coe_nnreal]
    exact ENNReal.lt_add_right hlt.ne (by exact_mod_cast hε.ne')
  obtain ⟨i, x, hq⟩ := B.exists_height_one_point hdD
  obtain ⟨v, w, hgram⟩ := exists_carrier_gram_pos W g ((B.collar i).toFun (x, halfSpaceOneLift 1))
  have hR := curvatureRadius_le_add_three_of_negative_plane g hD0
    (hq.trans (ENNReal.ofReal_le_ofReal (by linarith))) v w hgram (hneg i x v w)
  refine hR.trans (le_of_eq ?_)
  rw [hDdef, show (distanceToBoundary W g p).toReal + ε + 3 =
      (distanceToBoundary W g p).toReal + 3 + ε by ring,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hlt.ne,
    ENNReal.ofReal_coe_nnreal]

/-- **BSA01.c (kernel), finiteness.** Under the same curvature input, the curvature scale is finite
at every point of a connected carrier. -/
theorem NearlyCuspidalBoundary.curvatureRadius_lt_top (B : NearlyCuspidalBoundary W g K δ)
    [ConnectedSpace W.Carrier] (hδ : δ ≤ 1 / 100)
    (hneg : ∀ (i : Fin B.count) (x : Torus)
      (u w : TangentSpace W.model ((B.collar i).toFun (x, halfSpaceOneLift 1))),
      metricRm04StandardAt g ((B.collar i).toFun (x, halfSpaceOneLift 1)) u w w u ≤
        -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    (p : W.Carrier) : curvatureRadius g p < ⊤ :=
  (B.curvatureRadius_le_distanceToBoundary_add_three hδ hneg p).trans_lt
    (ENNReal.add_lt_top.mpr ⟨B.distanceToBoundary_lt_top p, ENNReal.ofReal_lt_top⟩)

end DifferentialGeometry.Geometry.Collapse
