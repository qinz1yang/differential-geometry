import DifferentialGeometry.Geometry.Connection.ParallelLineSplitting
import DifferentialGeometry.Geometry.Coordinates.RadialPairing
import DifferentialGeometry.Bundle.Frame
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Metric.ConeRadialCurve
import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Preimage
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.ConeChart.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

section

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator

variable {E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [PseudoMetricSpace Y]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
  DifferentialGeometry.normedAddCommGroupTangentSpace DifferentialGeometry.normedSpaceTangentSpace

private theorem bilinear_form_prod_eq_of_radial_pairing
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (g : B →L[ℝ] B →L[ℝ] ℝ) (D : A × ℝ →L[ℝ] B) (Q : A → A → ℝ)
    (hsym : ∀ z w, g z w = g w z)
    (hradial : ∀ u a b, g (D (0, a)) (D (u, b)) = a * b)
    (hangular : ∀ u v, g (D (u, 0)) (D (v, 0)) = Q u v)
    (u v : A) (a b : ℝ) : g (D (u, a)) (D (v, b)) = Q u v + a * b := by
  have hsplit (w : A) (c : ℝ) : D (w, c) = D (w, 0) + D (0, c) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using (map_add D (w, 0) (0, c))
  have hleft : g (D (0, a)) (D (v, 0)) = 0 := by
    simpa only [mul_zero] using hradial v a 0
  have hright : g (D (u, 0)) (D (0, b)) = 0 := by
    have h := hradial u b 0
    simpa only [mul_zero] using (hsym (D (u, 0)) (D (0, b))).trans h
  have hrr : g (D (0, a)) (D (0, b)) = a * b := hradial 0 a b
  rw [hsplit u a, hsplit v b]
  simp only [map_add, add_apply, hangular u v, hleft, hright, hrr, add_zero, zero_add]


omit [SigmaCompactSpace M] in
private theorem inner_angular_of_distance_cone_coordinates
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hdist : ∀ y ∈ e.source, ∀ z ∈ e.source,
      (riemannianEDistOf g y z).toReal = Metric.coneDistance (e y) (e z))
    (phi : PartialDiffeomorph (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I (A × ℝ) M ∞)
    {K : Set A} {J : Set ℝ} (hK : IsOpen K) (h0J : (0 : ℝ) ∈ J)
    (hsource : phi.source = K ×ˢ J) (htarget : phi.target ⊆ e.source)
    (r0 : ℝ) (hr0 : 0 < r0) (hpos : ∀ t ∈ J, 0 < r0 + t)
    (hecurve : ∀ k ∈ K, ∀ t ∈ J, e (phi (k, t)) = (r0 + t, (e (phi (k, 0))).2))
    {k : A} (hk : k ∈ K) {t : ℝ} (ht : t ∈ J) (u v : A) :
    g.inner (phi (k, t))
      (mfderiv (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, 0))
      (mfderiv (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I phi (k, t) (v, 0)) =
      ((r0 + t) / r0) ^ 2 * g.inner (phi (k, 0))
        (mfderiv (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (u, 0))
        (mfderiv (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (v, 0)) := by
  have hmem (l : A) (hl : l ∈ K) (q : ℝ) (hq : q ∈ J) : phi (l, q) ∈ e.source :=
    htarget (phi.map_source (hsource.symm ▸ ⟨hl, hq⟩))
  have hmd (q : ℝ) (hq : q ∈ J) : MDifferentiableAt 𝓘(ℝ, A) I (fun l => phi (l, q)) k :=
    (phi.mdifferentiableAt (by simp) (hsource.symm ▸ ⟨hk, hq⟩)).comp k
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hslice (q : ℝ) (hq : q ∈ J) (w : A) :
      mfderiv 𝓘(ℝ, A) I (fun l => phi (l, q)) k w =
        mfderiv (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I phi (k, q) (w, 0) := by
    have h := mfderiv_comp k (phi.mdifferentiableAt (by simp) (hsource.symm ▸ ⟨hk, hq⟩))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const :
        MDifferentiableAt 𝓘(ℝ, A) (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) (fun l => (l, q)) k)
    simp only [id_eq] at h
    rw [mfderiv_prod_left] at h
    exact congrArg (fun D : A →L[ℝ] E => D w) h
  let c := (r0 + t) / r0
  have hc : 0 < c := div_pos (hpos t ht) hr0
  have hscale (l : A) (hl : l ∈ K) : e (phi (l, t)) =
      (c * (e (phi (l, 0))).1, (e (phi (l, 0))).2) := by
    have hr : (e (phi (l, 0))).1 = r0 := by
      simpa only [add_zero] using congrArg Prod.fst (hecurve l hl 0 h0J)
    rw [hecurve l hl t ht, hr]
    change (r0 + t, _) = ((r0 + t) / r0 * r0, _)
    rw [div_mul_cancel₀ _ hr0.ne']
  have hdist' : ∀ᶠ l in 𝓝 k, (riemannianEDistOf g (phi (k, t)) (phi (l, t))).toReal =
      c * (riemannianEDistOf g (phi (k, 0)) (phi (l, 0))).toReal := by
    filter_upwards [hK.mem_nhds hk] with l hl
    rw [hdist _ (hmem k hk t ht) _ (hmem l hl t ht), hscale k hk, hscale l hl,
      Metric.coneDistance_radial_mul, abs_of_pos hc, hdist _ (hmem k hk 0 h0J) _ (hmem l hl 0 h0J)]
  have h := Geometry.inner_mfderiv_eq_of_local_distance_scaling g g (hmd 0 h0J) (hmd t ht) c hdist'
    u v
  rw [hslice t ht u, hslice t ht v, hslice 0 h0J u, hslice 0 h0J v] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_cone_metric_coordinates_of_local_riemannian_distance_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ y ∈ e.source, 0 < (e y).1)
    (hdist : ∀ y ∈ e.source, ∀ z ∈ e.source,
      (riemannianEDistOf g y z).toReal = Metric.coneDistance (e y) (e z))
    {x : M} (hx : x ∈ e.source) :
    ∃ s : Cₛ^∞⟮I; E, TangentSpace I⟯,
      g.inner x (s x) (s x) = 1 ∧
      ∃ (K : Set (perpSpace g x (s x))) (J : Set ℝ)
        (phi : PartialDiffeomorph ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
          (perpSpace g x (s x) × ℝ) M ∞),
        IsOpen K ∧ (0 : perpSpace g x (s x)) ∈ K ∧ IsOpen J ∧ (0 : ℝ) ∈ J ∧
        phi.source = K ×ˢ J ∧ phi (0, 0) = x ∧ phi.target ⊆ e.source ∧
        (∀ t ∈ J, 0 < (e x).1 + t) ∧
        ∀ k ∈ K, ∀ t ∈ J, ∀ (u v : perpSpace g x (s x)) (a b : ℝ),
          g.inner (phi (k, t))
            (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, a))
            (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I phi (k, t) (v, b)) =
            (((e x).1 + t) / (e x).1) ^ 2 * g.inner (phi (k, 0))
              (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (u, 0))
              (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (v, 0)) + a * b := by
  let r : M → ℝ := fun y => (e y).1
  have hr : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ r e.source :=
    contMDiffOn_radius_of_riemannianEDistOf_cone g e hpos hdist
  have hgrad : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% fun y => gradientFun g r y) e.source := by
    intro y hy
    exact (gradientFun_contMDiffAt g ((hr y hy).contMDiffAt
      (e.open_source.mem_nhds hy))).contMDiffWithinAt
  obtain ⟨sections, hsections⟩ := exists_contMDiffSection_eqOn_nhd (ι := Unit)
    (s := fun _ y => gradientFun g r y) (fun _ => hgrad) e.open_source hx
  let s := sections ()
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_source.mem_nhds hx) (hsections.mono fun _ hy => hy ()))
  have hUe : U ⊆ e.source := fun y hy => (hUsub hy).1
  have hs : ∀ y ∈ U, s y = gradientFun g r y := fun y hy => (hUsub hy).2
  have hunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1 := by
    intro y hy
    rw [hs y hy]
    exact gradient_radius_normSq_eq_one_of_riemannianEDistOf_cone g e hpos hdist (hUe hy)
  have hsne : s x ≠ 0 := by
    intro hz
    have h := hunit x hxU
    simp only [hz, map_zero] at h
    exact zero_ne_one h
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨ne_of_gt (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s x, hsne⟩)⟩
  let f : M → ℝ := fun y => r y - r x
  have hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U := (hr.mono hUe).sub contMDiffOn_const
  have hdf : ∀ y ∈ U, ∀ v : TangentSpace I y, mvfderiv I f y v = g.inner y (s y) v := by
    intro y hy v
    change mvfderiv I (r - fun _ => r x) y v = _
    rw [mvfderiv_sub (((hr y (hUe hy)).contMDiffAt
      (e.open_source.mem_nhds (hUe hy))).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mvfderiv_const, sub_zero, hs y hy, inner_gradientFun]
  obtain ⟨K, J, phi, hK, h0K, hJ, h0J, hsource, hcenter, htarget, hconn,
      hfphi, hrad, _⟩ := exists_local_flow_coordinates_of_unit_gradient g x hU hxU s hunit f
        (sub_self _) hf hdf
  let A := perpSpace g x (s x)
  let L := perpModel g x (s x)
  have hmem (k : A) (hk : k ∈ K) (t : ℝ) (ht : t ∈ J) : phi (k, t) ∈ U :=
    htarget (phi.map_source (hsource.symm ▸ ⟨hk, ht⟩))
  have hradius (k : A) (hk : k ∈ K) (t : ℝ) (ht : t ∈ J) : r (phi (k, t)) = r x + t := by
    have h := hfphi k hk t ht
    change r (phi (k, t)) - r x = t at h
    linarith
  have hcurve (k : A) (hk : k ∈ K) : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t => phi (k, t)) J := by
    intro t ht
    have hkt : (k, t) ∈ phi.source := hsource.symm ▸ ⟨hk, ht⟩
    have hpt := (phi.contMDiffOn_toFun _ hkt).contMDiffAt
      (phi.open_source.mem_nhds hkt)
    exact ((hpt.comp t (contMDiffAt_const.prodMk contMDiffAt_id)).of_le (by simp)).contMDiffWithinAt
  have hvelocity (k : A) (hk : k ∈ K) (t : ℝ) (ht : t ∈ J) :
      mfderiv 𝓘(ℝ, ℝ) I (fun q => phi (k, q)) t 1 = gradientFun g r (phi (k, t)) := by
    have h := mfderiv_comp t (phi.mdifferentiableAt (by simp) (hsource.symm ▸ ⟨hk, ht⟩))
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id :
        MDifferentiableAt 𝓘(ℝ, ℝ) (L.prod 𝓘(ℝ, ℝ)) (fun q => (k, q)) t)
    rw [mfderiv_prod_right] at h
    have hh := congrArg (fun D : ℝ →L[ℝ] E => D 1) h
    change mfderiv 𝓘(ℝ, ℝ) I (fun q => phi (k, q)) t 1 =
      mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t) (0, 1) at hh
    rw [hh, hrad k hk t ht 1, one_smul, hs _ (hmem k hk t ht)]
  have hecurve (k : A) (hk : k ∈ K) (t : ℝ) (ht : t ∈ J) :
      e (phi (k, t)) = (r x + t, (e (phi (k, 0))).2) := by
    have h := radial_image_of_gradient_curve_of_riemannianEDistOf_cone
      g e hpos hdist hJ hconn (hcurve k hk) (fun t ht => hUe (hmem k hk t ht))
      (hvelocity k hk) h0J ht
    change e (phi (k, t)) = (r (phi (k, 0)) + (t - 0), _) at h
    simpa only [sub_zero, hradius k hk 0 h0J, add_zero] using h
  have hrpos (t : ℝ) (ht : t ∈ J) : 0 < r x + t := by
    rw [← hradius 0 h0K t ht]
    exact hpos _ (hUe (hmem 0 h0K t ht))
  have hang (k : A) (hk : k ∈ K) (t : ℝ) (ht : t ∈ J) (u v : A) :=
    inner_angular_of_distance_cone_coordinates g e hdist phi hK h0J hsource
      (htarget.trans hUe) (r x) (hpos x hx) hrpos hecurve hk ht u v
  have hmixed (k : A) (hk : k ∈ K) (t : ℝ) (ht : t ∈ J) (u : A) (a b : ℝ) :
      g.inner (phi (k, t))
        (mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t) (0, a))
        (mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, b)) = a * b :=
    inner_mfderiv_radial_of_gradient_coordinate g s f phi hK hJ (by rw [hsource])
      ((hf.mdifferentiableOn (by simp)).mono htarget) (fun y hy => hdf y (htarget hy)) hfphi hrad
        hk ht u a b
  refine ⟨s, hunit x hxU, K, J, phi, hK, h0K, hJ, h0J, hsource, hcenter, htarget.trans hUe, ?_, ?_⟩
  · intro t ht
    exact hrpos t ht
  · intro k hk t ht u v a b
    exact bilinear_form_prod_eq_of_radial_pairing (g.inner (phi (k, t)))
      (mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t)) _ (g.symm _) (hmixed k hk t ht) (hang k hk t ht) u v
        a b

end DifferentialGeometry.Geometry.Riemannian

end

end

section


noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {S : Type*} [TopologicalSpace S] [ChartedSpace H S]

private def radialSliceTarget (K : TopologicalSpace.Opens P) :
    TopologicalSpace.Opens (P × ℝ) :=
  ⟨(K : Set P) ×ˢ Set.univ, K.isOpen.prod isOpen_univ⟩

private def radialSliceCoordinate (K : TopologicalSpace.Opens P)
    (f : Diffeomorph J 𝓘(ℝ, P) S K ∞) (r0 : ℝ) :
    Diffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ))
      (ℝ × S) (radialSliceTarget K) ∞ where
  toFun z := ⟨((f z.2).1, z.1 - r0), (f z.2).2, Set.mem_univ _⟩
  invFun z := (r0 + z.1.2, f.symm ⟨z.1.1, z.2.1⟩)
  left_inv z := by
    apply Prod.ext
    · change r0 + (z.1 - r0) = z.1
      ring
    · change f.symm (f z.2) = z.2
      exact f.symm_apply_apply z.2
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change (f (f.symm ⟨z.1.1, z.2.1⟩)).1 = z.1.1
      exact congrArg Subtype.val (f.apply_symm_apply ⟨z.1.1, z.2.1⟩)
    · change r0 + z.1.2 - r0 = z.1.2
      ring
  contMDiff_toFun := by
    intro z
    change ContMDiffAt (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × S =>
        (⟨((f q.2).1, q.1 - r0), (f q.2).2, Set.mem_univ _⟩ : radialSliceTarget K)) z
    have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, P) ∞
        (fun q : ℝ × S => (f q.2).1) z :=
      ((contMDiff_subtype_val (I := 𝓘(ℝ, P)) (U := K)).contMDiffAt).comp z
        (f.contMDiffAt.comp z contMDiffAt_snd)
    exact codRestr_contMDiffAt (V := radialSliceTarget K)
      (fun q : ℝ × S => ⟨(f q.2).2, Set.mem_univ _⟩)
      (hf.prodMk (contMDiffAt_fst.sub contMDiffAt_const))
  contMDiff_invFun := by
    intro z
    have hv : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ∞
        (Subtype.val : radialSliceTarget K → P × ℝ) z :=
      (contMDiff_subtype_val
        (I := 𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) (U := radialSliceTarget K)).contMDiffAt
    have hp : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) ∞
        (fun q : radialSliceTarget K => (⟨q.1.1, q.2.1⟩ : K)) z :=
      codRestr_contMDiffAt (fun q : radialSliceTarget K => q.2.1)
        (contMDiffAt_fst.comp z hv)
    have ht : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : radialSliceTarget K => q.1.2) z :=
      contMDiffAt_snd.comp z hv
    exact (contMDiffAt_const.add ht).prodMk (f.symm.contMDiffAt.comp z hp)

private def radialSlicePartialCoordinate
    (r0 : ℝ) (K : TopologicalSpace.Opens P) [Nonempty K]
    (f : Diffeomorph J 𝓘(ℝ, P) S K ∞) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ))
      (ℝ × S) (P × ℝ) ∞ := by
  let k : K := Classical.choice inferInstance
  let : Nonempty (radialSliceTarget K) :=
    ⟨⟨(k.1, 0), k.2, Set.mem_univ _⟩⟩
  exact PartialDiffeomorph.liftTargetOpen
    (radialSliceCoordinate K f r0).toPartialDiffeomorph rfl

end DifferentialGeometry

namespace DifferentialGeometry.Geometry.Riemannian

open TopologicalSpace Set

universe u uE uH v

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {m : ℕ} {S : Type v} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) S] [IsManifold (𝓡 m) ∞ S]
  [T2Space S] [SigmaCompactSpace S]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem cone_chart_of_rectangular_metric_of_surface_diffeomorph
    (g : SmoothRiemannianMetric I M) (K : Opens P) [Nonempty K]
    (f : Diffeomorph (𝓡 m) 𝓘(ℝ, P) S K ∞) (J : Opens ℝ) (hJ : 0 ∈ J)
    (r0 : ℝ) (hr0 : 0 < r0) (hpos : ∀ t ∈ J, 0 < r0 + t)
    (phi : PartialDiffeomorph (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (P × ℝ) M ∞)
    (hsource : phi.source = (K : Set P) ×ˢ (J : Set ℝ))
    (hmetric : ∀ k ∈ K, ∀ t ∈ J, ∀ (u v : P) (a b : ℝ),
      g.inner (phi (k, t))
        (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, a))
        (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, t) (v, b)) =
      ((r0 + t) / r0) ^ 2 *
        g.inner (phi (k, 0))
          (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (u, 0))
          (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (v, 0)) + a * b) :
    Nonempty (ConeChart.{u, uE, uH, v} m g phi.target) := by
  let q : S → P := fun s => (f s).1
  have hq : ContMDiff (𝓡 m) 𝓘(ℝ, P) ∞ q :=
    contMDiff_subtype_val.comp f.contMDiff
  have hqder (s : S) : mfderiv (𝓡 m) 𝓘(ℝ, P) q s = mfderiv (𝓡 m) 𝓘(ℝ, P) f s := by
    have hd := mfderiv_comp s
      ((contMDiff_subtype_val (I := 𝓘(ℝ, P)) (U := K)).contMDiffAt.mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0))
      (f.mdifferentiable (by decide) s)
    rw [mfderiv_subtype_val] at hd
    exact hd
  have hqinj (s : S) : Function.Injective (mfderiv (𝓡 m) 𝓘(ℝ, P) q s) := by
    rw [hqder, ← f.mfderivToContinuousLinearEquiv_coe (by decide)]
    exact (f.mfderivToContinuousLinearEquiv (by decide) s).injective
  have hs0 (s : S) : (q s, (0 : ℝ)) ∈ phi.source := by
    rw [hsource]
    exact ⟨(f s).2, hJ⟩
  let Y : S → M := fun s => phi (q s, 0)
  have hY : ContMDiff (𝓡 m) I ∞ Y := by
    intro s
    exact (phi.contMDiffOn.contMDiffAt (phi.open_source.mem_nhds (hs0 s))).comp s
      ((hq.prodMk contMDiff_const).contMDiffAt)
  have hYder (s : S) (v : TangentSpace (𝓡 m) s) :
      mfderiv (𝓡 m) I Y s v =
        mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (q s, 0)
          (mfderiv (𝓡 m) 𝓘(ℝ, P) q s v, 0) := by
    change mfderiv (𝓡 m) I (phi ∘ (fun s => (q s, (0 : ℝ)))) s v = _
    rw [mfderiv_comp s (phi.mdifferentiableAt (by decide) (hs0 s))
      ((hq.mdifferentiable (by decide) s).prodMk mdifferentiableAt_const),
      mfderiv_prodMk (hq.mdifferentiable (by decide) s) mdifferentiableAt_const,
      mfderiv_const]
    rfl
  have himm (s : S) : Function.Injective (mfderiv (𝓡 m) I Y s) := by
    intro v w hvw
    rw [hYder, hYder] at hvw
    have hlocal := phi.isLocalDiffeomorphAt _ _ _ (hs0 s)
    have hi : Function.Injective
        (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (q s, 0)) := by
      rw [← hlocal.mfderivToContinuousLinearEquiv_coe (by decide)]
      exact (hlocal.mfderivToContinuousLinearEquiv (by decide)).injective
    exact hqinj s (congrArg Prod.fst (hi hvw))
  let h : SmoothRiemannianMetric (𝓡 m) S :=
    scaleMetric ((r0 ^ 2)⁻¹) (inv_pos.mpr (sq_pos_of_pos hr0)) (g.pullback Y hY himm)
  let A := DifferentialGeometry.radialSlicePartialCoordinate r0 K f
  have hAsource : A.source = Set.univ := rfl
  have hAder (z : ℝ × S) (v : ℝ × EuclideanSpace ℝ (Fin m)) :
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) A z v =
        (mfderiv (𝓡 m) 𝓘(ℝ, P) q z.2 v.2, v.1) := by
    change mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ))
      (fun z : ℝ × S => (q z.2, z.1 - r0)) z v = _
    erw [mfderiv_prodMk (f := fun z : ℝ × S => q z.2)
      (g := fun z : ℝ × S => z.1 - r0)
      ((hq.mdifferentiable (by decide) z.2).comp z mdifferentiableAt_snd)
      (mdifferentiableAt_fst.sub mdifferentiableAt_const)]
    erw [mfderiv_comp z (hq.mdifferentiable (by decide) z.2) mdifferentiableAt_snd]
    change ((mfderiv (𝓡 m) 𝓘(ℝ, P) q z.2).comp
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓡 m) Prod.snd z) v,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) 𝓘(ℝ, ℝ)
        (Prod.fst - fun _ : ℝ × S => r0) z v) = _
    erw [mfderiv_snd, mfderiv_sub mdifferentiableAt_fst mdifferentiableAt_const,
      mfderiv_fst, mfderiv_const, sub_zero]
    rfl
  let psi := A.trans phi
  have hpsisource (z : ℝ × S) : z ∈ psi.source ↔ (q z.2, z.1 - r0) ∈ phi.source := by
    change (z ∈ A.source ∧ A z ∈ phi.source) ↔ _
    rw [hAsource]
    exact and_iff_right (Set.mem_univ z)
  have hpsitarget : psi.target = phi.target := by
    change phi.target ∩ phi.symm ⁻¹' A.target = phi.target
    apply Set.inter_eq_left.mpr
    intro y hy
    have hs := phi.map_target' hy
    rw [hsource] at hs
    exact ⟨hs.1, Set.mem_univ _⟩
  have hpsider (z : ℝ × S) (hz : z ∈ psi.source)
      (v : ℝ × EuclideanSpace ℝ (Fin m)) :
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I psi z v =
        mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (q z.2, z.1 - r0)
          (mfderiv (𝓡 m) 𝓘(ℝ, P) q z.2 v.2, v.1) := by
    change mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I (phi ∘ A) z v = _
    have ha : z ∈ A.source := by rw [hAsource]; exact Set.mem_univ z
    have hphiAt : MDifferentiableAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (A z) :=
      phi.mdifferentiableAt (by decide) hz.2
    erw [mfderiv_comp (f := (A : ℝ × S → P × ℝ)) (g := (phi : P × ℝ → M))
      z hphiAt (A.mdifferentiableAt (by decide) ha), ContinuousLinearMap.comp_apply, hAder]
    rfl
  refine ⟨{ surface := S
            metric := h
            map := psi
            positive_radius := ?_
            target_eq := hpsitarget
            radial_metric := ?_ }⟩
  · intro z hz
    have hs := (hpsisource z).mp hz
    rw [hsource] at hs
    have hp := hpos (z.1 - r0) hs.2
    linarith
  · intro z hz v w
    change ℝ × EuclideanSpace ℝ (Fin m) at v w
    rw [hpsider z hz v, hpsider z hz w]
    change g.inner (phi (q z.2, z.1 - r0)) _ _ = _
    have hs := (hpsisource z).mp hz
    rw [hsource] at hs
    erw [hmetric (q z.2) hs.1 (z.1 - r0) hs.2
      (mfderiv (𝓡 m) 𝓘(ℝ, P) q z.2 v.2) (mfderiv (𝓡 m) 𝓘(ℝ, P) q z.2 w.2) v.1 w.1]
    dsimp only [h]
    erw [scaleMetric_inner (I := (𝓡 m)) ((r0 ^ 2)⁻¹)
      (inv_pos.mpr (sq_pos_of_pos hr0)) (g.pullback Y hY himm) z.2 v.2 w.2]
    erw [SmoothRiemannianMetric.pullback_inner (I := (𝓡 m)) (J := I)
      g Y hY himm z.2 v.2 w.2]
    erw [hYder z.2 v.2, hYder z.2 w.2]
    change ((r0 + (z.1 - r0)) / r0) ^ 2 *
        g.inner (phi (q z.2, 0)) _ _ + v.1 * w.1 =
      v.1 * w.1 + z.1 ^ 2 * ((r0 ^ 2)⁻¹ * g.inner (phi (q z.2, 0)) _ _)
    field_simp [ne_of_gt hr0]
    ring

theorem cone_chart_of_rectangular_metric
    [FiniteDimensional ℝ P] (hdim : Module.finrank ℝ P = m)
    (g : SmoothRiemannianMetric I M) (K : Opens P) [Nonempty K]
    (J : Opens ℝ) (hJ : 0 ∈ J)
    (r0 : ℝ) (hr0 : 0 < r0) (hpos : ∀ t ∈ J, 0 < r0 + t)
    (phi : PartialDiffeomorph (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (P × ℝ) M ∞)
    (hsource : phi.source = (K : Set P) ×ˢ (J : Set ℝ))
    (hmetric : ∀ k ∈ K, ∀ t ∈ J, ∀ (u v : P) (a b : ℝ),
      g.inner (phi (k, t))
        (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, a))
        (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, t) (v, b)) =
      ((r0 + t) / r0) ^ 2 *
        g.inner (phi (k, 0))
          (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (u, 0))
          (mfderiv (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I phi (k, 0) (v, 0)) + a * b) :
    Nonempty (ConeChart.{u, uE, uH, v} m g phi.target) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hdim])
  let K' : Opens (EuclideanSpace ℝ (Fin m)) :=
    ⟨e ⁻¹' (K : Set P), K.isOpen.preimage e.continuous⟩
  let S := ULift.{v} K'
  let : ChartedSpace (EuclideanSpace ℝ (Fin m)) S :=
    DifferentialGeometry.Topology.uliftChartedSpace (EuclideanSpace ℝ (Fin m)) K'
  let : IsManifold (𝓡 m) ∞ S := DifferentialGeometry.Topology.isManifold_ulift (𝓡 m) K'
  let : LocallyCompactSpace K' := K'.isOpen.locallyCompactSpace
  let : SigmaCompactSpace K' := inferInstance
  let f : Diffeomorph (𝓡 m) 𝓘(ℝ, P) S K ∞ :=
    (DifferentialGeometry.Topology.uliftDiffeomorph (𝓡 m) K').symm.trans
      (DifferentialGeometry.Manifold.Diffeomorph.preimage e.toDiffeomorph K)
  exact cone_chart_of_rectangular_metric_of_surface_diffeomorph g K f J hJ r0 hr0 hpos phi hsource
    hmetric

end DifferentialGeometry.Geometry.Riemannian

end

end

section

noncomputable section
open Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Connection

universe u uE uH v

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {Y : Type*} [PseudoMetricSpace Y] {m : ℕ}

theorem exists_cone_chart_of_riemannianEDistOf_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ y ∈ e.source, 0 < (e y).1)
    (hdist : ∀ y ∈ e.source, ∀ z ∈ e.source,
      (riemannianEDistOf g y z).toReal = Metric.coneDistance (e y) (e z))
    (hdim : Module.finrank ℝ E = m + 1) {x : M} (hx : x ∈ e.source) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧ Nonempty (ConeChart.{u, uE, uH, v} m g V) := by
  obtain ⟨s, hunit, K, J, phi, hK, h0K, hJ, h0J, hsource, hcenter, htarget, hpositive, hmetric⟩ :=
    exists_cone_metric_coordinates_of_local_riemannian_distance_cone g e hpos hdist hx
  have hsne : s x ≠ 0 := by
    intro hz
    simp only [hz, map_zero] at hunit
    exact zero_ne_one hunit
  have hperp : Module.finrank ℝ (perpSpace g x (s x)) = m := by
    rw [finrank_perpSpace g x (s x) hsne, hdim]
    omega
  let Kopen : TopologicalSpace.Opens (perpSpace g x (s x)) := ⟨K, hK⟩
  let : Nonempty Kopen := ⟨⟨0, h0K⟩⟩
  refine ⟨phi.target, phi.open_target, ?_, htarget, ?_⟩
  · have hm : phi (0, 0) ∈ phi.target := phi.map_source (hsource.symm ▸ ⟨h0K, h0J⟩)
    rwa [hcenter] at hm
  · exact cone_chart_of_rectangular_metric hperp g Kopen ⟨J, hJ⟩ h0J
      (e x).1 (hpos x hx) hpositive phi hsource hmetric

end DifferentialGeometry.Geometry.Riemannian

end

end

noncomputable section
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] {Y : Type*} [PseudoMetricSpace Y] {m : ℕ}

theorem exists_cone_chart_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    (hdim : Module.finrank ℝ E = m + 1) {p : M} (hp : p ∈ e.source) :
    ∃ U : Set M, p ∈ U ∧ U ⊆ e.source ∧ Nonempty (ConeChart.{_, _, _, 0} m g U) := by
  obtain ⟨U, _, hpU, hsource, hchart⟩ :=
    exists_cone_chart_of_riemannianEDistOf_cone g e
      (fun x hx => hpositive (e x) (e.map_source hx)) (fun x hx y hy => by
        simpa only [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
          hdist x hx y hy) hdim hp
  exact ⟨U, hpU, hsource, hchart⟩

end DifferentialGeometry.Geometry.Riemannian
