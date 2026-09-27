import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayRegularity

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W]

private theorem endRay_cross_distance {E : UniformSpace.Completion W}
    (a b : EndRay E) {t s r : ℝ}
    (ht : t ∈ Ioc 0 a.length) (htb : t ≤ b.length)
    (hcontact : a.point t = b.point t)
    (hs : s ∈ Ioc 0 a.length) (hr : r ∈ Ioc 0 b.length)
    (hrt : r ≤ t) (hts : t ≤ s) : dist (a.point s) (b.point r) = s - r := by
  have hupper := dist_triangle (a.point s) (a.point t) (b.point r)
  rw [a.minimizing s hs t ht, hcontact, b.minimizing t ⟨ht.1, htb⟩ r hr,
    abs_of_nonneg (sub_nonneg.mpr hts), abs_of_nonneg (sub_nonneg.mpr hrt)] at hupper
  have hlower := dist_triangle (a.point s : UniformSpace.Completion W)
    (b.point r : UniformSpace.Completion W) E
  rw [UniformSpace.Completion.dist_eq, a.radial s hs, b.radial r hr] at hlower
  linarith

private def spliceEndRay {E : UniformSpace.Completion W}
    (a b : EndRay E) {t : ℝ} (ht : t ∈ Ioc 0 a.length)
    (htb : t ≤ b.length) (hcontact : a.point t = b.point t) : EndRay E where
  length := a.length
  length_pos := a.length_pos
  point s := if s ≤ t then b.point s else a.point s
  radial := by
    intro s hs
    split_ifs with hst
    · exact b.radial s ⟨hs.1, hst.trans htb⟩
    · exact a.radial s hs
  minimizing := by
    intro s hs r hr
    by_cases hst : s ≤ t
    · by_cases hrt : r ≤ t
      · simp only [if_pos hst, if_pos hrt]
        exact b.minimizing s ⟨hs.1, hst.trans htb⟩ r ⟨hr.1, hrt.trans htb⟩
      · simp only [if_pos hst, if_neg hrt]
        rw [dist_comm, endRay_cross_distance a b ht htb hcontact hr
          ⟨hs.1, hst.trans htb⟩ hst (not_le.mp hrt).le,
          abs_of_nonpos (by linarith : s - r ≤ 0)]
        ring
    · by_cases hrt : r ≤ t
      · simp only [if_neg hst, if_pos hrt]
        rw [endRay_cross_distance a b ht htb hcontact hs
          ⟨hr.1, hrt.trans htb⟩ hrt (not_le.mp hst).le,
          abs_of_nonneg (by linarith : 0 ≤ s - r)]
      · simp only [if_neg hst, if_neg hrt]
        exact a.minimizing s hs r hr

variable [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem geodesics_eqOn_of_common_germ
    (g : SmoothRiemannianMetric I3 W) {f h : ℝ → W} {L q : ℝ}
    (hq : q ∈ Ioo 0 L)
    (hf : Geodesic.IsGeodesicOn g f (Ioo 0 L))
    (hh : Geodesic.IsGeodesicOn g h (Ioo 0 L))
    (hfc : ContinuousOn f (Ioo 0 L)) (hhc : ContinuousOn h (Ioo 0 L))
    (hgerm : f =ᶠ[𝓝 q] h) : EqOn f h (Ioo 0 L) := by
  let O : Set ℝ := Ioo (-q) (L - q)
  have hmap : MapsTo (fun s : ℝ => s + q) O (Ioo 0 L) := by
    intro s hs
    change -q < s ∧ s < L - q at hs
    constructor <;> linarith [hs.1, hs.2]
  have hshift (c : ℝ → W) (hc : Geodesic.IsGeodesicOn g c (Ioo 0 L)) :
      Geodesic.IsGeodesicOn g (fun s => c (s + q)) O := by
    intro s hs
    have h := Geodesic.hasGeodesicEquationAt_comp_affine (c := (1 : ℝ)) (d := q)
      (t := s) (by simpa only [one_mul] using hc (s + q) (hmap hs))
    simpa only [one_mul] using h
  have hadd : Tendsto (fun s : ℝ => s + q) (𝓝 0) (𝓝 q) := by
    have h : Tendsto (fun s : ℝ => s + q) (𝓝 0) (𝓝 (0 + q)) :=
      (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).add tendsto_const_nhds
    simpa only [zero_add] using h
  have hlocal : (fun s : ℝ => f (s + q)) =ᶠ[𝓝 0] (fun s => h (s + q)) :=
    hadd.eventually hgerm
  have hzero : (0 : ℝ) ∈ O := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have heq : EqOn (fun s : ℝ => f (s + q)) (fun s => h (s + q)) O := by
    apply geo_eqOn_of_initial g isOpen_Ioo isPreconnected_Ioo hzero (hshift f hf) (hshift h hh)
      (hfc.comp (continuous_id.add continuous_const).continuousOn hmap)
      (hhc.comp (continuous_id.add continuous_const).continuousOn hmap) hlocal.eq_of_nhds
    have hmfd : mfderiv 𝓘(ℝ, ℝ) I3 (fun s : ℝ => f (s + q)) 0 =
        mfderiv 𝓘(ℝ, ℝ) I3 (fun s : ℝ => h (s + q)) 0 := hlocal.mfderiv_eq
    exact congrArg (fun A => (A (1 : ℝ) : ThreeSpace)) hmfd
  intro s hs
  have hsq : s - q ∈ O := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa only [sub_add_cancel] using heq hsq

variable [SigmaCompactSpace W]

theorem finiteHorn_endRay_unique_inward
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint, ∀ t : ℝ,
      0 < t → t < min a.length d → t ≤ b.length → a.point t = b.point t →
      ∀ s ∈ Ioc 0 t, a.point s = b.point s := by
  obtain ⟨d, hd, hregular⟩ := finiteHorn_endRay_smooth_geodesic g H
  refine ⟨d, hd, ?_⟩
  intro a b t ht htd htb hcontact
  have hta : t < a.length := htd.trans_le (min_le_left _ _)
  let c : EndRay H.endpoint := spliceEndRay a b ⟨ht, hta.le⟩ htb hcontact
  obtain ⟨haSmooth, haGeo⟩ := hregular a
  obtain ⟨hcSmooth, hcGeo⟩ := hregular c
  let L : ℝ := min a.length d
  let q : ℝ := (t + L) / 2
  have htq : t < q := by dsimp only [q]; linarith
  have hqL : q < L := by dsimp only [q]; linarith
  have hq : q ∈ Ioo 0 L := ⟨ht.trans htq, hqL⟩
  have hgerm : c.point =ᶠ[𝓝 q] a.point := by
    filter_upwards [isOpen_Ioi.mem_nhds htq] with s hs
    change (if s ≤ t then b.point s else a.point s) = a.point s
    exact if_neg (not_le_of_gt hs)
  have heq : EqOn c.point a.point (Ioo 0 L) :=
    geodesics_eqOn_of_common_germ g hq hcGeo haGeo hcSmooth.continuousOn haSmooth.continuousOn hgerm
  intro s hs
  have hsL : s ∈ Ioo 0 L := ⟨hs.1, hs.2.trans_lt htd⟩
  have h := heq hsL
  change (if s ≤ t then b.point s else a.point s) = a.point s at h
  simpa only [if_pos hs.2] using h.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
