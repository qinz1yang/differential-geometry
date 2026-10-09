import DifferentialGeometry.Geometry.Metric.GeodesicInterpolation
import DifferentialGeometry.Geometry.Metric.ShortGeodesicBounds
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

set_option backward.isDefEq.respectTransparency false in



theorem exists_geodesicInterpolation_ambient_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)) (r : EuclideanSpace ℝ (Fin n) → M),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      (∀ x, r (e x) = x) ∧
      ∃ (ρ C : ℝ≥0) (O : Set (ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))),
        let F := fun p : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          geodesicInterpolation g (r p.2.1) (r p.2.2) p.1
        0 < ρ ∧ IsOpen O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
          𝓘(ℝ, E) ∞ F O ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
          riemannianEDistOf g x y ≤ (ρ : ℝ≥0∞) →
            (t, (e x, e y)) ∈ O ∧
            ∀ v : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
              Real.sqrt (g.inner (F (t, (e x, e y)))
                (mfderiv 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
                  𝓘(ℝ, E) F (t, (e x, e y)) v)
                (mfderiv 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
                  𝓘(ℝ, E) F (t, (e x, e y)) v)) ≤ C * ‖v‖ := by
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    exists_compact_embedding_and_retraction (E := E) (M := M)
  refine ⟨n, e, r, he, hleft, ?_⟩
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton M := subsingleton_of_zero_model hdim
    let q : M := Classical.choice ‹Nonempty M›
    have hconst : geodesicInterpolation g = fun _ _ _ => q := by
      funext x y t
      exact Subsingleton.elim _ _
    refine ⟨1, 0, univ, ?_⟩
    dsimp only
    rw [hconst]
    refine ⟨zero_lt_one, isOpen_univ, contMDiffOn_const, fun _ _ _ _ _ => ⟨mem_univ _, ?_⟩⟩
    intro v
    rw [mfderiv_const]
    change Real.sqrt (g.inner q (0 : E) 0) ≤ 0 * ‖v‖
    simp only [map_zero, Real.sqrt_zero, zero_mul, le_refl]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
    let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
    have hG : geodesicInterpolation g = shortGeodesic g hg := by
      funext x y t
      simp only [geodesicInterpolation, dite_eq_right hdim]
      rfl
    erw [hG]
    exact exists_ambientShortGeodesic_bound g hg he.continuous hU heU hr hleft

omit [Nonempty M] in
theorem riemannianEDistOf_geodesicInterpolation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x y : M}
    (h : riemannianEDistOf g x y ≠ ⊤) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    riemannianEDistOf g (geodesicInterpolation g x y s) (geodesicInterpolation g x y t) =
      ENNReal.ofReal |s - t| * riemannianEDistOf g x y := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton M := subsingleton_of_zero_model hdim
    have hyx : y = x := Subsingleton.elim y x
    subst hyx
    simp only [geodesicInterpolation, dite_eq_left hdim, riemannianEDistOf_self, mul_zero]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
    let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
    set v : TangentSpace 𝓘(ℝ, E) x := minimizingLog g hg x y with hv
    set γ : ℝ → M := intrinsicGeodesic (I := 𝓘(ℝ, E)) g hg x v with hγ
    set r : ℝ := (riemannianEDistOf g x y).toReal with hr
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    have hshort (u : ℝ) : geodesicInterpolation g x y u = γ u := by
      have h1 : geodesicInterpolation g x y u = shortGeodesic g hg x y u := by
        simp only [geodesicInterpolation, dite_eq_right hdim]
        rfl
      rw [h1, shortGeodesic_eq_exp, expMapIntrinsic_def, intrinsicGeodesic_smul]
    have hγ0 : γ 0 = x := intrinsicGeodesic_zero (I := 𝓘(ℝ, E)) g hg x v
    have hgeo1 : intrinsicGeodesic (I := 𝓘(ℝ, E)) g hg x v 1 = y := minimizingLog_exp g hg h
    have hnorm : Real.sqrt (g.inner x v v) = r := minimizingLog_norm g hg h
    have hup (u w : ℝ) (huw : u ≤ w) :
        riemannianEDistOf g (γ u) (γ w) ≤ ENNReal.ofReal (r * (w - u)) := by
      have hle := intrinsicGeodesic_riemannianEDist_le (I := 𝓘(ℝ, E)) g hg x v huw
      rw [hnorm] at hle
      exact hle
    have hlow (u w : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) (huw : u ≤ w) :
        ENNReal.ofReal (r * (w - u)) ≤ riemannianEDistOf g (γ u) (γ w) := by
      have hAu := intrinsicGeodesic_riemannianEDist_le (I := 𝓘(ℝ, E)) g hg x v
        (s := 0) (t := u) hu.1
      rw [intrinsicGeodesic_zero, hnorm, sub_zero] at hAu
      have hBw := intrinsicGeodesic_riemannianEDist_le (I := 𝓘(ℝ, E)) g hg x v
        (s := w) (t := 1) hw.2
      rw [hgeo1, hnorm] at hBw
      have ht1 : riemannianEDistOf g x y ≤
          riemannianEDistOf g x (γ u) + riemannianEDistOf g (γ u) y :=
        riemannianEDistOf_triangle g x (γ u) y
      have ht2 : riemannianEDistOf g (γ u) y ≤
          riemannianEDistOf g (γ u) (γ w) + riemannianEDistOf g (γ w) y :=
        riemannianEDistOf_triangle g (γ u) (γ w) y
      have hle : riemannianEDistOf g x y ≤ ENNReal.ofReal (r * u) +
          (riemannianEDistOf g (γ u) (γ w) + ENNReal.ofReal (r * (1 - w))) := by
        refine ht1.trans ?_
        refine (add_le_add hAu ?_)
        exact ht2.trans (add_le_add le_rfl hBw)
      rw [← ENNReal.ofReal_toReal h] at hle
      have hadd : ENNReal.ofReal (r * u) +
          (riemannianEDistOf g (γ u) (γ w) + ENNReal.ofReal (r * (1 - w))) =
          riemannianEDistOf g (γ u) (γ w) + ENNReal.ofReal (r * (u + (1 - w))) := by
        rw [mul_add, ENNReal.ofReal_add (mul_nonneg hr0 hu.1) (mul_nonneg hr0 (sub_nonneg.mpr hw.2))]
        ac_rfl
      rw [hadd] at hle
      have hsub := (tsub_le_iff_right).mpr hle
      rw [← ENNReal.ofReal_sub r (mul_nonneg hr0 (by linarith [hu.1, hw.2]))] at hsub
      have harg : r - r * (u + (1 - w)) = r * (w - u) := by ring
      rwa [harg] at hsub
    have hgoal (u w : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
        riemannianEDistOf g (γ u) (γ w) = ENNReal.ofReal |u - w| * riemannianEDistOf g x y := by
      rcases le_total u w with huw | hwu
      · have harg : ENNReal.ofReal (r * (w - u)) = ENNReal.ofReal |u - w| * riemannianEDistOf g x y := by
          rw [← ENNReal.ofReal_toReal h, ← ENNReal.ofReal_mul (abs_nonneg (u - w))]
          congr 1
          rw [abs_sub_comm (a := u) (b := w), abs_of_nonneg (sub_nonneg.mpr huw)]
          ring
        rw [← harg]
        exact le_antisymm (hup u w huw) (hlow u w hu hw huw)
      · have harg : ENNReal.ofReal (r * (u - w)) = ENNReal.ofReal |u - w| * riemannianEDistOf g x y := by
          rw [← ENNReal.ofReal_toReal h, ← ENNReal.ofReal_mul (abs_nonneg (u - w))]
          congr 1
          rw [abs_of_nonneg (sub_nonneg.mpr hwu)]
          ring
        have hcomm : riemannianEDistOf g (γ u) (γ w) = riemannianEDistOf g (γ w) (γ u) :=
          riemannianEDistOf_comm g (γ u) (γ w)
        rw [hcomm, ← harg]
        exact le_antisymm (hup w u hwu) (hlow w u hw hu hwu)
    rw [hshort s, hshort t]
    exact hgoal s t hs ht

end DifferentialGeometry.Geometry
