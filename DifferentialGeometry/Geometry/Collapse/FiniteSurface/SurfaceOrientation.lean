import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrier
import DifferentialGeometry.Topology.Manifold.AmbientHypersurfaceOrientation
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameRegularity

/-!
# The orientation of the LFR16 surface factor, and LFR17 for it

LFR11's orientation clause in the rank-one 3-dimensional case, on the smooth carrier: an
orientation of `N`, together with the ordered normal factor (the splitting frame `∂_t`), orients
the smooth carrier `S` of the zero factor (`surfaceFactor_smoothCarrier_oriented`). The
orientation is the one for which `(∂_t, positive basis of T S)` is positive in `N`
(`ambientHypersurfaceSmoothOrientation` along `S → Z ⊆ N`). Consequently LFR17 applies with no
further input: `S` is diffeomorphic to `S²`, or to `ℝ²/ℤ²` with the induced metric flat.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Topology.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_orient_F7LFR11b :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u

/-- Re-indexing the dimension of a manifold orientation. -/
def manifoldOrientationCast {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {n m : ℕ} (h : n = m)
    (o : ManifoldOrientation I M n) : ManifoldOrientation I M m :=
  h ▸ o

/-- **LFR11 orientation clause and LFR17 for the LFR16 surface factor.** -/
theorem surfaceFactor_smoothCarrier_oriented {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [ConnectedSpace N]
    [SecondCountableTopology N] [MetricSpace W] [CompactSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompactSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
      ∃ φ : S ≃ₜ {x : N // (e x).fst = 0},
        ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ ∧
        ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
        ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((k + 1 : ℕ) : ℕ∞ω) E2
            (TangentSpace (𝓡 2) : S → Type _),
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x),
            κ.inner x v w = (inducedMetric G hk hnorm e).inner (φ x)
              (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x w)) ∧
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
          (Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
            (Nonempty (S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
              ∀ (x : S) (v w : TangentSpace (𝓡 2) x), κ.sectionalCurvature x v w = 0)) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  obtain ⟨S, mS, cS, iS, hc, hconn, φ, hφ, hφs, κ, hκ, hsecS, hor⟩ :=
    surfaceFactor_smoothCarrier G hk hnorm hsec hD e
  let Z := {x : N // (e x).fst = 0}
  have hk2 : 2 ≤ k := by exact_mod_cast hk
  have h1k : (1 : ℕ∞ω) ≤ ((k + 2 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 1 ≤ k + 2 by omega)
  have h1k' : (1 : ℕ∞ω) ≤ ((k : ℕ∞) : ℕ∞ω) + 2 := le_add_left (by norm_num)
  let f : S → N := Subtype.val ∘ φ
  have hval := contMDiff_splittingFactor_val G hk hnorm e
  have hf : ContMDiff (𝓡 2) (𝓡 3) 1 f := (hval.of_le h1k').comp (hφ.of_le h1k)
  let ν : ∀ x, TangentSpace (𝓡 3) (f x) := fun x => splittingFrame G e (f x) 1
  have hν : Continuous (fun x => (⟨f x, ν x⟩ : TangentBundle (𝓡 3) N)) :=
    (contMDiff_splittingFrame_apply G hk hnorm e).continuous.comp
      (continuous_const.prodMk hf.continuous)
  obtain ⟨-, -, -, hinjι, hrange, -⟩ := exactSplitting_regularity G hk hnorm e
  have hr0 : ((k + 2 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
  have hDφ : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x) := by
    intro x
    have hd := mfderiv_comp x (hφs.mdifferentiableAt hr0 (x := φ x))
      (hφ.mdifferentiableAt hr0 (x := x))
    have hid : (φ.symm : Z → S) ∘ φ = id := funext fun y => φ.symm_apply_apply y
    rw [hid, mfderiv_id] at hd
    intro a b hab
    exact (congrArg (fun L => L a) hd).trans
      ((congrArg (fun y => mfderiv 𝓘(ℝ, P) (𝓡 2) φ.symm (φ x) y) hab).trans
        (congrArg (fun L => L b) hd).symm)
  have hDf : ∀ x (v : TangentSpace (𝓡 2) x), mfderiv (𝓡 2) (𝓡 3) f x v =
      mfderiv 𝓘(ℝ, P) (𝓡 3) (Subtype.val : Z → N) (φ x) (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) := by
    intro x v
    have h := mfderiv_comp x (hval.mdifferentiableAt (by simp) (x := φ x))
      (hφ.mdifferentiableAt hr0 (x := x))
    exact congrArg (fun L => L v) h
  have hfin : Module.finrank ℝ (ℝ × E2) = Module.finrank ℝ E3 := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
  have hbij : ∀ x, Bijective (ambientNormalFrame f ν x) := by
    intro x
    have hinj : Injective (ambientNormalFrame f ν x) := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      rw [ambientNormalFrame_apply] at hw
      let dt : E3 →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E3) (fun y => (e y).fst) (f x)
      have hdtν : dt (ν x : E3) = 1 := mvfderiv_splittingFrame G hk hnorm e (f x) 1
      have hdtD : ∀ v : TangentSpace (𝓡 2) x, dt (mfderiv (𝓡 2) (𝓡 3) f x v : E3) = 0 := by
        intro v
        have hmem0 : mfderiv 𝓘(ℝ, P) (𝓡 3) (Subtype.val : Z → N) (φ x)
            (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) ∈ LinearMap.range
              (mfderiv 𝓘(ℝ, P) (𝓡 3) (Subtype.val : Z → N) (φ x)).toLinearMap := ⟨_, rfl⟩
        rw [hrange (φ x)] at hmem0
        exact (congrArg dt (hDf x v)).trans hmem0
      let v' : TangentSpace (𝓡 2) x := w.2
      let a : E3 := mfderiv (𝓡 2) (𝓡 3) f x v'
      let n : E3 := ν x
      change w.1 • n + a = 0 at hw
      have h0 : dt (w.1 • n + a) = 0 := (congrArg dt hw).trans dt.map_zero
      have hda : dt a = 0 := hdtD v'
      have hdn : dt n = 1 := hdtν
      rw [map_add, map_smul, hdn, hda, smul_eq_mul, mul_one, add_zero] at h0
      have hw' : a = 0 := by
        rw [h0, zero_smul, zero_add] at hw
        exact hw
      have h3 : mfderiv 𝓘(ℝ, P) (𝓡 3) (Subtype.val : Z → N) (φ x)
          (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v') =
          mfderiv 𝓘(ℝ, P) (𝓡 3) (Subtype.val : Z → N) (φ x) 0 :=
        (hDf x v').symm.trans (hw'.trans (map_zero _).symm)
      have h4 : mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v' = 0 :=
        (hinjι (φ x) h3).trans rfl
      have h5 : v' = 0 := hDφ x (h4.trans (map_zero _).symm)
      exact Prod.ext h0 h5
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩
  let oN' : SmoothOrientation (𝓡 3) N :=
    smoothOrientationOfManifoldOrientation (𝓡 3) (manifoldOrientationCast (by simp) oN)
  let oS := ambientHypersurfaceSmoothOrientation f hf ν hν hbij oN'
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) oS
  let O2 : ManifoldOrientation (𝓡 2) S 2 := manifoldOrientationCast (by simp) O
  exact ⟨S, mS, cS, iS, hc, hconn, ⟨O2⟩, φ, hφ, hφs, κ, hκ, hsecS, hor ⟨O2⟩⟩

end DifferentialGeometry.Geometry.Collapse
