import DifferentialGeometry.Geometry.Connection.SourceCovariantPartial
import DifferentialGeometry.Geometry.Connection.SourceSectionRestriction
import DifferentialGeometry.Geometry.Metric.ParameterTangentMap

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A normal velocity differentiates the actual induced metric by twice the negative
normal pairing with the second covariant source derivative. -/
theorem hasDerivAt_gramCoefficient_of_normal_velocity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {F : ℝ × A → M} {V : Set (ℝ × A)} (hV : IsOpen V)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) ∞ F V)
    {t₀ : ℝ} {z : A} (hz : (t₀, z) ∈ V)
    (hnormal : ∀ q, (t₀, q) ∈ V → ∀ a : A,
      g.inner (F (t₀, q))
        (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t₀, q) (1, 0))
        (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t₀, q) (0, a)) = 0)
    (v w : A) :
    HasDerivAt
      (fun t => g.inner (F (t, z))
        (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t, z) (0, v))
        (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t, z) (0, w)))
      (-2 * g.inner (F (t₀, z))
        (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t₀, z) (1, 0))
        (sourceCovariantPartial g (fun q => F (t₀, q)) z v w)) t₀ := by
  let P (a : ℝ × A) (p : ℝ × A) : TangentSpace 𝓘(ℝ, E) (F p) :=
    mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F p a
  have hP (a : ℝ × A) : ContMDiffOn 𝓘(ℝ, ℝ × A)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (F p) (P a p)) V :=
    contMDiffOn_source_partial hV hF (m := ∞) (by simp) a
  have hpair (a b : ℝ × A) : ContDiffAt ℝ ∞
      (fun p => g.inner (F p) (P a p) (P b p)) (t₀, z) :=
    ((contDiffOn_sourceSectionPairing g hF (hP a) (hP b)) (t₀, z) hz).contDiffAt
      (hV.mem_nhds hz)
  have hpair_deriv (a b d : ℝ × A) :
      fderiv ℝ (fun p => g.inner (F p) (P a p) (P b p)) (t₀, z) d =
        g.inner (F (t₀, z)) (sourceCovariantPartial g F (t₀, z) d a) (P b (t₀, z)) +
        g.inner (F (t₀, z)) (P a (t₀, z)) (sourceCovariantPartial g F (t₀, z) d b) :=
    fderiv_sourceSectionPairing g hV hF (hP a) (hP b) hz d
  let S : Set A := (fun q : A => (t₀, q)) ⁻¹' V
  have hS : IsOpen S := hV.preimage (continuous_const.prodMk continuous_id)
  have hzS : z ∈ S := hz
  have hspatial (a : A) :
      (fun q => P (0, a) (t₀, q)) =ᶠ[𝓝 z]
        fun q => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun y => F (t₀, y)) q a := by
    filter_upwards [hS.mem_nhds hzS] with q hq
    have hd : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A)) 𝓘(ℝ, E) F (t₀, q) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact ((hF (t₀, q) hq).contMDiffAt (hV.mem_nhds hq)).mdifferentiableAt (by simp)
    have heq := mfderiv_parameter_slice hd a
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at heq
    exact heq.symm
  have hcov_spatial (a b : A) :
      sourceCovariantPartial g F (t₀, z) (0, a) (0, b) =
        sourceCovariantPartial g (fun q => F (t₀, q)) z a b := by
    unfold sourceCovariantPartial
    rw [sourceSectionCovariantDerivative_parameter_slice]
    exact sourceSectionCovariantDerivative_congr g (fun q => F (t₀, q)) (hspatial b) a
  have hnormal_deriv (a b : A) :
      g.inner (F (t₀, z))
        (sourceCovariantPartial g F (t₀, z) (0, a) (1, 0)) (P (0, b) (t₀, z)) =
        -g.inner (F (t₀, z)) (P (1, 0) (t₀, z))
          (sourceCovariantPartial g (fun q => F (t₀, q)) z a b) := by
    let line : ℝ → ℝ × A := fun r => (t₀, z + r • a)
    have hl : HasDerivAt line (0, a) 0 := by
      simpa [line] using (hasDerivAt_const (0 : ℝ) t₀).prodMk
        (((hasDerivAt_id (0 : ℝ)).smul_const a).const_add z)
    have hl₀ : line 0 = (t₀, z) := by simp [line]
    have hd := ((hpair (1, 0) (0, b)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt_of_eq (x := 0) hl hl₀.symm
    have hzero : (fun r => g.inner (F (line r)) (P (1, 0) (line r)) (P (0, b) (line r)))
        =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), line r ∈ V :=
        hl.continuousAt (hV.mem_nhds (by simpa only [hl₀] using hz))
      filter_upwards [hnear] with r hr
      exact hnormal (z + r • a) hr b
    have heq := hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero)
    rw [hpair_deriv, hcov_spatial] at heq
    linarith
  have hswap : sourceCovariantPartial g (fun q => F (t₀, q)) z w v =
      sourceCovariantPartial g (fun q => F (t₀, q)) z v w := by
    rw [← hcov_spatial w v, sourceCovariantPartial_symm g hV hF hz (0, w) (0, v),
      hcov_spatial]
  have htime : HasDerivAt (fun t : ℝ => (t, z)) (1, 0) t₀ :=
    (hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ z)
  have hd := ((hpair (0, v) (0, w)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt t₀ htime
  rw [hpair_deriv,
    sourceCovariantPartial_symm g hV hF hz (1, 0) (0, v),
    sourceCovariantPartial_symm g hV hF hz (1, 0) (0, w),
    hnormal_deriv v w,
    g.symm (F (t₀, z)) (P (0, v) (t₀, z)), hnormal_deriv w v, hswap] at hd
  convert hd using 1
  · rfl
  · dsimp only [P]
    ring

end DifferentialGeometry.Geometry
