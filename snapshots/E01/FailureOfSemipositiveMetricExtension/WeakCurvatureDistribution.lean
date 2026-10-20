import FailureOfSemipositiveMetricExtension.WeakComplexHessian

/-! The real test-function vector space and actual weak Laplacian linear map. -/
namespace FailureOfSemipositiveMetricExtension.WeakComplexHessian
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

def tests (U : Set Coord) : Submodule ℝ (Coord → ℝ) where
  carrier := {f | IsTest U f}
  zero_mem' := by
    refine ⟨contDiff_const,HasCompactSupport.zero,?_⟩
    simp [tsupport]
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,?_⟩
    exact tsupport_add.trans (union_subset hf.2.2 hg.2.2)
  smul_mem' := by
    intro a f hf
    refine ⟨hf.1.const_smul a,?_,?_⟩
    · exact hf.2.1.smul_left (f := fun _ => a)
    · exact (tsupport_smul_subset_right (fun _ => a) f).trans hf.2.2

def weakTraceLinearMap {U : Set Coord} (u : Coord → ℝ)
    (hu : LocallyIntegrableOn u U) : tests U →ₗ[ℝ] ℝ where
  toFun f := weakTrace u f
  map_add' f g := weakTrace_add hu f.property g.property
  map_smul' a f := weakTrace_smul u f.property.1 a

theorem weakDirectional_add {U : Set Coord} {u f g : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) (hg : IsTest U g) (v : Coord) :
    weakDirectional u v (f+g) = weakDirectional u v f + weakDirectional u v g := by
  simp only [weakDirectional,complexLaplacian_add hf.1 hg.1,mul_add]
  rw [integral_add (complexLaplacian_integrable hu hf v) (complexLaplacian_integrable hu hg v)]

theorem weakDirectional_smul {f : Coord → ℝ} (u : Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (v : Coord) :
    weakDirectional u v (a • f) = a * weakDirectional u v f := by
  simp only [weakDirectional,complexLaplacian_smul hf]
  simp_rw [← mul_assoc, mul_comm (u _) a, mul_assoc a]
  rw [integral_const_mul]

def weakDirectionalLinearMap {U : Set Coord} (u : Coord → ℝ)
    (hu : LocallyIntegrableOn u U) (v : Coord) : tests U →ₗ[ℝ] ℝ where
  toFun f := weakDirectional u v f
  map_add' f g := weakDirectional_add hu f.property g.property v
  map_smul' a f := weakDirectional_smul u f.property.1 a v

theorem weakTrace_eq_sum {U : Set Coord} {u f : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) :
    weakTrace u f = (4 * Real.pi)⁻¹ *
      (weakDirectional u (1,0) f + weakDirectional u (0,1) f) := by
  simp only [weakTrace,weakDirectional,laplacian,mul_add]
  rw [integral_add (complexLaplacian_integrable hu hf _) (complexLaplacian_integrable hu hf _)]
  ring

/-- Positivity of all constant complex-direction Hessian distributions, tested
against every nonnegative smooth compactly supported function. -/
def PositiveComplexHessian (u : Coord → ℝ) (U : Set Coord) : Prop :=
  ∀ v f, IsTest U f → (∀ x, 0 ≤ f x) → 0 ≤ weakDirectional u v f

theorem weakTrace_nonnegative {U : Set Coord} {u f : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hp : PositiveComplexHessian u U)
    (hf : IsTest U f) (hn : ∀ x, 0 ≤ f x) : 0 ≤ weakTrace u f := by
  rw [weakTrace_eq_sum hu hf]
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (add_nonneg (hp _ _ hf hn) (hp _ _ hf hn))

/-- Compact-support local-L¹ pairing estimate. -/
theorem integral_mul_bound {U K : Set Coord} {u f g : Coord → ℝ} {B : ℝ}
    (hu : LocallyIntegrableOn u U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : IsTest U f) (hfK : tsupport f ⊆ K) (hg : Continuous g)
    (hs : ∀ x, x ∉ tsupport f → g x = 0) (hB : ∀ x ∈ K, ‖g x‖ ≤ B) :
    ‖∫ x, u x * g x‖ ≤ (∫ x in K, ‖u x‖) * B := by
  have hi := hu.integrableOn_compact_subset hKU hK
  have hig := hi.mul_continuousOn hg.continuousOn hK
  have he : (∫ x in K, u x * g x) = ∫ x, u x * g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have hxf : x ∉ tsupport f := fun h => hx (hfK h)
      simp [hs x hxf]
  rw [← he]
  calc
    _ ≤ ∫ x in K, ‖u x * g x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in K, ‖u x‖ * B := by
      apply integral_mono_ae hig.norm (hi.norm.mul_const B)
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg _)
    _ = _ := integral_mul_const B _

/-- Order-two seminorm control of the actual Euclidean Laplacian. -/
theorem norm_laplacian_le_four (f : Coord → ℝ) (x : Coord) :
    ‖laplacian f x‖ ≤ 4 * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have h (v : Coord) (hv : ‖v‖ ≤ 1) :
      ‖secondDirectional v f x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
    exact (iteratedFDeriv ℝ 2 f x).unit_le_opNorm (by simpa using hv)
  have h1 := h (1,0) (by simp [Prod.norm_def])
  have h2 := h (Complex.I • (1,0)) (by simp [Prod.norm_def])
  have h3 := h (0,1) (by simp [Prod.norm_def])
  have h4 := h (Complex.I • (0,1)) (by simp [Prod.norm_def])
  unfold laplacian complexLaplacian
  calc
    _ ≤ (‖secondDirectional (1,0) f x‖ + ‖secondDirectional (Complex.I • (1,0)) f x‖) +
        (‖secondDirectional (0,1) f x‖ + ‖secondDirectional (Complex.I • (0,1)) f x‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ _ := by linarith

/-- This is the finite-order distribution-continuity estimate, on every fixed
compact subset, with a constant independent of the test function. -/
theorem weakTrace_order_two_bound {U K : Set Coord} {u f : Coord → ℝ} {M : ℝ}
    (hu : LocallyIntegrableOn u U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : IsTest U f) (hfK : tsupport f ⊆ K)
    (hM : ∀ x ∈ K, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) :
    ‖weakTrace u f‖ ≤ (Real.pi⁻¹ * ∫ x in K, ‖u x‖) * M := by
  have hb := integral_mul_bound hu hK hKU hf hfK (laplacian_continuous hf.1)
    (laplacian_eq_zero_of_not_mem_tsupport f)
    (fun x hx => (norm_laplacian_le_four f x).trans (mul_le_mul_of_nonneg_left (hM x hx) (by norm_num)))
  simp only [weakTrace,norm_mul,Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 4 * Real.pi))]
  apply le_trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring_nf
  exact le_rfl

end
end FailureOfSemipositiveMetricExtension.WeakComplexHessian
