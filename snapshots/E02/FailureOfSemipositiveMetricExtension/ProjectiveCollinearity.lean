import FailureOfSemipositiveMetricExtension.ProjectivePlaneFamily

/-! Collinearity in the actual projectivization: the three one-dimensional
subspaces lie in the kernel of one nonzero complex linear functional. -/
namespace FailureOfSemipositiveMetricExtension.ProjectivePlane
noncomputable section
set_option maxHeartbeats 1200000
open Set Coordinates

/-- The projective hyperplane of an actual complex linear equation. -/
def projectiveHyperplane (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) : Set Point :=
  {p | p.submodule ≤ LinearMap.ker f}

@[simp] theorem mk_mem_projectiveHyperplane (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ projectiveHyperplane f ↔ f v = 0 := by
  simp [projectiveHyperplane,Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]

def ProjectivelyCollinear (p q r : Point) : Prop :=
  ∃ f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ, f ≠ 0 ∧ p ∈ projectiveHyperplane f ∧
    q ∈ projectiveHyperplane f ∧ r ∈ projectiveHyperplane f

theorem linear_functional_coordinates (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) (v : Fin 3 → ℂ) :
    f v = v 0 * f p₁ + v 1 * f p₂ + v 2 * f p₄ := by
  have he : v = v 0 • p₁ + v 1 • p₂ + v 2 • p₄ := by
    ext i
    fin_cases i <;> simp [p₁,p₂,p₄]
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul]

theorem linear_functional_eq_zero (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (h1 : f p₁ = 0) (h2 : f p₂ = 0) (h4 : f p₄ = 0) : f = 0 := by
  apply LinearMap.ext
  intro v
  simp only [linear_functional_coordinates f v,h1,h2,h4,mul_zero,add_zero,LinearMap.zero_apply]

theorem central_first_three_projectively_collinear : ProjectivelyCollinear P₁ P₂ (P₃ 0) := by
  let f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 2
  refine ⟨f,?_,?_,?_,?_⟩
  · intro hf
    have h := LinearMap.congr_fun hf p₄
    norm_num [f,p₄,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] at h
  · simp [P₁,f,p₁]
  · simp [P₂,f,p₂]
  · simp [P₃,f,p₃]

/-- All ordered distinct triples of the four actual projective points. -/
theorem nearby_no_three_projectively_collinear (t : ℂ) (ht : t ≠ 0)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ProjectivelyCollinear (centre i t) (centre j t) (centre k t) := by
  rintro ⟨f,hf,hi,hj,hk⟩
  have h3 : f (p₃ t) = f p₁ + f p₂ + t * f p₄ := by
    simpa [p₃] using linear_functional_coordinates f (p₃ t)
  have hvalues : f p₁ = 0 ∧ f p₂ = 0 ∧ f p₄ = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [centre,P₁,P₂,P₃,P₄,mul_eq_zero]
  exact hf (linear_functional_eq_zero f hvalues.1 hvalues.2.1 hvalues.2.2)

end
end FailureOfSemipositiveMetricExtension.ProjectivePlane
