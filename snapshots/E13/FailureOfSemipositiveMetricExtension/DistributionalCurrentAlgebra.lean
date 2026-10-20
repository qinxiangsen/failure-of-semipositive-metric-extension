import FailureOfSemipositiveMetricExtension.DistributionalCurrentAtlas

/-! Real linear operations on independent distribution currents, preserving
actual closedness and the full coordinate covariance law. -/
namespace FailureOfSemipositiveMetricExtension.DistributionalCurrent
noncomputable section
open Set
open WeakComplexHessian PshCurvatureCurrentInterface CurrentCoordinateCovariance
variable {M A : Type} [TopologicalSpace M] [ChartedSpace Coord M]
variable {D : CoordinateAtlas M A}

private theorem complexExtension_add (C E : CoefficientField A) (a : A) (j k : Fin 2) (f : Coord → ℂ) :
    complexExtension (fun a j k f => C a j k f + E a j k f) a j k f =
      complexExtension C a j k f + complexExtension E a j k f := by
  unfold complexExtension
  ring

private theorem complexExtension_smul (r : ℝ) (C : CoefficientField A) (a : A) (j k : Fin 2) (f : Coord → ℂ) :
    complexExtension (fun a j k f => (r:ℂ)*C a j k f) a j k f =
      (r:ℂ)*complexExtension C a j k f := by
  unfold complexExtension
  ring

def Current.add (T S : Current D) : Current D where
  coefficient a j k f := T.coefficient a j k f + S.coefficient a j k f
  additive a j k f g hf hg := by rw [T.additive a j k f g hf hg,S.additive a j k f g hf hg]; ring
  homogeneous a j k f hf r := by rw [T.homogeneous a j k f hf r,S.homogeneous a j k f hf r]; ring
  orderTwo a j k K hK hKU := by
    obtain ⟨B,hB,hT⟩ := T.orderTwo a j k K hK hKU
    obtain ⟨C,hC,hS⟩ := S.orderTwo a j k K hK hKU
    refine ⟨B+C,add_nonneg hB hC,?_⟩
    intro f hf hfK R hR h0 h1 h2
    exact (norm_add_le _ _).trans ((add_le_add (hT f hf hfK R hR h0 h1 h2)
      (hS f hf hfK R hR h0 h1 h2)).trans_eq (add_mul _ _ _).symm)
  real a j k f hf := by rw [T.real a j k f hf,S.real a j k f hf,star_add]
  closed_holomorphic a f hf l j k := by
    have hT := T.closed_holomorphic a f hf l j k
    have hS := S.closed_holomorphic a f hf l j k
    linear_combination hT + hS
  closed_antiholomorphic a f hf l j k := by
    have hT := T.closed_antiholomorphic a f hf l j k
    have hS := S.closed_antiholomorphic a f hf l j k
    linear_combination hT + hS
  transported_test := T.transported_test
  compatible a b f hf j k := by
    rw [T.compatible a b f hf j k,S.compatible a b f hf j k]
    simp only [complexExtension_add,Finset.sum_add_distrib]

def Current.smul (r : ℝ) (T : Current D) : Current D where
  coefficient a j k f := (r:ℂ)*T.coefficient a j k f
  additive a j k f g hf hg := by rw [T.additive a j k f g hf hg]; ring
  homogeneous a j k f hf s := by rw [T.homogeneous a j k f hf s]; ring
  orderTwo a j k K hK hKU := by
    obtain ⟨B,hB,hT⟩ := T.orderTwo a j k K hK hKU
    refine ⟨‖(r:ℂ)‖*B,mul_nonneg (norm_nonneg _) hB,?_⟩
    intro f hf hfK R hR h0 h1 h2
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hT f hf hfK R hR h0 h1 h2) (norm_nonneg _)
  real a j k f hf := by simp only [T.real a j k f hf,map_mul,Complex.star_def,Complex.conj_ofReal]
  closed_holomorphic a f hf l j k := by
    have hT := T.closed_holomorphic a f hf l j k
    linear_combination (r:ℂ)*hT
  closed_antiholomorphic a f hf l j k := by
    have hT := T.closed_antiholomorphic a f hf l j k
    linear_combination (r:ℂ)*hT
  transported_test := T.transported_test
  compatible a b f hf j k := by
    rw [T.compatible a b f hf j k]
    simp only [complexExtension_smul,Finset.mul_sum]

@[simp] theorem Current.add_coefficient (T S : Current D) (a : A) (j k : Fin 2) (f : Coord → ℝ) :
    (T.add S).coefficient a j k f = T.coefficient a j k f + S.coefficient a j k f := rfl

@[simp] theorem Current.smul_coefficient (r : ℝ) (T : Current D) (a : A) (j k : Fin 2) (f : Coord → ℝ) :
    (T.smul r).coefficient a j k f = (r:ℂ)*T.coefficient a j k f := rfl

end
end FailureOfSemipositiveMetricExtension.DistributionalCurrent
