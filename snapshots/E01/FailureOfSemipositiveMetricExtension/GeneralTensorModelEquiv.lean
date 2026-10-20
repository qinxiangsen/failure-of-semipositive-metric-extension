import FailureOfSemipositiveMetricExtension.GeneralCaoFiniteNormInterface
import Mathlib.LinearAlgebra.TensorPower.Basic

/-! The actual mathlib m-fold tensor product of a complex line is identified
with its scalar coordinate model. Tensoring a frame gain acts by its mth power. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open scoped TensorProduct

abbrev ScalarTensorPower (m : ℕ) := TensorPower ℂ m ℂ

def tensorMultiplication (m : ℕ) : ScalarTensorPower m →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift (MultilinearMap.mkPiAlgebra ℂ (Fin m) ℂ)

def tensorUnit (m : ℕ) : ℂ →ₗ[ℂ] ScalarTensorPower m :=
  (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (PiTensorProduct.tprod ℂ (fun _ : Fin m => (1 : ℂ)))

theorem tensor_pure_eq_product (m : ℕ) (v : Fin m → ℂ) :
    PiTensorProduct.tprod ℂ v =
      (∏ k, v k) • PiTensorProduct.tprod ℂ (fun _ : Fin m => (1 : ℂ)) := by
  simpa only [smul_eq_mul,mul_one] using
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin m => ℂ)).map_smul_univ v (fun _ => 1)

@[simp] theorem tensorMultiplication_pure (m : ℕ) (v : Fin m → ℂ) :
    tensorMultiplication m (PiTensorProduct.tprod ℂ v) = ∏ k, v k :=
  PiTensorProduct.lift.tprod _

theorem tensorUnit_leftInverse (m : ℕ) :
    (tensorUnit m).comp (tensorMultiplication m) = LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change tensorUnit m (tensorMultiplication m (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.tprod ℂ v
  rw [tensorMultiplication_pure]
  exact (tensor_pure_eq_product m v).symm

theorem tensorUnit_rightInverse (m : ℕ) (z : ℂ) : tensorMultiplication m (tensorUnit m z) = z := by
  change tensorMultiplication m (z • PiTensorProduct.tprod ℂ (fun _ : Fin m => (1 : ℂ))) = z
  rw [map_smul,tensorMultiplication_pure]
  simp

def scalarTensorEquiv (m : ℕ) : ScalarTensorPower m ≃ₗ[ℂ] ℂ where
  toLinearMap := tensorMultiplication m
  invFun := tensorUnit m
  left_inv x := congrArg (fun f : ScalarTensorPower m →ₗ[ℂ] ScalarTensorPower m => f x) (tensorUnit_leftInverse m)
  right_inv := tensorUnit_rightInverse m

@[simp] theorem scalarTensorEquiv_pure (m : ℕ) (v : Fin m → ℂ) :
    scalarTensorEquiv m (PiTensorProduct.tprod ℂ v) = ∏ k, v k := tensorMultiplication_pure m v

def scalarTensorGain (m : ℕ) (g : ℂ) : ScalarTensorPower m →ₗ[ℂ] ScalarTensorPower m :=
  PiTensorProduct.map (fun _ : Fin m => g • LinearMap.id)

theorem scalarTensorGain_equiv (m : ℕ) (g : ℂ) (x : ScalarTensorPower m) :
    scalarTensorEquiv m (scalarTensorGain m g x) = g^m * scalarTensorEquiv m x := by
  have he : (scalarTensorEquiv m).toLinearMap.comp (scalarTensorGain m g) =
      (g^m) • (scalarTensorEquiv m).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp [scalarTensorGain,PiTensorProduct.map_tprod,Finset.prod_mul_distrib]
  exact congrArg (fun f : ScalarTensorPower m →ₗ[ℂ] ℂ => f x) he

end
end FailureOfSemipositiveMetricExtension.GeneralCao
