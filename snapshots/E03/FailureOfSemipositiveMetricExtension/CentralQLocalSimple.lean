import FailureOfSemipositiveMetricExtension.CentralAuxiliaryZeroSets
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Explicit nonzero transverse derivatives of the actual divided cubic in
all eight charts. These are genuine complex derivatives, not formal labels. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section

def qTransversePath (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) (z : ℂ) : FixedFiber.Coord :=
  if r ≠ 3 ∧ e = 0 then (z,q.2) else (q.1,z)

def qTransverseParameter (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : ℂ :=
  if r ≠ 3 ∧ e = 0 then q.1 else q.2

def qTransverseDerivative (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : ℂ :=
  match r with
  | 0 => if e = 0 then -1 else 1-2*q.1*q.2
  | 1 => if e = 0 then 1 else 2*q.1*q.2-1
  | 2 => if e = 0 then -1 else -1-2*q.1*q.2
  | 3 => if e = 0 then 1-2*q.2 else 2*q.2-1

@[simp] theorem qTransversePath_at_parameter (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    qTransversePath r e q (qTransverseParameter r e q) = q := by
  unfold qTransversePath qTransverseParameter
  split_ifs <;> rfl

theorem qTransversePath_contDiff (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    ContDiff ℂ ω (qTransversePath r e q) := by
  unfold qTransversePath
  split_ifs <;> fun_prop

theorem qLocalCoefficient_transverse_hasDerivAt (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    HasDerivAt (fun z => qLocalCoefficient r e (qTransversePath r e q z))
      (qTransverseDerivative r e q) (qTransverseParameter r e q) := by
  fin_cases r <;> fin_cases e <;>
    norm_num [qLocalCoefficient,qTransversePath,qTransverseDerivative,qTransverseParameter]
  · convert (hasDerivAt_const q.1 (1:ℂ)).sub (hasDerivAt_id q.1) using 1 <;> simp <;> ring
  · convert (hasDerivAt_id q.2).mul ((hasDerivAt_const q.2 (1:ℂ)).sub
      ((hasDerivAt_id q.2).const_mul q.1)) using 1 <;> simp <;> ring
  · exact hasDerivAt_id q.1
  · convert (hasDerivAt_id q.2).mul (((hasDerivAt_id q.2).const_mul q.1).sub_const (1:ℂ)) using 1 <;> simp <;> ring
  · convert (hasDerivAt_const q.1 (-1:ℂ)).sub (hasDerivAt_id q.1) using 1 <;> simp <;> ring
  · convert (hasDerivAt_id q.2).neg.sub (((hasDerivAt_id q.2).pow 2).const_mul q.1) using 1 <;> simp <;> ring
  · convert (hasDerivAt_id q.2).mul ((hasDerivAt_const q.2 (1:ℂ)).sub (hasDerivAt_id q.2)) using 1 <;> simp <;> ring
  · convert (hasDerivAt_id q.2).mul ((hasDerivAt_id q.2).sub_const (1:ℂ)) using 1 <;> simp <;> ring

theorem qTransverseDerivative_ne_zero_at_zero (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : qLocalCoefficient r e q = 0) : qTransverseDerivative r e q ≠ 0 := by
  fin_cases r <;> fin_cases e <;> simp [qLocalCoefficient,qTransverseDerivative] at hq ⊢
  · rcases hq with h | h
    · simp [h]
    · intro hd
      have hh : (1:ℂ) = 0 := by linear_combination 2*h - hd
      exact one_ne_zero hh
  · rcases hq with h | h
    · simp [h]
    · intro hd
      have hh : (1:ℂ) = 0 := by linear_combination hd - 2*h
      exact one_ne_zero hh
  · intro hd
    have hfac : q.2 * (1+q.1*q.2) = 0 := by linear_combination -hq
    rcases mul_eq_zero.mp hfac with h | h
    · simpa [h] using hd
    · have hh : (1:ℂ) = 0 := by linear_combination 2*h + hd
      exact one_ne_zero hh
  · rcases hq with h | h
    · simp [h]
    · have hv : q.2=1 := (sub_eq_zero.mp h).symm
      norm_num [hv]
  · rcases hq with h | h
    · simp [h]
    · have hv : q.2=1 := sub_eq_zero.mp h
      norm_num [hv]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
