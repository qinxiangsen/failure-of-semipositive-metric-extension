import FailureOfSemipositiveMetricExtension.RelativeIncidenceProjPoints

/-! Comparison of the original total space with the points of the genuine global
scheme arising from complex homogeneous coordinates. The topology here is still
the scheme's Zariski topology; no analytification theorem is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Set

/-- Homogeneous evaluation has its exact degree under scalar change. -/
theorem evaluate_smul_of_homogeneous (t c : ℂ) (z : Vector)
    (f : PolynomialRing) {d : ℕ} (hf : IsHomogeneous f d) :
    evaluate t (c • z) f = c ^ d * evaluate t z f := by
  classical
  simp only [evaluate,eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : ∑ i ∈ m.support, m i = d := by
    simpa [IsHomogeneous,IsWeightedHomogeneous,Finsupp.weight_apply,Finsupp.sum] using hf (mem_support_iff.mp hm)
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hmdeg]
  ring

theorem evaluationPrime_eq_of_projective_eq (t : ℂ) (z w : Vector) (hz : z ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk ℂ z hz = Projectivization.mk ℂ w hw) :
    evaluationPrime t z hz = evaluationPrime t w hw := by
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hc0 : c ≠ 0 := by intro h0; rw [h0,zero_smul] at hc; exact hz hc.symm
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d f hf
  rw [mem_evaluationPrime_iff t z hz f hf,mem_evaluationPrime_iff t w hw f hf,← hc,
    evaluate_smul_of_homogeneous t c w f hf]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d hc0))

/-- Equality of the genuine homogeneous primes recovers both the parameter and
all projective coordinates. -/
theorem evaluationPrime_eq_imp (t u : ℂ) (z w : Vector) (hz : z ≠ 0) (hw : w ≠ 0)
    (h : evaluationPrime t z hz = evaluationPrime u w hw) :
    t = u ∧ Projectivization.mk ℂ z hz = Projectivization.mk ℂ w hw := by
  have transfer (f : PolynomialRing) {d : ℕ} (hf : IsHomogeneous f d)
      (he : evaluate t z f = 0) : evaluate u w f = 0 := by
    apply (mem_evaluationPrime_iff u w hw f hf).mp
    rw [← h]
    exact (mem_evaluationPrime_iff t z hz f hf).mpr he
  have ht := transfer (C (Polynomial.X - Polynomial.C t))
    (isHomogeneous_C Index _) (by simp [evaluate])
  have htu : t = u := by simpa [evaluate,sub_eq_zero,eq_comm] using ht
  refine ⟨htu,?_⟩
  have hex : ∃ p, z p ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hz (funext hn)
  obtain ⟨p,hp⟩ := hex
  have hwp : w p ≠ 0 := by
    intro hwp
    have hm := (mem_evaluationPrime_iff u w hw (X p) (isHomogeneous_X Coefficient p)).mpr
      (by simpa [evaluate] using hwp)
    rw [← h] at hm
    exact hp (by simpa [evaluate] using
      (mem_evaluationPrime_iff t z hz (X p) (isHomogeneous_X Coefficient p)).mp hm)
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z p / w p,?_⟩
  ext i
  have hi := transfer (C (Polynomial.C (z p)) * X i - C (Polynomial.C (z i)) * X p)
    (((isHomogeneous_X Coefficient i).C_mul _).sub ((isHomogeneous_X Coefficient p).C_mul _))
    (by simp [evaluate]; ring)
  have hie : z p * w i = z i * w p := by simpa [evaluate,sub_eq_zero] using hi
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [div_mul_eq_mul_div,hie,mul_div_cancel_right₀ _ hwp]

theorem evaluationPrime_eq_iff (t u : ℂ) (z w : Vector) (hz : z ≠ 0) (hw : w ≠ 0) :
    evaluationPrime t z hz = evaluationPrime u w hw ↔
      t = u ∧ Projectivization.mk ℂ z hz = Projectivization.mk ℂ w hw := by
  constructor
  · exact evaluationPrime_eq_imp t u z w hz hw
  · rintro ⟨rfl,h⟩
    exact evaluationPrime_eq_of_projective_eq t z w hz hw h

def totalVector (q : Total) : Vector := tensorVector (blowdown q).rep (fun r => (directions q r).rep)

theorem totalVector_nonzero (q : Total) : totalVector q ≠ 0 :=
  tensorVector_nonzero _ (blowdown q).rep_nonzero _ (fun r => (directions q r).rep_nonzero)

def totalPrime (q : Total) : projectiveScheme :=
  evaluationPrime (projection q) (totalVector q) (totalVector_nonzero q)

theorem totalPrime_mem_range (q : Total) : totalPrime q ∈ range incidenceInclusion.base :=
  (evaluationPrime_mem_range_incidenceInclusion_iff _ _ _).mpr ⟨q,rfl⟩

/-- The actual original total space mapped to the globally glued scheme's points. -/
def toIncidenceScheme (q : Total) : incidenceScheme := (totalPrime_mem_range q).choose

@[simp] theorem toIncidenceScheme_inclusion (q : Total) :
    incidenceInclusion.base (toIncidenceScheme q) = totalPrime q :=
  (totalPrime_mem_range q).choose_spec

theorem toIncidenceScheme_injective : Function.Injective toIncidenceScheme := by
  intro q q' h
  have he := congrArg incidenceInclusion.base h
  simp only [toIncidenceScheme_inclusion] at he
  have ht := evaluationPrime_eq_imp _ _ _ _ _ _ he
  exact relativePoint_injective (Prod.ext ht.2 ht.1)

/-- Points represented by nonzero complex homogeneous coordinates. This is a
subset of actual scheme points, not a replacement definition of a scheme. -/
def homogeneousComplexLocus : Set incidenceScheme :=
  {x | ∃ (t : ℂ) (z : Vector) (hz : z ≠ 0), incidenceInclusion.base x = evaluationPrime t z hz}

theorem range_toIncidenceScheme : range toIncidenceScheme = homogeneousComplexLocus := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨projection q,totalVector q,totalVector_nonzero q,toIncidenceScheme_inclusion q⟩
  · rintro ⟨t,z,hz,hx⟩
    have hr : evaluationPrime t z hz ∈ range incidenceInclusion.base := ⟨x,hx⟩
    obtain ⟨q,hq⟩ := (evaluationPrime_mem_range_incidenceInclusion_iff t z hz).mp hr
    refine ⟨q,incidenceInclusion_injective ?_⟩
    rw [toIncidenceScheme_inclusion,hx]
    apply (evaluationPrime_eq_iff _ _ _ _ _ _).mpr
    exact ⟨congrArg (fun y : Point × ℂ => y.2) hq,congrArg (fun y : Point × ℂ => y.1) hq⟩

/-- A genuine set equivalence onto these complex-coordinate points of the global scheme. -/
def complexPointEquiv : Total ≃ homogeneousComplexLocus :=
  Equiv.ofBijective (fun q => ⟨toIncidenceScheme q,range_toIncidenceScheme ▸ ⟨q,rfl⟩⟩)
    ⟨fun _ _ h => toIncidenceScheme_injective (congrArg Subtype.val h),by
      rintro ⟨x,hx⟩
      obtain ⟨q,hq⟩ := range_toIncidenceScheme.symm ▸ hx
      exact ⟨q,Subtype.ext hq⟩⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
